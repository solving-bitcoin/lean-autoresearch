//! File-based access to generated SecretRelease tools. Seeded fixtures are
//! test data, never production key generation or a proof of uniform sampling.
//! Run test executables via scripts/test_rust.py for aggregate RSS/disk caps.
use serde_json::Value;
use std::io::Write;
use sha2::{Digest, Sha256};
use std::{fs, path::{Path, PathBuf}, process::{Command, Stdio}, thread, time::{Duration, Instant}};
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

pub struct Bundle { directory: PathBuf, pub metadata: Value }
pub struct Fixture {
    pub private: Vec<u8>, pub input: Vec<u8>, pub coins: Vec<u8>,
    pub input_keys: Vec<u8>, pub output_keys: Vec<u8>,
}
pub struct Evaluation { pub artifact: Vec<u8>, pub known: Vec<u8>, pub active: Vec<u8>, pub output: Vec<u8> }

fn equal(actual: &[u8], expected: &[u8], what: &str) -> Result<()> {
    if actual != expected { return Err(format!("{what} mismatch ({} versus {} bytes)", actual.len(), expected.len()).into()); }
    Ok(())
}
fn hex(bytes: &[u8]) -> String { bytes.iter().map(|x| format!("{x:02x}")).collect() }

impl Bundle {
    pub fn from_env() -> Result<Self> { Self::open(std::env::var("SECRET_RELEASE_BUNDLE")?) }
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let directory = path.as_ref().canonicalize()?;
        let metadata: Value = serde_json::from_slice(&fs::read(directory.join("bundle.json"))?)?;
        if metadata["wireVersion"] != 1 { return Err("unsupported wire version".into()); }
        for name in ["garble", "encode", "evaluate", "challenge"] {
            let binary = fs::read(directory.join(name))?;
            if metadata["tools"][name]["sha256"] != hex(&Sha256::digest(&binary)) {
                return Err(format!("{name} binary digest mismatch").into());
            }
        }
        Ok(Self { directory, metadata })
    }
    pub fn has_candidate(&self) -> bool { self.metadata["status"] != "missing" }

    /// Each argument is a separate OS argument; never invoke a shell. Child
    /// output goes to bounded files, avoiding pipe deadlock and unbounded RAM.
    pub fn call(&self, tool: &str, commands: &[&str], inputs: &[&[u8]], output_count: usize) -> Result<Vec<Vec<u8>>> {
        if !["garble", "encode", "evaluate", "challenge"].contains(&tool) { return Err("unknown tool".into()); }
        let state = std::env::current_dir()?.join(".yukon");
        fs::create_dir_all(&state)?;
        let temp = tempfile::tempdir_in(state)?;
        let mut command = Command::new(self.directory.join(tool));
        command.args(commands).stdin(Stdio::null());
        for (i, bytes) in inputs.iter().enumerate() {
            let path = temp.path().join(format!("in-{i}")); fs::write(&path, bytes)?; command.arg(path);
        }
        let outputs: Vec<_> = (0..output_count).map(|i| temp.path().join(format!("out-{i}"))).collect();
        command.args(&outputs);
        let stdout = temp.path().join("stdout"); let stderr = temp.path().join("stderr");
        command.stdout(fs::File::create(&stdout)?).stderr(fs::File::create(&stderr)?);
        let mut child = command.spawn()?;
        let start = Instant::now();
        let status = loop {
            if let Some(status) = child.try_wait()? { break status; }
            if start.elapsed() > Duration::from_secs(60) ||
                [&stdout, &stderr].iter().any(|p| fs::metadata(p).map(|m| m.len() > 16*1024*1024).unwrap_or(false)) {
                child.kill()?; child.wait()?; return Err("tool timeout or excessive side output".into());
            }
            thread::sleep(Duration::from_millis(10));
        };
        if [&stdout, &stderr].iter().any(|p| fs::metadata(p).map(|m| m.len() > 16*1024*1024).unwrap_or(true)) {
            return Err("excessive or unreadable side output".into());
        }
        if !status.success() {
            return Err(format!("{tool} {commands:?} failed: {}", String::from_utf8_lossy(&fs::read(stderr)?)).into());
        }
        outputs.iter().map(|p| {
            if fs::metadata(p)?.len() > 256*1024*1024 { return Err("SDK output exceeds 256 MiB read limit".into()); }
            Ok(fs::read(p)?)
        }).collect()
    }
    pub fn reference(&self, private: &[u8], input: &[u8]) -> Result<Vec<u8>> {
        Ok(self.call("challenge", &["reference"], &[private, input], 1)?.remove(0))
    }
    pub fn roundtrip(&self, kind: &str, bytes: &[u8]) -> Result<Vec<u8>> {
        Ok(self.call("challenge", &["roundtrip", kind], &[bytes], 1)?.remove(0))
    }
    pub fn test_fixture(&self, private: &[u8], input: &[u8], seed: u64) -> Result<Fixture> {
        Ok(Fixture { private: private.to_vec(), input: input.to_vec(),
            coins: test_bytes(seed, b"coins", self.metadata["randomnessBytes"].as_u64().unwrap_or(0) as usize),
            input_keys: fixture_keys(&self.metadata["inputKeys"], seed, b"input")?,
            output_keys: fixture_keys(&self.metadata["outputKeys"], seed, b"output")? })
    }
    pub fn evaluate(&self, f: &Fixture) -> Result<Evaluation> {
        if !self.has_candidate() { return Err("no candidate implementation".into()); }
        let artifact = self.call("garble", &[], &[&f.coins, &f.private, &f.input_keys, &f.output_keys], 1)?.remove(0);
        let mut encoded = self.call("encode", &[], &[&f.input, &f.input_keys], 2)?;
        let active = encoded.pop().unwrap(); let known = encoded.pop().unwrap();
        equal(&known, &f.input, "known input channel")?;
        let output = self.call("evaluate", &[], &[&artifact, &known, &active], 1)?.remove(0);
        if artifact.len() as u64 > self.metadata["claimedBytes"].as_u64().ok_or("missing bound")? {
            return Err("artifact exceeds declared size".into());
        }
        if let Ok(path) = std::env::var("SECRET_RELEASE_METRICS_FILE") {
            let mut stream = fs::OpenOptions::new().create(true).append(true).open(path)?;
            writeln!(stream, "{}", serde_json::json!({"artifactBytes":artifact.len(),
                "knownInputBytes":known.len(),"activeInputBytes":active.len(),"releasedOutputBytes":output.len()}))?;
        }
        Ok(Evaluation { artifact, known, active, output })
    }
    pub fn assert_case(&self, f: &Fixture, expected: &[u8]) -> Result<Evaluation> {
        equal(&self.reference(&f.private, &f.input)?, expected, "independent reference")?;
        let selected = self.call("challenge", &["release"], &[expected, &f.output_keys], 1)?.remove(0);
        if let Some(independent) = selected_labels(&self.metadata["outputKeys"], expected, &f.output_keys)? {
            equal(&selected, &independent, "output disclosure selection")?;
        }
        let run = self.assert_released(f, &selected)?;
        if let Some(independent) = selected_labels(&self.metadata["inputKeys"], &f.input, &f.input_keys)? {
            equal(&run.active, &independent, "input disclosure selection")?;
        }
        Ok(run)
    }
    /// Custom output types without a full-value codec can supply expected
    /// released bytes directly. They are not forced into a built-in enum.
    pub fn assert_released(&self, f: &Fixture, expected: &[u8]) -> Result<Evaluation> {
        let run = self.evaluate(f)?; equal(&run.output, expected, "released output")?; Ok(run)
    }
    pub fn check_sha256(&self) -> Result<()> {
        for n in [0, 3, 55, 56, 63, 64, 65, 127, 128, 256, 1024] {
            let raw = test_bytes(7, b"sha-vector", n);
            let hash = self.call("challenge", &["sha256"], &[&raw], 1)?.remove(0);
            equal(&hash, &Sha256::digest(&raw), "C SHA-256")?;
        }
        Ok(())
    }
}

pub fn test_bytes(seed: u64, domain: &[u8], n: usize) -> Vec<u8> {
    (0..n.div_ceil(32)).flat_map(|i| {
        let mut h = Sha256::new(); h.update(b"SecretRelease test fixture v1");
        h.update(seed.to_le_bytes()); h.update(domain); h.update((i as u64).to_le_bytes()); h.finalize().to_vec()
    }).take(n).collect()
}
fn fixture_keys(meta: &Value, seed: u64, domain: &[u8]) -> Result<Vec<u8>> {
    let n = meta["count"].as_u64().ok_or("missing key count")? as usize;
    let count = match meta["kind"].as_str() {
        Some("lamport") => n*2, Some("hors" | "ones-only" | "preimage") => n,
        Some("plain") => 0, _ => return Err("custom disclosure: supply Fixture keys explicitly".into()),
    };
    let bytes = test_bytes(seed, domain, count*32);
    if meta["kind"] == "lamport" && bytes.chunks_exact(64).any(|p| p[..32] == p[32..]) {
        return Err("test fixture contains equal pair; choose another seed".into());
    }
    Ok(bytes)
}
/// Independent selection for standard bit disclosures; hash-dependent/custom
/// selectors remain author-defined and are exercised through the Lean adapter.
pub fn selected_labels(meta: &Value, input: &[u8], keys: &[u8]) -> Result<Option<Vec<u8>>> {
    let n = meta["count"].as_u64().ok_or("missing key count")? as usize;
    let kind = meta["kind"].as_str().ok_or("missing key kind")?;
    if kind == "plain" { return Ok(Some(input.to_vec())); }
    if !["lamport", "ones-only"].contains(&kind) { return Ok(None); }
    if input.len()*8 < n || keys.len() != n*32*if kind == "lamport" {2} else {1} {
        return Err("invalid bit/key shape".into());
    }
    let mut out = Vec::new();
    for i in 0..n {
        let bit = (input[i/8] >> (i%8)) & 1;
        if kind == "lamport" || bit == 1 {
            let index = if kind == "lamport" { 2*i + bit as usize } else { i };
            out.extend_from_slice(&keys[index*32..(index+1)*32]);
        }
    }
    Ok(Some(out))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn bit_order_and_ones_only() -> Result<()> {
        let keys: Vec<_> = (0..4).flat_map(|i| vec![i;32]).collect();
        assert_eq!(selected_labels(&serde_json::json!({"kind":"lamport","count":2}), &[1], &keys)?.unwrap(), [vec![1;32],vec![2;32]].concat());
        assert_eq!(selected_labels(&serde_json::json!({"kind":"ones-only","count":2}), &[2], &keys[..64])?.unwrap(), vec![1;32]);
        assert!(selected_labels(&serde_json::json!({"kind":"lamport","count":2}), &[], &keys).is_err());
        Ok(())
    }
}
