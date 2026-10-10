# Official Lean installation: observed denial versus requested access

The **confirmed executor denial** is:

```
https://elan.lean-lang.org/elan-init.sh
curl: (56) CONNECT tunnel failed, response 403
HTTP/1.1 403 Forbidden
server: envoy
```

Domain: **`elan.lean-lang.org`**. The GET also returned HTTP 403. Evidence is
`/workspace/toolchains/logs/lean-download.txt`. Installation stopped at this
step; no mirror, proxy workaround or security-setting change was attempted.

GitHub access is not uniformly absent: cloning the pinned public
`https://github.com/solving-bitcoin/bitcoin-scripts.git` succeeded. Web retrieval
of GitHub documentation also succeeded, but that uses a different tool and does
not establish executor download access. **No denial of a Lean GitHub release
asset has yet been observed**, because installation did not reach that stage.
It would be inaccurate to report GitHub's asset URLs as already denied.

After permitted access is enabled, the official Elan path uses these download
locations (the latter two are installation requirements to verify, not observed
denials):

- Bootstrap script: `https://elan.lean-lang.org/elan-init.sh`
- Elan Linux x86-64 asset:
  `https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz`
- Pinned Lean release: `https://github.com/leanprover/lean4/releases/tag/v4.33.1`
  and its Linux x86-64 binary asset, conventionally
  `https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst`.
  GitHub may redirect binary assets to `release-assets.githubusercontent.com`;
  the exact redirect must be observed during a permitted installation.

Sources: [official Elan installer source](https://github.com/leanprover/elan/blob/master/elan-init.sh)
and [Lean v4.33.1 release](https://github.com/leanprover/lean4/releases/tag/v4.33.1).
Allowing GitHub alone may leave the already-denied bootstrap host blocked.
The environment must explicitly permit the official install path; no workaround
is being used while the user arranges access.

Separately, the paper PDF request to `https://eprint.iacr.org/2026/1684.pdf`
returned HTTP 403. This is not a Lean dependency. Its HTML abstract was readable;
the unavailable PDF's proof details have not been represented as inspected.
