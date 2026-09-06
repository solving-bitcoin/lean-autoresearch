import json
from pathlib import Path

def summarize(project, destination):
    config=json.loads((project/'challenge.json').read_text())
    r=json.loads((project/'.yukon'/config['report']).read_text())
    size='No accepted size' if r['score'] is None else f"Accepted bound: {r['score']:,} bytes"
    text=(f"### {r['bundle']['challenge']}\n\n"
          f"**{r['status']}** · Candidate: **{r['candidateStatus']}** · {size}.\n\n"
          "Four generated tools: `garble`, `encode`, `evaluate`, `challenge`. "
          "Independent Rust reference and binary pipeline checks passed.\n\n"
          f"Build peak: {r['compilerPeakMemoryBytes']/2**20:.1f} MiB; "
          f"native peak: {r['nativePeakMemoryBytes']/2**20:.1f} MiB. "
          "Caps: 8192 MiB CI / 4096 MiB local builds; 1024 MiB native.\n\n"
          "Kernel certificate and size are separate from executable test results. "
          "SHA-256 instantiation of the ideal ROM remains heuristic / unproved.\n")
    for name in ('fixture','submission'):
        run=r['native'][name]
        observed=run['observedArtifactBytes']
        if observed is not None:
            text+=f"\n{name.capitalize()}: {run['pipelineCases']} complete pipelines; **{observed:,} measured artifact bytes**.\n"
    text+=f"\nTool bundle: {r['bundle']['installedBytes']:,} installed bytes; {r['bundle']['unpackedToolBytes']:,} bytes across all four files.\n"
    with destination.open('a') as stream: stream.write(text)
