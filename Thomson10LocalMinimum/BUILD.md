# Build and audit

Install Lean 4.34.1, Git and Python 3.10+. From this directory run:

```text
lake exe cache get
python verify.py
```

The manifest fixes Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` and fixes all inherited
upstream dependency revisions. The cache command supplies upstream compiled dependencies.
The verifier rebuilds 183 local modules in a fresh directory using one Lean job, then compiles
the matrix-witness controls and audit entry point. It does not reuse compiled project proofs.

`python verify.py --static-only` checks source hashes, local imports and dependency order only.
`lake build` is also available through the declared default library target.

Each compiler command has a 600-second cap. Verification defaults to a two-hour cumulative cap.
`THOMSON_VERIFY_TOTAL_SECONDS` can select a cumulative budget between 60 and 7200 seconds.
The initial Windows rebuild and CI use this ceiling. `LAKE_BIN`, `LEAN_BIN` and
`GIT_BIN` can select installed tools without changing global configuration. Checks and logs are
written to a new `.verification-output/` directory on each run.

An interrupted run may be continued with `python continue_verify.py .verification-output/RUN_NAME`.
This uses only the successful, dependency-ordered prefix of your own interrupted fresh build,
rechecks sources and dependency revisions, and retains the original failed-attempt logs.
The cumulative configured time budget is preserved. The default `python verify.py` and CI
always start a new source rebuild. No compiled project artifacts are shipped in this package.

The main theorem gives a local minimum in the full unit-sphere configuration space. Strict increase is stated and proved only in the explicit gauge-fixed slice; rotationally equivalent configurations have equal energy.
