# Lean-verified local minimality for ten charges on a sphere

**Status:** a local minimum in the full space of ten unit-sphere points is proved in Lean.
**Global minimality is not proved by this project.**

The configuration has two polar points and two squares at opposite heights, with the lower square
turned through 45 degrees. The height is a certified real number in
`(42268741/100000000, 42268743/100000000)`, rather than a decimal assumed to be an exact solution.
This is the familiar D4d ten-point Thomson candidate family.

For nearby positions of all ten charges, moving the points on the sphere cannot lower the energy.
The proof allows arbitrary sufficiently small movements, beyond movements that preserve the two
squares. Rotating the whole arrangement preserves energy. Strict increase is separately proved in
the explicit 17-dimensional coordinate slice that removes the three rotation directions.

## Mathematical statements

The energy is

$$E(q)=\sum_{0\leq i<j<10}\frac{1}{\|q_i-q_j\|}.$$

`Thomson10Stability.certified_full_sphere_local_minimum` proves the existence of a height in the
interval above for which the source-defined configuration consists of ten unit-sphere points and
is a local minimum of this energy on all labelled unit-sphere configurations.

`Thomson10Stability.certified_gauged_slice_local_minimum` proves strict increase for every nonzero
sufficiently small perturbation in the gauge-fixed slice. The fixed-height intermediate theorems
have interval and stationarity assumptions; the final existence statements discharge those
assumptions using a certified root. A numerical radius for the neighborhood is not supplied.

See [the full-space theorem](src/FullLocalMinimum.lean), [the strict slice theorem](src/SliceLocalMinimum.lean),
[the configuration](src/GeometryCore.lean), and [the audit entry point](src/Audit.lean).

## Reproduce

Install the toolchain in `lean-toolchain`, Git and Python 3.10 or newer. From this directory:

```text
lake exe cache get
python verify.py
```

The first command obtains upstream Mathlib build artifacts. All dependency revisions are pinned in
`lake-manifest.json`. The verifier checks their actual checkout revisions, the exact Lean version,
source hashes and local import closure. It builds all 183 original project modules from source in
dependency order with one Lean job. Each run has a fresh directory, and previously compiled project
proofs are excluded from its import path. Only the pinned upstream dependency artifacts are reused.

It then checks both main theorem axiom reports and two controls for the actual matrix-certificate
checker. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The verifier also
requires Lean to reject `0=1` and a certificate with one interval endpoint deliberately changed.
It requires the failures to occur at the intended false statements, rather than missing imports.

The [initial fresh-build record](verification/initial-fresh-build.json) records the maintainer's
local run, including all module outcomes, axiom reports and negative-control results.
It does not assert a GitHub CI result. [SHA256SUMS](SHA256SUMS) lists the published file hashes.

Outputs go to `.verification-output/`. `python verify.py --static-only` checks packaging and hashes
without proving the mathematical statements. `lake build` is an additional conventional build
entry point; the sequential verifier is the reproducibility and axiom-audit entry point.

## Provenance and scope

The [Cambridge Thomson database](https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html)
provides the numerical candidate context. The formal configuration and exact height certificate
are defined in this package. Numerical coordinates are not used as an unproved hypothesis.

The proof sources and verification tooling were developed with AI assistance. The release is
maintained by the GitHub account `saberwatchmanga` (formerly `terry2418`). It claims neither a new
global solution nor first formalization. Public source statements, dependencies and executable
checks are supplied so readers can independently inspect the formalization.

The scope of this package is the completed local result. The research project's unfinished global
branches, experimental search data, prompts and private research notes are outside this release.
Other Thomson formalizations include the [N=7 project](https://github.com/huwngtran/thomson-n7-lean)
and [N=8 warrant](https://github.com/jstoobysmith/Thomson-N-8-Warrant).

The [MIT license](LICENSE) applies to this subproject's original formalization and verification
code. Lean, Mathlib and cited upstream materials retain their own licenses and attribution.
This subproject's license does not change the terms of the repository's other projects.

## 简体中文

这份成果证明：存在一个经过精确认证的十电荷构型，附近任意足够小的球面移动都不能降低能量。
它包含两个极点，以及上下两组相错45度的正方形。允许每个电荷独立移动，没有把变化限制为保持
对称形状。整体旋转会保持能量；排除旋转自由度后，证明了非零小扰动使能量严格增加。

它还没有证明这个构型在整个球面配置空间中能量最低，也没有给出“足够小”的明确数值半径。
本包提供完整证明源码、固定依赖、逐项检查工具和故意损坏数据的对照。
