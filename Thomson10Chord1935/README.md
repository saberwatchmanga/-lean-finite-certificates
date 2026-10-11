# A Lean-checked distance restriction for ten charges on a sphere

**Verified release:** all 237 project modules were rebuilt from source in an initially
empty project build directory, with hash-checked resumption. The three final theorem
axiom audits passed, and both deliberately damaged statements were rejected.**
**Global minimality is not proved.**

For ten pairwise distinct points on a sphere of radius one, let

    E(q) = sum over i < j of 1 / distance(q_i, q_j).

The energy is normalized: the sphere radius and the Coulomb prefactor are both one.
Distance means Euclidean distance between the points, also called chord distance.
If all 45 distances are at most 387/200 (1.935), then E(q) > 32717/1000 (32.717).
Equivalently, E(q) <= 32.717 requires at least one pair farther apart than 1.935.
The sphere's diameter is 2. This rules out a family of competing arrangements;
it does not identify the best arrangement among all ten-point configurations.

The [Cambridge Cluster Database](https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html)
reports a numerical ten-point candidate with energy about 32.71695, below 32.717.
This is numerical context for the threshold, rather than a certified upper bound in
this package. For configurations with energy at most 32.717, this result strengthens
the earlier necessary pair-distance condition from greater than 1.90 to greater than
1.935. The formal conclusion retains its explicit energy premise.

The final statements, including distinctness and unit-sphere assumptions, are in
[M36Chord1935Exclusion.lean](src/M36Chord1935Exclusion.lean).
All finite computations are checked by Lean's kernel. The final theorem's permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Use the pinned toolchain and dependencies, Git, and Python 3.10 or later:

```text
lake exe cache get
python verify.py --package-root . --seconds 16200
```

The verifier checks revisions, source hashes and import closure, then compiles every
project module from source sequentially in a fresh directory. Only pinned upstream
library artifacts are reused. It audits the three final theorem reports and requires
two deliberately damaged statements to fail at the intended proof goals.

`--static-only` checks packaging only and does not prove the theorem. A stopped build
can be resumed with `--resume .verification-output/<run-id>`; source, artifact and log
hashes must still match. The command above permits 4.5 hours; each individual command
is limited to ten minutes. The per-invocation default is 85 minutes. Prior checked steps
are retained. Local maintainers may set `MATHLIB_DIR` to the existing pinned Mathlib
checkout and `LEAN_BIN` / `LAKE_BIN` to the corresponding executables.

## Scope and provenance

This is a stage result in an AI-assisted Thomson N=10 project, maintained by
`saberwatchmanga` (formerly `terry2418`). It makes no claim of first formalization or
a complete global solution. The published certificate and proof sources establish
only the statements above. Unfinished global search methods and research notes are
outside this release. Dependency versions are fixed in the included manifests.
