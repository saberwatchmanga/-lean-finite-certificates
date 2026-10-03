# Initial package verification

Run command: py scripts/verify.py from the package root, with LEAN_BIN set to the installed Lean 4.34.1 executable.

Result: PASS on 2026-10-03 UTC with Lean 4.34.1 release, commit 5045d0056413266e57c625dcd7c365b10e377c52. The current package runner built the packaged matrix theorem, S-box data module, and S-box certificate in 14.760 s, 6.404 s, and 159.678 s. All builds used two Lean jobs and bundled Std only. Total elapsed time was 226.079 s.

The runner explicitly required and found all seven axiom reports: Weighing22.certificate, Weighing22.exists_symmetric_weighing_22_16, Sbox.planes_complete, Sbox.G0_exact_plane_maximum, Sbox.G3_exact_plane_maximum, Sbox.same_single_difference_maximum, and Sbox.structured_difference_comparison. The only observed axioms were propext, Classical.choice, and Quot.sound; no positive build reported sorryAx.

All six original damaged controls were rejected. Each output contains Lean's decide false-proposition diagnostic and the intended false proposition. Individual results and exact commands are in summary.json; full output is in logs/.

The negative-control logs may show sorryAx after a rejected declaration because Lean continues error recovery in those intentionally invalid files. This does not occur in any positive certificate.

The normalized 50% S-box figure is contextual finite-count information. The Lean theorem in this package certifies ordinary differential maximum 4 and raw affine-plane maxima 32 and 26; it does not state a theorem about normalized probability.

The nine original Lean files copied into this package are byte-identical to their project sources. Their SHA-256 values are in source-hashes.txt. The portable runner writes future builds under the git-ignored .verification-output/ directory.
