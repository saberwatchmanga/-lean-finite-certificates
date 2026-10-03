# Finite Lean Certificates

Two standalone Lean certificates for previously published finite results. The package checks the published matrix witness and two published 4-bit S-box representatives. It claims no new mathematical result and makes no claim of first formalization.

## Results

**Symmetric weighing matrix W(22,16).** The certificate establishes existence of a 22 × 22 symmetric integer matrix with entries in {−1, 0, 1}, with row inner products 16 on the diagonal and 0 off the diagonal (M Mᵀ = 16I). It checks all 484 ordered row pairs and every entry against the alphabet. The witness is transcribed from the cited paper’s Appendix B, Figure 2.

**Two 4-bit S-box representatives, G₀ and G₃.** The Lean certificate proves the ordinary differential maximum is 4 for each. It checks all 140 legal affine planes on each side (19,600 plane pairs) and proves exact raw aggregate maxima 32 for G₀ and 26 for G₃, with witnesses. When zero-containing input planes are included, the maximum normalized aggregate probability is 50% for both. That percentage is contextual finite-count information; the Lean theorem here certifies the raw maxima. These results do not establish optimality over all S-boxes or security of any full cipher.

## Verify

Install Lean 4.34.1 with bundled Std, then run the standard-library-only Python runner:

    py scripts/verify.py


On systems where py is unavailable, use python scripts/verify.py. The runner uses LEAN_BIN when set, otherwise lean from PATH. Set LEAN_BIN to your Lean executable path if Lean is not on PATH, then run py scripts/verify.py.

The runner checks the pinned version, builds each positive certificate from these package files, requires #print axioms reports for all seven named main theorems, rejects axioms outside the standard three, and requires all six damaged controls to fail on their intended false proposition. It runs sequentially with at most two Lean jobs. Fresh logs and build outputs go under .verification-output/; the first package verification is preserved under verification/initial/.

The Lean proofs import only bundled Std; no Mathlib, network access, Python proof dependency, upstream archive, or generated project artifact is required to check them.

## Sources and attribution

- W(22,16): Christopher D. Rosin, “Using Reasoning Models to Generate Search Heuristics that Solve Open Instances of Combinatorial Design Problems,” arXiv:2505.23881v1 (2025), Appendix B, Figure 2: [arXiv record](https://arxiv.org/abs/2505.23881), [version 1 paper](https://arxiv.org/html/2505.23881v1).
- S-box results and representatives: Sondre Rønjom, Arne Sandrib, and Joakim Sunde, “Subspace differential uniformity,” *Cryptography and Communications* 18 (2026), 1831–1860, published 22 May 2026, [DOI 10.1007/s12095-026-00896-w](https://doi.org/10.1007/s12095-026-00896-w). The G₀/G₃ representative data are attributed to the authors’ repository at fixed commit [7fe4f154ef64279ca5ba6b2bf9d4735c7a74dd0f](https://github.com/arnesandrib/subspace_equivalence/tree/7fe4f154ef64279ca5ba6b2bf9d4735c7a74dd0f).

The Lean certificates and verification runner are attributed to the GitHub account terry2418. No upstream source code or paper text is included. This package grants no license; the authors’ publications, repositories, and data retain their own terms.

## 简体中文概览

这是两份对已有公开有限结果的 Lean 证明证书，不主张新数学结果，也不声称首次形式化。

- W(22,16)：给出一个 22×22 对称矩阵，元素只取 −1、0、1；任意两行内积在同一行时为 16，不同行时为 0。Lean 检查全部 484 个有序行对以及矩阵的对称性。
- 4 位 S 盒 G₀、G₃：普通差分计数最大值都为 4。对每侧 140 个合法仿射平面组成的 19,600 对组合，Lean 证明原始总计数最大值分别为 32 和 26，并给出达到最大值的例子。把零所在输入平面也纳入并按输入差分数归一化时，两个代表的最大概率都是 50%；这项归一化数字在此作为有限计数背景，Lean 定理直接证明的是原始计数最大值。

这些 S 盒数字不代表所有 S 盒中的最优性，也不构成整个分组密码安全性的证明。矩阵和 S 盒数据均注明原论文或固定上游提交；本包不含上游代码或论文全文。

