import IndexedDagEvaluation
import IndexedMatrixBlock00
import IndexedMatrixBlock01
import IndexedMatrixBlock02
import IndexedMatrixBlock03
import IndexedMatrixBlock04
import IndexedMatrixBlock05
import IndexedMatrixBlock06
import IndexedMatrixBlock07
import IndexedMatrixBlock08
import IndexedMatrixBlock09
import IndexedMatrixBlock10
import IndexedMatrixBlock11
import IndexedMatrixBlock12
import IndexedMatrixBlock13
import IndexedMatrixBlock14
import IndexedMatrixBlock15
import IndexedMatrixBlock16
import IndexedMatrixBlock17
import IndexedMatrixBlock18
import IndexedMatrixBlock19
import IndexedMatrixBlock20
import IndexedMatrixBlock21
import IndexedMatrixBlock22
import IndexedMatrixBlock23
import IndexedMatrixBlock24
import IndexedMatrixBlock25
import IndexedMatrixBlock26
import IndexedMatrixBlock27
import IndexedMatrixBlock28
import IndexedMatrixBlock29

namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
open Thomson10Intervals (Contains)
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem all_matrix_nodes_checked (i : Nat) (hi : i < matrixNodeCount) :
    certifiedNode matrixHeightBounds matrixBounds matrixProgram i = true := by
  change i < 7440 at hi
  by_cases h0 : i < 256
  ·
    have hs : i - 0 < 256 := by omega
    have he : 0 + (i - 0) = i := by omega
    have hc := IndexedMatrixBlock00_checks ⟨i - 0, hs⟩
    change certifiedNode matrixHeightBounds matrixBounds matrixProgram (0 + (i - 0)) = true at hc
    rw [he] at hc
    exact hc
  ·
    by_cases h1 : i < 512
    ·
      have hs : i - 256 < 256 := by omega
      have he : 256 + (i - 256) = i := by omega
      have hc := IndexedMatrixBlock01_checks ⟨i - 256, hs⟩
      change certifiedNode matrixHeightBounds matrixBounds matrixProgram (256 + (i - 256)) = true at hc
      rw [he] at hc
      exact hc
    ·
      by_cases h2 : i < 768
      ·
        have hs : i - 512 < 256 := by omega
        have he : 512 + (i - 512) = i := by omega
        have hc := IndexedMatrixBlock02_checks ⟨i - 512, hs⟩
        change certifiedNode matrixHeightBounds matrixBounds matrixProgram (512 + (i - 512)) = true at hc
        rw [he] at hc
        exact hc
      ·
        by_cases h3 : i < 1024
        ·
          have hs : i - 768 < 256 := by omega
          have he : 768 + (i - 768) = i := by omega
          have hc := IndexedMatrixBlock03_checks ⟨i - 768, hs⟩
          change certifiedNode matrixHeightBounds matrixBounds matrixProgram (768 + (i - 768)) = true at hc
          rw [he] at hc
          exact hc
        ·
          by_cases h4 : i < 1280
          ·
            have hs : i - 1024 < 256 := by omega
            have he : 1024 + (i - 1024) = i := by omega
            have hc := IndexedMatrixBlock04_checks ⟨i - 1024, hs⟩
            change certifiedNode matrixHeightBounds matrixBounds matrixProgram (1024 + (i - 1024)) = true at hc
            rw [he] at hc
            exact hc
          ·
            by_cases h5 : i < 1536
            ·
              have hs : i - 1280 < 256 := by omega
              have he : 1280 + (i - 1280) = i := by omega
              have hc := IndexedMatrixBlock05_checks ⟨i - 1280, hs⟩
              change certifiedNode matrixHeightBounds matrixBounds matrixProgram (1280 + (i - 1280)) = true at hc
              rw [he] at hc
              exact hc
            ·
              by_cases h6 : i < 1792
              ·
                have hs : i - 1536 < 256 := by omega
                have he : 1536 + (i - 1536) = i := by omega
                have hc := IndexedMatrixBlock06_checks ⟨i - 1536, hs⟩
                change certifiedNode matrixHeightBounds matrixBounds matrixProgram (1536 + (i - 1536)) = true at hc
                rw [he] at hc
                exact hc
              ·
                by_cases h7 : i < 2048
                ·
                  have hs : i - 1792 < 256 := by omega
                  have he : 1792 + (i - 1792) = i := by omega
                  have hc := IndexedMatrixBlock07_checks ⟨i - 1792, hs⟩
                  change certifiedNode matrixHeightBounds matrixBounds matrixProgram (1792 + (i - 1792)) = true at hc
                  rw [he] at hc
                  exact hc
                ·
                  by_cases h8 : i < 2304
                  ·
                    have hs : i - 2048 < 256 := by omega
                    have he : 2048 + (i - 2048) = i := by omega
                    have hc := IndexedMatrixBlock08_checks ⟨i - 2048, hs⟩
                    change certifiedNode matrixHeightBounds matrixBounds matrixProgram (2048 + (i - 2048)) = true at hc
                    rw [he] at hc
                    exact hc
                  ·
                    by_cases h9 : i < 2560
                    ·
                      have hs : i - 2304 < 256 := by omega
                      have he : 2304 + (i - 2304) = i := by omega
                      have hc := IndexedMatrixBlock09_checks ⟨i - 2304, hs⟩
                      change certifiedNode matrixHeightBounds matrixBounds matrixProgram (2304 + (i - 2304)) = true at hc
                      rw [he] at hc
                      exact hc
                    ·
                      by_cases h10 : i < 2816
                      ·
                        have hs : i - 2560 < 256 := by omega
                        have he : 2560 + (i - 2560) = i := by omega
                        have hc := IndexedMatrixBlock10_checks ⟨i - 2560, hs⟩
                        change certifiedNode matrixHeightBounds matrixBounds matrixProgram (2560 + (i - 2560)) = true at hc
                        rw [he] at hc
                        exact hc
                      ·
                        by_cases h11 : i < 3072
                        ·
                          have hs : i - 2816 < 256 := by omega
                          have he : 2816 + (i - 2816) = i := by omega
                          have hc := IndexedMatrixBlock11_checks ⟨i - 2816, hs⟩
                          change certifiedNode matrixHeightBounds matrixBounds matrixProgram (2816 + (i - 2816)) = true at hc
                          rw [he] at hc
                          exact hc
                        ·
                          by_cases h12 : i < 3328
                          ·
                            have hs : i - 3072 < 256 := by omega
                            have he : 3072 + (i - 3072) = i := by omega
                            have hc := IndexedMatrixBlock12_checks ⟨i - 3072, hs⟩
                            change certifiedNode matrixHeightBounds matrixBounds matrixProgram (3072 + (i - 3072)) = true at hc
                            rw [he] at hc
                            exact hc
                          ·
                            by_cases h13 : i < 3584
                            ·
                              have hs : i - 3328 < 256 := by omega
                              have he : 3328 + (i - 3328) = i := by omega
                              have hc := IndexedMatrixBlock13_checks ⟨i - 3328, hs⟩
                              change certifiedNode matrixHeightBounds matrixBounds matrixProgram (3328 + (i - 3328)) = true at hc
                              rw [he] at hc
                              exact hc
                            ·
                              by_cases h14 : i < 3840
                              ·
                                have hs : i - 3584 < 256 := by omega
                                have he : 3584 + (i - 3584) = i := by omega
                                have hc := IndexedMatrixBlock14_checks ⟨i - 3584, hs⟩
                                change certifiedNode matrixHeightBounds matrixBounds matrixProgram (3584 + (i - 3584)) = true at hc
                                rw [he] at hc
                                exact hc
                              ·
                                by_cases h15 : i < 4096
                                ·
                                  have hs : i - 3840 < 256 := by omega
                                  have he : 3840 + (i - 3840) = i := by omega
                                  have hc := IndexedMatrixBlock15_checks ⟨i - 3840, hs⟩
                                  change certifiedNode matrixHeightBounds matrixBounds matrixProgram (3840 + (i - 3840)) = true at hc
                                  rw [he] at hc
                                  exact hc
                                ·
                                  by_cases h16 : i < 4352
                                  ·
                                    have hs : i - 4096 < 256 := by omega
                                    have he : 4096 + (i - 4096) = i := by omega
                                    have hc := IndexedMatrixBlock16_checks ⟨i - 4096, hs⟩
                                    change certifiedNode matrixHeightBounds matrixBounds matrixProgram (4096 + (i - 4096)) = true at hc
                                    rw [he] at hc
                                    exact hc
                                  ·
                                    by_cases h17 : i < 4608
                                    ·
                                      have hs : i - 4352 < 256 := by omega
                                      have he : 4352 + (i - 4352) = i := by omega
                                      have hc := IndexedMatrixBlock17_checks ⟨i - 4352, hs⟩
                                      change certifiedNode matrixHeightBounds matrixBounds matrixProgram (4352 + (i - 4352)) = true at hc
                                      rw [he] at hc
                                      exact hc
                                    ·
                                      by_cases h18 : i < 4864
                                      ·
                                        have hs : i - 4608 < 256 := by omega
                                        have he : 4608 + (i - 4608) = i := by omega
                                        have hc := IndexedMatrixBlock18_checks ⟨i - 4608, hs⟩
                                        change certifiedNode matrixHeightBounds matrixBounds matrixProgram (4608 + (i - 4608)) = true at hc
                                        rw [he] at hc
                                        exact hc
                                      ·
                                        by_cases h19 : i < 5120
                                        ·
                                          have hs : i - 4864 < 256 := by omega
                                          have he : 4864 + (i - 4864) = i := by omega
                                          have hc := IndexedMatrixBlock19_checks ⟨i - 4864, hs⟩
                                          change certifiedNode matrixHeightBounds matrixBounds matrixProgram (4864 + (i - 4864)) = true at hc
                                          rw [he] at hc
                                          exact hc
                                        ·
                                          by_cases h20 : i < 5376
                                          ·
                                            have hs : i - 5120 < 256 := by omega
                                            have he : 5120 + (i - 5120) = i := by omega
                                            have hc := IndexedMatrixBlock20_checks ⟨i - 5120, hs⟩
                                            change certifiedNode matrixHeightBounds matrixBounds matrixProgram (5120 + (i - 5120)) = true at hc
                                            rw [he] at hc
                                            exact hc
                                          ·
                                            by_cases h21 : i < 5632
                                            ·
                                              have hs : i - 5376 < 256 := by omega
                                              have he : 5376 + (i - 5376) = i := by omega
                                              have hc := IndexedMatrixBlock21_checks ⟨i - 5376, hs⟩
                                              change certifiedNode matrixHeightBounds matrixBounds matrixProgram (5376 + (i - 5376)) = true at hc
                                              rw [he] at hc
                                              exact hc
                                            ·
                                              by_cases h22 : i < 5888
                                              ·
                                                have hs : i - 5632 < 256 := by omega
                                                have he : 5632 + (i - 5632) = i := by omega
                                                have hc := IndexedMatrixBlock22_checks ⟨i - 5632, hs⟩
                                                change certifiedNode matrixHeightBounds matrixBounds matrixProgram (5632 + (i - 5632)) = true at hc
                                                rw [he] at hc
                                                exact hc
                                              ·
                                                by_cases h23 : i < 6144
                                                ·
                                                  have hs : i - 5888 < 256 := by omega
                                                  have he : 5888 + (i - 5888) = i := by omega
                                                  have hc := IndexedMatrixBlock23_checks ⟨i - 5888, hs⟩
                                                  change certifiedNode matrixHeightBounds matrixBounds matrixProgram (5888 + (i - 5888)) = true at hc
                                                  rw [he] at hc
                                                  exact hc
                                                ·
                                                  by_cases h24 : i < 6400
                                                  ·
                                                    have hs : i - 6144 < 256 := by omega
                                                    have he : 6144 + (i - 6144) = i := by omega
                                                    have hc := IndexedMatrixBlock24_checks ⟨i - 6144, hs⟩
                                                    change certifiedNode matrixHeightBounds matrixBounds matrixProgram (6144 + (i - 6144)) = true at hc
                                                    rw [he] at hc
                                                    exact hc
                                                  ·
                                                    by_cases h25 : i < 6656
                                                    ·
                                                      have hs : i - 6400 < 256 := by omega
                                                      have he : 6400 + (i - 6400) = i := by omega
                                                      have hc := IndexedMatrixBlock25_checks ⟨i - 6400, hs⟩
                                                      change certifiedNode matrixHeightBounds matrixBounds matrixProgram (6400 + (i - 6400)) = true at hc
                                                      rw [he] at hc
                                                      exact hc
                                                    ·
                                                      by_cases h26 : i < 6912
                                                      ·
                                                        have hs : i - 6656 < 256 := by omega
                                                        have he : 6656 + (i - 6656) = i := by omega
                                                        have hc := IndexedMatrixBlock26_checks ⟨i - 6656, hs⟩
                                                        change certifiedNode matrixHeightBounds matrixBounds matrixProgram (6656 + (i - 6656)) = true at hc
                                                        rw [he] at hc
                                                        exact hc
                                                      ·
                                                        by_cases h27 : i < 7168
                                                        ·
                                                          have hs : i - 6912 < 256 := by omega
                                                          have he : 6912 + (i - 6912) = i := by omega
                                                          have hc := IndexedMatrixBlock27_checks ⟨i - 6912, hs⟩
                                                          change certifiedNode matrixHeightBounds matrixBounds matrixProgram (6912 + (i - 6912)) = true at hc
                                                          rw [he] at hc
                                                          exact hc
                                                        ·
                                                          by_cases h28 : i < 7424
                                                          ·
                                                            have hs : i - 7168 < 256 := by omega
                                                            have he : 7168 + (i - 7168) = i := by omega
                                                            have hc := IndexedMatrixBlock28_checks ⟨i - 7168, hs⟩
                                                            change certifiedNode matrixHeightBounds matrixBounds matrixProgram (7168 + (i - 7168)) = true at hc
                                                            rw [he] at hc
                                                            exact hc
                                                          ·
                                                            have hs : i - 7424 < 16 := by omega
                                                            have he : 7424 + (i - 7424) = i := by omega
                                                            have hc := IndexedMatrixBlock29_checks ⟨i - 7424, hs⟩
                                                            change certifiedNode matrixHeightBounds matrixBounds matrixProgram (7424 + (i - 7424)) = true at hc
                                                            rw [he] at hc
                                                            exact hc

theorem all_matrix_program_values_enclosed (x : ℝ)
    (hx : Contains matrixHeightBounds x) :
    ∀ i, i < matrixNodeCount →
      Contains (matrixBounds i) (evaluate matrixProgram x i) :=
  certified_evaluation_sound matrixHeightBounds x matrixBounds matrixProgram
    matrixNodeCount hx all_matrix_nodes_checked

#print axioms all_matrix_nodes_checked
#print axioms all_matrix_program_values_enclosed
end Thomson10IndexedMatrix
