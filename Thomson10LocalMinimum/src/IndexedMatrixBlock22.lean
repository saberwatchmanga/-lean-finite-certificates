import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock22_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (5632+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock22_checks
end Thomson10IndexedMatrix
