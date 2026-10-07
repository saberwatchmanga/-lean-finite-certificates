import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock06_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (1536+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock06_checks
end Thomson10IndexedMatrix
