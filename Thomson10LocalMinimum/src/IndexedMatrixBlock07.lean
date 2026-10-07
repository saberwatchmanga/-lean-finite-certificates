import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock07_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (1792+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock07_checks
end Thomson10IndexedMatrix
