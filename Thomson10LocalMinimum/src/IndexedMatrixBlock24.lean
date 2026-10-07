import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock24_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (6144+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock24_checks
end Thomson10IndexedMatrix
