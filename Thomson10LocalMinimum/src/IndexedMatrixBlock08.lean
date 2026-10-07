import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock08_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (2048+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock08_checks
end Thomson10IndexedMatrix
