import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock14_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (3584+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock14_checks
end Thomson10IndexedMatrix
