import IndexedMatrixData
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem IndexedMatrixBlock15_checks : ∀ i : Fin 256,
    certifiedNode matrixHeightBounds matrixBounds matrixProgram (3840+i.val) = true := by
  decide +kernel
#print axioms IndexedMatrixBlock15_checks
end Thomson10IndexedMatrix
