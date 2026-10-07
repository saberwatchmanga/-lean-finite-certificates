import IndexedMatrixBlock00

namespace Thomson10PublicWitness

open Thomson10IndexedDag Thomson10IndexedMatrix

/-- A deliberately corrupted copy of node 0's interval bounds. -/
def damagedBounds (i : Nat) : Thomson10Arithmetic.I :=
  if i = 0 then
    { matrixBounds 0 with lo := (matrixBounds 0).lo + 1 }
  else matrixBounds i

theorem original_node_0_check :
    certifiedNode matrixHeightBounds matrixBounds matrixProgram 0 = true := by
  decide +kernel

theorem damaged_node_0_check :
    certifiedNode matrixHeightBounds damagedBounds matrixProgram 0 = false := by
  decide +kernel

#print axioms original_node_0_check
#print axioms damaged_node_0_check

end Thomson10PublicWitness
