import WitnessControls

#check Thomson10PublicWitness.damaged_node_0_check

open Thomson10IndexedDag Thomson10IndexedMatrix

example :
    certifiedNode matrixHeightBounds Thomson10PublicWitness.damagedBounds
      matrixProgram 0 = true := by
  decide +kernel
