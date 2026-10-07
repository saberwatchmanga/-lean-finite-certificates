import IndexedIntervalDag
import IndexedMatrixData00
import IndexedMatrixData01
import IndexedMatrixData02
import IndexedMatrixData03
import IndexedMatrixData04
import IndexedMatrixData05
import IndexedMatrixData06
import IndexedMatrixData07
import IndexedMatrixData08
import IndexedMatrixData09
import IndexedMatrixData10
import IndexedMatrixData11
import IndexedMatrixData12
import IndexedMatrixData13
import IndexedMatrixData14

namespace Thomson10IndexedMatrix
open Thomson10Arithmetic Thomson10IntervalDag Thomson10IndexedDag
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def matrixHeightBounds : Thomson10Arithmetic.I := ⟨(42268741/100000000 : Rat),(42268743/100000000 : Rat)⟩
def matrixNodeCount : Nat := 7440
def matrixBounds (i : Nat) : Thomson10Arithmetic.I :=
  if i < matrixNodeCount then (if i < 3584 then (if i < 1536 then (if i < 512 then matrixBounds00 i else (if i < 1024 then matrixBounds01 i else matrixBounds02 i)) else (if i < 2560 then (if i < 2048 then matrixBounds03 i else matrixBounds04 i) else (if i < 3072 then matrixBounds05 i else matrixBounds06 i))) else (if i < 5632 then (if i < 4608 then (if i < 4096 then matrixBounds07 i else matrixBounds08 i) else (if i < 5120 then matrixBounds09 i else matrixBounds10 i)) else (if i < 6656 then (if i < 6144 then matrixBounds11 i else matrixBounds12 i) else (if i < 7168 then matrixBounds13 i else matrixBounds14 i)))) else point 0

def matrixProgram (i : Nat) : Instruction :=
  if i < matrixNodeCount then (if i < 3584 then (if i < 1536 then (if i < 512 then matrixProgram00 i else (if i < 1024 then matrixProgram01 i else matrixProgram02 i)) else (if i < 2560 then (if i < 2048 then matrixProgram03 i else matrixProgram04 i) else (if i < 3072 then matrixProgram05 i else matrixProgram06 i))) else (if i < 5632 then (if i < 4608 then (if i < 4096 then matrixProgram07 i else matrixProgram08 i) else (if i < 5120 then matrixProgram09 i else matrixProgram10 i)) else (if i < 6656 then (if i < 6144 then matrixProgram11 i else matrixProgram12 i) else (if i < 7168 then matrixProgram13 i else matrixProgram14 i)))) else .constant 0
end Thomson10IndexedMatrix
