import SboxData
namespace Sbox
set_option maxRecDepth 200000
example : ∃ i : Fin 139, (allPlanes.pop)[i.val]! = plane 12 1 2 := by decide
end Sbox
