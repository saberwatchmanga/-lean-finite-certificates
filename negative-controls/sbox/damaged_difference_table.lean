import SboxData
namespace Sbox
def damaged : Counts := fun a b => if a == 1 && b == 0 then 16 else G3Counts a b
example : ∀ a b : Word, differenceCount G3 a b = damaged a b := by decide
end Sbox
