import Std

/- This file proves only rational arithmetic checks. No claim of real-valued
   derivative correctness, interval algorithm soundness, geometry, or minimality. -/
namespace Thomson10Arithmetic

structure I where
  lo : Rat
  hi : Rat
deriving DecidableEq

def point (x : Rat) : I := ⟨x, x⟩
def add (x y : I) : I := ⟨x.lo + y.lo, x.hi + y.hi⟩
def neg (x : I) : I := ⟨-x.hi, -x.lo⟩
def sub (x y : I) : I := add x (neg y)
def mul (x y : I) : I :=
  ⟨min (min (x.lo*y.lo) (x.lo*y.hi)) (min (x.hi*y.lo) (x.hi*y.hi)),
   max (max (x.lo*y.lo) (x.lo*y.hi)) (max (x.hi*y.lo) (x.hi*y.hi))⟩
def reciprocal (x : I) : I := ⟨1/x.hi, 1/x.lo⟩
def divide (x y : I) : I := mul x (reciprocal y)
def cube (x : I) : I := mul (mul x x) x
def scale (n : Rat) (x : I) : I := mul (point n) x

def RootBounds (argument candidate : I) : Prop :=
  0 ≤ argument.lo ∧ argument.lo ≤ argument.hi ∧
  0 < candidate.lo ∧ candidate.lo ≤ candidate.hi ∧
  candidate.lo*candidate.lo ≤ argument.lo ∧
  argument.hi ≤ candidate.hi*candidate.hi
instance (a b : I) : Decidable (RootBounds a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def EndpointChecks (t : Rat) (roots : List I) (negative : Bool) : Prop :=
  match roots with
  | [s, q, u, v, w] =>
    let a := add (sub (point 2) s) (scale t (add (point 2) s))
    let b := add (add (point 2) s) (scale t (sub (point 2) s))
    let denominator := cube q
    let result := sub (sub
      (divide (add (add (point 1) (scale 2 s))
        (divide (scale 2 (add q (point 2))) u)) denominator)
      (divide (scale 4 (add (point 2) s)) (mul a v)))
      (divide (scale 4 (sub (point 2) s)) (mul b w))
    0 < t ∧ t < 1 ∧
    RootBounds (point 2) s ∧ RootBounds (point (1-t)) q ∧
    RootBounds (add (point 1) q) u ∧ RootBounds a v ∧ RootBounds b w ∧
    0 < denominator.lo ∧ 0 < (mul a v).lo ∧ 0 < (mul b w).lo ∧
    (if negative then result.hi < 0 else 0 < result.lo)
  | _ => False
instance (t : Rat) (roots : List I) (negative : Bool) : Decidable (EndpointChecks t roots negative) := by
  unfold EndpointChecks
  split <;> infer_instance

def tLeft : Rat := ((3573293 : Rat) / 20000000)
def tRight : Rat := ((8933233 : Rat) / 50000000)
def rootsLeft : List I := [⟨((176776695296636881 : Rat) / 125000000000000000), ((1414213562373095049 : Rat) / 1000000000000000000)⟩,
  ⟨((453137768785608953 : Rat) / 500000000000000000), ((906275537571217907 : Rat) / 1000000000000000000)⟩,
  ⟨((1380679375369682961 : Rat) / 1000000000000000000), ((1380679375369682963 : Rat) / 1000000000000000000)⟩,
  ⟨((68344991951837031 : Rat) / 62500000000000000), ((1093519871229392497 : Rat) / 1000000000000000000)⟩,
  ⟨((937932952191473659 : Rat) / 500000000000000000), ((1875865904382947319 : Rat) / 1000000000000000000)⟩]
def rootsRight : List I := [⟨((176776695296636881 : Rat) / 125000000000000000), ((1414213562373095049 : Rat) / 1000000000000000000)⟩,
  ⟨((453137766027065989 : Rat) / 500000000000000000), ((906275532054131979 : Rat) / 1000000000000000000)⟩,
  ⟨((1380679373371722381 : Rat) / 1000000000000000000), ((690339686685861191 : Rat) / 500000000000000000)⟩,
  ⟨((546759943420255223 : Rat) / 500000000000000000), ((1093519886840510447 : Rat) / 1000000000000000000)⟩,
  ⟨((234483238243040427 : Rat) / 125000000000000000), ((937932952972161709 : Rat) / 500000000000000000)⟩]

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem left_endpoint_arithmetic : EndpointChecks tLeft rootsLeft true := by
  decide +kernel
theorem right_endpoint_arithmetic : EndpointChecks tRight rootsRight false := by
  decide +kernel

#print axioms left_endpoint_arithmetic
#print axioms right_endpoint_arithmetic
end Thomson10Arithmetic
