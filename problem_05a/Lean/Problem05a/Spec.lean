import Mathlib

namespace Problem05a
open CategoryTheory
universe u v

/-- All modules are included; no finite-generation restriction is imposed. -/
def GlobalDimensionLE (R : Type u) [Ring R] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{max u v} R, HasProjectiveDimensionLE M n

def GlobalDimensionEq (R : Type u) [Ring R] (n : ℕ) : Prop :=
  GlobalDimensionLE.{u,v} R n ∧ ∀ m < n, ¬ GlobalDimensionLE.{u,v} R m

abbrev G := ℕ →₀ ZMod 2
abbrev A := AddMonoidAlgebra (ZMod 3) G
abbrev B := Polynomial (ZMod 3)

/-- Additive notation for the torsion-order admissibility condition. -/
def Admissible (R : Type*) [CommRing R] : Prop :=
  ∀ g : G, IsOfFinAddOrder g → IsUnit (addOrderOf g : R)

/-- The four exact dimensions and both admissibility conditions in the manuscript. -/
def Claim : Prop :=
  Admissible A ∧ Admissible B ∧
  GlobalDimensionEq.{0,v} A 1 ∧ GlobalDimensionEq.{0,v} B 1 ∧
  GlobalDimensionEq.{0,v} (AddMonoidAlgebra A G) 1 ∧
  GlobalDimensionEq.{0,v} (AddMonoidAlgebra B G) 2

end Problem05a
