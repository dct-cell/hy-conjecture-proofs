import Mathlib

/-!
The finite conductor quotient and its module, over F₂.
The decision procedure below uses kernel reduction, never native_decide.
The quotient is only an intermediate lemma, not the definition of the original ideal problem.
-/

namespace Problem32b.FiniteQuotient

abbrev F := ZMod 2
abbrev A := Fin 3 → F
abbrev Q := Fin 5 → F

def mul (a b : A) : A :=
  ![a 0*b 0, a 0*b 1+a 1*b 0, a 0*b 2+a 2*b 0]

def act (a : A) (q : Q) : Q :=
  ![a 0*q 0, a 0*q 1, a 0*q 2,
    a 0*q 3+a 1*q 1+a 2*q 0,
    a 0*q 4+a 1*q 2+a 2*q 1]

def IsIdeal (J : Finset A) : Prop :=
  0 ∈ J ∧ (∀ a ∈ J, ∀ b ∈ J, a+b ∈ J) ∧
    ∀ r a, a ∈ J → mul r a ∈ J

instance (J : Finset A) : Decidable (IsIdeal J) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ann (q : Q) : Finset A := Finset.univ.filter fun a => act a q = 0

def witnesses : List Q :=
  [![0,0,0,0,0], ![0,0,0,1,0], ![0,1,0,0,0],
   ![1,0,0,0,0], ![0,0,1,0,0], ![1,1,1,0,0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem every_ideal_is_ann :
    ∀ J : Finset A, IsIdeal J → ∃ q ∈ witnesses, ann q = J := by
  decide

theorem every_ideal_has_single_witness (J : Finset A) (hJ : IsIdeal J) :
    ∃ q : Q, ∀ a : A, a ∈ J ↔ act a q = 0 := by
  obtain ⟨q, _, h⟩ := every_ideal_is_ann J hJ
  refine ⟨q, ?_⟩
  intro a
  rw [← h]
  simp [ann]

#print axioms every_ideal_is_ann

end Problem32b.FiniteQuotient
