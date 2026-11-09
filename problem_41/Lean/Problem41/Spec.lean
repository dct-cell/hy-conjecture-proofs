import Mathlib

/-!
The specification uses actual polynomial rings and integrality over powers of
an ideal. It imports no implementation of the proof. No theorem is assumed.
-/

namespace Problem41

/-- Integrality over an ideal, via a monic equation with power-ideal coefficients. -/
def IntegralOverIdeal {R : Type*} [CommRing R] (I : Ideal R) (x : R) : Prop :=
  ∃ p : Polynomial R, p.Monic ∧ p.eval x = 0 ∧
    ∀ i : ℕ, p.coeff i ∈ I ^ (p.natDegree - i)

def IntegrallyClosedIdeal {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x : R, IntegralOverIdeal I x → x ∈ I

/-- The initial ideal in the three-variable polynomial ring. -/
noncomputable def pureIdeal (k : Type*) [Field k] (a b c : ℕ) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {MvPolynomial.X 0 ^ a, MvPolynomial.X 1 ^ b, MvPolynomial.X 2 ^ c}

/-- An ideal realizing precisely the integral closure, all of whose positive
powers are integrally closed. The existential does not assume that the set of
integral elements is an ideal: proving its existence is part of the target. -/
def NormalIntegralClosure (k : Type*) [Field k] (a b c : ℕ) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin 3) k),
    (∀ f, f ∈ I ↔ IntegralOverIdeal (pureIdeal k a b c) f) ∧
    ∀ n : ℕ, 0 < n → IntegrallyClosedIdeal (I ^ n)

def weight (a b c i j l : ℕ) : ℚ :=
  (i : ℚ) / a + (j : ℚ) / b + (l : ℚ) / c

/-- The finite box criterion to be proved equivalent to the original problem. -/
def BoxCriterion (a b c : ℕ) : Prop :=
  ∀ i < a, ∀ j < b, ∀ l < c,
    2 ≤ weight a b c i j l →
    ∃ p ≤ i, ∃ q ≤ j, ∃ r ≤ l,
      1 ≤ weight a b c p q r ∧
      1 ≤ weight a b c (i-p) (j-q) (l-r)

/-- Explicit finite algorithm, using rational arithmetic. -/
def decideBox (a b c : ℕ) : Bool :=
  (List.range a).all fun i => (List.range b).all fun j =>
    (List.range c).all fun l =>
      if 2 ≤ weight a b c i j l then
        (List.range (i+1)).any fun p => (List.range (j+1)).any fun q =>
          (List.range (l+1)).any fun r =>
            decide (1 ≤ weight a b c p q r ∧
              1 ≤ weight a b c (i-p) (j-q) (l-r))
      else true

/-- Full all-fields, all-positive-triples statement. -/
def Claim : Prop :=
  ∀ (k : Type) [Field k] (a b c : ℕ), 0 < a → 0 < b → 0 < c →
    (decideBox a b c = true ↔ NormalIntegralClosure k a b c)

end Problem41
