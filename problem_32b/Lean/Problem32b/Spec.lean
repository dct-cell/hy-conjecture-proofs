import Mathlib

/-!
# Problem 32(b): mathematical specification

This file is the human-review boundary. It states the question independently of
any counterexample construction. Lean checks that these definitions are well
typed; it cannot decide whether they faithfully translate the source question.

All colons and ordinary products are taken in the ambient field K. The predicate
Claim explicitly requires that K is the fraction field of the domain D.
There is no Noetherian hypothesis in the source question or in Claim.

The specification contains definitions of propositions, not assumed theorems.
Proof.lean establishes the negation of Conjecture without changing these definitions.
The release hash of this file is recorded in Lean/verification.json.
-/

namespace Problem32b

variable {K : Type*} [Field K]

/-- The colon (S:T), computed in K. -/
def colon (S T : Set K) : Set K := {x | ∀ y ∈ T, x*y ∈ S}

/-- The divisorial closure with respect to the base ring D. -/
def vClosure (D : Subring K) (I : Set K) : Set K := colon D (colon D I)

/-- The ordinary ideal aD+bD, as a subset of K. -/
def twoSpan (D : Subring K) (a b : K) : Set K :=
  {x | ∃ r ∈ D, ∃ s ∈ D, x = r*a+s*b}

/-- Ordinary products are all finite sums of products, including the empty sum. -/
def productSet (S T : Set K) : Set K :=
  {x | ∃ l : List (K × K), (∀ p ∈ l, p.1 ∈ S ∧ p.2 ∈ T) ∧
    x = (l.map fun p => p.1*p.2).sum}

/-- Stability: I is invertible as an ideal of its endomorphism ring (I:I). -/
def StableSet (I : Set K) : Prop :=
  productSet I (colon (colon I I) I) = colon I I

/-- The image of an ordinary mathlib ideal of D in the ambient field K. -/
def idealSet (D : Subring K) (I : Ideal D) : Set K :=
  {x | ∃ hx : x ∈ D, (⟨x,hx⟩ : D) ∈ I}

/-- Nonzero integral divisorial ideals, with their ordinary inclusion order. -/
abbrev DivisorialIdeals (D : Subring K) :=
  {I : Ideal D // I ≠ ⊥ ∧ vClosure D (idealSet D I) = idealSet D I}

/-- The Mori condition: ACC on nonzero integral divisorial ideals. -/
def MoriCondition (D : Subring K) : Prop :=
  WellFoundedGT (DivisorialIdeals D)

namespace Spec

/-- The universal hypothesis: every nonzero divisorial ideal is two-v-generated. -/
def AllTwoVGenerated (D : Subring K) : Prop :=
  ∀ I : Ideal D, I ≠ ⊥ → vClosure D (idealSet D I) = idealSet D I →
    ∃ a b : D, a ∈ I ∧ b ∈ I ∧
      vClosure D (twoSpan D (a : K) (b : K)) = idealSet D I

/-- The proposed conclusion: every nonzero divisorial ideal is stable. -/
def AllDivisorialStable (D : Subring K) : Prop :=
  ∀ I : Ideal D, I ≠ ⊥ → vClosure D (idealSet D I) = idealSet D I →
    StableSet (idealSet D I)

/-- The complete implication asked about in Problem 32(b).
A domain is represented as a subring of its fraction field. -/
def Claim (D : Subring K) : Prop :=
  IsFractionRing D K → ringKrullDim D = 1 → MoriCondition D →
    AllTwoVGenerated D → AllDivisorialStable D

/-- The universal assertion in the source question. -/
def Conjecture : Prop :=
  ∀ (K : Type) [Field K] (D : Subring K), Claim D

end Spec
end Problem32b
