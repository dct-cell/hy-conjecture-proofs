import Problem32b.Spec
import Problem32b.Proofs.Result

/-!
# Proof of the negation of the fixed specification

Spec.lean supplies the target. All construction details and helper lemmas live
in Proofs/. The target below is applied directly, rather than redefined here.
Kernel acceptance certifies this proof relative to the definitions in Spec.lean;
faithfulness of those definitions to the informal problem is reviewed separately.
-/

namespace Problem32b

/-- The concrete domain fails the exact implication defined by Spec.Claim. -/
theorem concrete_refutation : ¬ Spec.Claim Laurent.R := by
  intro h
  have hstable : Spec.AllDivisorialStable Laurent.R :=
    h (inferInstance : IsFractionRing Laurent.R (Laurent.K Laurent.F2))
      Laurent.R_dimension Laurent.R_mori
      Laurent.all_ordinary_divisorial_ideals_two_generated
  exact Laurent.badIdeal_not_stable
    (hstable Laurent.badIdeal Laurent.badIdeal_ne_bot Laurent.badIdeal_divisorial)

/-- Main result: the universal assertion in Problem 32(b) is false. -/
theorem refutation : ¬ Spec.Conjecture := by
  intro h
  exact concrete_refutation (h (Laurent.K Laurent.F2) Laurent.R)

end Problem32b
