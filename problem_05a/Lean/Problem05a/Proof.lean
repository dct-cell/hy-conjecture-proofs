import Problem05a.Spec
import Problem05a.Proofs.Admissibility
import Problem05a.Proofs.Augmentation
import Problem05a.Proofs.PolynomialBaseLower
import Problem05a.Proofs.IteratedGroupAlgebra
import Problem05a.Proofs.IdealsOfHereditary
import Problem05a.Proofs.PolynomialUpper
import Problem05a.Proofs.PolynomialLower
import Problem05a.Proofs.RingEquivalence

namespace Problem05a
open CategoryTheory
universe v

theorem polynomial_A_not_le_one : ¬ GlobalDimensionLE.{0,v} (Polynomial A) 1 := by
  intro h
  exact PolynomialLower.obstruction_not_projective
    (ideals_projective_of_globalDimensionLE_one h _)

theorem globalDimension_polynomial_A : GlobalDimensionEq.{0,v} (Polynomial A) 2 := by
  refine ⟨polynomial_dimension_le_two globalDimension_A_le_one, ?_⟩
  intro m hm h
  apply polynomial_A_not_le_one
  intro M
  haveI := h M
  exact hasProjectiveDimensionLT_of_ge M (m+1) 2 (by omega)

theorem globalDimension_group_B :
    GlobalDimensionEq.{0,v} (AddMonoidAlgebra B G) 2 :=
  globalDimensionEq_of_ringEquiv polynomialGroupEquiv.symm 2 globalDimension_polynomial_A

theorem solution : Claim.{v} :=
  ⟨admissible_A, admissible_B, globalDimension_A, globalDimension_B,
    Iterated.globalDimension_A, globalDimension_group_B⟩

/-- The four dimensions are for all modules, not only finitely generated modules. -/
theorem complete_counterexample :
    (∀ g : G, IsOfFinAddOrder g → IsUnit (addOrderOf g : A)) ∧
    (∀ g : G, IsOfFinAddOrder g → IsUnit (addOrderOf g : B)) ∧
    GlobalDimensionEq.{0,v} A 1 ∧ GlobalDimensionEq.{0,v} B 1 ∧
    GlobalDimensionEq.{0,v} (AddMonoidAlgebra A G) 1 ∧
    GlobalDimensionEq.{0,v} (AddMonoidAlgebra B G) 2 := solution

theorem expanded_counterexample :
    (∀ g : G, IsOfFinAddOrder g → IsUnit (addOrderOf g : A)) ∧
    (∀ g : G, IsOfFinAddOrder g → IsUnit (addOrderOf g : B)) ∧
    (∀ M : ModuleCat.{v} A, HasProjectiveDimensionLE M 1) ∧
    (¬ ∀ M : ModuleCat.{v} A, HasProjectiveDimensionLE M 0) ∧
    (∀ M : ModuleCat.{v} B, HasProjectiveDimensionLE M 1) ∧
    (¬ ∀ M : ModuleCat.{v} B, HasProjectiveDimensionLE M 0) ∧
    (∀ M : ModuleCat.{v} (AddMonoidAlgebra A G), HasProjectiveDimensionLE M 1) ∧
    (¬ ∀ M : ModuleCat.{v} (AddMonoidAlgebra A G), HasProjectiveDimensionLE M 0) ∧
    (∀ M : ModuleCat.{v} (AddMonoidAlgebra B G), HasProjectiveDimensionLE M 2) ∧
    (¬ ∀ M : ModuleCat.{v} (AddMonoidAlgebra B G), HasProjectiveDimensionLE M 1) :=
  ⟨admissible_A, admissible_B,
    globalDimension_A.1, globalDimension_A_not_zero,
    globalDimension_B.1, globalDimension_B_not_zero,
    Iterated.globalDimension_A.1, Iterated.globalDimension_A_not_zero,
    globalDimension_group_B.1, globalDimension_group_B.2 1 (by decide)⟩

end Problem05a
