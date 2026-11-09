import Problem05a.Proofs.BaseChangeDimension
import Problem05a.Proofs.PolynomialResolution

namespace Problem05a
open CategoryTheory Polynomial PolynomialModule
open scoped TensorProduct
universe u v

theorem polynomial_dimension_le_two {R : Type u} [CommRing R]
    (h : GlobalDimensionLE.{u,v} R 1) : GlobalDimensionLE.{u,v} R[X] 2 := by
  intro M
  letI : Module R M := Module.compHom M (algebraMap R R[X])
  letI : IsScalarTower R R[X] M := IsScalarTower.of_compHom R R[X] M
  haveI := h (ModuleCat.of R M)
  haveI : HasProjectiveDimensionLE (ModuleCat.of R[X] (R[X] ⊗[R] M)) 1 :=
    baseChange_dimension_one (ModuleCat.of R M)
  haveI : HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R M)) 1 :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R[X] (R[X] ⊗[R] M))
      (N := ModuleCat.of R[X] (PolynomialModule R M))
      (polynomialTensorProductLEquivPolynomialModule R M) 1
  let f := PolynomialResolution.delta (R := R) (M := M)
  let g := PolynomialResolution.epsilon (R := R) (M := M)
  let C := ShortComplex.moduleCatMk f g
    (LinearMap.ext PolynomialResolution.epsilon_delta)
  have hC : C.ShortExact := ModuleCat.shortComplex_shortExact C
    (PolynomialResolution.exact_delta_epsilon (R := R) (M := M))
    (PolynomialResolution.delta_injective (R := R) (M := M))
    (PolynomialResolution.epsilon_surjective (R := R) (M := M))
  have h₁ : HasProjectiveDimensionLT C.X₁ 2 := by
    change HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R M)) 1
    infer_instance
  have h₂ : HasProjectiveDimensionLT C.X₂ 3 := by
    change HasProjectiveDimensionLT (ModuleCat.of R[X] (PolynomialModule R M)) 3
    infer_instance
  exact hC.hasProjectiveDimensionLT_X₃ 2 h₁ h₂

end Problem05a
