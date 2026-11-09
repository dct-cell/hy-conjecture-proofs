import Problem05a.Spec
namespace Problem05a
open CategoryTheory
universe u v

theorem ideals_projective_of_globalDimensionLE_one {R : Type u} [CommRing R]
    (h : GlobalDimensionLE.{u,v} R 1) (I : Ideal R) : Module.Projective R I := by
  haveI := h (ModuleCat.of R (ULift.{v} (R ⧸ I)))
  haveI : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) 1 :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R (ULift.{v} (R ⧸ I)))
      (N := ModuleCat.of R (R ⧸ I)) ULift.moduleEquiv 1
  let C := ShortComplex.moduleCatMk I.subtype I.mkQ (by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property)
  have hC : C.ShortExact := ModuleCat.shortComplex_shortExact C
    (LinearMap.exact_subtype_mkQ I) I.subtype_injective I.mkQ_surjective
  haveI : CategoryTheory.Projective C.X₂ := by
    change CategoryTheory.Projective (ModuleCat.of R R)
    infer_instance
  haveI : HasProjectiveDimensionLE C.X₃ 1 := by
    change HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) 1
    infer_instance
  have hp : CategoryTheory.Projective (ModuleCat.of R I) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr
      ((hC.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp inferInstance)
  exact (IsProjective.iff_projective I).mpr hp

end Problem05a
