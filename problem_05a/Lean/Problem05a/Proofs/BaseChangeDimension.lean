import Problem05a.Spec

namespace Problem05a
open CategoryTheory
open scoped TensorProduct
universe u v

/-- Flat scalar extension preserves the bound at most one. -/
theorem baseChange_dimension_one {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (M : ModuleCat.{max u v} R)
    [HasProjectiveDimensionLE M 1] :
    HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) 1 := by
  let C := M.projectiveShortComplex
  have hC := M.shortExact_projectiveShortComplex
  haveI : Mono C.f := hC.mono_f
  haveI : Epi C.g := hC.epi_g
  haveI : CategoryTheory.Projective C.X₁ := by
    apply projective_iff_hasProjectiveDimensionLT_one.mpr
    exact (hC.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp inferInstance
  haveI : Module.Projective R C.X₁ :=
    (IsProjective.iff_projective (R := R) C.X₁).mpr inferInstance
  haveI : Module.Projective R C.X₂ :=
    (IsProjective.iff_projective (R := R) C.X₂).mpr inferInstance
  let f := C.f.hom.baseChange S
  let g := C.g.hom.baseChange S
  have hex : Function.Exact f g := Module.Flat.lTensor_exact S
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).mp hC.exact)
  have hinj : Function.Injective f := Module.Flat.lTensor_preserves_injective_linearMap
    C.f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have hsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective S ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  let T := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (ModuleCat.hom_ext (LinearMap.ext hex.apply_apply_eq_zero))
  have hT : T.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr hex
      mono_f := (ModuleCat.mono_iff_injective _).mpr hinj
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hsurj }
  exact hT.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

end Problem05a
