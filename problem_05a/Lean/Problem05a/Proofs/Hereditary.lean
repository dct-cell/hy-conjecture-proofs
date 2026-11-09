import Problem05a.Proofs.CountableIdeals

namespace Problem05a
open CategoryTheory CategoryTheory.Limits
universe u v

/-- Baer's criterion turns projectivity of every ideal into closure of injective
modules under surjective images. -/
theorem injective_of_surjective_of_ideals_projective
    {R : Type u} [CommRing R]
    (hproj : ∀ I : Ideal R, Module.Projective R I)
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Small.{v} R] [Module.Injective R M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Injective R N := by
  apply Module.Baer.injective
  intro I g
  letI := hproj I
  obtain ⟨l,hl⟩ := Module.projective_lifting_property f g hf
  obtain ⟨l',hl'⟩ := Module.Baer.of_injective (inferInstance : Module.Injective R M) I l
  refine ⟨f.comp l', ?_⟩
  intro x hx
  simp only [LinearMap.comp_apply, hl' x hx]
  exact LinearMap.congr_fun hl ⟨x,hx⟩

/-- The global-dimension bound includes all modules in the chosen universe. -/
theorem globalDimensionLE_one_of_ideals_projective
    (R : Type u) [CommRing R]
    (hproj : ∀ I : Ideal R, Module.Projective R I) : GlobalDimensionLE.{u,v} R 1 := by
  have hinj (N : ModuleCat.{max u v} R) : HasInjectiveDimensionLT N 2 := by
    let J := CategoryTheory.Injective.under N
    let f := CategoryTheory.Injective.ι N
    let Q := cokernel f
    haveI : CategoryTheory.Injective (ModuleCat.of R J) := by
      change CategoryTheory.Injective (CategoryTheory.Injective.under N)
      infer_instance
    letI : Module.Injective R J := Module.injective_module_of_injective_object R J
    letI : Module.Injective R Q := injective_of_surjective_of_ideals_projective hproj
      (cokernel.π f).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    letI : CategoryTheory.Injective Q := Module.injective_object_of_injective_module R Q
    have hs : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    exact hs.hasInjectiveDimensionLT_X₁ 1 inferInstance inferInstance
  intro M
  letI := HasExt.standard (ModuleCat.{max u v} R)
  apply HasProjectiveDimensionLT.mk
  intro i hi N e
  letI := hinj N
  exact e.eq_zero_of_hasInjectiveDimensionLT 2 hi

theorem globalDimension_A_le_one : GlobalDimensionLE.{0,v} A 1 :=
  globalDimensionLE_one_of_ideals_projective A ideals_of_A_projective

end Problem05a
