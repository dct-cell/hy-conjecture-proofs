import Problem05a.Proofs.Hereditary

namespace Problem05a
universe v

noncomputable def augmentation : A →+* ZMod 3 :=
  (AddMonoidAlgebra.lift (ZMod 3) (ZMod 3) G 1).toRingHom

@[simp] theorem augmentation_single (g : G) (r : ZMod 3) :
    augmentation (AddMonoidAlgebra.single g r) = r := by
  simp [augmentation, AddMonoidAlgebra.lift_single]

instance : Infinite G := by infer_instance

theorem no_invariant_element (x : A)
    (hx : ∀ g : G, AddMonoidAlgebra.single g 1 * x = x) : x = 0 := by
  classical
  obtain ⟨h,hh⟩ := Infinite.exists_notMem_finset x.coeff.support
  have hz : x.coeff h = 0 := by simpa using hh
  ext k
  have he := congrArg (fun y : A => y.coeff h) (hx (h - k))
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at he
  have hk : -(h-k)+h = k := by abel
  rw [hk,hz] at he
  simpa using he

noncomputable def augmentationModule : Module A (ZMod 3) :=
  Module.compHom (ZMod 3) augmentation

theorem augmentation_not_projective :
    letI := augmentationModule
    ¬ Module.Projective A (ZMod 3) := by
  letI := augmentationModule
  intro h
  let f : A →ₗ[A] ZMod 3 :=
    { toFun := augmentation
      map_add' := augmentation.map_add
      map_smul' := by
        intro r x
        change augmentation (r*x) = augmentation r * augmentation x
        exact augmentation.map_mul r x }
  have hf : Function.Surjective f := by
    intro r
    exact ⟨AddMonoidAlgebra.single 0 r, augmentation_single 0 r⟩
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : ZMod 3 →ₗ[A] ZMod 3) hf
  have he : s 1 = 0 := no_invariant_element (s 1) (by
    intro g
    have hact : (AddMonoidAlgebra.single g 1 : A) • (1 : ZMod 3) = 1 := by
      change augmentation (AddMonoidAlgebra.single g 1) * 1 = 1
      simp
    have := s.map_smul (AddMonoidAlgebra.single g 1) 1
    simpa only [hact, smul_eq_mul] using this.symm)
  have hc := LinearMap.congr_fun hs 1
  simp only [LinearMap.comp_apply, LinearMap.id_apply, he, map_zero] at hc
  exact zero_ne_one hc

theorem globalDimension_A_not_zero : ¬ GlobalDimensionLE.{0,v} A 0 := by
  intro h
  letI := augmentationModule
  have hp := h (ModuleCat.of A (ULift.{v} (ZMod 3)))
  haveI : CategoryTheory.Projective (ModuleCat.of A (ULift.{v} (ZMod 3))) :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hp
  haveI : Module.Projective A (ULift.{v} (ZMod 3)) :=
    (IsProjective.iff_projective (R := A) (ULift.{v} (ZMod 3))).mpr inferInstance
  exact augmentation_not_projective Module.Projective.of_ulift

theorem globalDimension_A : GlobalDimensionEq.{0,v} A 1 := by
  refine ⟨globalDimension_A_le_one, ?_⟩
  intro m hm
  have : m = 0 := by omega
  subst m
  exact globalDimension_A_not_zero

end Problem05a
