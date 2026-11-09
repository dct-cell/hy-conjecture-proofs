import Problem05a.Proofs.Augmentation

namespace Problem05a.Iterated
universe v
abbrev T := AddMonoidAlgebra A G
instance : CharP T 3 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 3) T) 3 (by decide)

theorem cube (x : T) : x^3 = x := by
  induction x using AddMonoidAlgebra.induction_on with
  | of g =>
    change (AddMonoidAlgebra.single g (1 : A))^3 = AddMonoidAlgebra.single g 1
    simp [AddMonoidAlgebra.single_pow, triple_smul]
  | add x y hx hy => rw [add_pow_char x y 3, hx,hy]
  | smul r x hx => simp [smul_pow,cube_eq,hx]

theorem upper : GlobalDimensionLE.{0,v} T 1 :=
  globalDimensionLE_one_of_ideals_projective T (ideals_projective_of_cube cube)


noncomputable def augmentation : T →+* A :=
  (AddMonoidAlgebra.lift (A) (A) G 1).toRingHom

@[simp] theorem augmentation_single (g : G) (r : A) :
    augmentation (AddMonoidAlgebra.single g r) = r := by
  simp [augmentation, AddMonoidAlgebra.lift_single]



theorem no_invariant_element (x : T)
    (hx : ∀ g : G, AddMonoidAlgebra.single g 1 * x = x) : x = 0 := by
  classical
  obtain ⟨h,hh⟩ := Infinite.exists_notMem_finset x.coeff.support
  have hz : x.coeff h = 0 := by simpa using hh
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro k
  have he := congrArg (fun y : T => y.coeff h) (hx (h - k))
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at he
  have hk : -(h-k)+h = k := by abel
  rw [hk,hz] at he
  simpa using he

noncomputable def augmentationModule : Module T (A) :=
  Module.compHom (A) augmentation

theorem augmentation_not_projective :
    letI := augmentationModule
    ¬ Module.Projective T (A) := by
  letI := augmentationModule
  intro h
  let f : T →ₗ[T] A :=
    { toFun := augmentation
      map_add' := augmentation.map_add
      map_smul' := by
        intro r x
        change augmentation (r*x) = augmentation r * augmentation x
        exact augmentation.map_mul r x }
  have hf : Function.Surjective f := by
    intro r
    exact ⟨AddMonoidAlgebra.single 0 r, augmentation_single 0 r⟩
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : A →ₗ[T] A) hf
  have he : s 1 = 0 := no_invariant_element (s 1) (by
    intro g
    have hact : (AddMonoidAlgebra.single g 1 : T) • (1 : A) = 1 := by
      change augmentation (AddMonoidAlgebra.single g 1) * 1 = 1
      simp
    have := s.map_smul (AddMonoidAlgebra.single g 1) 1
    simpa only [hact, smul_eq_mul] using this.symm)
  have hc := LinearMap.congr_fun hs 1
  simp only [LinearMap.comp_apply, LinearMap.id_apply, he, map_zero] at hc
  exact zero_ne_one hc

theorem globalDimension_A_not_zero : ¬ GlobalDimensionLE.{0,v} T 0 := by
  intro h
  letI := augmentationModule
  have hp := h (ModuleCat.of T (ULift.{v} (A)))
  haveI : CategoryTheory.Projective (ModuleCat.of T (ULift.{v} (A))) :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hp
  haveI : Module.Projective T (ULift.{v} (A)) :=
    (IsProjective.iff_projective (R := T) (ULift.{v} (A))).mpr inferInstance
  exact augmentation_not_projective Module.Projective.of_ulift

theorem globalDimension_A : GlobalDimensionEq.{0,v} T 1 := by
  refine ⟨upper, ?_⟩
  intro m hm
  have : m = 0 := by omega
  subst m
  exact globalDimension_A_not_zero

end Problem05a.Iterated
