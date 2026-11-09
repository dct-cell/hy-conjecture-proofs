import Problem05a.Proofs.PolynomialBase

namespace Problem05a
universe v

noncomputable def residueModule : Module B (ZMod 3) :=
  Module.compHom (ZMod 3) (Polynomial.evalRingHom 0)

theorem residue_not_projective :
    letI := residueModule
    ¬ Module.Projective B (ZMod 3) := by
  letI := residueModule
  intro h
  let f : B →ₗ[B] ZMod 3 :=
    { toFun := Polynomial.eval 0
      map_add' := fun _ _ => Polynomial.eval_add
      map_smul' := by
        intro r x
        change Polynomial.eval 0 (r*x) = Polynomial.eval 0 r * Polynomial.eval 0 x
        exact Polynomial.eval_mul }
  have hf : Function.Surjective f := by
    intro r
    exact ⟨Polynomial.C r, Polynomial.eval_C⟩
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : ZMod 3 →ₗ[B] ZMod 3) hf
  have hact : (Polynomial.X : B) • (1 : ZMod 3) = 0 := by
    change Polynomial.eval 0 Polynomial.X * 1 = 0
    simp
  have hx : (Polynomial.X : B) * s 1 = 0 := by
    simpa only [hact, map_zero, smul_eq_mul] using (s.map_smul (Polynomial.X : B) 1).symm
  have he : s 1 = 0 := (mul_eq_zero.mp hx).resolve_left Polynomial.X_ne_zero
  have hc := LinearMap.congr_fun hs 1
  simp only [LinearMap.comp_apply, LinearMap.id_apply, he, map_zero] at hc
  exact zero_ne_one hc

theorem globalDimension_B_not_zero : ¬ GlobalDimensionLE.{0,v} B 0 := by
  intro h
  letI := residueModule
  have hp := h (ModuleCat.of B (ULift.{v} (ZMod 3)))
  haveI : CategoryTheory.Projective (ModuleCat.of B (ULift.{v} (ZMod 3))) :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hp
  haveI : Module.Projective B (ULift.{v} (ZMod 3)) :=
    (IsProjective.iff_projective (R := B) (ULift.{v} (ZMod 3))).mpr inferInstance
  exact residue_not_projective Module.Projective.of_ulift

theorem globalDimension_B : GlobalDimensionEq.{0,v} B 1 := by
  refine ⟨globalDimension_B_le_one, ?_⟩
  intro m hm
  have : m = 0 := by omega
  subst m
  exact globalDimension_B_not_zero

end Problem05a
