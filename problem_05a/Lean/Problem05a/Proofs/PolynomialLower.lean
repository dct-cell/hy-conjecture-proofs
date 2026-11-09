import Problem05a.Proofs.Augmentation

namespace Problem05a.PolynomialLower
open Polynomial
abbrev S := Polynomial A
noncomputable def residue : S →+* ZMod 3 :=
  augmentation.comp (evalRingHom 0)
noncomputable def obstruction : Ideal S := RingHom.ker residue

@[simp] theorem residue_X : residue (X : S) = 0 := by simp [residue]
@[simp] theorem residue_C (a : A) : residue (C a) = augmentation a := by simp [residue]

theorem obstruction_not_projective : ¬ Module.Projective S obstruction := by
  classical
  intro hp
  obtain ⟨s,hs⟩ := hp.out
  let t : obstruction := ⟨X, by simp [obstruction, RingHom.mem_ker]⟩
  let c (g : G) : obstruction :=
    ⟨C (AddMonoidAlgebra.single g 1 - 1), by simp [obstruction, RingHom.mem_ker]⟩
  have hconst (i : obstruction) : (s t i).eval 0 = 0 := by
    apply no_invariant_element
    intro g
    have he : (X : S) • c g = C ((AddMonoidAlgebra.single g 1 : A) - 1) • t := by
      apply Subtype.ext
      change X * C _ = C _ * X
      exact mul_comm _ _
    have h := congrArg (fun x : obstruction => (s x i).eval 0) he
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, eval_mul, eval_X, eval_C,
      zero_mul] at h
    exact sub_eq_zero.mp (by simpa only [sub_mul,one_mul] using h.symm)
  let u : obstruction →₀ S := (s t).mapRange Polynomial.divX Polynomial.divX_zero
  have hu : (X : S) • u = s t := by
    ext1 i
    change X * divX (s t i) = s t i
    have hz : (s t i).coeff 0 = 0 := by simpa only [← coeff_zero_eq_eval_zero] using hconst i
    simpa only [hz,C_0,add_zero] using X_mul_divX_add (s t i)
  let l := Finsupp.linearCombination S (id : obstruction → obstruction)
  have hl : (X : S) • l u = t := by
    rw [← map_smul,hu]
    exact hs t
  have hp' := congrArg (fun y : obstruction => (y : S)) hl
  change (X : S) * (l u : S) = X at hp'
  have hcoeff := congrArg (fun p : S => p.coeff 1) hp'
  have hunit : (l u : S).coeff 0 = 1 := by simpa using hcoeff
  have hzero : residue (l u : S) = 0 := (l u).property
  have hres : residue (l u : S) = 1 := by
    change augmentation ((l u : S).eval 0) = 1
    rw [← coeff_zero_eq_eval_zero, hunit, map_one]
  exact zero_ne_one (hzero.symm.trans hres)

end Problem05a.PolynomialLower
