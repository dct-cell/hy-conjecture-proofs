import Problem05a.Spec

namespace Problem05a

instance : Countable G := inferInstance
instance : Countable A := inferInstance
instance : CharP A 3 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 3) A) 3 (by decide)

theorem triple_smul (g : G) : (3:ℕ) • g = g := by
  ext i
  simp only [Finsupp.smul_apply]
  have h : (2:ℕ) • g i = 0 := ZModModule.char_nsmul_eq_zero 2 (g i)
  simp only [show (3:ℕ)=2+1 from rfl, add_nsmul, one_nsmul, h, zero_add]

theorem cube_coeff (r : ZMod 3) : r^3=r := by
  exact ZMod.pow_card r

theorem cube_eq (x : A) : x^3=x := by
  induction x using AddMonoidAlgebra.induction_on with
  | of g =>
    change (AddMonoidAlgebra.single g (1:ZMod 3))^3 = AddMonoidAlgebra.single g 1
    simp [AddMonoidAlgebra.single_pow, triple_smul]
  | add x y hx hy => rw [add_pow_char x y 3, hx, hy]
  | smul r x hx => simp [smul_pow, cube_coeff, hx]

theorem vonNeumannRegular (x : A) : ∃ y : A, x*x*y=x := by
  exact ⟨x, by simpa only [pow_succ, pow_zero, one_mul] using cube_eq x⟩

end Problem05a
