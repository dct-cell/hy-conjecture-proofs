import Problem41.Proofs.MonomialIdeals

namespace Problem41
open MvPolynomial

/-- The integer degree obtained by clearing the three positive denominators. -/
def integerDegree (a b c : ℕ) (d : Fin 3 →₀ ℕ) : ℕ :=
  b * c * d 0 + a * c * d 1 + a * b * d 2

def variableWeight (a b c : ℕ) : Fin 3 → ℕ := ![b*c, a*c, a*b]

noncomputable def homogenize (k : Type*) [Field k] (a b c : ℕ) :
    MvPolynomial (Fin 3) k →+* Polynomial (MvPolynomial (Fin 3) k) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ variableWeight a b c i)

theorem integerDegree_add (a b c : ℕ) (d e : Fin 3 →₀ ℕ) :
    integerDegree a b c (d+e) = integerDegree a b c d + integerDegree a b c e := by
  simp only [integerDegree, Finsupp.add_apply]
  ring

theorem homogenize_monomial (k : Type*) [Field k] (a b c : ℕ)
    (d : Fin 3 →₀ ℕ) (r : k) :
    homogenize k a b c (MvPolynomial.monomial d r) =
      Polynomial.C (MvPolynomial.monomial d r) * Polynomial.X ^ integerDegree a b c d := by
  rw [homogenize, eval₂Hom_monomial, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_three, variableWeight, RingHom.comp_apply, map_mul, map_pow, mul_pow,
    integerDegree, pow_add, pow_mul]
  ring

theorem integerDegree_eq_scaledWeight {a b c : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (d : Fin 3 →₀ ℕ) :
    (integerDegree a b c d : ℚ) = (a*b*c : ℕ) * exponentWeight a b c d := by
  simp only [integerDegree, exponentWeight, weight, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- Retaining each original monomial in the coefficient ring prevents cancellation
between different monomials of the same weight. -/
theorem coeff_coeff_homogenize (k : Type*) [Field k] (a b c : ℕ)
    (f : MvPolynomial (Fin 3) k) (d : Fin 3 →₀ ℕ) (j : ℕ) :
    ((homogenize k a b c f).coeff j).coeff d =
      if integerDegree a b c d = j then f.coeff d else 0 := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | monomial e r =>
    rw [homogenize_monomial, Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases h : e = d
    · subst e
      split_ifs <;> simp_all
    · split_ifs <;> simp_all [MvPolynomial.coeff_monomial]

theorem X_pow_dvd_homogenize_iff (k : Type*) [Field k] (a b c N : ℕ)
    (f : MvPolynomial (Fin 3) k) :
    (Polynomial.X : Polynomial (MvPolynomial (Fin 3) k))^N ∣ homogenize k a b c f ↔
      ∀ d ∈ f.support, N ≤ integerDegree a b c d := by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h d hd
    by_contra hN
    have he := congrArg (fun g : MvPolynomial (Fin 3) k => g.coeff d)
      (h _ (Nat.lt_of_not_ge hN))
    rw [coeff_coeff_homogenize] at he
    simp [MvPolynomial.mem_support_iff.mp hd] at he
  · intro h j hj
    ext d
    rw [coeff_coeff_homogenize]
    by_cases he : integerDegree a b c d = j
    · have hd : d ∉ f.support := by
        intro hd
        have hh := h d hd
        omega
      simp only [MvPolynomial.mem_support_iff, not_not] at hd
      simp [he, hd]
    · simp [he]

theorem X_pow_dvd_homogenize_iff_mem (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (n : ℕ)
    (f : MvPolynomial (Fin 3) k) :
    (Polynomial.X : Polynomial (MvPolynomial (Fin 3) k))^(a*b*c*n) ∣ homogenize k a b c f ↔
      f ∈ weightedIdeal k a b c n := by
  rw [X_pow_dvd_homogenize_iff, mem_weightedIdeal]
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro hd
  have hpos : (0 : ℚ) < (a*b*c : ℕ) := by positivity
  rw [← Nat.cast_le (α := ℚ), Nat.cast_mul, integerDegree_eq_scaledWeight ha hb hc]
  exact mul_le_mul_iff_right₀ hpos

end Problem41
