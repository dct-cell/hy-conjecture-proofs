import Problem41.Proofs.Homogenization
import Problem41.Proofs.IntegralDegreeBound
import Problem41.Proofs.ReesCriterion

namespace Problem41
open MvPolynomial

/-- A monomial above the defining plane has a positive power in the corresponding
power of any ideal containing the three axis monomials. -/
theorem weighted_monomial_power (k : Type*) [Field k]
    {a b c n : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hn : 0<n)
    (H : Ideal (MvPolynomial (Fin 3) k))
    (h0 : X 0 ^ (a*n) ∈ H) (h1 : X 1 ^ (b*n) ∈ H) (h2 : X 2 ^ (c*n) ∈ H)
    (d : Fin 3 →₀ ℕ) (hd : (n:ℚ) ≤ exponentWeight a b c d) :
    ∃ N : ℕ, 0<N ∧ monomial d (1:k)^N ∈ H^N := by
  let N := a*b*c*n
  have hN : 0<N := by dsimp [N]; positivity
  have hle : N ≤ integerDegree a b c d := by
    have hs := mul_le_mul_of_nonneg_left hd (show (0:ℚ) ≤ (a*b*c:ℕ) by positivity)
    rw [← integerDegree_eq_scaledWeight ha hb hc] at hs
    exact_mod_cast hs
  have hprod :
      (X 0 ^ (a*n)) ^ (b*c*d 0) * (X 1 ^ (b*n)) ^ (a*c*d 1) *
        (X 2 ^ (c*n)) ^ (a*b*d 2) ∈ H ^ integerDegree a b c d := by
    unfold integerDegree
    rw [pow_add, pow_add]
    exact Ideal.mul_mem_mul
      (Ideal.mul_mem_mul (Ideal.pow_mem_pow h0 _) (Ideal.pow_mem_pow h1 _))
      (Ideal.pow_mem_pow h2 _)
  have heq : monomial d (1:k)^N =
      (X 0 ^ (a*n)) ^ (b*c*d 0) * (X 1 ^ (b*n)) ^ (a*c*d 1) *
        (X 2 ^ (c*n)) ^ (a*b*d 2) := by
    simp only [X_pow_eq_monomial, monomial_pow, one_pow, monomial_mul_monomial, one_mul]
    apply congrArg (fun e : Fin 3 →₀ ℕ => monomial e (1:k))
    ext i
    fin_cases i <;> simp [N, Finsupp.smul_apply, smul_eq_mul] <;> ring
  exact ⟨N,hN,Ideal.pow_le_pow_right hle (heq.symm ▸ hprod)⟩

theorem integralOverIdeal_of_mem_weightedIdeal (k : Type*) [Field k]
    {a b c n : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hn : 0<n)
    (H : Ideal (MvPolynomial (Fin 3) k))
    (h0 : X 0 ^ (a*n) ∈ H) (h1 : X 1 ^ (b*n) ∈ H) (h2 : X 2 ^ (c*n) ∈ H)
    {f : MvPolynomial (Fin 3) k} (hf : f ∈ weightedIdeal k a b c n) :
    IntegralOverIdeal H f := by
  apply integralOverIdeal_of_span_powers (s :=
    (fun d : Fin 3 →₀ ℕ => monomial d (1:k)) '' {d | (n:ℚ) ≤ exponentWeight a b c d}) _ hf
  rintro g ⟨d,hd,rfl⟩
  exact weighted_monomial_power k ha hb hc hn H h0 h1 h2 d hd

/-- Integral dependence preserves the actual weighted support condition. -/
theorem mem_weightedIdeal_of_integralOverIdeal (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (n : ℕ)
    (H : Ideal (MvPolynomial (Fin 3) k)) (hH : H ≤ weightedIdeal k a b c n)
    {f : MvPolynomial (Fin 3) k} (hf : IntegralOverIdeal H f) :
    f ∈ weightedIdeal k a b c n := by
  apply (X_pow_dvd_homogenize_iff_mem k ha hb hc n f).mp
  apply X_pow_dvd_of_integralOverIdeal (homogenize k a b c) H (a*b*c*n) _ hf
  intro y hy
  exact (X_pow_dvd_homogenize_iff_mem k ha hb hc n y).mpr (hH hy)

theorem X_a_mem_weightedIdeal (k : Type*) [Field k]
    {a : ℕ} (ha : 0<a) (b c : ℕ) :
    (X 0 : MvPolynomial (Fin 3) k)^a ∈ weightedIdeal k a b c 1 := by
  rw [X_pow_eq_monomial, monomial_mem_weightedIdeal]
  simp [exponentWeight, weight, ha.ne']

theorem X_b_mem_weightedIdeal (k : Type*) [Field k]
    {b : ℕ} (hb : 0<b) (a c : ℕ) :
    (X 1 : MvPolynomial (Fin 3) k)^b ∈ weightedIdeal k a b c 1 := by
  rw [X_pow_eq_monomial, monomial_mem_weightedIdeal]
  simp [exponentWeight, weight, hb.ne']

theorem X_c_mem_weightedIdeal (k : Type*) [Field k]
    {c : ℕ} (hc : 0<c) (a b : ℕ) :
    (X 2 : MvPolynomial (Fin 3) k)^c ∈ weightedIdeal k a b c 1 := by
  rw [X_pow_eq_monomial, monomial_mem_weightedIdeal]
  simp [exponentWeight, weight, hc.ne']

theorem pureIdeal_le_weightedIdeal (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    pureIdeal k a b c ≤ weightedIdeal k a b c 1 := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact X_a_mem_weightedIdeal k ha b c
  · exact X_b_mem_weightedIdeal k hb a c
  · exact X_c_mem_weightedIdeal k hc a b

/-- Integral closure of the axis ideal, with integrality interpreted by monic
polynomial equations over its ideal powers. -/
theorem integral_closure_pureIdeal (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (f : MvPolynomial (Fin 3) k) :
    IntegralOverIdeal (pureIdeal k a b c) f ↔ f ∈ weightedIdeal k a b c 1 := by
  constructor
  · exact mem_weightedIdeal_of_integralOverIdeal k ha hb hc 1 _
      (pureIdeal_le_weightedIdeal k ha hb hc)
  · apply integralOverIdeal_of_mem_weightedIdeal k ha hb hc (by omega)
    all_goals
      simp only [mul_one]
      apply Ideal.subset_span
      simp

end Problem41
