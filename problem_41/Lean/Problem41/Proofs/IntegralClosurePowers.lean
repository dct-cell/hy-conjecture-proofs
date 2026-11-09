import Problem41.Proofs.IntegralClosure
import Problem41.Proofs.IdealPowers

namespace Problem41
open MvPolynomial

/-- The power filtration of the actual monomial ideal is bounded by the weight filtration. -/
theorem weightedIdeal_pow_le (k : Type*) [Field k] (a b c n : ℕ) :
    weightedIdeal k a b c 1 ^ n ≤ weightedIdeal k a b c n := by
  intro f hf
  rw [weightedIdeal_pow, decompositionIdeal, mem_ideal_span_monomial_image] at hf
  rw [mem_weightedIdeal]
  intro d hd
  obtain ⟨e, he, hle⟩ := hf d hd
  exact (decomposes_weight he).trans (exponentWeight_mono a b c hle)

/-- The integral closure of every positive power is described without assuming
normality or the finite box criterion. -/
theorem integral_closure_weightedIdeal_pow (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    {n : ℕ} (hn : 0<n) (f : MvPolynomial (Fin 3) k) :
    IntegralOverIdeal (weightedIdeal k a b c 1 ^ n) f ↔ f ∈ weightedIdeal k a b c n := by
  constructor
  · exact mem_weightedIdeal_of_integralOverIdeal k ha hb hc n _
      (weightedIdeal_pow_le k a b c n)
  · apply integralOverIdeal_of_mem_weightedIdeal k ha hb hc hn
    · simpa only [pow_mul] using Ideal.pow_mem_pow (X_a_mem_weightedIdeal k ha b c) n
    · simpa only [pow_mul] using Ideal.pow_mem_pow (X_b_mem_weightedIdeal k hb a c) n
    · simpa only [pow_mul] using Ideal.pow_mem_pow (X_c_mem_weightedIdeal k hc a b) n

/-- The finite criterion implies equality, not merely equality of integral closures. -/
theorem weightedIdeal_pow_eq_of_box (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hbox : BoxCriterion a b c) {n : ℕ} (hn : 0<n) :
    weightedIdeal k a b c 1 ^ n = weightedIdeal k a b c n := by
  apply le_antisymm (weightedIdeal_pow_le k a b c n)
  apply Ideal.span_le.mpr
  rintro f ⟨d,hd,rfl⟩
  change monomial d (1:k) ∈ weightedIdeal k a b c 1 ^ n
  rw [monomial_mem_weightedIdeal_pow k a b c n hn]
  exact (box_iff_all_decompositions ha hb hc).mp hbox n (d 0) (d 1) (d 2) hn hd

end Problem41
