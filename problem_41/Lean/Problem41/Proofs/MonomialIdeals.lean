import Problem41.Proofs.FiniteCriterion

namespace Problem41

open MvPolynomial

def exponentWeight (a b c : ℕ) (d : Fin 3 →₀ ℕ) : ℚ :=
  weight a b c (d 0) (d 1) (d 2)

noncomputable def weightedIdeal (k : Type*) [Field k] (a b c n : ℕ) :
    Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ((fun d : Fin 3 →₀ ℕ => monomial d (1 : k)) ''
    {d | (n : ℚ) ≤ exponentWeight a b c d})

theorem exponentWeight_mono (a b c : ℕ) {d e : Fin 3 →₀ ℕ} (h : d ≤ e) :
    exponentWeight a b c d ≤ exponentWeight a b c e := by
  unfold exponentWeight weight
  have h0 : (d 0 : ℚ) ≤ e 0 := by exact_mod_cast h 0
  have h1 : (d 1 : ℚ) ≤ e 1 := by exact_mod_cast h 1
  have h2 : (d 2 : ℚ) ≤ e 2 := by exact_mod_cast h 2
  have ha : (0 : ℚ) ≤ a := by positivity
  have hb : (0 : ℚ) ≤ b := by positivity
  have hc : (0 : ℚ) ≤ c := by positivity
  exact add_le_add (add_le_add (div_le_div_of_nonneg_right h0 ha)
    (div_le_div_of_nonneg_right h1 hb)) (div_le_div_of_nonneg_right h2 hc)

/-- Membership in the actual polynomial ideal is a support condition. -/
theorem mem_weightedIdeal (k : Type*) [Field k] (a b c n : ℕ)
    (f : MvPolynomial (Fin 3) k) :
    f ∈ weightedIdeal k a b c n ↔
      ∀ d ∈ f.support, (n : ℚ) ≤ exponentWeight a b c d := by
  rw [weightedIdeal, mem_ideal_span_monomial_image]
  constructor
  · intro h d hd
    obtain ⟨e,he,hle⟩ := h d hd
    exact le_trans he (exponentWeight_mono a b c hle)
  · intro h d hd
    exact ⟨d, h d hd, le_rfl⟩

theorem monomial_mem_weightedIdeal (k : Type*) [Field k] (a b c n : ℕ)
    (d : Fin 3 →₀ ℕ) :
    monomial d (1 : k) ∈ weightedIdeal k a b c n ↔
      (n : ℚ) ≤ exponentWeight a b c d := by
  rw [mem_weightedIdeal]
  simp

end Problem41
