import Problem41.Spec
import Problem41.Proofs.IntegralClosurePowers

namespace Problem41
open MvPolynomial

theorem box_iff_normalIntegralClosure (k : Type*) [Field k]
    {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    BoxCriterion a b c ↔ NormalIntegralClosure k a b c := by
  constructor
  · intro hbox
    refine ⟨weightedIdeal k a b c 1, ?_, ?_⟩
    · intro f
      exact (integral_closure_pureIdeal k ha hb hc f).symm
    · intro n hn f hf
      have hw := (integral_closure_weightedIdeal_pow k ha hb hc hn f).mp hf
      rwa [weightedIdeal_pow_eq_of_box k ha hb hc hbox hn]
  · rintro ⟨I,hI,hpow⟩
    have heq : I = weightedIdeal k a b c 1 := by
      ext f
      exact (hI f).trans (integral_closure_pureIdeal k ha hb hc f)
    subst I
    apply (box_iff_all_decompositions ha hb hc).mpr
    intro n i j l hn hw
    have hm : monomial (exponent i j l) (1:k) ∈ weightedIdeal k a b c n := by
      rw [monomial_mem_weightedIdeal]
      simpa [exponentWeight] using hw
    have hi := hpow n hn _ ((integral_closure_weightedIdeal_pow k ha hb hc hn _).mpr hm)
    simpa using (monomial_mem_weightedIdeal_pow k a b c n hn (exponent i j l)).mp hi

/-- The complete all-fields, all-positive-triples classification in the fixed specification. -/
theorem solution : Claim := by
  intro k inst a b c ha hb hc
  exact (decideBox_correct a b c).trans (box_iff_normalIntegralClosure k ha hb hc)

/-- The expanded theorem is also an explicit audit entry point. -/
theorem complete_classification (k : Type*) [Field k]
    (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    decideBox a b c = true ↔
      ∃ I : Ideal (MvPolynomial (Fin 3) k),
        (∀ f, f ∈ I ↔ IntegralOverIdeal (pureIdeal k a b c) f) ∧
        ∀ n : ℕ, 0<n → ∀ f, (IntegralOverIdeal (I^n) f ↔ f∈I^n) := by
  rw [(decideBox_correct a b c).trans (box_iff_normalIntegralClosure k ha hb hc)]
  constructor
  · rintro ⟨I,hI,hpow⟩
    exact ⟨I,hI,fun n hn f => ⟨hpow n hn f,integralOverIdeal_of_mem⟩⟩
  · rintro ⟨I,hI,hpow⟩
    exact ⟨I,hI,fun n hn f => (hpow n hn f).mp⟩

end Problem41
