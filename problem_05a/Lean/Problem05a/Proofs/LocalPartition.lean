import Problem05a.Spec

namespace Problem05a

/-- A locally finite idempotent partition gives an actual retraction from a free
module, hence projectivity. This is an auxiliary lemma, not the global-dimension result. -/
theorem projective_of_local_partition {R : Type*} [CommRing R]
    (I : Ideal R) (e : ℕ → R) (he : ∀ n, e n ∈ I) (hi : ∀ n, e n * e n = e n)
    (hloc : ∀ x : I, ∃ N : ℕ,
      (∀ n, N ≤ n → (x:R)*e n=0) ∧
      (x:R) * ∑ n ∈ Finset.range N, e n = (x:R)) : Module.Projective R I := by
  classical
  choose N htail hsum using hloc
  let v (x:I) : ℕ →₀ R := Finsupp.onFinset (Finset.range (N x))
    (fun n => (x:R)*e n) (by
      intro n hn
      apply Finset.mem_range.mpr
      by_contra h
      exact hn (htail x n (Nat.le_of_not_gt h)))
  let i : I →ₗ[R] (ℕ →₀ R) := {
    toFun := v
    map_add' := by intro x y; ext n; simp [v, add_mul]
    map_smul' := by intro r x; ext n; simp [v, mul_assoc]
  }
  let s : (ℕ →₀ R) →ₗ[R] I := Finsupp.linearCombination R (fun n => (⟨e n,he n⟩:I))
  apply Module.Projective.of_split i s
  ext x
  change ((Finsupp.linearCombination R (fun n => (⟨e n,he n⟩:I))) (v x) : R) = (x:R)
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (v x) (Finsupp.support_onFinset_subset) _ (by simp)]
  simp only [v, Finsupp.onFinset_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  simpa only [smul_eq_mul, mul_assoc, hi, ← Finset.mul_sum] using hsum x

end Problem05a
