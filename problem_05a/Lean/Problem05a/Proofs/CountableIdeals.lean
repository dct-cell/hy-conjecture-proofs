import Problem05a.Proofs.LocalPartition
import Problem05a.Proofs.GroupAlgebra

namespace Problem05a

/-- In a countable commutative ring satisfying x^3=x, every ideal is projective.
This proves the countable-regular-ring step for the actual coefficient ring. -/
theorem ideals_projective_of_cube {R : Type*} [CommRing R] [Countable R]
    (hcube : ∀ x:R, x^3=x) (I : Ideal R) : Module.Projective R I := by
  classical
  obtain ⟨a, ha⟩ := exists_surjective_nat I
  let e (n:ℕ) : R := (a n : R)^2
  let q (n:ℕ) : R := ∏ j ∈ Finset.range n, (1-e j)
  let f (n:ℕ) : R := q n * e n
  have he (n:ℕ) : IsIdempotentElem (e n) := by
    change (a n : R)^2 * (a n : R)^2 = (a n : R)^2
    calc
      (a n : R)^2 * (a n : R)^2 = (a n : R)^3 * (a n : R) := by ring
      _ = (a n : R)^2 := by rw [hcube]; ring
  have hq (n:ℕ) : IsIdempotentElem (q n) := by
    induction n with
    | zero => simpa [q] using (IsIdempotentElem.one : IsIdempotentElem (1:R))
    | succ n ih =>
      simpa [q, Finset.prod_range_succ] using ih.mul (he n).one_sub
  have hfmem (n:ℕ) : f n ∈ I := by
    apply I.mul_mem_left (q n)
    change (a n:R)^2 ∈ I
    simpa only [pow_two] using I.mul_mem_left (a n:R) (a n).property
  have hfid (n:ℕ) : f n * f n = f n := (hq n).mul (he n)
  have hann (m:ℕ) : (a m:R)*(1-e m)=0 := by
    dsimp [e]
    calc
      (a m:R)*(1-(a m:R)^2) = (a m:R) - (a m:R)^3 := by ring
      _ = 0 := by rw [hcube]; ring
  have hkill (m n:ℕ) (hm:m<n) : (a m:R)*q n=0 := by
    have hdiv : 1-e m ∣ q n := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hm)
    obtain ⟨r,hr⟩ := hdiv
    rw [hr, ← mul_assoc, hann, zero_mul]
  have hsum (n:ℕ) : ∑ j ∈ Finset.range n, f j = 1-q n := by
    induction n with
    | zero => simp [q]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [f, q, Finset.prod_range_succ]
      ring
  apply projective_of_local_partition I f hfmem hfid
  intro x
  obtain ⟨m,rfl⟩ := ha x
  refine ⟨m+1, ?_, ?_⟩
  · intro n hn
    dsimp [f]
    rw [← mul_assoc, hkill m n (by omega), zero_mul]
  · rw [hsum, mul_sub, mul_one, hkill m (m+1) (by omega), sub_zero]

theorem ideals_of_A_projective (I : Ideal A) : Module.Projective A I :=
  ideals_projective_of_cube cube_eq I

end Problem05a
