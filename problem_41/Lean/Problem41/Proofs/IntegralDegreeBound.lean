import Problem41.Spec

namespace Problem41
open Polynomial

/-- A polynomial's order of vanishing at zero is additive on its powers. -/
theorem natTrailingDegree_pow' {S : Type*} [CommRing S] [IsDomain S]
    (g : S[X]) (hg : g ≠ 0) (m : ℕ) :
    (g^m).natTrailingDegree = g.natTrailingDegree * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, natTrailingDegree_mul (pow_ne_zero _ hg) hg, ih]
    ring

/-- Integral dependence cannot decrease an integer-valued order.  The map is
into an actual polynomial ring over a domain, not a formal degree model. -/
theorem X_pow_dvd_of_integralOverIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S[X]) (I : Ideal R) (N : ℕ)
    (hI : ∀ y ∈ I, (X : S[X])^N ∣ φ y)
    {x : R} (hx : IntegralOverIdeal I x) : (X : S[X])^N ∣ φ x := by
  classical
  have hm : I.map φ ≤ Ideal.span {(X : S[X])^N} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact Ideal.mem_span_singleton.mpr (hI y hy)
  have hpowers (j : ℕ) (y : R) (hy : y ∈ I^j) :
      (X : S[X])^(N*j) ∣ φ y := by
    apply Ideal.mem_span_singleton.mp
    rw [pow_mul, ← Ideal.span_singleton_pow]
    apply Ideal.pow_right_mono hm j
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ hy
  by_cases hg : φ x = 0
  · simp [hg]
  let t := (φ x).natTrailingDegree
  have htd : (X : S[X])^t ∣ φ x := by
    apply X_pow_dvd_iff.mpr
    intro j hj
    exact coeff_eq_zero_of_lt_natTrailingDegree hj
  have hNt : N ≤ t := by
    by_contra h
    have hlt : t < N := Nat.lt_of_not_ge h
    obtain ⟨p, hp, he, hc⟩ := hx
    let m := p.natDegree
    have hzero : φ x ^ m + ∑ i ∈ Finset.range m, φ (p.coeff i) * φ x ^ i = 0 := by
      have hmap := congrArg φ he
      rw [eval_eq_sum_range] at hmap
      simp only [map_sum, map_mul, map_pow, map_zero] at hmap
      rw [Finset.sum_range_succ] at hmap
      simpa [m, hp.coeff_natDegree, add_comm] using hmap
    have hlow (i : ℕ) (hi : i ∈ Finset.range m) :
        (φ (p.coeff i) * φ x ^ i).coeff (t*m) = 0 := by
      have hil : i < m := Finset.mem_range.mp hi
      have hd : (X : S[X])^(N*(m-i)+t*i) ∣ φ (p.coeff i) * φ x ^ i := by
        rw [pow_add]
        exact mul_dvd_mul (hpowers (m-i) (p.coeff i) (hc i))
          (by simpa [pow_mul] using pow_dvd_pow_of_dvd htd i)
      have hs : t*m < N*(m-i)+t*i := by
        have hpos : 0 < (N-t)*(m-i) := Nat.mul_pos (Nat.sub_pos_of_lt hlt) (Nat.sub_pos_of_lt hil)
        have hN : N = t + (N-t) := by omega
        have hM : m = (m-i)+i := by omega
        nlinarith
      exact X_pow_dvd_iff.mp hd (t*m) hs
    have hz := congrArg (fun q : S[X] => q.coeff (t*m)) hzero
    simp only [coeff_add, finsetSum_coeff, coeff_zero] at hz
    rw [Finset.sum_eq_zero (fun i hi => hlow i hi), add_zero] at hz
    have hdg : (φ x^m).natTrailingDegree = t*m := natTrailingDegree_pow' (φ x) hg m
    have hnz := trailingCoeff_nonzero_iff_nonzero.mpr (pow_ne_zero m hg)
    exact hnz (by simpa [trailingCoeff, hdg] using hz)
  exact dvd_trans (pow_dvd_pow _ hNt) htd

end Problem41
