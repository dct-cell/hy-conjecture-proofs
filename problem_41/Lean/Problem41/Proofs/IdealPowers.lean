import Problem41.Proofs.MonomialIdeals

namespace Problem41
open MvPolynomial
open scoped Pointwise

noncomputable def exponent (i j l : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 l

@[simp] theorem exponent_zero (i j l : ℕ) : exponent i j l 0 = i := by simp [exponent]
@[simp] theorem exponent_one (i j l : ℕ) : exponent i j l 1 = j := by simp [exponent]
@[simp] theorem exponent_two (i j l : ℕ) : exponent i j l 2 = l := by simp [exponent]

theorem exponent_repr (d : Fin 3 →₀ ℕ) : exponent (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp

theorem exponent_add (i j l p q r : ℕ) :
    exponent (i+p) (j+q) (l+r) = exponent i j l + exponent p q r := by
  ext t
  fin_cases t <;> simp

noncomputable def decompositionIdeal (k : Type*) [Field k] (a b c n : ℕ) :
    Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ((fun d : Fin 3 →₀ ℕ => monomial d (1:k)) ''
    {d | Decomposes a b c n (d 0) (d 1) (d 2)})

theorem decomposes_succ_cases {a b c n i j l : ℕ}
    (h : Decomposes a b c (n+1) i j l) :
    ∃ p q r u v w, i=p+u ∧ j=q+v ∧ l=r+w ∧
      1 ≤ weight a b c p q r ∧ Decomposes a b c n u v w := by
  cases h with
  | cons hw ht => exact ⟨_,_,_,_,_,_,rfl,rfl,rfl,hw,ht⟩

theorem weightedIdeal_pow (k : Type*) [Field k] (a b c n : ℕ) :
    weightedIdeal k a b c 1 ^ n = decompositionIdeal k a b c n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    symm
    rw [Ideal.one_eq_top]
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    refine ⟨0, ?_, by simp⟩
    simpa using (Decomposes.zero (a:=a) (b:=b) (c:=c))
  | succ n ih =>
    rw [pow_succ', ih]
    apply le_antisymm
    · rw [weightedIdeal, decompositionIdeal, Ideal.span_mul_span]
      apply Ideal.span_le.mpr
      rintro f ⟨g, ⟨d, hd, rfl⟩, h, ⟨e, he, rfl⟩, rfl⟩
      change monomial d (1:k) * monomial e (1:k) ∈ _
      rw [monomial_mul_monomial, one_mul]
      apply Ideal.subset_span
      refine ⟨d+e, ?_, rfl⟩
      exact Decomposes.cons hd he
    · apply Ideal.span_le.mpr
      rintro f ⟨d, hd, rfl⟩
      obtain ⟨p,q,r,i,j,l,h0,h1,h2,hw,ht⟩ := decomposes_succ_cases hd
      have hd : d = exponent p q r + exponent i j l := by
        rw [← exponent_add, ← exponent_repr d]
        rw [h0,h1,h2]
      rw [hd]
      change monomial (exponent p q r + exponent i j l) (1:k) ∈ _
      rw [← one_mul (1:k), ← monomial_mul_monomial]
      apply Ideal.mul_mem_mul
      · apply Ideal.subset_span
        refine ⟨exponent p q r, ?_, rfl⟩
        simpa [exponentWeight] using hw
      · apply Ideal.subset_span
        refine ⟨exponent i j l, ?_, rfl⟩
        simpa using ht

theorem decomposes_mono {a b c n i j l p q r : ℕ}
    (hn : 0<n) (h : Decomposes a b c n i j l)
    (hi : i≤p) (hj : j≤q) (hl : l≤r) :
    Decomposes a b c n p q r := by
  cases h with
  | zero => omega
  | cons hw ht =>
    rename_i n' i' j' l' p' q' r'
    have hwp : 1 ≤ weight a b c (p-i') (q-j') (r-l') := by
      apply le_trans hw
      have hm := exponentWeight_mono a b c (d:=exponent p' q' r')
        (e:=exponent (p-i') (q-j') (r-l')) ?_
      · simpa [exponentWeight] using hm
      · intro t
        fin_cases t <;> simp <;> omega
    convert Decomposes.cons hwp ht using 1 <;> omega

theorem monomial_mem_weightedIdeal_pow (k : Type*) [Field k] (a b c n : ℕ)
    (hn : 0<n) (d : Fin 3 →₀ ℕ) :
    monomial d (1:k) ∈ weightedIdeal k a b c 1 ^ n ↔
      Decomposes a b c n (d 0) (d 1) (d 2) := by
  classical
  rw [weightedIdeal_pow, decompositionIdeal, mem_ideal_span_monomial_image]
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨e, he, hle⟩
    exact decomposes_mono hn he (hle 0) (hle 1) (hle 2)
  · intro h
    exact ⟨d,h,le_rfl⟩

end Problem41
