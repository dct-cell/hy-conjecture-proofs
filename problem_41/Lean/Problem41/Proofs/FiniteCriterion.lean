import Problem41.Spec

namespace Problem41

theorem decideBox_correct (a b c : ℕ) :
    decideBox a b c = true ↔ BoxCriterion a b c := by
  simp [decideBox, BoxCriterion]
  constructor
  · intro h i hi j hj l hl hw
    rcases h i hi j hj l hl with hlt | he
    · exact False.elim ((not_lt.mpr hw) hlt)
    · exact he
  · intro h i hi j hj l hl
    by_cases hw : 2 ≤ weight a b c i j l
    · exact Or.inr (h i hi j hj l hl hw)
    · exact Or.inl (lt_of_not_ge hw)

/-- Decomposition into n exponent vectors of weight at least one. -/
inductive Decomposes (a b c : ℕ) : ℕ → ℕ → ℕ → ℕ → Prop
  | zero : Decomposes a b c 0 0 0 0
  | cons {n i j l p q r : ℕ} :
      1 ≤ weight a b c p q r → Decomposes a b c n i j l →
      Decomposes a b c (n+1) (p+i) (q+j) (r+l)

theorem weight_add (a b c i j l p q r : ℕ) :
    weight a b c (i+p) (j+q) (l+r) =
      weight a b c i j l + weight a b c p q r := by
  simp only [weight, Nat.cast_add, add_div]
  ring

theorem weight_sub (a b c i j l p q r : ℕ)
    (hp : p ≤ i) (hq : q ≤ j) (hr : r ≤ l) :
    weight a b c (i-p) (j-q) (l-r) =
      weight a b c i j l - weight a b c p q r := by
  simp only [weight, Nat.cast_sub hp, Nat.cast_sub hq, Nat.cast_sub hr, sub_div]
  ring

theorem decomposes_weight {a b c n i j l : ℕ}
    (h : Decomposes a b c n i j l) : (n : ℚ) ≤ weight a b c i j l := by
  induction h with
  | zero => simp [weight]
  | cons hw hd ih =>
    rw [weight_add]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith


theorem weight_unit_a {a : ℕ} (ha : 0 < a) (b c : ℕ) :
    weight a b c a 0 0 = 1 := by
  simp [weight, ha.ne']

theorem weight_unit_b {b : ℕ} (hb : 0 < b) (a c : ℕ) :
    weight a b c 0 b 0 = 1 := by
  simp [weight, hb.ne']

theorem weight_unit_c {c : ℕ} (hc : 0 < c) (a b : ℕ) :
    weight a b c 0 0 c = 1 := by
  simp [weight, hc.ne']

theorem one_decomposes {a b c i j l : ℕ}
    (h : 1 ≤ weight a b c i j l) : Decomposes a b c 1 i j l := by
  simpa using (Decomposes.cons h (Decomposes.zero (a := a) (b := b) (c := c)))

theorem prepend_decomposition {a b c n i j l p q r : ℕ}
    (hp : p ≤ i) (hq : q ≤ j) (hr : r ≤ l)
    (hw : 1 ≤ weight a b c p q r)
    (hd : Decomposes a b c n (i-p) (j-q) (l-r)) :
    Decomposes a b c (n+1) i j l := by
  have h := Decomposes.cons hw hd
  simpa only [Nat.add_sub_of_le hp, Nat.add_sub_of_le hq, Nat.add_sub_of_le hr] using h

theorem box_implies_two_split {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hbox : BoxCriterion a b c)
    (i j l : ℕ) (hw : 2 ≤ weight a b c i j l) :
    ∃ p ≤ i, ∃ q ≤ j, ∃ r ≤ l,
      1 ≤ weight a b c p q r ∧
      1 ≤ weight a b c (i-p) (j-q) (l-r) := by
  by_cases hi : a ≤ i
  · refine ⟨a, hi, 0, Nat.zero_le _, 0, Nat.zero_le _, ?_, ?_⟩
    · rw [weight_unit_a ha]
    · have hs := weight_sub a b c i j l a 0 0 hi (Nat.zero_le _) (Nat.zero_le _)
      rw [weight_unit_a ha] at hs
      linarith
  by_cases hj : b ≤ j
  · refine ⟨0, Nat.zero_le _, b, hj, 0, Nat.zero_le _, ?_, ?_⟩
    · rw [weight_unit_b hb]
    · have hs := weight_sub a b c i j l 0 b 0 (Nat.zero_le _) hj (Nat.zero_le _)
      rw [weight_unit_b hb] at hs
      linarith
  by_cases hl : c ≤ l
  · refine ⟨0, Nat.zero_le _, 0, Nat.zero_le _, c, hl, ?_, ?_⟩
    · rw [weight_unit_c hc]
    · have hs := weight_sub a b c i j l 0 0 c (Nat.zero_le _) (Nat.zero_le _) hl
      rw [weight_unit_c hc] at hs
      linarith
  exact hbox i (by omega) j (by omega) l (by omega) hw

theorem large_coordinate {a b c i j l : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw : 3 ≤ weight a b c i j l) : a ≤ i ∨ b ≤ j ∨ c ≤ l := by
  by_contra h
  push Not at h
  have h1 : (i : ℚ) / a < 1 :=
    (div_lt_one (by exact_mod_cast ha)).mpr (by exact_mod_cast h.1)
  have h2 : (j : ℚ) / b < 1 :=
    (div_lt_one (by exact_mod_cast hb)).mpr (by exact_mod_cast h.2.1)
  have h3 : (l : ℚ) / c < 1 :=
    (div_lt_one (by exact_mod_cast hc)).mpr (by exact_mod_cast h.2.2)
  unfold weight at hw
  linarith

theorem all_decompositions_of_box {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hbox : BoxCriterion a b c)
    (n : ℕ) : ∀ i j l : ℕ, 0 < n → (n : ℚ) ≤ weight a b c i j l →
      Decomposes a b c n i j l := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j l hn hw
    by_cases h1 : n = 1
    · subst n; exact one_decomposes hw
    by_cases h2 : n = 2
    · subst n
      obtain ⟨p,hp,q,hq,r,hr,hv,hu⟩ := box_implies_two_split ha hb hc hbox i j l hw
      exact prepend_decomposition hp hq hr hv (one_decomposes hu)
    have hn3 : 3 ≤ n := by omega
    have hw3 : 3 ≤ weight a b c i j l := le_trans (by exact_mod_cast hn3) hw
    have step : ∀ p q r : ℕ, p ≤ i → q ≤ j → r ≤ l →
        weight a b c p q r = 1 → Decomposes a b c n i j l := by
      intro p q r hp hq hr hv
      have hs := weight_sub a b c i j l p q r hp hq hr
      have hcast : ((n-1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      have hd := ih (n-1) (by omega) (i-p) (j-q) (l-r) (by omega)
        (by rw [hcast, hs, hv]; linarith)
      have hh := prepend_decomposition hp hq hr (le_of_eq hv.symm) hd
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hh
    rcases large_coordinate ha hb hc hw3 with hi | hj | hl
    · exact step a 0 0 hi (Nat.zero_le _) (Nat.zero_le _) (weight_unit_a ha b c)
    · exact step 0 b 0 (Nat.zero_le _) hj (Nat.zero_le _) (weight_unit_b hb a c)
    · exact step 0 0 c (Nat.zero_le _) (Nat.zero_le _) hl (weight_unit_c hc a b)


theorem two_decomposes_split {a b c i j l : ℕ}
    (h : Decomposes a b c 2 i j l) :
    ∃ p ≤ i, ∃ q ≤ j, ∃ r ≤ l,
      1 ≤ weight a b c p q r ∧
      1 ≤ weight a b c (i-p) (j-q) (l-r) := by
  cases h with
  | @cons n i j l p q r hp hd =>
    refine ⟨p, by omega, q, by omega, r, by omega, hp, ?_⟩
    simpa using decomposes_weight hd

theorem box_iff_all_decompositions {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    BoxCriterion a b c ↔
      ∀ n i j l : ℕ, 0 < n → (n : ℚ) ≤ weight a b c i j l →
        Decomposes a b c n i j l := by
  constructor
  · exact fun h => all_decompositions_of_box ha hb hc h
  · intro h i _ j _ l _ hw
    exact two_decomposes_split (h 2 i j l (by decide) hw)

end Problem41
