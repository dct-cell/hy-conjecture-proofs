import Problem32b.Proofs.LaurentRing
import Problem32b.Proofs.IdealSets

noncomputable section
open HahnSeries
namespace Problem32b.Laurent
variable (k : Type*) [Field k]

def M : Set (K k) := {z | z ∈ baseRing k ∧ z ∈ Tail k 4}
def E : Set (K k) := {z | ∀ i : ℤ, i < 4 → i ≠ 0 → z.coeff i = 0}

theorem M_sub_D : M k ⊆ baseRing k := fun _ h => h.1
theorem M_sub_V : M k ⊆ powerRing k := fun _ h => baseRing_le_powerRing k h.1
theorem E_sub_V : E k ⊆ powerRing k := by
  intro z hz
  apply (mem_powerRing_iff k z).mpr
  intro i hi
  exact hz i (by omega) (by omega)

theorem monomial_M (n : ℤ) (hn : AllowedZ n) (hn4 : 4 ≤ n) :
    single n (1:k) ∈ M k := by
  refine ⟨monomial_mem k hn, ?_⟩
  intro i hi
  have hne : i ≠ n := by omega
  simp [hne]

theorem monomial_E (n : ℤ) (hn : n = 0 ∨ 4 ≤ n) :
    single n (1:k) ∈ E k := by
  intro i hi h0
  have hne : i ≠ n := by rcases hn with rfl | hn <;> omega
  simp [hne]

theorem one_E : (1 : K k) ∈ E k := by
  simpa using monomial_E k 0 (Or.inl rfl)

theorem E_mul_M {a b : K k} (ha : a ∈ E k) (hb : b ∈ M k) :
    a*b ∈ M k := by
  have hc (i : ℤ) (hi : i < 8) (hz : b.coeff i = 0) : (a*b).coeff i = 0 := by
    rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have he := (Finset.mem_antidiagonal.mp hp).2.2
    by_cases hp1 : p.1 < 4
    · by_cases hp0 : p.1 = 0
      · have hp2 : p.2 = i := by omega
        simp [hp2,hz]
      · simp [ha p.1 hp1 hp0]
    · have hp2 : p.2 < 4 := by omega
      simp [hb.2 p.2 hp2]
  constructor
  · apply (mem_baseRing_iff k _).mpr
    intro i hi
    apply hc i (by unfold AllowedZ at hi; omega)
    exact (mem_baseRing_iff k b).mp hb.1 i hi
  · intro i hi
    exact hc i (by omega) (hb.2 i hi)

theorem colon_D_M : colon (baseRing k) (M k) = E k := by
  ext q
  constructor
  · intro h i hi h0
    let n : ℤ := if i = -4 ∨ i = 1 then 5 else 4
    have hn : single n (1:k) ∈ M k := by
      dsimp [n]
      split <;> apply monomial_M k <;> norm_num [AllowedZ]
    have hd := (mem_baseRing_iff k _).mp (h _ hn) (i+n)
    have hi' : ¬ AllowedZ (i+n) := by
      dsimp [n]
      split <;> unfold AllowedZ <;> omega
    simpa [HahnSeries.coeff_mul_single] using hd hi'
  · intro h b hb
    exact (E_mul_M k h hb).1

theorem colon_M_M : colon (M k) (M k) = E k := by
  apply Set.Subset.antisymm
  · intro q h
    rw [← colon_D_M]
    exact fun b hb => (h b hb).1
  · exact fun q h b hb => E_mul_M k h hb

theorem D_zero_const {q : K k} (hq : q ∈ baseRing k) :
    q ∈ M k ↔ q.coeff 0 = 0 := by
  constructor
  · exact fun h => h.2 0 (by norm_num [AllowedZ])
  · intro h
    refine ⟨hq, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using h
    · apply (mem_baseRing_iff k q).mp hq
      unfold AllowedZ
      omega

theorem colon_D_E : colon (baseRing k) (E k) = M k := by
  ext q
  constructor
  · intro h
    have hq : q ∈ baseRing k := by simpa using h 1 (one_E k)
    apply (D_zero_const k hq).mpr
    have h6 := (mem_baseRing_iff k _).mp
      (h _ (monomial_E k 6 (Or.inr (by norm_num [AllowedZ])))) 6 (by norm_num [AllowedZ])
    simpa [HahnSeries.coeff_mul_single] using h6
  · intro h b hb
    simpa [mul_comm] using (E_mul_M k hb h).1

theorem colon_E_M : colon (E k) (M k) = powerRing k := by
  ext q
  constructor
  · intro h
    apply (mem_powerRing_iff k q).mpr
    intro i hi
    let n : ℤ := if i = -4 then 5 else 4
    have hn : single n (1:k) ∈ M k := by
      dsimp [n]; split <;> apply monomial_M k <;> norm_num [AllowedZ]
    have hi4 : i+n < 4 := by dsimp [n]; split <;> omega
    have hi0 : i+n ≠ 0 := by dsimp [n]; split <;> omega
    simpa [HahnSeries.coeff_mul_single] using h _ hn (i+n) hi4 hi0
  · intro h b hb i hi h0
    have ht := tail_mul_power k hb.2 h
    simpa [mul_comm] using ht i hi

theorem M_divisorial : vClosure (baseRing k) (M k) = M k := by
  unfold vClosure
  rw [colon_D_M,colon_D_E]

theorem M_module : IsModuleSet (baseRing k) (M k) := by
  rw [← colon_D_E]
  exact moduleSet_colon _ (moduleSet_subring _)

theorem M_not_stable : ¬ StableSet (M k) := by
  intro h
  unfold StableSet at h
  rw [colon_M_M,colon_E_M] at h
  have h1 : (1 : K k) ∈ productSet (M k) (powerRing k) := h ▸ one_E k
  obtain ⟨l,hl,he⟩ := h1
  have hz : ((l.map fun p : K k × K k => p.1*p.2).sum).coeff 0 = 0 := by
    clear he h
    induction l with
    | nil => simp
    | cons p l ih =>
      have hp := hl p (by simp)
      have hp0 : (p.1*p.2).coeff 0 = 0 :=
        tail_mul_power k hp.1.2 hp.2 0 (by norm_num [AllowedZ])
      have hl' : ∀ p ∈ l, p.1 ∈ M k ∧ p.2 ∈ powerRing k :=
        fun p hp => hl p (by simp [hp])
      simp [hp0, ih hl']
  rw [← he] at hz
  simp at hz

end Problem32b.Laurent
