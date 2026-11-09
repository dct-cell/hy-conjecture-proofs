import Problem32b.Proofs.PowerSeriesRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
open PowerSeries HahnSeries

namespace Problem32b.Laurent
variable (k : Type*) [Field k]

abbrev K := LaurentSeries k
def AllowedZ (n : ℤ) : Prop := n = 0 ∨ n = 4 ∨ n = 5 ∨ 8 ≤ n

def baseRing : Subring (K k) :=
  (seriesRing k).map (HahnSeries.ofPowerSeries ℤ k)

def powerRing : Subring (K k) := (HahnSeries.ofPowerSeries ℤ k).range

theorem mem_powerRing_iff (z : K k) :
    z ∈ powerRing k ↔ ∀ n : ℤ, n < 0 → z.coeff n = 0 := by
  constructor
  · rintro ⟨f,rfl⟩ n hn
    change (f : LaurentSeries k).coeff n = 0
    simp [PowerSeries.coeff_coe, hn]
  · intro hz
    let f : PowerSeries k := PowerSeries.mk fun n => z.coeff n
    refine ⟨f, ?_⟩
    change (f : LaurentSeries k) = z
    ext n
    cases n with
    | ofNat n => simp [f, PowerSeries.coeff_coe]
    | negSucc n => simp [PowerSeries.coeff_coe, hz _ (Int.negSucc_lt_zero n)]

theorem mem_baseRing_iff (z : K k) :
    z ∈ baseRing k ↔ ∀ n : ℤ, ¬ AllowedZ n → z.coeff n = 0 := by
  constructor
  · rintro ⟨f,hf,rfl⟩ n hn
    change (f : LaurentSeries k).coeff n = 0
    cases n with
    | ofNat n =>
      have hn' : ¬ Allowed n := by
        intro ha
        apply hn
        rcases ha with h | h | h | h
        · subst n; exact Or.inl rfl
        · subst n; exact Or.inr (Or.inl rfl)
        · subst n; exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (by change (8:ℤ) ≤ (n:ℤ); omega)))
      simpa [PowerSeries.coeff_coe] using hf n hn'
    | negSucc n => simp [PowerSeries.coeff_coe]
  · intro hz
    let f : PowerSeries k := PowerSeries.mk fun n => z.coeff n
    have hf : f ∈ seriesRing k := by
      intro n hn
      simp only [f, coeff_mk]
      apply hz
      unfold AllowedZ
      unfold Allowed at hn
      omega
    refine ⟨f,hf, ?_⟩
    change (f : LaurentSeries k) = z
    ext n
    cases n with
    | ofNat n => simp [f, PowerSeries.coeff_coe]
    | negSucc n =>
      have hn : ¬ AllowedZ (Int.negSucc n) := by unfold AllowedZ; omega
      simp [PowerSeries.coeff_coe, hz _ hn]

theorem baseRing_le_powerRing : baseRing k ≤ powerRing k := by
  intro z hz
  apply (mem_powerRing_iff k z).mpr
  intro n hn
  apply (mem_baseRing_iff k z).mp hz
  unfold AllowedZ
  omega

def Tail (n : ℤ) : Set (K k) := {z | ∀ i : ℤ, i < n → z.coeff i = 0}

theorem tail_eight_le_baseRing : Tail k 8 ⊆ baseRing k := by
  intro z hz
  apply (mem_baseRing_iff k z).mpr
  intro n hn
  apply hz
  unfold AllowedZ at hn
  omega

theorem monomial_mem {n : ℤ} (hn : AllowedZ n) :
    (HahnSeries.single n (1:k) : K k) ∈ baseRing k := by
  apply (mem_baseRing_iff k _).mpr
  intro i hi
  have hne : n ≠ i := by intro e; exact hi (e ▸ hn)
  simp [Ne.symm hne]

theorem tail_mul_power {a b : K k} {n : ℤ}
    (ha : a ∈ Tail k n) (hb : b ∈ powerRing k) : a*b ∈ Tail k n := by
  intro i hi
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have he := (Finset.mem_antidiagonal.mp hp).2.2
  by_cases hp1 : p.1 < n
  · simp [ha _ hp1]
  · have hp2 : p.2 < 0 := by omega
    simp [(mem_powerRing_iff k b).mp hb _ hp2]

theorem tail_sub {a b : K k} {n : ℤ}
    (ha : a ∈ Tail k n) (hb : b ∈ Tail k n) : a-b ∈ Tail k n := by
  intro i hi
  simp [ha i hi, hb i hi]

def ringEquiv : D k ≃+* baseRing k :=
  (seriesRing k).equivMapOfInjective (HahnSeries.ofPowerSeries ℤ k)
    HahnSeries.ofPowerSeries_injective

instance faithful : FaithfulSMul (baseRing k) (K k) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  exact Subtype.val_injective

instance fractionRing : IsFractionRing (baseRing k) (K k) := by
  apply IsFractionRing.of_field
  intro z
  let n : ℤ := 8 + max 0 (-z.order)
  have hn : 8 ≤ n := by dsimp [n]; omega
  let s : K k := HahnSeries.single n 1
  have hs : s ∈ baseRing k := monomial_mem k (Or.inr (Or.inr (Or.inr hn)))
  have hzs : z*s ∈ baseRing k := by
    apply tail_eight_le_baseRing k
    intro i hi
    change (z * HahnSeries.single n 1).coeff i = 0
    rw [HahnSeries.coeff_mul_single, mul_one]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    dsimp [n]
    omega
  have hs0 : s ≠ 0 := by
    intro h
    have hc := congrArg (fun f : K k => f.coeff n) h
    simp [s] at hc
  refine ⟨⟨z*s,hzs⟩,⟨s,hs⟩,?_⟩
  change z = z*s/s
  simp [hs0]

end Problem32b.Laurent
