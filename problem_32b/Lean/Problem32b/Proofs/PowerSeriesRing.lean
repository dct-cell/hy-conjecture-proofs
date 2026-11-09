import Mathlib

/-!
# The concrete ring in the HY counterexample

The ring consists of power series whose coefficients in degrees 1, 2, 3, 6, 7 vanish.
It is a genuine subring of the usual power series ring, not an axiomatized model.
-/

noncomputable section
open PowerSeries

namespace Problem32b

variable (k : Type*) [Field k]

def Allowed (n : ℕ) : Prop := n = 0 ∨ n = 4 ∨ n = 5 ∨ 8 ≤ n

instance (n : ℕ) : Decidable (Allowed n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem allowed_add {m n : ℕ} (hm : Allowed m) (hn : Allowed n) :
    Allowed (m + n) := by
  unfold Allowed at *
  omega

def seriesRing : Subring (PowerSeries k) where
  carrier := {f | ∀ n, ¬ Allowed n → coeff n f = 0}
  zero_mem' := by simp
  one_mem' := by
    intro n hn
    have h : n ≠ 0 := by intro e; exact hn (Or.inl e)
    simp [h]
  add_mem' := by
    intro f g hf hg n hn
    simp [hf n hn, hg n hn]
  neg_mem' := by
    intro f hf n hn
    simp [hf n hn]
  mul_mem' := by
    intro f g hf hg n hn
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have he : p.1 + p.2 = n := by simpa using hp
    by_cases h₁ : Allowed p.1
    · have h₂ : ¬ Allowed p.2 := by
        intro h₂
        exact hn (he ▸ allowed_add h₁ h₂)
      simp [hg p.2 h₂]
    · simp [hf p.1 h₁]

abbrev D := seriesRing k

theorem mem_seriesRing_iff (f : PowerSeries k) :
    f ∈ seriesRing k ↔
      coeff 1 f = 0 ∧ coeff 2 f = 0 ∧ coeff 3 f = 0 ∧
      coeff 6 f = 0 ∧ coeff 7 f = 0 := by
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 6 (by decide), h 7 (by decide)⟩
  · rintro ⟨h1, h2, h3, h6, h7⟩ n hn
    have h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 7 := by
      unfold Allowed at hn
      omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem C_mem (a : k) : C a ∈ seriesRing k := by
  rw [mem_seriesRing_iff]
  simp

theorem X_pow_mem {n : ℕ} (hn : Allowed n) :
    (X : PowerSeries k) ^ n ∈ seriesRing k := by
  intro m hm
  have hmn : m ≠ n := by intro e; exact hm (e ▸ hn)
  simp [coeff_X_pow, hmn]

theorem tail_mem (f : PowerSeries k) {n : ℕ} (hn : 8 ≤ n) :
    (X : PowerSeries k) ^ n * f ∈ seriesRing k := by
  intro m hm
  have hmn : m < n := by
    unfold Allowed at hm
    omega
  simp [coeff_X_pow_mul', Nat.not_le.mpr hmn]

def tailShift (n : ℕ) (f : PowerSeries k) : PowerSeries k :=
  PowerSeries.mk fun j => coeff (j + n) f

theorem coeff_tailShift (n j : ℕ) (f : PowerSeries k) :
    coeff j (tailShift k n f) = coeff (j + n) f := by
  simp [tailShift]

theorem normal_form (f : PowerSeries k) (hf : f ∈ seriesRing k) :
    f = C (coeff 0 f) + C (coeff 4 f) * X ^ 4 + C (coeff 5 f) * X ^ 5 +
      X ^ 8 * tailShift k 8 f := by
  obtain ⟨h1,h2,h3,h6,h7⟩ := (mem_seriesRing_iff k f).mp hf
  ext n
  by_cases h : n < 8
  · interval_cases n <;>
      simp [coeff_X_pow_mul', coeff_C, coeff_C_mul, coeff_tailShift,
        h1,h2,h3,h6,h7]
  · have h8 : 8 ≤ n := by omega
    have h0 : n ≠ 0 := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    simp [coeff_X_pow_mul', coeff_C, coeff_C_mul, coeff_tailShift,
      h8,h0,h4,h5, Nat.sub_add_cancel h8]

def t4 : D k := ⟨X^4, X_pow_mem k (by decide)⟩
def t5 : D k := ⟨X^5, X_pow_mem k (by decide)⟩
def t11 : D k := ⟨X^11, X_pow_mem k (by decide)⟩

def residue : D k →+* k :=
  (PowerSeries.constantCoeff (R := k)).comp (seriesRing k).subtype

def maximalIdeal : Ideal (D k) := RingHom.ker (residue k)

theorem mem_maximalIdeal_iff (f : D k) :
    f ∈ maximalIdeal k ↔ coeff 0 (f : PowerSeries k) = 0 := by
  simp [maximalIdeal, residue, coeff_zero_eq_constantCoeff]

end Problem32b
