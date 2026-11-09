import Problem32b.Proofs.PowerSeriesRing
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.KrullDimension.LocalRing

noncomputable section
open PowerSeries

namespace Problem32b
variable (k : Type*) [Field k]

def constant (a : k) : D k := ⟨C a, C_mem k a⟩
def monomial (n : ℕ) (h : Allowed n) : D k := ⟨X^n, X_pow_mem k h⟩
def tail (n : ℕ) (h : 8 ≤ n) (f : PowerSeries k) : D k :=
  ⟨X^n*f, tail_mem k f h⟩

theorem residue_surjective : Function.Surjective (residue k) := by
  intro a
  exact ⟨constant k a, by simp [residue, constant]⟩

instance maximalIdeal_isMaximal : (maximalIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (residue k) (residue_surjective k)

theorem maximal_normal_form (f : D k) (hf : f ∈ maximalIdeal k) :
    f =
      constant k (coeff 4 (f : PowerSeries k)) * t4 k +
      constant k (coeff 5 (f : PowerSeries k)) * t5 k +
      constant k (coeff 8 (f : PowerSeries k)) * monomial k 8 (by decide) +
      constant k (coeff 9 (f : PowerSeries k)) * monomial k 9 (by decide) +
      constant k (coeff 10 (f : PowerSeries k)) * monomial k 10 (by decide) +
      constant k (coeff 11 (f : PowerSeries k)) * t11 k +
      t4 k * tail k 8 (by decide) (tailShift k 12 f) := by
  apply Subtype.ext
  obtain ⟨h1,h2,h3,h6,h7⟩ := (mem_seriesRing_iff k _).mp f.property
  have h0 := (mem_maximalIdeal_iff k f).mp hf
  change (f : PowerSeries k) =
    C _ * X^4 + C _ * X^5 + C _ * X^8 + C _ * X^9 +
      C _ * X^10 + C _ * X^11 + X^4 * (X^8 * tailShift k 12 f)
  rw [← mul_assoc, ← pow_add]
  ext n
  by_cases h : n < 12
  · interval_cases n <;>
      simp [coeff_C_mul, coeff_X_pow_mul',
        h0,h1,h2,h3,h6,h7]
  · have hn : 12 ≤ n := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    have h8 : n ≠ 8 := by omega
    have h9 : n ≠ 9 := by omega
    have h10 : n ≠ 10 := by omega
    have h11 : n ≠ 11 := by omega
    simp [coeff_C_mul, coeff_X_pow_mul', coeff_tailShift,
      hn,h4,h5,h8,h9,h10,h11, Nat.sub_add_cancel hn]

def generators : Finset (D k) := by
  classical
  exact {t4 k,t5 k,monomial k 8 (by decide),monomial k 9 (by decide),
    monomial k 10 (by decide),t11 k}

theorem maximalIdeal_eq_span :
    maximalIdeal k = Ideal.span (generators k : Set (D k)) := by
  apply le_antisymm
  · intro f hf
    rw [maximal_normal_form k f hf]
    apply Ideal.add_mem
    · repeat' apply Ideal.add_mem
      all_goals
        apply Ideal.mul_mem_left
        apply Ideal.subset_span
        simp [generators]
    · apply Ideal.mul_mem_right
      apply Ideal.subset_span
      simp [generators]
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [generators, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply (mem_maximalIdeal_iff k _).mpr
      simp [t4,t5,t11,monomial]

theorem maximalIdeal_fg : (maximalIdeal k).FG := by
  exact ⟨generators k, (maximalIdeal_eq_span k).symm⟩

theorem t4_mem_of_nonzero_prime (P : Ideal (D k)) (hp : P.IsPrime)
    (hne : P ≠ ⊥) : t4 k ∈ P := by
  obtain ⟨f,hf,hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfv : (f : PowerSeries k) ≠ 0 := by
    intro h
    apply hf0
    exact Subtype.ext h
  obtain ⟨u,hu⟩ := isUnit_divided_by_X_pow_order hfv
  let n := (f : PowerSeries k).order.toNat
  let b : D k := tail k (3*n+32) (by omega) ((↑(u⁻¹) : PowerSeries k))
  have he : f*b = (t4 k)^(n+8) := by
    apply Subtype.ext
    change (f : PowerSeries k) * (X^(3*n+32) * (↑(u⁻¹) : PowerSeries k)) = (X^4)^(n+8)
    have hfac : (f : PowerSeries k) = X^n * (u : PowerSeries k) := by
      rw [hu]
      exact X_pow_order_mul_divXPowOrder.symm
    rw [hfac]
    calc
      (X^n * (u : PowerSeries k)) * (X^(3*n+32) * (↑(u⁻¹) : PowerSeries k))
          = X^n * X^(3*n+32) * ((u : PowerSeries k) * (↑(u⁻¹) : PowerSeries k)) := by ring
      _ = X^(n+(3*n+32)) := by simp [← pow_add]
      _ = (X^4)^(n+8) := by
        rw [← pow_mul]
        congr 1
        omega
  apply hp.mem_of_pow_mem (n := n+8)
  rw [← he]
  exact P.mul_mem_right b hf

theorem monomial_mem_of_t4_mem (P : Ideal (D k)) (hp : P.IsPrime)
    (h4 : t4 k ∈ P) (n : ℕ) (hn : Allowed n) (npos : 0 < n) :
    monomial k n hn ∈ P := by
  have he : (monomial k n hn)^4 = (t4 k)^n := by
    apply Subtype.ext
    change (X^n : PowerSeries k)^4 = (X^4)^n
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]
  apply hp.mem_of_pow_mem (n := 4)
  rw [he]
  exact Ideal.pow_mem_of_mem P h4 n npos

theorem nonzero_prime_eq_maximalIdeal (P : Ideal (D k)) (hp : P.IsPrime)
    (hne : P ≠ ⊥) : P = maximalIdeal k := by
  have h4 := t4_mem_of_nonzero_prime k P hp hne
  have hle : maximalIdeal k ≤ P := by
    rw [maximalIdeal_eq_span]
    apply Ideal.span_le.mpr
    intro f hf
    simp only [generators, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h4
    · exact monomial_mem_of_t4_mem k P hp h4 5 (by decide) (by decide)
    · exact monomial_mem_of_t4_mem k P hp h4 8 (by decide) (by decide)
    · exact monomial_mem_of_t4_mem k P hp h4 9 (by decide) (by decide)
    · exact monomial_mem_of_t4_mem k P hp h4 10 (by decide) (by decide)
    · exact monomial_mem_of_t4_mem k P hp h4 11 (by decide) (by decide)
  exact ((maximalIdeal_isMaximal k).eq_of_le hp.ne_top hle).symm

instance domain_noetherian : IsNoetherianRing (D k) :=
  IsNoetherianRing.of_prime_ne_bot fun P hp hn => by
    rw [nonzero_prime_eq_maximalIdeal k P hp hn]
    exact maximalIdeal_fg k

theorem maximalIdeal_ne_bot : maximalIdeal k ≠ ⊥ := by
  intro h
  have hm : t4 k ∈ maximalIdeal k := (mem_maximalIdeal_iff k _).mpr (by simp [t4])
  rw [h, Submodule.mem_bot] at hm
  have he := congrArg (fun f : D k => (f : PowerSeries k)) hm
  simp [t4] at he

theorem dimension_one : ringKrullDim (D k) = 1 := by
  have hnf : ¬ IsField (D k) :=
    Ring.not_isField_iff_exists_prime.mpr
      ⟨maximalIdeal k, maximalIdeal_ne_bot k, (maximalIdeal_isMaximal k).isPrime⟩
  have hn0 : ¬ ringKrullDim (D k) ≤ 0 := fun h => by
    have : Ring.KrullDimLE 0 (D k) := Ring.krullDimLE_iff.mpr h
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hle : Ring.KrullDimLE 1 (D k) :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun P hP hprime => by
      rw [nonzero_prime_eq_maximalIdeal k P hprime hP]
      infer_instance
  rw [Ring.krullDimLE_iff] at hle
  exact le_antisymm hle (Order.succ_le_of_lt (lt_of_not_ge hn0))

end Problem32b
