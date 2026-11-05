import Problem32b.Proofs.LaurentRing
import Problem32b.Proofs.FiniteQuotient

noncomputable section
open PowerSeries HahnSeries
namespace Problem32b.Laurent

theorem coeff_low (k : Type*) [Field k] (f g : PowerSeries k)
    (hf : f ∈ seriesRing k) (n : ℕ) (hn : n < 8) :
    PowerSeries.coeff n (f*g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff n g +
      (if 4 ≤ n then PowerSeries.coeff 4 f * PowerSeries.coeff (n-4) g else 0) +
      (if 5 ≤ n then PowerSeries.coeff 5 f * PowerSeries.coeff (n-5) g else 0) := by
  conv_lhs => rw [normal_form k f hf]
  simp [add_mul,mul_assoc,PowerSeries.coeff_X_pow_mul',show ¬8≤n by omega]

abbrev F := FiniteQuotient.F
abbrev A := FiniteQuotient.A
abbrev Q := FiniteQuotient.Q

def aCoords (d : K F) : A := ![d.coeff 0,d.coeff 4,d.coeff 5]
def qCoords (d : K F) : Q := ![d.coeff 1,d.coeff 2,d.coeff 3,d.coeff 6,d.coeff 7]
def aRepPS (a : A) : PowerSeries F :=
  PowerSeries.C (a 0) + PowerSeries.C (a 1)*PowerSeries.X^4 +
    PowerSeries.C (a 2)*PowerSeries.X^5
def qRepPS (q : Q) : PowerSeries F :=
  PowerSeries.C (q 0)*PowerSeries.X + PowerSeries.C (q 1)*PowerSeries.X^2 +
  PowerSeries.C (q 2)*PowerSeries.X^3 + PowerSeries.C (q 3)*PowerSeries.X^6 +
  PowerSeries.C (q 4)*PowerSeries.X^7
def aRep (a : A) : K F := (aRepPS a : LaurentSeries F)
def qRep (q : Q) : K F := (qRepPS q : LaurentSeries F)

theorem aRep_mem (a : A) : aRep a ∈ baseRing F := by
  refine ⟨aRepPS a, ?_, rfl⟩
  apply (seriesRing F).add_mem
  · apply (seriesRing F).add_mem
    · exact C_mem F _
    · exact (seriesRing F).mul_mem (C_mem F _) (X_pow_mem F (by decide))
  · exact (seriesRing F).mul_mem (C_mem F _) (X_pow_mem F (by decide))

theorem qRep_mem (q : Q) : qRep q ∈ powerRing F := ⟨qRepPS q,rfl⟩

theorem aCoords_aRep (a : A) : aCoords (aRep a) = a := by
  funext i
  fin_cases i <;> simp [aCoords,aRep,aRepPS]

theorem qCoords_qRep (q : Q) : qCoords (qRep q) = q := by
  funext i
  fin_cases i <;> simp [qCoords,qRep,qRepPS]

theorem qCoords_zero_iff {z : K F} (hz : z ∈ powerRing F) :
    qCoords z = 0 ↔ z ∈ baseRing F := by
  rcases hz with ⟨f,rfl⟩
  have hq : qCoords ((HahnSeries.ofPowerSeries ℤ F) f) = 0 ↔
      PowerSeries.coeff 1 f = 0 ∧ PowerSeries.coeff 2 f = 0 ∧
      PowerSeries.coeff 3 f = 0 ∧ PowerSeries.coeff 6 f = 0 ∧
      PowerSeries.coeff 7 f = 0 := by
    simp [qCoords,funext_iff,Fin.forall_fin_succ,PowerSeries.coeff_coe]
  rw [hq,← mem_seriesRing_iff]
  constructor
  · exact fun hf => ⟨f,hf,rfl⟩
  · rintro ⟨g,hg,he⟩
    have := HahnSeries.ofPowerSeries_injective he
    simpa [this] using hg

theorem aCoords_add (a b : K F) : aCoords (a+b) = aCoords a + aCoords b := by
  funext i; fin_cases i <;> simp [aCoords]

theorem aCoords_zero : aCoords (0 : K F) = 0 := by
  funext i; fin_cases i <;> simp [aCoords]

theorem aCoords_coe (f : PowerSeries F) :
    aCoords (f : LaurentSeries F) =
      ![PowerSeries.coeff 0 f,PowerSeries.coeff 4 f,PowerSeries.coeff 5 f] := by
  funext i
  fin_cases i <;> simp [aCoords,PowerSeries.coeff_coe]

theorem qCoords_coe (f : PowerSeries F) :
    qCoords (f : LaurentSeries F) =
      ![PowerSeries.coeff 1 f,PowerSeries.coeff 2 f,PowerSeries.coeff 3 f,
        PowerSeries.coeff 6 f,PowerSeries.coeff 7 f] := by
  funext i
  fin_cases i <;> simp [qCoords,PowerSeries.coeff_coe]

theorem aCoords_mul {a b : K F} (ha : a ∈ baseRing F) (hb : b ∈ baseRing F) :
    aCoords (a*b) = FiniteQuotient.mul (aCoords a) (aCoords b) := by
  rcases ha with ⟨f,hf,rfl⟩
  rcases hb with ⟨g,hg,rfl⟩
  have hlow (n : ℕ) (hn : n < 8) := coeff_low F f g hf n hn
  have h1 := (mem_seriesRing_iff F g).mp hg
  rw [← map_mul]
  change aCoords ((f*g : PowerSeries F) : LaurentSeries F) =
    FiniteQuotient.mul (aCoords (f : LaurentSeries F)) (aCoords (g : LaurentSeries F))
  rw [aCoords_coe,aCoords_coe,aCoords_coe]
  funext i
  fin_cases i <;>
    simp [FiniteQuotient.mul,hlow 0 (by decide),hlow 4 (by decide),hlow 5 (by decide),h1.1]

theorem qCoords_mul {a b : K F} (ha : a ∈ baseRing F) (hb : b ∈ powerRing F) :
    qCoords (a*b) = FiniteQuotient.act (aCoords a) (qCoords b) := by
  rcases ha with ⟨f,hf,rfl⟩
  rcases hb with ⟨g,rfl⟩
  have hlow (n : ℕ) (hn : n < 8) := coeff_low F f g hf n hn
  rw [← map_mul]
  change qCoords ((f*g : PowerSeries F) : LaurentSeries F) =
    FiniteQuotient.act (aCoords (f : LaurentSeries F)) (qCoords (g : LaurentSeries F))
  rw [qCoords_coe,aCoords_coe,qCoords_coe]
  funext i
  fin_cases i <;>
    simp [FiniteQuotient.act,hlow 1 (by decide),hlow 2 (by decide),hlow 3 (by decide),
      hlow 6 (by decide),hlow 7 (by decide)]

theorem same_aCoords_sub_tail {a b : K F} (ha : a ∈ baseRing F)
    (hb : b ∈ baseRing F) (he : aCoords a = aCoords b) : a-b ∈ Tail F 8 := by
  have h0 := congrFun he 0
  have h4 := congrFun he 1
  have h5 := congrFun he 2
  simp [aCoords] at h0 h4 h5
  intro n hn
  by_cases h : AllowedZ n
  · rcases h with rfl | rfl | rfl | h
    · simp [h0]
    · simp [h4]
    · simp [h5]
    · omega
  · simp [(mem_baseRing_iff F a).mp ha n h,(mem_baseRing_iff F b).mp hb n h]

end Problem32b.Laurent
