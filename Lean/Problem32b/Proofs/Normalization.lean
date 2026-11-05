import Problem32b.Proofs.LaurentRing
import Problem32b.Proofs.IdealSets

noncomputable section
open HahnSeries
namespace Problem32b.Laurent
variable (k : Type*) [Field k]

theorem nonnegative_order {z : K k} (hz : z ∈ powerRing k) : 0 ≤ z.order := by
  by_cases h0 : z = 0
  · simp [h0]
  · by_contra h
    have hc := (mem_powerRing_iff k z).mp hz z.order (by omega)
    exact h0 (HahnSeries.coeff_order_eq_zero.mp hc)

theorem mem_power_of_order {z : K k} (hz : 0 ≤ z.order) : z ∈ powerRing k := by
  apply (mem_powerRing_iff k z).mpr
  intro n hn
  apply HahnSeries.coeff_eq_zero_of_lt_order
  omega

theorem normalize (I : Set (K k)) (hI : IsModuleSet (baseRing k) I)
    (hID : I ⊆ baseRing k) (hne : ∃ z ∈ I, z ≠ 0)
    (hv : vClosure (baseRing k) I = I) :
    ∃ f L, f ∈ I ∧ f ≠ 0 ∧ IsModuleSet (baseRing k) L ∧
      (baseRing k : Set (K k)) ⊆ L ∧ L ⊆ powerRing k ∧
      vClosure (baseRing k) L = L ∧ I = (fun x => f*x) '' L := by
  classical
  let P : ℕ → Prop := fun n => ∃ f ∈ I, f ≠ 0 ∧ f.order = (n:ℤ)
  have hex : ∃ n, P n := by
    obtain ⟨f,hf,hf0⟩ := hne
    have ho := nonnegative_order k (baseRing_le_powerRing k (hID hf))
    exact ⟨f.order.toNat, f, hf, hf0, (Int.toNat_of_nonneg ho).symm⟩
  obtain ⟨f,hf,hf0,hord⟩ := Nat.find_spec hex
  let L : Set (K k) := {z | f*z ∈ I}
  have hmin (g : K k) (hg : g ∈ I) (hg0 : g ≠ 0) : f.order ≤ g.order := by
    have ho := nonnegative_order k (baseRing_le_powerRing k (hID hg))
    have hp : P g.order.toNat := ⟨g,hg,hg0,(Int.toNat_of_nonneg ho).symm⟩
    have hm := Nat.find_min' hex hp
    rw [hord]
    exact_mod_cast (show (Nat.find hex:ℤ) ≤ g.order by omega)
  have hIL : I = (fun x => f*x) '' L := by
    ext z
    constructor
    · intro hz
      exact ⟨z/f,by
          change f*(z/f) ∈ I
          have he : f*(z/f) = z := by field_simp
          rwa [he],
        by field_simp⟩
    · rintro ⟨z,hz,rfl⟩
      exact hz
  refine ⟨f,L,hf,hf0,?_,?_,?_,?_,hIL⟩
  · constructor
    · change f*0 ∈ I
      simpa using hI.zero_mem
    · intro a b ha hb
      change f*(a+b) ∈ I
      simpa [mul_add] using hI.add_mem ha hb
    · intro a ha
      change f*(-a) ∈ I
      simpa using hI.neg_mem ha
    · intro r a hr ha
      change f*(r*a) ∈ I
      simpa [mul_left_comm] using hI.smul_mem hr ha
  · intro r hr
    change f*r ∈ I
    simpa [mul_comm] using hI.smul_mem hr hf
  · intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hmul := HahnSeries.order_mul hf0 hz0
      have hm := hmin (f*z) hz (mul_ne_zero hf0 hz0)
      apply mem_power_of_order k
      omega
  · apply Set.Subset.antisymm
    · intro z hz
      change f*z ∈ I
      rw [← hv,hIL,scale_vClosure _ _ _ hf0]
      exact ⟨z,hz,rfl⟩
    · exact subset_vClosure _ _

end Problem32b.Laurent
