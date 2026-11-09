import Problem32b.Proofs.Witness
import Problem32b.Proofs.TwoGeneration

noncomputable section
namespace Problem32b.Laurent

theorem all_ordinary_divisorial_ideals_two_generated
    (I : Ideal R) (hne : I ≠ ⊥)
    (hv : vClosure R (idealSet R I) = idealSet R I) :
    ∃ a b : R, a ∈ I ∧ b ∈ I ∧
      vClosure R (twoSpan R (a : K F2) (b : K F2)) = idealSet R I := by
  have hne' : ∃ z ∈ idealSet R I, z ≠ 0 := by
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨x,⟨x.property,hx⟩,?_⟩
    intro he
    exact hx0 (Subtype.ext he)
  have hsub : idealSet R I ⊆ (R : Set (K F2)) := by
    rintro x ⟨hx,_⟩
    exact hx
  obtain ⟨a,ha,b,hb,he⟩ :=
    all_divisorial_ideals_two_generated (idealSet R I) (idealSet_isModule R I) hsub hne' hv
  rcases ha with ⟨haR,haI⟩
  rcases hb with ⟨hbR,hbI⟩
  exact ⟨⟨a,haR⟩,⟨b,hbR⟩,haI,hbI,he⟩

/-- The entire counterexample, including the universal two-v-generation hypothesis.
    All ideals in this statement are ordinary mathlib ideals of the concrete domain R.
    Colon and product are evaluated in the genuine fraction field F2((t)). -/
theorem problem32b_counterexample :
    IsDomain R ∧ IsFractionRing R (K F2) ∧ IsNoetherianRing R ∧
    ringKrullDim R = 1 ∧ MoriCondition R ∧
    (∀ I : Ideal R, I ≠ ⊥ → vClosure R (idealSet R I) = idealSet R I →
      ∃ a b : R, a ∈ I ∧ b ∈ I ∧
        vClosure R (twoSpan R (a : K F2) (b : K F2)) = idealSet R I) ∧
    (∃ I : Ideal R, I ≠ ⊥ ∧ vClosure R (idealSet R I) = idealSet R I ∧
      ¬ StableSet (idealSet R I)) := by
  exact ⟨inferInstance,inferInstance,inferInstance,R_dimension,R_mori,
    all_ordinary_divisorial_ideals_two_generated,
    badIdeal,badIdeal_ne_bot,badIdeal_divisorial,badIdeal_not_stable⟩

end Problem32b.Laurent
