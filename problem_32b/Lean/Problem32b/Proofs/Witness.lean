import Problem32b.Proofs.Noetherian
import Problem32b.Proofs.Colons

noncomputable section
namespace Problem32b
open HahnSeries

namespace Laurent
abbrev F2 := ZMod 2
abbrev R := baseRing F2

instance R_noetherian : IsNoetherianRing R :=
  isNoetherianRing_of_ringEquiv (D F2) (ringEquiv F2)

theorem R_dimension : ringKrullDim R = 1 := by
  rw [← ringKrullDim_eq_of_ringEquiv (ringEquiv F2)]
  exact dimension_one F2

theorem R_mori : MoriCondition R := by
  unfold MoriCondition DivisorialIdeals
  infer_instance

def badIdeal : Ideal R where
  carrier := {x | (x : K F2) ∈ M F2}
  zero_mem' := (M_module F2).zero_mem
  add_mem' := fun ha hb => (M_module F2).add_mem ha hb
  smul_mem' := fun r _ ha => (M_module F2).smul_mem r.property ha

theorem badIdeal_set : idealSet R badIdeal = M F2 := by
  ext x
  constructor
  · rintro ⟨hx,hI⟩
    exact hI
  · intro h
    exact ⟨h.1,h⟩

theorem badIdeal_ne_bot : badIdeal ≠ ⊥ := by
  intro he
  let a : R := ⟨single 4 1,monomial_mem F2 (by norm_num [AllowedZ])⟩
  have ha : a ∈ badIdeal := monomial_M F2 4 (by norm_num [AllowedZ]) (by norm_num)
  rw [he,Submodule.mem_bot] at ha
  have hc := congrArg (fun z : R => (z : K F2).coeff 4) ha
  simp [a] at hc

theorem badIdeal_divisorial : vClosure R (idealSet R badIdeal) = idealSet R badIdeal := by
  rw [badIdeal_set]
  exact M_divisorial F2

theorem badIdeal_not_stable : ¬ StableSet (idealSet R badIdeal) := by
  rw [badIdeal_set]
  exact M_not_stable F2

end Laurent
end Problem32b
