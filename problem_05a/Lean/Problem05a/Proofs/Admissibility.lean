import Problem05a.Proofs.GroupAlgebra

namespace Problem05a

theorem twice_smul (g : G) : (2:ℕ) • g = 0 := by
  ext i
  simp only [Finsupp.smul_apply, Finsupp.zero_apply]
  exact ZModModule.char_nsmul_eq_zero 2 (g i)

theorem orders (g : G) : addOrderOf g = 1 ∨ addOrderOf g = 2 := by
  apply (Nat.dvd_prime Nat.prime_two).mp
  exact addOrderOf_dvd_of_nsmul_eq_zero (twice_smul g)

theorem admissible_of_char_three (R : Type*) [CommRing R] [Algebra (ZMod 3) R] :
    Admissible R := by
  intro g hg
  rcases orders g with h | h
  · simp [h]
  · rw [h]
    have ht : IsUnit ((2:ℕ):ZMod 3) := isUnit_iff_ne_zero.mpr (by decide)
    have hu := ht.map (algebraMap (ZMod 3) R)
    simpa only [map_natCast] using hu

theorem admissible_A : Admissible A := admissible_of_char_three A

theorem admissible_B : Admissible B := admissible_of_char_three B

end Problem05a
