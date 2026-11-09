import Problem41.Spec
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

namespace Problem41
open Polynomial

variable {R : Type*} [CommRing R]
attribute [local instance] Polynomial.algebra

/-- The degree-one generated presentation of the Rees algebra. -/
noncomputable def reesPresentation (I : Ideal R) : Subalgebra R R[X] :=
  Algebra.adjoin R {C r * X | r ∈ I}

theorem reesPresentation_eq (I : Ideal R) : reesPresentation I = reesAlgebra I := by
  rw [reesPresentation, ← adjoin_monomial_eq_reesAlgebra]
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, C_mul_X_eq_monomial.symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, C_mul_X_eq_monomial⟩

/-- A sufficient condition stated in terms of actual powers of an ideal. -/
theorem rees_integral_of_power {I : Ideal R} {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n ∈ I ^ n) :
    IsIntegral (reesPresentation I) (C x * X) := by
  apply IsIntegral.of_pow hn
  have hm : (C x * X) ^ n ∈ reesPresentation I := by
    rw [reesPresentation_eq, mul_pow, ← C_pow, C_mul_X_pow_eq_monomial]
    exact reesAlgebra.monomial_mem.mpr hx
  simpa [Subalgebra.algebraMap_def] using
    (isIntegral_algebraMap (R := reesPresentation I) (A := R[X]) (x := ⟨_, hm⟩))

/-- Homogeneous integrality in the Rees algebra gives the defining equation. -/
theorem integralOverIdeal_of_rees_integral {I : Ideal R} {x : R}
    (hx : IsIntegral (reesPresentation I) (C x * X)) : IntegralOverIdeal I x := by
  have hx' : @IsIntegral (reesPresentation I) R[X] _ _
      (@Subalgebra.toAlgebra R[X] R R[X] _ _ _ _
        (Polynomial.algebra R R) (reesPresentation I)) (C x * X) := by
    obtain ⟨q, hq, he⟩ := hx
    refine ⟨q, hq, ?_⟩
    simpa [Subalgebra.algebraMap_eq, Polynomial.algebra] using he
  obtain ⟨p, hp, he, hc⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
      (R := R) (S := R) (I := I) (x := x) hx'
  exact ⟨p, hp, by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using he, hc⟩

/-- Ideal-span combinations of homogeneous integral elements are still integral. -/
theorem rees_integral_of_mem_span {I : Ideal R} {s : Set R}
    (hs : ∀ x ∈ s, IsIntegral (reesPresentation I) (C x * X))
    {x : R} (hx : x ∈ Ideal.span s) :
    IsIntegral (reesPresentation I) (C x * X) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa using (isIntegral_zero : IsIntegral (reesPresentation I) (0 : R[X]))
  | add x y hx hy ihx ihy => simpa [add_mul] using ihx.add ihy
  | smul r x hx ih =>
    have hr : IsIntegral (reesPresentation I) (C r) := by
      simpa [Subalgebra.algebraMap_def] using
        (isIntegral_algebraMap (R := reesPresentation I) (A := R[X])
          (x := ⟨C r, (reesPresentation I).algebraMap_mem r⟩))
    simpa only [smul_eq_mul, C_mul, mul_assoc] using hr.mul ih

/-- A useful span formulation requiring no assumption that the integral elements
already form an ideal. -/
theorem integralOverIdeal_of_span_powers {I : Ideal R} {s : Set R}
    (hs : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I ^ n)
    {x : R} (hx : x ∈ Ideal.span s) : IntegralOverIdeal I x := by
  apply integralOverIdeal_of_rees_integral
  apply rees_integral_of_mem_span (s := s) _ hx
  intro y hy
  obtain ⟨n, hn, hpow⟩ := hs y hy
  exact rees_integral_of_power hn hpow

/-- The reverse inclusion in the usual integral-closure equality is automatic,
but is recorded formally rather than left to the specification review. -/
theorem integralOverIdeal_of_mem {I : Ideal R} {x : R} (hx : x ∈ I) :
    IntegralOverIdeal I x := by
  apply integralOverIdeal_of_rees_integral
  apply rees_integral_of_power (n := 1) (by decide)
  simpa using hx

end Problem41
