import Problem05a.Spec

namespace Problem05a.PolynomialResolution
open Polynomial PolynomialModule
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

noncomputable def coefficientMap (f : M →ₗ[R] N) :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R N where
  toFun := PolynomialModule.map R f
  map_add' := (PolynomialModule.map R f).map_add
  map_smul' p q := by
    simpa using PolynomialModule.map_smul R f p q

@[simp] theorem coefficientMap_single (f : M →ₗ[R] N) (i : ℕ) (m : M) :
    coefficientMap f (single R i m) = single R i (f m) := by
  simp [coefficientMap]

variable [Module R[X] M] [IsScalarTower R R[X] M]

noncomputable def actionX : M →ₗ[R] M where
  toFun m := (X : R[X]) • m
  map_add' := smul_add _
  map_smul' r m := by
    simpa using smul_comm (X : R[X]) r m

noncomputable def delta : PolynomialModule R M →ₗ[R[X]] PolynomialModule R M :=
  LinearMap.lsmul R[X] (PolynomialModule R M) X - coefficientMap (actionX (R := R))

noncomputable def epsilon : PolynomialModule R M →ₗ[R[X]] M :=
  (LinearMap.liftBaseChange R[X] (LinearMap.id : M →ₗ[R] M)).comp
    (polynomialTensorProductLEquivPolynomialModule R M).symm.toLinearMap

@[simp] theorem delta_single (i : ℕ) (m : M) :
    delta (single R i m) = single R (i+1) m - single R i ((X : R[X]) • m) := by
  simp only [delta, LinearMap.sub_apply, coefficientMap_single]
  change (X : R[X]) • single R i m - single R i ((X : R[X]) • m) = _
  rw [show (X : R[X]) = monomial 1 1 by exact (monomial_one_one_eq_X).symm, monomial_smul_single]
  simp [Nat.add_comm]

@[simp] theorem epsilon_single (i : ℕ) (m : M) :
    epsilon (single R i m) = (X : R[X])^i • m := by
  simp [epsilon, polynomialTensorProductLEquivPolynomialModule,
    ← monomial_one_right_eq_X_pow]

 theorem epsilon_delta (q : PolynomialModule R M) : epsilon (delta q) = 0 := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | single i m => simp [pow_succ, mul_smul]

 theorem epsilon_surjective : Function.Surjective (epsilon (R := R) (M := M)) := by
  intro m
  exact ⟨single R 0 m, by simp⟩

theorem difference_mem_range (q : PolynomialModule R M) :
    q - single R 0 (epsilon q) ∈ LinearMap.range (delta (R := R)) := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simpa only [map_add, single_add, add_sub_add_comm] using
      (LinearMap.range (delta (R := R))).add_mem ha hb
  | single i m =>
    simp only [epsilon_single]
    induction i generalizing m with
    | zero => simp
    | succ i ih =>
      have h₁ : delta (single R i m) ∈ LinearMap.range (delta (R := R)) :=
        ⟨single R i m, rfl⟩
      have h₂ := (LinearMap.range (delta (R := R))).add_mem h₁ (ih ((X : R[X]) • m))
      simpa only [delta_single, sub_add_sub_cancel, pow_succ, mul_smul] using h₂

theorem exact_delta_epsilon : Function.Exact (delta (R := R) (M := M)) epsilon := by
  intro q
  constructor
  · intro hq
    have h := difference_mem_range q
    simpa [hq] using h
  · rintro ⟨p,rfl⟩
    exact epsilon_delta p

theorem delta_coefficient (q : PolynomialModule R M) (n : ℕ) :
    (delta q).coeff (n+1) = q.coeff n - (X : R[X]) • q.coeff (n+1) := by
  change ((X : R[X]) • q).coeff (n+1) - (X : R[X]) • q.coeff (n+1) = _
  rw [show (X : R[X]) = monomial 1 1 by exact (monomial_one_one_eq_X).symm, monomial_smul_apply]
  simp

theorem delta_injective : Function.Injective (delta (R := R) (M := M)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  by_contra hne
  have hcoeff : q.coeff ≠ 0 := fun h => hne (PolynomialModule.coeff_eq_zero.mp h)
  have hnon := Finsupp.support_nonempty_iff.mpr hcoeff
  let n := q.coeff.support.max' hnon
  have hn : n ∈ q.coeff.support := Finset.max'_mem _ hnon
  have hn' : n+1 ∉ q.coeff.support := by
    intro h
    have := Finset.le_max' _ _ h
    change n+1 ≤ n at this
    omega
  have hz : q.coeff (n+1) = 0 := Finsupp.notMem_support_iff.mp hn'
  have hc := congrArg (fun p : PolynomialModule R M => p.coeff (n+1)) hq
  rw [delta_coefficient, hz, smul_zero, sub_zero] at hc
  exact (Finsupp.mem_support_iff.mp hn) hc

end Problem05a.PolynomialResolution
