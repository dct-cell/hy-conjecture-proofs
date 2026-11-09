import Problem05a.Spec
namespace Problem05a
open CategoryTheory
universe u v

attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem globalDimensionLE_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (n : ℕ) (h : GlobalDimensionLE.{u,v} R n) :
    GlobalDimensionLE.{u,v} S n := by
  intro N
  let M : ModuleCat.{max u v} R := (ModuleCat.restrictScalars e.toRingHom).obj N
  let e' : M ≃ₛₗ[RingHomClass.toRingHom e] N :=
    { toEquiv := Equiv.refl N
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI := h M
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e e' n

theorem globalDimensionEq_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (n : ℕ) (h : GlobalDimensionEq.{u,v} R n) :
    GlobalDimensionEq.{u,v} S n := by
  refine ⟨globalDimensionLE_of_ringEquiv e n h.1, ?_⟩
  intro m hm hs
  exact h.2 m hm (globalDimensionLE_of_ringEquiv e.symm m hs)

noncomputable def polynomialGroupEquiv : AddMonoidAlgebra B G ≃+* Polynomial A :=
  (AddMonoidAlgebra.mapRingEquiv G (Polynomial.toFinsuppIso (ZMod 3))).trans
    (AddMonoidAlgebra.commRingEquiv.trans (Polynomial.toFinsuppIso A).symm)

end Problem05a
