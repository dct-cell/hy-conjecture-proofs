import Problem32b.Spec

noncomputable section
namespace Problem32b

variable {K : Type*} [Field K]

/-- An R-submodule of its containing field, written as a set. -/
structure IsModuleSet (R : Subring K) (S : Set K) : Prop where
  zero_mem : 0 ∈ S
  add_mem : ∀ {x y}, x ∈ S → y ∈ S → x+y ∈ S
  neg_mem : ∀ {x}, x ∈ S → -x ∈ S
  smul_mem : ∀ {r x}, r ∈ R → x ∈ S → r*x ∈ S

theorem moduleSet_subring (R : Subring K) : IsModuleSet R R :=
  ⟨R.zero_mem, R.add_mem, R.neg_mem, R.mul_mem⟩

theorem moduleSet_colon (R : Subring K) {S T : Set K}
    (hS : IsModuleSet R S) : IsModuleSet R (colon S T) := by
  constructor
  · intro y hy
    simpa using hS.zero_mem
  · intro x y hx hy z hz
    simpa [add_mul] using hS.add_mem (hx z hz) (hy z hz)
  · intro x hx y hy
    simpa using hS.neg_mem (hx y hy)
  · intro r x hr hx y hy
    simpa [mul_assoc] using hS.smul_mem hr (hx y hy)

theorem subset_vClosure (R : Subring K) (S : Set K) : S ⊆ vClosure R S := by
  intro x hx y hy
  simpa [mul_comm] using hy x hx

theorem colon_twoSpan (R : Subring K) (a b x : K) :
    x ∈ colon R (twoSpan R a b) ↔ x*a ∈ R ∧ x*b ∈ R := by
  constructor
  · intro h
    constructor
    · apply h
      exact ⟨1,R.one_mem,0,R.zero_mem,by simp⟩
    · apply h
      exact ⟨0,R.zero_mem,1,R.one_mem,by simp⟩
  · rintro ⟨ha,hb⟩ y ⟨r,hr,s,hs,rfl⟩
    change x*(r*a+s*b) ∈ R
    convert R.add_mem (R.mul_mem hr ha) (R.mul_mem hs hb) using 1; ring

theorem colon_mono_right {S T U : Set K} (h : T ⊆ U) :
    colon S U ⊆ colon S T := fun _ hx y hy => hx y (h hy)

theorem scale_vClosure (R : Subring K) (S : Set K) (f : K) (hf : f ≠ 0) :
    vClosure R ((fun x => f*x) '' S) = (fun x => f*x) '' vClosure R S := by
  ext x
  constructor
  · intro hx
    refine ⟨x/f, ?_, by field_simp⟩
    intro y hy
    have h : y/f ∈ colon R ((fun z => f*z) '' S) := by
      rintro _ ⟨z,hz,rfl⟩
      convert hy z hz using 1; field_simp
    have := hx (y/f) h
    convert this using 1; field_simp
  · rintro ⟨z,hz,rfl⟩ y hy
    have h : f*y ∈ colon R S := by
      intro w hw
      have := hy (f*w) ⟨w,hw,rfl⟩
      convert this using 1; ring
    have := hz (f*y) h
    convert this using 1; ring

theorem idealSet_isModule (R : Subring K) (I : Ideal R) :
    IsModuleSet R (idealSet R I) := by
  constructor
  · exact ⟨R.zero_mem,I.zero_mem⟩
  · rintro x y ⟨hx,hI⟩ ⟨hy,hJ⟩
    exact ⟨R.add_mem hx hy,I.add_mem hI hJ⟩
  · rintro x ⟨hx,hI⟩
    exact ⟨R.neg_mem hx,I.neg_mem hI⟩
  · rintro r x hr ⟨hx,hI⟩
    exact ⟨R.mul_mem hr hx,I.mul_mem_left (⟨r,hr⟩ : R) hI⟩

end Problem32b
