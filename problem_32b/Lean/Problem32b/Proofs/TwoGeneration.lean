import Problem32b.Proofs.Coordinates
import Problem32b.Proofs.Normalization

noncomputable section
open HahnSeries
namespace Problem32b.Laurent

theorem normalized_two_generated (L : Set (K F))
    (hDL : (baseRing F : Set (K F)) ⊆ L) (hLV : L ⊆ powerRing F)
    (hv : vClosure (baseRing F) L = L) :
    ∃ b ∈ L, vClosure (baseRing F) (twoSpan (baseRing F) 1 b) = L := by
  classical
  let B := colon (baseRing F) L
  have hB : IsModuleSet (baseRing F) B := moduleSet_colon _ (moduleSet_subring _)
  have hBD : B ⊆ baseRing F := by
    intro d hd
    simpa using hd 1 (hDL (baseRing F).one_mem)
  have hCB : Tail F 8 ⊆ B := by
    intro c hc z hz
    exact tail_eight_le_baseRing F (tail_mul_power F hc (hLV hz))
  let J : Finset A := Finset.univ.filter fun a => ∃ d ∈ B, aCoords d = a
  have hJmem (a : A) : a ∈ J ↔ ∃ d ∈ B, aCoords d = a := by simp [J]
  have hJ : FiniteQuotient.IsIdeal J := by
    refine ⟨?_,?_,?_⟩
    · exact (hJmem 0).mpr ⟨0,hB.zero_mem,aCoords_zero⟩
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := (hJmem a).mp ha
      obtain ⟨y,hy,rfl⟩ := (hJmem b).mp hb
      exact (hJmem _).mpr ⟨x+y,hB.add_mem hx hy,aCoords_add x y⟩
    · intro r a ha
      obtain ⟨x,hx,rfl⟩ := (hJmem a).mp ha
      refine (hJmem _).mpr ⟨aRep r*x,hB.smul_mem (aRep_mem r) hx,?_⟩
      rw [aCoords_mul (aRep_mem r) (hBD hx),aCoords_aRep]
  obtain ⟨q,hq⟩ := FiniteQuotient.every_ideal_has_single_witness J hJ
  have hb (d : K F) (hd : d ∈ baseRing F) :
      d ∈ B ↔ d*qRep q ∈ baseRing F := by
    have hprod : d*qRep q ∈ powerRing F :=
      (powerRing F).mul_mem (baseRing_le_powerRing F hd) (qRep_mem q)
    rw [← qCoords_zero_iff hprod,qCoords_mul hd (qRep_mem q),qCoords_qRep,← hq]
    constructor
    · intro hdB
      exact (hJmem _).mpr ⟨d,hdB,rfl⟩
    · intro hdJ
      obtain ⟨c,hc,he⟩ := (hJmem _).mp hdJ
      have hdc := same_aCoords_sub_tail hd (hBD hc) he.symm
      have hadd := hB.add_mem (hCB hdc) hc
      simpa using hadd
  have hcol : colon (baseRing F) (twoSpan (baseRing F) 1 (qRep q)) = B := by
    ext d
    rw [colon_twoSpan,mul_one]
    constructor
    · rintro ⟨hd,hprod⟩
      exact (hb d hd).mpr hprod
    · intro hd
      exact ⟨hBD hd,(hb d (hBD hd)).mp hd⟩
  have he : vClosure (baseRing F) (twoSpan (baseRing F) 1 (qRep q)) = L := by
    unfold vClosure
    rw [hcol]
    exact hv
  refine ⟨qRep q, ?_,he⟩
  rw [← he]
  apply subset_vClosure
  exact ⟨0,(baseRing F).zero_mem,1,(baseRing F).one_mem,by simp⟩

theorem scale_twoSpan (f b : K F) :
    (fun x => f*x) '' twoSpan (baseRing F) 1 b =
      twoSpan (baseRing F) f (f*b) := by
  ext x
  constructor
  · rintro ⟨y,⟨r,hr,s,hs,rfl⟩,rfl⟩
    exact ⟨r,hr,s,hs,by ring⟩
  · rintro ⟨r,hr,s,hs,rfl⟩
    refine ⟨r*1+s*b,⟨r,hr,s,hs,rfl⟩,?_⟩
    ring

theorem all_divisorial_ideals_two_generated (I : Set (K F))
    (hI : IsModuleSet (baseRing F) I) (hID : I ⊆ baseRing F)
    (hne : ∃ z ∈ I, z ≠ 0) (hv : vClosure (baseRing F) I = I) :
    ∃ a ∈ I, ∃ b ∈ I, vClosure (baseRing F) (twoSpan (baseRing F) a b) = I := by
  obtain ⟨f,L,hf,hf0,hL,hDL,hLV,hvL,hIL⟩ := normalize F I hI hID hne hv
  obtain ⟨b,hb,he⟩ := normalized_two_generated L hDL hLV hvL
  refine ⟨f,hf,f*b,?_,?_⟩
  · rw [hIL]
    exact ⟨b,hb,rfl⟩
  · rw [← scale_twoSpan,scale_vClosure _ _ _ hf0,he,← hIL]

end Problem32b.Laurent
