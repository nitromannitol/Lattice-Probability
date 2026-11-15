import LatticeProb.Prob.GlobalEntryClock
import LatticeProb.Prob.AlternatingSegmentOutside

/-! # Global open entry and alternating segments -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The finite global entrance time of a continuous path into an open set is outside it. -/
theorem globalOpenEntry_not_mem_of_eq_coe {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) {V : Set E} (hV : IsOpen V) (ω : Ω)
    (hf : Continuous (f ω)) {t : ℝ} (ht : globalOpenEntry f V ω = (t : EReal)) :
    f ω t ∉ V := by
  intro hmem
  have hopen : IsOpen ((f ω) ⁻¹' V) := hV.preimage hf
  obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hmem)
  let s := (l + t) / 2
  have hls : l < s := by dsimp [s]; linarith
  have hst : s < t := by dsimp [s]; linarith
  have hs : f ω s ∈ V := hsub ⟨hls, hst.trans htu⟩
  have hle : (t : EReal) ≤ (s : EReal) := by
    rw [← ht]
    exact sInf_le ⟨s, hs, rfl⟩
  exact (not_le_of_gt hst) (EReal.coe_le_coe_iff.mp hle)

/-- Alternating segments initialized at a finite global entrance avoid the inner open set. -/
theorem alternatingSegment_image_subset_compl_of_globalEntry {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)))
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (ω : Ω) {t : ℝ}
    (ht : globalOpenEntry (fun ω t => f ω t) V ω = (t : EReal)) (n : ℕ)
    (hn : n < alternatingExcursionCount f
      (fun ω => entryClockOfEReal (globalOpenEntry (fun ω t => f ω t) V ω)) U V ω) :
    f ω '' Icc
      ((alternatingExitClock f
        (fun ω => entryClockOfEReal (globalOpenEntry (fun ω t => f ω t) V ω)) U V n ω).untopD 0)
      ((openEntryAfter (fun ω t => f ω t)
        (alternatingExitClock f
          (fun ω => entryClockOfEReal (globalOpenEntry (fun ω t => f ω t) V ω)) U V n) U ω).untopD 0) ⊆ Uᶜ := by
  apply alternatingSegment_image_subset_compl_of_initial f _ hU hV hUV ω _ n hn
  simp only [ht, entryClockOfEReal_coe, WithTop.untopD_coe]
  exact fun hu => globalOpenEntry_not_mem_of_eq_coe (fun ω t => f ω t) hV ω
    (f ω).continuous ht (hUV hu)

end LatticeProb
