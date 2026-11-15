import LatticeProb.Topology.RationalSegmentDensity
import Mathlib.Topology.Connected.Basic

/-! # Connected interiors of curve segments -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- If every rational subsegment has connected interior and is the closure of
its interior, the same holds for a nondegenerate real segment. -/
theorem connected_interior_image_of_rational_subsegments
    {X : Type*} [TopologicalSpace X] [T2Space X] (f : ℝ → X)
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hconn : ∀ (p q : ℚ), a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      IsConnected (interior (f '' Icc (p : ℝ) (q : ℝ))))
    (hregular : ∀ (p q : ℚ), a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      closure (interior (f '' Icc (p : ℝ) (q : ℝ))) = f '' Icc (p : ℝ) (q : ℝ)) :
    IsConnected (interior (f '' Icc a b)) ∧
      closure (interior (f '' Icc a b)) = f '' Icc a b := by
  let S : Set (Set X) := {U | ∃ (p q : ℚ),
    a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b ∧
      U = interior (f '' Icc (p : ℝ) (q : ℝ))}
  have hdir : DirectedOn (· ⊆ ·) S := by
    rintro U ⟨p, q, hap, hpq, hqb, rfl⟩ V ⟨r, s, har, hrs, hsb, rfl⟩
    have hleft : a < ((min p r : ℚ) : ℝ) := by simpa using lt_min hap har
    have hright : ((max q s : ℚ) : ℝ) < b := by simpa using max_lt hqb hsb
    have hmid : ((min p r : ℚ) : ℝ) < ((max q s : ℚ) : ℝ) := by
      have hl : ((min p r : ℚ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast min_le_left p r
      have hr : (q : ℝ) ≤ ((max q s : ℚ) : ℝ) := by exact_mod_cast le_max_left q s
      exact hl.trans_lt (hpq.trans_le hr)
    refine ⟨interior (f '' Icc ((min p r : ℚ) : ℝ) ((max q s : ℚ) : ℝ)),
      ⟨min p r, max q s, hleft, hmid, hright, rfl⟩, ?_, ?_⟩
    · apply interior_mono (image_mono (Icc_subset_Icc ?_ ?_))
      · exact_mod_cast min_le_left p r
      · exact_mod_cast le_max_left q s
    · apply interior_mono (image_mono (Icc_subset_Icc ?_ ?_))
      · exact_mod_cast min_le_right p r
      · exact_mod_cast le_max_right q s
  have hnonempty : (⋃₀ S).Nonempty := by
    obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
    obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
    obtain ⟨x, hx⟩ := (hconn p q hap hpq hqb).1
    exact ⟨x, mem_sUnion.mpr ⟨_, ⟨p, q, hap, hpq, hqb, rfl⟩, hx⟩⟩
  have hU : IsConnected (⋃₀ S) := by
    refine ⟨hnonempty, IsPreconnected.sUnion_directed hdir ?_⟩
    rintro U ⟨p, q, hap, hpq, hqb, rfl⟩
    exact (hconn p q hap hpq hqb).2
  have hsub : (⋃₀ S) ⊆ interior (f '' Icc a b) := by
    rintro x ⟨U, ⟨p, q, hap, hpq, hqb, rfl⟩, hx⟩
    exact interior_mono (image_mono (Icc_subset_Icc hap.le hqb.le)) hx
  have hdense : f '' Icc a b ⊆ closure (⋃₀ S) := by
    rw [← closure_iUnion_rational_subsegment_image f hf hab]
    apply closure_minimal _ isClosed_closure
    simp only [iUnion_subset_iff]
    intro p q hpq
    rcases hpq with ⟨hap, hpq, hqb⟩
    rw [← hregular p q hap hpq hqb]
    apply closure_mono
    exact subset_sUnion_of_mem ⟨p, q, hap, hpq, hqb, rfl⟩
  have hcl : closure (⋃₀ S) = f '' Icc a b :=
    Subset.antisymm (closure_minimal (hsub.trans interior_subset)
      (isCompact_Icc.image hf).isClosed) hdense
  constructor
  · apply hU.subset_closure hsub
    rw [hcl]
    exact interior_subset
  · apply Subset.antisymm
    · exact closure_minimal interior_subset (isCompact_Icc.image hf).isClosed
    · exact hdense.trans (closure_mono hsub)

end LatticeProb
