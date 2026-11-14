import LatticeProb.Topology.IntervalReparamEDist

/-! # Reparametrization distance for zero-length intervals -/

set_option autoImplicit false

open scoped ENNReal NNReal

namespace LatticeProb.IntervalReparamEDist

variable {E : Type*} [PseudoEMetricSpace E]

private theorem timeInterval_zero_val (t : TimeInterval 0) : t.1 = 0 := by
  have h : (t.1 : ℝ≥0∞) = 0 := le_antisymm t.2 bot_le
  exact ENNReal.coe_eq_zero.mp h

/-- For two zero durations, the distance is the distance between the starting points. -/
theorem intervalEDist_zero_zero (f g : ℝ≥0 → E) :
    intervalEDist f g 0 0 = edist (f 0) (g 0) := by
  apply le_antisymm
  · calc
      intervalEDist f g 0 0 ≤ ⨆ t : TimeInterval 0, edist (f t.1) (g t.1) :=
        intervalEDist_le_iSup_edist f g 0
      _ ≤ edist (f 0) (g 0) := by
        apply iSup_le
        intro t
        rw [timeInterval_zero_val t]
  · apply le_iInf
    intro φ
    let t : TimeInterval 0 := ⟨0, by simp⟩
    calc
      edist (f 0) (g 0) = edist (f t.1) (g (φ t).1) := by
        rw [timeInterval_zero_val (φ t)]
      _ ≤ ⨆ s : TimeInterval 0, edist (f s.1) (g (φ s).1) :=
        le_iSup (fun s : TimeInterval 0 => edist (f s.1) (g (φ s).1)) t

/-- A singleton time interval has no increasing bijection onto a positive interval. -/
theorem intervalEDist_zero_of_pos (f g : ℝ≥0 → E) {T : ℝ≥0∞} (hT : 0 < T) :
    intervalEDist f g 0 T = ⊤ := by
  have hempty : IsEmpty (TimeInterval 0 ≃o TimeInterval T) := by
    constructor
    intro φ
    obtain ⟨s, hs0, hsT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hT
    let a : TimeInterval T := ⟨0, bot_le⟩
    let b : TimeInterval T := ⟨s, le_of_lt hsT⟩
    have hab : a = b := by
      apply φ.symm.injective
      apply Subtype.ext
      rw [timeInterval_zero_val (φ.symm a), timeInterval_zero_val (φ.symm b)]
    have hs : s = 0 := by
      have h := congrArg Subtype.val hab
      exact h.symm
    subst s
    simp only [ENNReal.coe_zero, lt_self_iff_false] at hs0
  let : IsEmpty (TimeInterval 0 ≃o TimeInterval T) := hempty
  simp only [intervalEDist, iInf_of_empty]

/-- A positive time interval has no increasing bijection onto a singleton interval. -/
theorem intervalEDist_of_pos_zero (f g : ℝ≥0 → E) {T : ℝ≥0∞} (hT : 0 < T) :
    intervalEDist f g T 0 = ⊤ := by
  rw [intervalEDist_comm, intervalEDist_zero_of_pos g f hT]

end LatticeProb.IntervalReparamEDist
