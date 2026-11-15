import LatticeProb.Topology.MeasurableSegmentBall

/-! # Ball containment observed through a curve segment -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- Positive-radius open-ball containment in a continuous compact trace is equivalent to
closed-ball containment with the same centre and radius. -/
theorem ball_subset_segment_iff_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(ℝ, E)) (a b r : ℝ)
    (hr : 0 < r) (z : E) :
    ball z r ⊆ f '' Icc a b ↔ closedBall z r ⊆ f '' Icc a b := by
  constructor
  · intro h
    have hc : IsClosed (f '' Icc a b) := (isCompact_Icc.image f.continuous).isClosed
    rw [← closure_ball z hr.ne']
    exact closure_minimal h hc
  · exact fun h => ball_subset_closedBall.trans h

/-- If an observed curve agrees with a curve on a segment, and the observation and
ordered endpoints are measurable, positive-radius ball containment in the original segment
is measurable for the observation's sigma algebra. -/
theorem measurableSet_exists_ball_subset_observed_segment
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : Ω → C(ℝ, E)} {g : Ω → ℝ → E} {a b : Ω → ℝ} {r : ℝ}
    (hf : Measurable f) (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ ω, a ω ≤ b ω) (hr : 0 < r)
    (hag : ∀ ω t, t ∈ Icc (a ω) (b ω) → f ω t = g ω t) :
    MeasurableSet {ω | ∃ z, ball z r ⊆ g ω '' Icc (a ω) (b ω)} := by
  have hmeas := measurableSet_exists_closedBall_subset_segment
    (δ := fun _ : Ω => r) hf ha hb measurable_const
  convert hmeas using 1
  ext ω
  simp only [mem_ofPred_eq]
  have himage : f ω '' Icc (a ω) (b ω) = g ω '' Icc (a ω) (b ω) :=
    image_congr (fun t ht => hag ω t ht)
  simp only [hab ω, hr.le, true_and]
  rw [← himage]
  exact exists_congr fun z => ball_subset_segment_iff_closedBall (f ω) (a ω) (b ω) r hr z

end LatticeProb
