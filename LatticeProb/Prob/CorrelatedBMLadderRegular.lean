import LatticeProb.Analysis.ContourRigidity
import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0

/-!
# Ladder regularity of the coordinates of a correlated Brownian pair

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` (`IsCorrelatedBM2 γ μ`). A continuous function
is *ladder regular* on a set `Q` of anchors (`IsLadderRegularOn`) when it is unbounded below on both sides of every
time, its distinct local minima have distinct values, it is immediately descended from at every anchor, and the drop of
its running minimum from every anchor is recovered from the excursion counts of the ladder sets.

The first two conditions hold almost surely for each coordinate: it reaches arbitrarily low values at arbitrarily remote
integer times on both half-lines, and its local minima have distinct values. The last two conditions are statements at a
single anchor; for a countable set of anchors they hold simultaneously almost surely as soon as they hold almost surely
at each anchor. This reduces the almost sure ladder regularity of the coordinates on the rational anchors to the
immediate descent at a fixed time and to the excursion-count (downcrossing) representation of the running minimum at a
fixed time.

## Main results
* `ae_coordinate_low`: almost surely each coordinate takes values below every level before and after every time.
* `ae_isLadderRegularOn_of_forall_mem`: for a countable set `Q` of anchors, almost surely the coordinate `i` is ladder
  regular on `Q`, given the descent and excursion-count conditions almost surely at each anchor of `Q`.
* `ae_forall_isLadderRegularOn_rat`: the same for both coordinates on the rational anchors.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT LatticeProb.LadderSet

variable {γ : ℝ} {μ : Measure Path2}

/-- **Each coordinate is unbounded below on both sides of every time**, almost surely. -/
theorem ae_coordinate_low (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ ω ∂μ, ∀ w l : ℝ, (∃ a ≤ w, lrCoord i a ω ≤ l) ∧ ∃ b, w ≤ b ∧ lrCoord i b ω ≤ l := by
  filter_upwards [BrownianPathFacts.ae_coordinate_unboundedBelowInt_both hμ i] with ω hω w l
  obtain ⟨hpos, hneg⟩ := hω
  have hm : -((⌈-l⌉₊ : ℕ) : ℝ) ≤ l := by linarith [Nat.le_ceil (-l)]
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hkn, hn⟩ := hneg ⌈-l⌉₊ ⌈-w⌉₊
    refine ⟨-(n : ℝ), ?_, ?_⟩
    · have h1 : (⌈-w⌉₊ : ℝ) ≤ n := by exact_mod_cast hkn
      linarith [Nat.le_ceil (-w)]
    · have hn' : lrCoord i (-(n : ℝ)) ω < -((⌈-l⌉₊ : ℕ) : ℝ) := by simpa using hn
      linarith
  · obtain ⟨n, hkn, hn⟩ := hpos ⌈-l⌉₊ ⌈w⌉₊
    refine ⟨(n : ℝ), ?_, ?_⟩
    · have h1 : (⌈w⌉₊ : ℝ) ≤ n := by exact_mod_cast hkn
      linarith [Nat.le_ceil w]
    · have hn' : lrCoord i (n : ℝ) ω < -((⌈-l⌉₊ : ℕ) : ℝ) := by simpa using hn
      linarith

/-- **Ladder regularity on a countable set of anchors from conditions at single anchors.** If, for each anchor `a` of a
countable set `Q`, the coordinate `i` is almost surely immediately descended from on both sides of `a`, and almost surely
the drop of its running minimum from `a` (forwards and backwards) is the limit of `√(π ε / 2)` times the excursion count
of the ladder set from `a`, then almost surely the coordinate `i` is ladder regular on `Q`. -/
theorem ae_isLadderRegularOn_of_forall_mem (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {Q : Set ℝ}
    (hQ : Q.Countable)
    (hdesc : ∀ a ∈ Q, ∀ᵐ ω ∂μ,
      (∀ u < a, ∃ w ∈ Ioo u a, lrCoord i w ω < lrCoord i a ω) ∧
        ∀ u, a < u → ∃ w ∈ Ioo a u, lrCoord i w ω < lrCoord i a ω)
    (hexc : ∀ a ∈ Q, ∀ᵐ ω ∂μ,
      (∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (forwardLadderSet (fun s => lrCoord i s ω) a) a t ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i a ω - sInf ((fun s => lrCoord i s ω) '' Icc a t)))) ∧
      ∀ t, t ≤ a → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (backwardLadderSet (fun s => lrCoord i s ω) a) t a ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i a ω - sInf ((fun s => lrCoord i s ω) '' Icc t a)))) :
    ∀ᵐ ω ∂μ, IsLadderRegularOn (fun t => lrCoord i t ω) Q := by
  have hD := (ae_ball_iff hQ).2 hdesc
  have hE := (ae_ball_iff hQ).2 hexc
  filter_upwards [ae_coordinate_low hμ i, ae_locMinDistinct hμ, hD, hE] with ω hlow hloc hd he
  exact
    { continuous := continuous_lrCoord_time i ω
      low := hlow
      locMin_ne := fun p q hpq hp hq => hloc i p q hpq.ne hp hq
      descent_left := fun a ha => (hd a ha).1
      descent_right := fun a ha => (hd a ha).2
      excursion_forward := fun a ha => (he a ha).1
      excursion_backward := fun b hb => (he b hb).2 }

/-- **Both coordinates are ladder regular on the rational anchors**, almost surely, given the descent and
excursion-count conditions almost surely at each rational time. -/
theorem ae_forall_isLadderRegularOn_rat (hμ : IsCorrelatedBM2 γ μ)
    (hdesc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ u < (q : ℝ), ∃ w ∈ Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
        ∀ u, (q : ℝ) < u → ∃ w ∈ Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω)
    (hexc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ))))) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, IsLadderRegularOn (fun t => lrCoord i t ω) (range ((↑) : ℚ → ℝ)) := by
  refine ae_all_iff.2 fun i => ae_isLadderRegularOn_of_forall_mem hμ i (countable_range _) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact hdesc i q
  · rintro _ ⟨q, rfl⟩
    exact hexc i q

end LatticeProb.CorrelatedBM
