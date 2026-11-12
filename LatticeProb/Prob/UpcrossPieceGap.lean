import Mathlib
import LatticeProb.Prob.PathOscillationSet
import LatticeProb.Prob.StayWeakLimitStop
import LatticeProb.Prob.StayLastZero
import LatticeProb.Prob.UpcrossAttempt

/-!
# The first up-crossing piece and the stopped path differ by a small time lag

For a path `y` with `y 0 = 0` that hits the level `c`, the first up-crossing piece is the path
stopped at its first hit of `c`, started at the last zero `g` before that hit:
`firstUpcrossPiece c y s = stopAt (hitFrom c 0 y) y (g + s)`.  Hence at finitely many times in
`[0, k]` the piece and the stopped path differ by at least `η` only if the stopped path has an
`η`-increment over a lag at most `g`, i.e. lies in `pathOscSet g k η`.

Under the drifted Brownian law conditioned on `staySet δ`, the last zero tends to be early
(`tendsto_cond_staySet_lastZero`), and the limsup of the probability of the closed oscillation set
of stopped paths is at most its limiting value; hence the probability that the piece and the
stopped path differ by at least `η` at finitely many times tends to `0` as `δ → 0⁺`.

* `LatticeProb.firstUpcrossPiece_eq_stopAt_add`: the pathwise identity.
* `LatticeProb.stopAt_mem_pathOscSet_of_norm_ge`: the pathwise oscillation bound.
* `LatticeProb.ae_tendsto_cond_staySet_pieceGap`: the conditional probability of an
  `η`-gap at finitely many times tends to `0`, for Lebesgue-almost every level `c > 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

/-- For a path starting at `0` that hits `c`, the first up-crossing piece is the path stopped at its
first hit of `c`, read from the last zero before that hit. -/
lemma firstUpcrossPiece_eq_stopAt_add {c : ℝ} {y : C(ℝ≥0, ℝ)} (hy0 : y 0 = 0)
    (hτ : hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤) (s : ℝ≥0) :
    firstUpcrossPiece c (y : ℝ≥0 → ℝ) s =
      stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (upcrossStart₁ c (y : ℝ≥0 → ℝ) + s) := by
  unfold firstUpcrossPiece pieceAt
  rw [upcrossEnd₁_of_zero_start hy0, stopAt_apply]
  congr 1
  generalize hitFrom c 0 (y : ℝ≥0 → ℝ) = τ at hτ ⊢
  lift τ to ℝ≥0 using hτ
  rw [ENNReal.toNNReal_coe, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

/-- If the piece and the stopped path differ by at least `η` in sup norm at finitely many times
in `[0, k]`, and the start of the piece is at most `s₀`, the stopped path lies in the oscillation
set `pathOscSet s₀ k η`. -/
lemma stopAt_mem_pathOscSet_of_norm_ge {c : ℝ} {n : ℕ} {t : Fin n → ℝ≥0} {k : ℝ≥0}
    (ht : ∀ i, t i ≤ k) {η : ℝ} (hη : 0 < η) {y : C(ℝ≥0, ℝ)} (hy0 : y 0 = 0)
    (hτ : hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤) {s₀ : ℝ≥0}
    (hg : upcrossStart₁ c (y : ℝ≥0 → ℝ) ≤ s₀)
    (hge : η ≤ ‖(fun i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i)) -
        fun i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i)‖) :
    stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y ∈ pathOscSet s₀ k η := by
  by_contra hnot
  have hlt : ‖(fun i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i)) -
        fun i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i)‖ < η := by
    rw [pi_norm_lt_iff hη]
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    by_contra hge'
    have h' := not_lt.1 hge'
    rw [firstUpcrossPiece_eq_stopAt_add hy0 hτ] at h'
    exact hnot ⟨_, hg, t i, ht i, h'⟩
  exact absurd hge (not_le.2 hlt)

section Gap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The piece and the stopped path are close under the conditioning.**  For Lebesgue-almost every
level `c > 0`, at finitely many times in `[0, k]` the first up-crossing piece and the path stopped at
its first hit of `c` differ by at least `η` with conditional probability (given `staySet δ`)
tending to `0` as `δ → 0⁺`. -/
theorem ae_tendsto_cond_staySet_pieceGap [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), ∀ (n : ℕ) (k : ℝ≥0) (t : Fin n → ℝ≥0),
      (∀ i, t i ≤ k) → ∀ η : ℝ, 0 < η →
        Tendsto (fun δ : ℝ => ((driftLaw P B hcont mu)[|staySet δ])
          {y | η ≤ ‖(fun i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i)) -
              fun i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i)‖}) (𝓝[>] 0) (𝓝 0) := by
  have : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    isProb_map (measurable_pathMap B hm hcont).aemeasurable
  filter_upwards [ae_limsup_cond_staySet_stopAtHit_closed_le (P.map (pathMap B hcont)) mu hν,
    ae_restrict_mem measurableSet_Ioi] with c hc hc0 n k t ht η hη
  have : IsProbabilityMeasure (ν.map (driftMap mu)) :=
    isProb_map (measurable_driftMap mu).aemeasurable
  have hSm : Measurable fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y :=
    measurable_stopAt_path (measurable_hitFrom (r := fun _ => 0) measurable_const c)
  have : IsProbabilityMeasure ((ν.map (driftMap mu)).map
      fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y) := isProb_map hSm.aemeasurable
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨s₀, hs₀, hms⟩ : ∃ s₀ : ℝ≥0, 0 < s₀ ∧ ((ν.map (driftMap mu)).map
      fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y) (pathOscSet s₀ k η) < ε / 2 := by
    have h1 := (tendsto_measure_pathOscSet ((ν.map (driftMap mu)).map
      fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y) k hη).eventually
      (gt_mem_nhds hε2)
    obtain ⟨s₀, h2, h3⟩ := (h1.and (self_mem_nhdsWithin : _ ∈ 𝓝[>] (0 : ℝ≥0))).exists
    exact ⟨s₀, h3, h2⟩
  have hO := hc (pathOscSet s₀ k η) (isClosed_pathOscSet s₀ k η)
  have hO' := Measure.map_apply hSm (measurableSet_pathOscSet s₀ k η) (μ := ν.map (driftMap mu))
  have hOev := eventually_lt_of_limsup_lt (lt_of_le_of_lt hO (hO'.symm.trans_lt hms))
  have hLev := (tendsto_cond_staySet_lastZero hB hm hcont mu c hs₀).eventually
    (gt_mem_nhds hε2)
  have hN0 : ∀ δ : ℝ, ((driftLaw P B hcont mu)[|staySet δ])
      {y : C(ℝ≥0, ℝ) | ¬ (y 0 = 0 ∧ hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤)} = 0 := fun δ =>
    cond_absolutelyContinuous (ae_iff.1
      (ae_start_hitFrom_driftLaw hB hm hcont hmu (show (0 : ℝ) < c from hc0).le))
  filter_upwards [hOev, hLev] with δ hOδ hLδ
  have hsub : {y : C(ℝ≥0, ℝ) | η ≤ ‖(fun i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i)) -
        fun i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i)‖} ⊆
      ({y : C(ℝ≥0, ℝ) | ¬ (y 0 = 0 ∧ hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤)} ∪
        {w : C(ℝ≥0, ℝ) | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal}) ∪
      {y : C(ℝ≥0, ℝ) | stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y ∈ pathOscSet s₀ k η} := by
    intro y hy
    by_cases hN : (y 0 = 0 ∧ hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    · by_cases hL : s₀ < lastZeroBefore (y : ℝ≥0 → ℝ) (hitFrom c 0 (y : ℝ≥0 → ℝ)).toNNReal
      · exact Or.inl (Or.inr hL)
      · refine Or.inr (stopAt_mem_pathOscSet_of_norm_ge ht hη hN.1 hN.2 ?_ hy)
        unfold upcrossStart₁
        rw [upcrossEnd₁_of_zero_start hN.1]
        exact not_lt.1 hL
    · exact Or.inl (Or.inl hN)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (_ + _) + _ := add_le_add_left (measure_union_le _ _) _
    _ = _ := by rw [hN0 δ, zero_add]
    _ ≤ ε / 2 + ε / 2 := add_le_add hLδ.le hOδ.le
    _ = ε := ENNReal.add_halves ε

end Gap

end LatticeProb
