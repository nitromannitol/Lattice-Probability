import Mathlib
import LatticeProb.Prob.CrossingTimesMoments
import LatticeProb.Prob.BrownianRestartLaw
import LatticeProb.Prob.BrownianStepTimeScaled

/-!
# The mean of the first crossing time of a Brownian motion

For a Brownian motion `B` in `ℝ ^ d`, `d ≥ 1`, with continuous paths, the first `ε`-crossing time
`σ₁ = crossTime ε (B · ω) 1` is the first exit time from the ball of radius `ε`.  Its mean is
`ε ^ 2 m` where `m = E σ₁¹` does not depend on the motion (nor on the probability space or the
starting point) and `0 < m < ∞`.

* `crossTime_one_pos`: the first crossing time of a path continuous at `0` is positive;
* `IsBrownianSpace.lintegral_crossTime_eq`: the mean of the `k`-th `ε`-crossing time is the same
  for any two Brownian motions (the law of the centred path does not depend on the motion);
* `IsBrownianSpace.lintegral_crossTime_scale`: Brownian scaling, `E σ₁^c = c ^ 2 E σ₁¹`;
* `exists_lintegral_crossTime_eq`: `E σ₁^ε = ε ^ 2 m` for a constant `m ∈ (0, ∞)`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Positive

variable {E : Type*} [PseudoMetricSpace E]

/-- The first `ε`-crossing time of a path that is continuous at `0` is positive. -/
theorem crossTime_one_pos {f : ℝ≥0 → E} (hf : ContinuousAt f 0) {ε : ℝ} (hε : 0 < ε) :
    0 < crossTime ε f 1 := by
  rw [crossTime_one_eq]
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf ε hε
  have hpos : (0 : ℝ≥0∞) < ((δ.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hδ)
  refine lt_of_lt_of_le hpos (le_nextCrossTime_iff.2 fun s _ hs => ?_)
  rw [ENNReal.coe_le_coe]
  by_contra hlt
  rw [not_le] at hlt
  have hs0 : dist s 0 < δ := by
    rw [NNReal.dist_eq]
    have h1 : (s : ℝ) < δ := by
      have := (NNReal.coe_lt_coe.2 hlt)
      rwa [Real.coe_toNNReal _ hδ.le] at this
    simpa using h1
  have h2 := hδf hs0
  simp only [ENNReal.toNNReal_zero] at hs
  exact absurd hs (not_le.2 h2)

end Positive

section Mean

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

/-- **The mean of the `k`-th `ε`-crossing time does not depend on the Brownian motion.**  Two
motions of `IsBrownianSpace` in the same dimension with continuous paths, on any probability
spaces and from any starting points, have the same mean `k`-th `ε`-crossing time. -/
theorem IsBrownianSpace.lintegral_crossTime_eq {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {x x' : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {B' : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hB' : IsBrownianSpace d x' B' P')
    (hm : ∀ t, StronglyMeasurable (B t)) (hm' : ∀ t, StronglyMeasurable (B' t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (hcont' : ∀ ω, Continuous fun t => B' t ω)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∫⁻ ω, crossTime ε (fun t => B t ω) k ∂P = ∫⁻ ω, crossTime ε (fun t => B' t ω) k ∂P' := by
  have hG : Measurable fun y : BrownianPath d => crossTime ε (fun s => y s) k :=
    measurable_crossTime (E := EuclideanSpace ℝ (Fin d)) hε k
  have hR := measurable_restartPath hm hcont (τ := fun _ => 0) measurable_const
  have hR' := measurable_restartPath hm' hcont' (τ := fun _ => 0) measurable_const
  have h1 : ∫⁻ ω, crossTime ε (fun t => B t ω) k ∂P =
      ∫⁻ y, crossTime ε (fun s => y s) k ∂(P.map (restartPath B hcont fun _ => 0)) := by
    rw [lintegral_map hG hR]
    exact lintegral_congr fun ω => (crossTime_restartPath_zero B hcont ε k ω).symm
  have h2 : ∫⁻ ω, crossTime ε (fun t => B' t ω) k ∂P' =
      ∫⁻ y, crossTime ε (fun s => y s) k ∂(P'.map (restartPath B' hcont' fun _ => 0)) := by
    rw [lintegral_map hG hR']
    exact lintegral_congr fun ω => (crossTime_restartPath_zero B' hcont' ε k ω).symm
  rw [h1, h2, hB.map_restartPath_zero_eq hB' hcont hcont']

/-- **Brownian scaling of the mean first crossing time.**  For a Brownian motion started at `0`,
`E σ₁^c = c ^ 2 E σ₁¹` for every `c > 0`. -/
theorem IsBrownianSpace.lintegral_crossTime_scale {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d 0 B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {c : ℝ≥0} (hc : c ≠ 0) :
    ∫⁻ ω, crossTime (c : ℝ) (fun t => B t ω) 1 ∂P =
      ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ ω, crossTime 1 (fun t => B t ω) 1 ∂P := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hB' := hB.timeScale hc2
  have hm' : ∀ t, StronglyMeasurable
      ((fun t ω => (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹ • B (c ^ 2 * t) ω) t) := fun t =>
    (hm (c ^ 2 * t)).const_smul (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹
  have hcont' : ∀ ω, Continuous fun t => (fun t ω => (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹ •
      B (c ^ 2 * t) ω) t ω := fun ω => by
    have h : Continuous fun t : ℝ≥0 => B (c ^ 2 * t) ω :=
      (hcont ω).comp (continuous_const.mul continuous_id)
    show Continuous fun t : ℝ≥0 => (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹ • B (c ^ 2 * t) ω
    exact h.const_smul (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹
  have h1 := hB'.lintegral_crossTime_eq hB hm' hm hcont' hcont zero_lt_one 1
  have hsq : √((c ^ 2 : ℝ≥0) : ℝ) = c := by
    rw [NNReal.coe_pow]
    exact Real.sqrt_sq c.2
  have h2 : ∀ ω, crossTime (c : ℝ) (fun t => B t ω) 1 =
      ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * crossTime 1 (fun s => (√((c ^ 2 : ℝ≥0) : ℝ))⁻¹ •
        B (c ^ 2 * s) ω) 1 := by
    intro ω
    rw [hsq]
    exact (crossTime_scaled (fun t => B t ω) hc 1).symm
  simp only [h2]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end Mean

section Exists

private theorem ennreal_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  by_cases h : x ≤ 1
  · exact h.trans le_self_add
  · rw [not_le] at h
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 2 := pow_le_pow_right₀ h.le (by norm_num)
      _ ≤ 1 + x ^ 2 := le_add_self

/-- **The mean first crossing time of a Brownian motion in `ℝ ^ d`, `d ≥ 1`.**  There is a
constant `m ∈ (0, ∞)`, depending only on the dimension, such that for every probability space,
starting point and Brownian motion with continuous paths, `E σ₁^ε = ε ^ 2 m` for all `ε > 0`,
where `σ₁^ε` is the first `ε`-crossing time. -/
theorem exists_lintegral_crossTime_eq (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ∞ ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin d))
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ ε : ℝ, 0 < ε →
        ∫⁻ ω, crossTime ε (fun t => B t ω) 1 ∂P = ENNReal.ofReal (ε ^ 2) * m := by
  obtain ⟨Ω₀, mΩ₀, P₀, B₀, hB₀, hm₀, hcont₀⟩ := exists_isBrownianSpace_cont d 0
  have hP₀ : IsProbabilityMeasure P₀ :=
    (hB₀.coord ⟨0, hd⟩).isGaussianProcess.isProbabilityMeasure
  have hmeas : Measurable fun ω => crossTime 1 (fun t => B₀ t ω) 1 :=
    measurable_crossTime_process B₀ hm₀ hcont₀ zero_lt_one 1
  have hpos : ∀ ω, 0 < crossTime 1 (fun t => B₀ t ω) 1 := fun ω =>
    crossTime_one_pos (hcont₀ ω).continuousAt zero_lt_one
  refine ⟨∫⁻ ω, crossTime 1 (fun t => B₀ t ω) 1 ∂P₀, ?_, ?_, ?_⟩
  · rw [pos_iff_ne_zero]
    intro h0
    rw [lintegral_eq_zero_iff hmeas] at h0
    obtain ⟨ω, hω⟩ := h0.exists
    exact (hpos ω).ne' hω
  · obtain ⟨C, -, hC⟩ := exists_crossTime_one_sq_lintegral_le d hd
    have hsq := hC Ω₀ P₀ 0 B₀ hB₀ hm₀ hcont₀ 1 zero_lt_one
    refine lt_of_le_of_lt (lintegral_mono fun ω => ennreal_le_one_add_sq _) ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_lt hsq ENNReal.ofReal_lt_top⟩
  · intro Ω _ P _ x B hB hm hcont ε hε
    have hc : ε.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hε).ne'
    have h1 := hB.lintegral_crossTime_eq hB₀ hm hm₀ hcont hcont₀ hε 1
    have h2 := hB₀.lintegral_crossTime_scale hm₀ hcont₀ hc
    rw [Real.coe_toNNReal _ hε.le] at h2
    have h3 : ((ε.toNNReal ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (ε ^ 2) := by
      rw [ENNReal.ofReal_pow hε.le, ENNReal.coe_pow]
      rfl
    rw [h1, h2, h3]

end Exists

end LatticeProb
