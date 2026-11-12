import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Mollification of Lipschitz functions: convergence of the directional derivatives in `L²`

Real analysis on a finite-dimensional real normed space `E` with a Haar measure `μ`; no external input.

A compactly supported Lipschitz function `g : E → ℝ` belongs to the Sobolev space `H¹`, and its mollifications
converge to it in `H¹`. The statements are in terms of line derivatives (`lineDeriv`), which exist almost
everywhere by Rademacher's theorem.

* `lineDeriv_eq_zero_of_notMem_tsupport`: the line derivative vanishes off the topological support.
* `hasLineDerivAt_convolution_of_lipschitz`: for `ρ` continuous with compact support and `g` Lipschitz, the
  convolution `ρ ⋆ g` has at every point the line derivative `ρ ⋆ ∂_v g` (differentiation under the integral
  sign, with the almost everywhere line differentiability of `g`).
* `exists_contDiff_approx_of_lipschitz`: for `g` Lipschitz with compact support there are smooth compactly
  supported `u n` with `|u n - g| ≤ C / (n + 1)` uniformly and `∂_v (u n) → ∂_v g` in `L²(μ)` for every
  direction `v`. The `u n` are the convolutions of `g` with normalized bump functions of radius `1 / (n + 1)`;
  the convergence is the Lebesgue differentiation theorem for `∂_v g` and dominated convergence.
-/

open MeasureTheory Filter Topology Metric Set ContinuousLinearMap
open scoped Convolution NNReal ContDiff Pointwise

namespace LatticeProb

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The line derivative of a function vanishes at the points outside its topological support. -/
theorem lineDeriv_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) (v : E) :
    lineDeriv ℝ f x v = 0 := by
  have h0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [h0.lineDeriv_eq]
  simp [lineDeriv]

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Line derivative of the convolution with a Lipschitz function.** For `ρ` continuous with compact support
and `g` Lipschitz, the convolution `ρ ⋆ g` has, at every point `x` and in every direction `v`, the line
derivative `(ρ ⋆ ∂_v g) x`, where `∂_v g = lineDeriv ℝ g · v` exists almost everywhere. -/
theorem hasLineDerivAt_convolution_of_lipschitz {ρ g : E → ℝ} {C : ℝ≥0} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hg : LipschitzWith C g) (x v : E) :
    HasLineDerivAt ℝ (ρ ⋆[lsmul ℝ ℝ, μ] g) ((ρ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ g y v) x) x v := by
  have hρi : Integrable ρ μ := hρ.integrable_of_hasCompactSupport hρc
  have hF_cont : ∀ s : ℝ, Continuous fun t => ρ t * g (x + s • v - t) := fun s =>
    hρ.mul (hg.continuous.comp (continuous_const.sub continuous_id))
  have hF_int : Integrable (fun t => ρ t * g (x + (0 : ℝ) • v - t)) μ :=
    (hF_cont 0).integrable_of_hasCompactSupport
      (hρc.mono fun t ht => left_ne_zero_of_mul ht)
  have hF'_meas : AEStronglyMeasurable (fun t => ρ t * lineDeriv ℝ g (x - t) v) μ :=
    (hρ.measurable.mul ((measurable_lineDeriv hg.continuous).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  have h_lip : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs (‖ρ t‖ * (C * ‖v‖)))
      (fun s : ℝ => ρ t * g (x + s • v - t)) Set.univ := by
    refine Eventually.of_forall fun t => LipschitzWith.lipschitzOnWith ?_
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    rw [Real.coe_nnabs, abs_of_nonneg (by positivity), Real.dist_eq, ← mul_sub, abs_mul,
      Real.norm_eq_abs]
    have h1 : |g (x + s • v - t) - g (x + s' • v - t)| ≤ C * (‖v‖ * dist s s') := by
      have h := hg.dist_le_mul (x + s • v - t) (x + s' • v - t)
      have e : x + s • v - t - (x + s' • v - t) = (s - s') • v := by
        rw [sub_smul]
        abel
      have e2 : dist (x + s • v - t) (x + s' • v - t) = ‖v‖ * dist s s' := by
        rw [dist_eq_norm, e, norm_smul, Real.dist_eq, Real.norm_eq_abs, mul_comm]
      rw [e2, Real.dist_eq] at h
      exact h
    calc |ρ t| * |g (x + s • v - t) - g (x + s' • v - t)|
        ≤ |ρ t| * (C * (‖v‖ * dist s s')) := by gcongr
      _ = |ρ t| * (C * ‖v‖) * dist s s' := by ring
  have h_bound : Integrable (fun t => ‖ρ t‖ * (C * ‖v‖)) μ := hρi.norm.mul_const _
  have h_diff : ∀ᵐ t ∂μ, HasDerivAt (fun s : ℝ => ρ t * g (x + s • v - t))
      (ρ t * lineDeriv ℝ g (x - t) v) 0 := by
    have h1 : ∀ᵐ t ∂μ, LineDifferentiableAt ℝ g (x - t) v :=
      (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae (hg.ae_lineDifferentiableAt v)
    filter_upwards [h1] with t ht
    have h2 : HasDerivAt (fun s : ℝ => g (x - t + s • v)) (lineDeriv ℝ g (x - t) v) 0 :=
      ht.hasLineDerivAt
    have e : (fun s : ℝ => ρ t * g (x + s • v - t)) = fun s : ℝ => ρ t * g (x - t + s • v) := by
      funext s
      congr 2
      abel
    rw [e]
    exact h2.const_mul (ρ t)
  have key := (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun (s : ℝ) t => ρ t * g (x + s • v - t))
    (F' := fun t => ρ t * lineDeriv ℝ g (x - t) v) (x₀ := 0)
    (bound := fun t => ‖ρ t‖ * (C * ‖v‖)) (s := Set.univ) univ_mem
    (Eventually.of_forall fun s => (hF_cont s).aestronglyMeasurable) hF_int hF'_meas h_lip h_bound
    h_diff).2
  simpa only [HasLineDerivAt, convolution_def, lsmul_apply, smul_eq_mul] using key

/-- **Mollification of a compactly supported Lipschitz function in `H¹`.** For `g : E → ℝ` Lipschitz with
compact support there is a sequence `u n` of smooth compactly supported functions which converges to `g`
uniformly, with `|u n - g| ≤ C / (n + 1)`, and whose line derivatives in every direction `v` converge to the
(almost everywhere defined) line derivative of `g` in `L²(μ)`. -/
theorem exists_contDiff_approx_of_lipschitz (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hgc : HasCompactSupport g) :
    ∃ u : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n x, |u n x - g x| ≤ C / (n + 1)) ∧
      ∀ v : E, (∀ n, Integrable (fun x => (lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v) ^ 2) μ) ∧
        Tendsto (fun n => ∫ x, (lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hlt : ∀ n : ℕ, (1 : ℝ) / (2 * (n + 1)) < 1 / (n + 1) := fun n => by
    have h : (0 : ℝ) < n + 1 := by positivity
    exact one_div_lt_one_div_of_lt h (by linarith)
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity, hlt n⟩
  have hrOut : ∀ n, (φ n).rOut = 1 / ((n : ℝ) + 1) := fun n => rfl
  have hrIn : ∀ n, (φ n).rIn = 1 / (2 * ((n : ℝ) + 1)) := fun n => rfl
  have hrOut_le : ∀ n, (φ n).rOut ≤ 1 := fun n => by
    rw [hrOut, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h'φ : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := Eventually.of_forall fun n => by
    rw [hrOut, hrIn]
    have h : (0 : ℝ) < n + 1 := by positivity
    apply le_of_eq
    field_simp
  have hgcont : Continuous g := hg.continuous
  have hgli : LocallyIntegrable g μ := hgcont.locallyIntegrable
  let u : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] g
  have hsmooth : ∀ n, ContDiff ℝ ∞ (u n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (L := lsmul ℝ ℝ) (φ n).contDiff_normed hgli
  have hcs : ∀ n, HasCompactSupport (u n) := fun n =>
    (φ n).hasCompactSupport_normed.convolution (L := lsmul ℝ ℝ) hgc
  have hunif : ∀ n x, |u n x - g x| ≤ C / (n + 1) := by
    intro n x
    have hball : ∀ y ∈ ball x (φ n).rOut, dist (g y) (g x) ≤ C / (n + 1) := by
      intro y hy
      have h2 : dist y x ≤ 1 / ((n : ℝ) + 1) := (mem_ball.1 hy).le
      calc dist (g y) (g x) ≤ C * dist y x := hg.dist_le_mul y x
        _ ≤ C * (1 / ((n : ℝ) + 1)) := by gcongr
        _ = C / (n + 1) := by ring
    have h := (φ n).dist_normed_convolution_le (μ := μ) hgcont.aestronglyMeasurable hball
    rwa [Real.dist_eq] at h
  refine ⟨u, hsmooth, hcs, hunif, fun v => ?_⟩
  have hmeas : Measurable fun y => lineDeriv ℝ g y v := measurable_lineDeriv hgcont
  have hbd : ∀ y, |lineDeriv ℝ g y v| ≤ C * ‖v‖ := fun y => by
    simpa [Real.norm_eq_abs] using norm_lineDeriv_le_of_lipschitz ℝ hg (x₀ := y) (v := v)
  have hCv : (0 : ℝ) ≤ C * ‖v‖ := by positivity
  have hli : LocallyIntegrable (fun y => lineDeriv ℝ g y v) μ :=
    (locallyIntegrable_const (C * ‖v‖ : ℝ)).mono hmeas.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_of_nonneg hCv]
        exact hbd y)
  have hderiv : ∀ n x, lineDeriv ℝ (u n) x v =
      ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ g y v) x := fun n x =>
    (hasLineDerivAt_convolution_of_lipschitz (μ := μ) (φ n).continuous_normed
      (φ n).hasCompactSupport_normed hg x v).lineDeriv
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) (φ := φ)
    (l := atTop) (K := 2) hφ h'φ hli
  -- a compact set containing all the supports
  have hKc : IsCompact (closedBall (0 : E) 1 + tsupport g) := (isCompact_closedBall 0 1).add hgc
  have hsupp : ∀ n, tsupport (u n) ⊆ closedBall (0 : E) 1 + tsupport g := by
    intro n
    refine closure_minimal ?_ hKc.isClosed
    refine (support_convolution_subset (L := lsmul ℝ ℝ) (μ := μ)).trans ?_
    refine Set.add_subset_add ?_ (subset_tsupport g)
    rw [(φ n).support_normed_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (hrOut_le n))
  have hzero : ∀ n x, x ∉ closedBall (0 : E) 1 + tsupport g →
      lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v = 0 := by
    intro n x hx
    have h1 : x ∉ tsupport (u n) := fun hx' => hx (hsupp n hx')
    have h2 : x ∉ tsupport g := fun hx' =>
      hx (Set.mem_add.2 ⟨0, mem_closedBall_self zero_le_one, x, hx', zero_add x⟩)
    rw [lineDeriv_eq_zero_of_notMem_tsupport h1, lineDeriv_eq_zero_of_notMem_tsupport h2, sub_zero]
  have hdiff : ∀ n x, |lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v| ≤ 2 * (C * ‖v‖) := by
    intro n x
    rw [hderiv n x, ← Real.dist_eq]
    refine (φ n).dist_normed_convolution_le hmeas.aestronglyMeasurable (fun y _ => ?_)
    rw [Real.dist_eq]
    obtain ⟨h1, h2⟩ := abs_le.1 (hbd y)
    obtain ⟨h3, h4⟩ := abs_le.1 (hbd x)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hB_int : Integrable ((closedBall (0 : E) 1 + tsupport g).indicator
      fun _ => (2 * (C * ‖v‖)) ^ 2) μ :=
    (integrable_indicator_iff hKc.measurableSet).2 (continuousOn_const.integrableOn_compact hKc)
  have hF_meas : ∀ n, AEStronglyMeasurable
      (fun x => (lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v) ^ 2) μ := fun n =>
    (((measurable_lineDeriv (hsmooth n).continuous).sub hmeas).pow_const 2).aestronglyMeasurable
  have hF_bd : ∀ n x, ‖(lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v) ^ 2‖ ≤
      (closedBall (0 : E) 1 + tsupport g).indicator (fun _ => (2 * (C * ‖v‖)) ^ 2) x := by
    intro n x
    by_cases hx : x ∈ closedBall (0 : E) 1 + tsupport g
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hdiff n x) 2
    · rw [Set.indicator_of_notMem hx, hzero n x hx]
      simp
  refine ⟨fun n => hB_int.mono' (hF_meas n) (Eventually.of_forall (hF_bd n)), ?_⟩
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (lineDeriv ℝ (u n) x v - lineDeriv ℝ g x v) ^ 2) atTop
      (𝓝 0) := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun n => lineDeriv ℝ (u n) x v) atTop (𝓝 (lineDeriv ℝ g x v)) := by
      rw [show (fun n => lineDeriv ℝ (u n) x v) =
        fun n => ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ g y v) x from
        funext fun n => hderiv n x]
      exact hx
    have h2 := (h1.sub_const (lineDeriv ℝ g x v)).pow 2
    simpa using h2
  have h3 := tendsto_integral_of_dominated_convergence
    ((closedBall (0 : E) 1 + tsupport g).indicator fun _ => (2 * (C * ‖v‖)) ^ 2) hF_meas hB_int
    (fun n => Eventually.of_forall (hF_bd n)) hlim
  simpa using h3

end LatticeProb
