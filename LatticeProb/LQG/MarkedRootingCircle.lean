import Mathlib
import LatticeProb.LQG.MarkedRootingFunction
import LatticeProb.Gauss.CircleAverageApprox2

/-!
# The marked rooting identity with the circle average as an extra mark

Limit lemmas for the iterated integrals `E ∫ f dμ` of bounded integrands, and the convergence of the root
shifts `z ↦ ∫ ψ_j(x) Cov (h(x), h(z)) dx` of the annular approximants `ψ_j` of the circle average of radius `ρ`
to the root shift `c_ρ(z) = ∫ Cov (h(x), h(z)) dσ_ρ(x)` of the circle average.

## Main statements

* `LatticeProb.Gauss.tendsto_lintegral_lintegral_randomMeasure`,
  `LatticeProb.Gauss.tendsto_lintegral_lintegral_prod`: dominated convergence for the two sides of a marked
  rooting identity.
* `LatticeProb.Gauss.tendsto_integral_circleApprox_mul_wholePlaneCov`: convergence of the root shifts.
* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasure_marked_circle_fun_eq`: the marked rooting identity
  `E [∫_{𝔻} f ((z, X), h_ρ(0)) dμ (z)] = ∫_{𝔻} E [f ((z, X + γ c(z)), h_ρ(0) + γ c_ρ(z))] dz` with the circle
  average `h_ρ(0)` as an extra mark, for measurable `f ≥ 0` (a limit of the identity for the annular
  approximants of the circle average).
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Gauss

section DominatedConvergence

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Dominated convergence for `∫⁻ ω, ∫⁻ a, H n ω a ∂(ν ω) ∂P` with integrands bounded by `1` when the total
mass `ν ω univ` of the random measure has finite expectation. -/
theorem tendsto_lintegral_lintegral_randomMeasure {P : Measure Ω} (ν : Ω → Measure α)
    (hfin : ∫⁻ ω, ν ω Set.univ ∂P ≠ ∞) (hνm : AEMeasurable (fun ω => ν ω Set.univ) P)
    {H : ℕ → Ω → α → ℝ≥0∞} {H₀ : Ω → α → ℝ≥0∞} (hHm : ∀ n ω, Measurable (H n ω))
    (hle : ∀ n ω a, H n ω a ≤ 1)
    (hmeas : ∀ n, AEMeasurable (fun ω => ∫⁻ a, H n ω a ∂(ν ω)) P)
    (hlim : ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n => H n ω a) atTop (𝓝 (H₀ ω a))) :
    AEMeasurable (fun ω => ∫⁻ a, H₀ ω a ∂(ν ω)) P ∧
      Tendsto (fun n => ∫⁻ ω, ∫⁻ a, H n ω a ∂(ν ω) ∂P) atTop
        (𝓝 (∫⁻ ω, ∫⁻ a, H₀ ω a ∂(ν ω) ∂P)) := by
  have hfin' : ∀ᵐ ω ∂P, ν ω Set.univ < ∞ := ae_lt_top' hνm hfin
  have hpt : ∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ a, H n ω a ∂(ν ω)) atTop
      (𝓝 (∫⁻ a, H₀ ω a ∂(ν ω))) := by
    filter_upwards [hfin', hlim] with ω hω hl
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (hHm · ω)
      (fun n => Eventually.of_forall (hle n ω)) ?_ (Eventually.of_forall hl)
    simpa using hω.ne
  refine ⟨aemeasurable_of_tendsto_metrizable_ae atTop hmeas hpt, ?_⟩
  refine tendsto_lintegral_of_dominated_convergence' (fun ω => ν ω Set.univ) hmeas
    (fun n => Eventually.of_forall fun ω => ?_) hfin hpt
  calc ∫⁻ a, H n ω a ∂(ν ω) ≤ ∫⁻ _a, 1 ∂(ν ω) := lintegral_mono (hle n ω)
    _ = ν ω Set.univ := by simp

/-- Dominated convergence for `∫⁻ a, ∫⁻ ω, H n a ω ∂P ∂μ₁` with jointly measurable integrands bounded by `1`
and finite measures. -/
theorem tendsto_lintegral_lintegral_prod {μ₁ : Measure α} [IsFiniteMeasure μ₁] {P : Measure Ω}
    [IsFiniteMeasure P] {H : ℕ → α → Ω → ℝ≥0∞} {H₀ : α → Ω → ℝ≥0∞}
    (hHm : ∀ n, Measurable (Function.uncurry (H n))) (hle : ∀ n a ω, H n a ω ≤ 1)
    (hlim : ∀ a, ∀ᵐ ω ∂P, Tendsto (fun n => H n a ω) atTop (𝓝 (H₀ a ω))) :
    Tendsto (fun n => ∫⁻ a, ∫⁻ ω, H n a ω ∂P ∂μ₁) atTop
      (𝓝 (∫⁻ a, ∫⁻ ω, H₀ a ω ∂P ∂μ₁)) := by
  have hin : ∀ a, Tendsto (fun n => ∫⁻ ω, H n a ω ∂P) atTop (𝓝 (∫⁻ ω, H₀ a ω ∂P)) := fun a =>
    tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun n => (hHm n).comp measurable_prodMk_left) (fun n => Eventually.of_forall (hle n a))
      (by simp) (hlim a)
  refine tendsto_lintegral_of_dominated_convergence (fun _ => P Set.univ)
    (fun n => (hHm n).lintegral_prod_right') (fun n => Eventually.of_forall fun a => ?_) ?_
    (Eventually.of_forall hin)
  · calc ∫⁻ ω, H n a ω ∂P ≤ ∫⁻ _ω, 1 ∂P := lintegral_mono (hle n a)
      _ = P Set.univ := by simp
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

end DominatedConvergence

theorem wholePlaneCov_symm (x y : ℂ) : wholePlaneCov x y = wholePlaneCov y x := by
  unfold wholePlaneCov
  rw [norm_sub_rev, mul_comm (max ‖x‖ 1)]

theorem tendsto_approxEta (ρ : ℝ) : Tendsto (approxEta ρ) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul
    (ρ / 4)
  show Tendsto (fun j : ℕ => ρ / 4 * (1 / 2 : ℝ) ^ j) atTop (𝓝 0)
  simpa using h

/-- The root shifts of the annular approximants of the circle average of radius `ρ` converge to the root shift
`∫ Cov (h(x), h(z)) dσ_ρ(x)` of the circle average. -/
theorem tendsto_integral_circleApprox_mul_wholePlaneCov {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    Tendsto (fun j => ∫ x, circleApprox hρ 0 j x * wholePlaneCov x z) atTop
      (𝓝 (Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ)) := by
  have hδ : ∀ j, 0 < ρ * approxEta ρ j := fun j => mul_pos hρ (approxEta_pos hρ j)
  have hrw : ∀ j, ∫ x, circleApprox hρ 0 j x * wholePlaneCov x z =
      logMaxAbs z + (∫ y, unitCircleDensity ρ (ρ * approxEta ρ j) (hδ j) 0 y * logMaxAbs y) -
        logPotential ρ (ρ * approxEta ρ j) (hδ j) 0 z := fun j => by
    have h := integral_unitCircleDensity_mul_wholePlaneCov hρ.le (hδ j) 0 z
    have hfun : (fun x => circleApprox hρ 0 j x * wholePlaneCov x z) =
        fun x => unitCircleDensity ρ (ρ * approxEta ρ j) (hδ j) 0 x * wholePlaneCov z x :=
      funext fun x => by rw [wholePlaneCov_symm x z]; rfl
    rw [hfun]
    exact h
  have h2 : Tendsto (fun j => ∫ y, unitCircleDensity ρ (ρ * approxEta ρ j) (hδ j) 0 y * logMaxAbs y)
      atTop (𝓝 (Real.circleAverage logMaxAbs 0 ρ)) := by
    refine tendsto_unitCircleDensity_mul_continuous hρ (δ := fun j => ρ * approxEta ρ j) hδ ?_ 0
      logMaxAbs_continuous
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_approxEta ρ).eventually (gt_mem_nhds hη))
    exact ⟨N, fun j hj => mul_le_mul_of_nonneg_left (hN j hj).le hρ.le⟩
  have h3 : Tendsto (fun j => logPotential ρ (ρ * approxEta ρ j) (hδ j) 0 z) atTop
      (𝓝 (circlePotential ρ 0 z)) := by
    have hb : ∀ j, ‖logPotential ρ (ρ * approxEta ρ j) (hδ j) 0 z - circlePotential ρ 0 z‖ ≤
        Real.log (ρ + approxEta ρ j) - Real.log (ρ - approxEta ρ j) := fun j => by
      rw [Real.norm_eq_abs]
      exact abs_logPotential_sub_circlePotential_le hρ (hδ j) (by linarith [approxEta_le hρ j]) le_rfl 0 z
    have hlim : Tendsto (fun j => Real.log (ρ + approxEta ρ j) - Real.log (ρ - approxEta ρ j)) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun j => Real.log (ρ + approxEta ρ j)) atTop (𝓝 (Real.log (ρ + 0))) :=
        (Real.continuousAt_log (by positivity)).tendsto.comp
          (tendsto_const_nhds.add (tendsto_approxEta ρ))
      have h1' : Tendsto (fun j => Real.log (ρ - approxEta ρ j)) atTop (𝓝 (Real.log (ρ - 0))) :=
        (Real.continuousAt_log (by linarith)).tendsto.comp
          (tendsto_const_nhds.sub (tendsto_approxEta ρ))
      simpa using h1.sub h1'
    exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb hlim)
  have hval : Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ =
      logMaxAbs z + Real.circleAverage logMaxAbs 0 ρ - circlePotential ρ 0 z := by
    rw [circleAverage_wholePlaneCov hρ]
    rfl
  rw [hval]
  simp_rw [hrw]
  exact (h2.const_add _).sub h3


theorem continuous_circleAverage_wholePlaneCov_root {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun z : ℂ => Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ := by
  have h : (fun z : ℂ => Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ) =
      fun z => logMaxAbs z + Real.circleAverage logMaxAbs 0 ρ - Real.log (max ρ ‖z - 0‖) :=
    funext fun z => circleAverage_wholePlaneCov hρ
  rw [h]
  exact (logMaxAbs_continuous.add continuous_const).sub
    (Continuous.log (by fun_prop) fun z => (lt_max_of_lt_left hρ).ne')

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The marked rooting identity with one more test function `ψ` as a last mark: for measurable
`G : (ℂ × ℝ^m) × ℝ → [0, ∞]`, `E [∫_{𝔻} G ((z, X), (h, ψ)) dμ (z)] = ∫_{𝔻} E [G ((z, X + γ c(z)), (h, ψ) + γ c_ψ(z))] dz`,
with `c_ψ(z) = ∫ ψ(x) Cov (h(x), h(z)) dx`. -/
theorem lintegral_lqgMeasure_marked_fun_eq_snoc (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction Set.univ ψ) {G : (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞} (hG : Measurable G) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1,
        G ((z, fun i => hC ω (φ i)), hC ω ψ) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1, G ((z, fun i => hC ω (φ i)), hC ω ψ) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        G ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
          hC ω ψ + γ * ∫ x, ψ x * wholePlaneCov x z) ∂P := by
  have hmeasf : Measurable fun q : ℂ × (Fin (m + 1) → ℝ) =>
      G ((q.1, fun i => q.2 i.castSucc), q.2 (Fin.last m)) :=
    hG.comp ((measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
      (measurable_pi_apply _).comp measurable_snd)).prodMk ((measurable_pi_apply _).comp measurable_snd))
  have h := hh.lintegral_lqgMeasure_marked_fun_eq hγ0 hγ2 hμ
    (φ := Fin.snoc (α := fun _ => ℂ → ℝ) φ ψ)
    (Fin.forall_fin_succ'.2 ⟨fun j => by simpa using hφ j, by simpa using hψ⟩) hmeasf
  simpa [Fin.snoc_castSucc, Fin.snoc_last] using h

/-- The total mass `μ(𝔻)` of the Liouville measure on the unit disk is almost everywhere measurable with
finite expectation (the expectation is the area of `𝔻`). -/
theorem restrict_ball_total_mass (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) :
    AEMeasurable (fun ω => ((μ ω).restrict (Metric.ball (0 : ℂ) 1)) Set.univ) P ∧
      ∫⁻ ω, ((μ ω).restrict (Metric.ball (0 : ℂ) 1)) Set.univ ∂P ≠ ∞ := by
  have hP := hh.isProbabilityMeasure
  have hone := hh.lintegral_lqgMeasure_marked_fun_eq hγ0 hγ2 hμ hφ (f := fun _ => (1 : ℝ≥0∞))
    measurable_const
  have hmass : ∫⁻ ω, ((μ ω).restrict (Metric.ball (0 : ℂ) 1)) Set.univ ∂P =
      volume (Metric.ball (0 : ℂ) 1) := by
    simpa using hone.2
  exact ⟨by simpa [Measure.restrict_apply_univ] using hone.1, by rw [hmass]; exact measure_ball_lt_top.ne⟩

/-- **The marked rooting identity with the circle average as an extra mark, bounded integrands continuous in
the circle coordinate.** For measurable `G : (ℂ × ℝ^m) × ℝ → [0, 1]` continuous in the last variable,
`E [∫_{𝔻} G ((z, X), h_ρ(0)) dμ (z)] = ∫_{𝔻} E [G ((z, X + γ c(z)), h_ρ(0) + γ c_ρ(z))] dz`, where
`c_ρ(z) = ∫ Cov (h(x), h(z)) dσ_ρ(x)`. -/
theorem lintegral_lqgMeasure_marked_circle_eq_of_continuous (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    {m : ℕ} {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {ρ : ℝ} (hρ : 0 < ρ)
    {G : (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞} (hG : Measurable G) (hG1 : ∀ y, G y ≤ 1)
    (hGc : ∀ y : ℂ × (Fin m → ℝ), Continuous fun t => G (y, t)) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1,
        G ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1, G ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        G ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
          hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hψt : ∀ j, IsTestFunction Set.univ (circleApprox hρ 0 j) := fun j =>
    isTestFunction_circleApprox hρ 0 j
  have hpair : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have hsmψ : ∀ j, Measurable fun z : ℂ => ∫ x, circleApprox hρ 0 j x * wholePlaneCov x z := fun j =>
    measurable_integral_mul_wholePlaneCov (hψt j)
  have hτm : ∀ j, Measurable fun ω => hC ω (circleApprox hρ 0 j) := fun j =>
    hh.measurable_pairing _ (hψt j)
  have hae := ae_tendsto_circleApprox hh hρ 0
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  obtain ⟨hνm, hfin⟩ := restrict_ball_total_mass hh hγ0 hγ2 hμ hφ
  have hL := tendsto_lintegral_lintegral_randomMeasure (P := P)
    (fun ω => (μ ω).restrict (Metric.ball (0 : ℂ) 1)) hfin hνm
    (H := fun j ω z => G ((z, fun i => hC ω (φ i)), hC ω (circleApprox hρ 0 j)))
    (H₀ := fun ω z => G ((z, fun i => hC ω (φ i)), hcirc ω ρ 0))
    (fun j ω => hG.comp ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    (fun j ω a => hG1 _)
    (fun j => (lintegral_lqgMeasure_marked_fun_eq_snoc hh hγ0 hγ2 hμ hφ (hψt j) hG).1)
    (by
      filter_upwards [hae] with ω hω z
      exact (hGc (z, fun i => hC ω (φ i))).continuousAt.tendsto.comp hω)
  have hR := tendsto_lintegral_lintegral_prod (μ₁ := volume.restrict (Metric.ball (0 : ℂ) 1)) (P := P)
    (H := fun j z ω => G ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
      hC ω (circleApprox hρ 0 j) + γ * ∫ x, circleApprox hρ 0 j x * wholePlaneCov x z))
    (H₀ := fun z ω => G ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
      hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ))
    (fun j => by
      have hF : Measurable fun p : ℂ × Ω => ((p.1, fun i => hC p.2 (φ i) +
          γ * ∫ x, φ i x * wholePlaneCov x p.1),
          hC p.2 (circleApprox hρ 0 j) + γ * ∫ x, circleApprox hρ 0 j x * wholePlaneCov x p.1) :=
        (measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
          ((hpair i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))).prodMk
          (((hτm j).comp measurable_snd).add (((hsmψ j).comp measurable_fst).const_mul γ))
      exact hG.comp hF)
    (fun j z ω => hG1 _)
    (fun z => by
      filter_upwards [hae] with ω hω
      exact (hGc _).continuousAt.tendsto.comp
        (hω.add ((tendsto_integral_circleApprox_mul_wholePlaneCov hρ z).const_mul γ)))
  exact ⟨hL.1, tendsto_nhds_unique hL.2 (hR.congr fun j =>
    (lintegral_lqgMeasure_marked_fun_eq_snoc hh hγ0 hγ2 hμ hφ (hψt j) hG).2.symm)⟩

/-- **Open product sets.** The marked rooting identity with the circle average as an extra mark for the
indicator of `A ×ˢ U` with `A` measurable and `U ⊆ ℝ` open. -/
theorem lintegral_lqgMeasure_marked_circle_eq_of_prod_isOpen (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    {m : ℕ} {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {ρ : ℝ} (hρ : 0 < ρ)
    {A : Set (ℂ × (Fin m → ℝ))} (hA : MeasurableSet A) {U : Set ℝ} (hU : IsOpen U) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1,
        (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1,
        (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞))
          ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
          hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ) ∂P := by
  classical
  have hP := hh.isProbabilityMeasure
  have hpair : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have hcm : Measurable fun ω => hcirc ω ρ 0 := hh.measurable_circle ρ 0 hρ
  have hcτ : Measurable fun z : ℂ => Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ :=
    (continuous_circleAverage_wholePlaneCov_root hρ).measurable
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  obtain ⟨hνm, hfin⟩ := restrict_ball_total_mass hh hγ0 hγ2 hμ hφ
  obtain ⟨f, hfc, hf01, -, -, hflim⟩ := exists_monotone_continuous_tendsto_indicator_iUnion
    (fun _ : ℕ => U) (fun _ => hU) monotone_const
  set Gn : ℕ → (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞ := fun n q =>
    if q.1 ∈ A then ENNReal.ofReal (f n q.2) else 0 with hGn
  have hGnm : ∀ n, Measurable (Gn n) := fun n =>
    Measurable.ite (measurable_fst hA) (ENNReal.measurable_ofReal.comp ((hfc n).measurable.comp measurable_snd))
      measurable_const
  have hGn1 : ∀ n q, Gn n q ≤ 1 := fun n q => by
    by_cases hq : q.1 ∈ A
    · simp only [hGn, hq, ite_true]
      exact ENNReal.ofReal_le_one.2 (hf01 n q.2).2
    · simp [hGn, hq]
  have hGnc : ∀ n y, Continuous fun t => Gn n (y, t) := fun n y => by
    by_cases hy : y ∈ A
    · simp only [hGn, hy, ite_true]
      exact ENNReal.continuous_ofReal.comp (hfc n)
    · have h0 : (fun t => Gn n (y, t)) = fun _ => 0 := funext fun t => by simp [hGn, hy]
      rw [h0]
      exact continuous_const
  have hGlim : ∀ q, Tendsto (fun n => Gn n q) atTop
      (𝓝 ((A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) q)) := fun q => by
    by_cases hq : q.1 ∈ A
    · have hind : (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) q = ENNReal.ofReal ((U.indicator (1 : ℝ → ℝ)) q.2) := by
        by_cases hu : q.2 ∈ U <;> simp [Set.indicator, hq, hu]
      rw [hind]
      simp only [hGn, hq, ite_true]
      have := hflim q.2
      rw [Set.iUnion_const] at this
      exact ENNReal.tendsto_ofReal this
    · have hind : (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) q = 0 := by simp [Set.indicator, hq]
      rw [hind]
      simp [hGn, hq]
  have hW := fun n => lintegral_lqgMeasure_marked_circle_eq_of_continuous hh hγ0 hγ2 hμ hφ hρ
    (hGnm n) (hGn1 n) (hGnc n)
  have hL := tendsto_lintegral_lintegral_randomMeasure (P := P)
    (fun ω => (μ ω).restrict (Metric.ball (0 : ℂ) 1)) hfin hνm
    (H := fun n ω z => Gn n ((z, fun i => hC ω (φ i)), hcirc ω ρ 0))
    (H₀ := fun ω z => (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) ((z, fun i => hC ω (φ i)), hcirc ω ρ 0))
    (fun n ω => (hGnm n).comp ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    (fun n ω a => hGn1 _ _) (fun n => (hW n).1)
    (Filter.Eventually.of_forall fun ω z => hGlim _)
  have hR := tendsto_lintegral_lintegral_prod (μ₁ := volume.restrict (Metric.ball (0 : ℂ) 1)) (P := P)
    (H := fun n z ω => Gn n ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
      hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ))
    (H₀ := fun z ω => (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞))
      ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
      hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ))
    (fun n => by
      have hF : Measurable fun p : ℂ × Ω => ((p.1, fun i => hC p.2 (φ i) +
          γ * ∫ x, φ i x * wholePlaneCov x p.1),
          hcirc p.2 ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov p.1 y) 0 ρ) :=
        (measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
          ((hpair i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))).prodMk
          ((hcm.comp measurable_snd).add ((hcτ.comp measurable_fst).const_mul γ))
      exact (hGnm n).comp hF)
    (fun n z ω => hGn1 _ _) (fun z => Filter.Eventually.of_forall fun ω => hGlim _)
  exact ⟨hL.1, tendsto_nhds_unique hL.2 (hR.congr fun n => (hW n).2.symm)⟩

/-- **The marked rooting identity with the circle average as an extra mark.** For measurable
`f : (ℂ × ℝ^m) × ℝ → [0, ∞]`, with `X = ((h, φ_i))_i`, `c(z) = (∫ φ_i(x) Cov (h(x), h(z)) dx)_i` and
`c_ρ(z) = ∫ Cov (h(x), h(z)) dσ_ρ(x)` (`σ_ρ` the uniform probability measure on `∂B_ρ(0)`),
`E [∫_{𝔻} f ((z, X), h_ρ(0)) dμ (z)] = ∫_{𝔻} E [f ((z, X + γ c(z)), h_ρ(0) + γ c_ρ(z))] dz`;
the left integrand is almost everywhere measurable. -/
theorem lintegral_lqgMeasure_marked_circle_fun_eq (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {ρ : ℝ} (hρ : 0 < ρ)
    {f : (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1,
        f ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1, f ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        f ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
          hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hpair : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have hcm : Measurable fun ω => hcirc ω ρ 0 := hh.measurable_circle ρ 0 hρ
  have hcτ : Measurable fun z : ℂ => Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ :=
    (continuous_circleAverage_wholePlaneCov_root hρ).measurable
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hFm : Measurable fun p : ℂ × Ω => ((p.1, fun i => hC p.2 (φ i) +
      γ * ∫ x, φ i x * wholePlaneCov x p.1),
      hcirc p.2 ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov p.1 y) 0 ρ) :=
    (measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
      ((hpair i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))).prodMk
      ((hcm.comp measurable_snd).add ((hcτ.comp measurable_fst).const_mul γ))
  let ν : Ω → Measure ((ℂ × (Fin m → ℝ)) × ℝ) := fun ω =>
    ((μ ω).restrict (Metric.ball (0 : ℂ) 1)).map
      (fun z => ((z, fun i => hC ω (φ i)), hcirc ω ρ 0))
  let ρ' : Measure ((ℂ × (Fin m → ℝ)) × ℝ) :=
    ((volume.restrict (Metric.ball (0 : ℂ) 1)).prod P).map
      (fun p : ℂ × Ω => ((p.1, fun i => hC p.2 (φ i) + γ * ∫ x, φ i x * wholePlaneCov x p.1),
        hcirc p.2 ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov p.1 y) 0 ρ))
  have hνg : ∀ g : (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞, Measurable g → ∀ ω, ∫⁻ y, g y ∂(ν ω) =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, g ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω) :=
    fun g hg ω => lintegral_map hg ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  have hρg : ∀ g : (ℂ × (Fin m → ℝ)) × ℝ → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂ρ' =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        g ((z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z),
          hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov z y) 0 ρ) ∂P := fun g hg => by
    simp only [ρ']
    rw [lintegral_map hg hFm]
    exact lintegral_prod (fun p => g _) (hg.comp hFm).aemeasurable
  let Sys : Set (Set ((ℂ × (Fin m → ℝ)) × ℝ)) :=
    Set.image2 (· ×ˢ ·) {A : Set (ℂ × (Fin m → ℝ)) | MeasurableSet A} {U : Set ℝ | IsOpen U}
  have hpi : IsPiSystem Sys := IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet isPiSystem_isOpen
  have huniv : (Set.univ : Set ((ℂ × (Fin m → ℝ)) × ℝ)) ∈ Sys :=
    ⟨Set.univ, (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℂ × (Fin m → ℝ)))), Set.univ,
      (isOpen_univ : IsOpen (Set.univ : Set ℝ)), Set.univ_prod_univ⟩
  have hgen : (inferInstance : MeasurableSpace ((ℂ × (Fin m → ℝ)) × ℝ)) =
      MeasurableSpace.generateFrom Sys := by
    have h := generateFrom_prod_eq (C := {s : Set (ℂ × (Fin m → ℝ)) | MeasurableSet s})
      (D := {s : Set ℝ | IsOpen s}) isCountablySpanning_measurableSet
      ⟨fun _ => Set.univ, fun _ => (isOpen_univ : IsOpen (Set.univ : Set ℝ)), Set.iUnion_const _⟩
    have e1 : MeasurableSpace.generateFrom {s : Set (ℂ × (Fin m → ℝ)) | MeasurableSet s} =
        (inferInstance : MeasurableSpace (ℂ × (Fin m → ℝ))) := MeasurableSpace.generateFrom_measurableSet
    have e2 : MeasurableSpace.generateFrom {s : Set ℝ | IsOpen s} = (inferInstance : MeasurableSpace ℝ) :=
      (BorelSpace.measurable_eq (α := ℝ)).symm
    rw [e1, e2] at h
    exact h
  have hbase : ∀ s ∈ Sys, AEMeasurable (fun ω => ν ω s) P ∧ ∫⁻ ω, ν ω s ∂P = ρ' s := by
    rintro s ⟨A, hA, U, hU, rfl⟩
    replace hA : MeasurableSet A := hA
    replace hU : IsOpen U := hU
    have hs : MeasurableSet (A ×ˢ U) := hA.prod hU.measurableSet
    have hind : Measurable ((A ×ˢ U).indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hs
    have h := hh.lintegral_lqgMeasure_marked_circle_eq_of_prod_isOpen hγ0 hγ2 hμ hφ hρ hA hU
    have hνS : ∀ ω, ν ω (A ×ˢ U) = ∫⁻ z in Metric.ball (0 : ℂ) 1,
        (A ×ˢ U).indicator (fun _ => (1 : ℝ≥0∞)) ((z, fun i => hC ω (φ i)), hcirc ω ρ 0) ∂(μ ω) :=
      fun ω => (lintegral_indicator_one hs).symm.trans (hνg _ hind ω)
    have hρS := (lintegral_indicator_one hs).symm.trans (hρg _ hind)
    exact ⟨h.1.congr (Filter.Eventually.of_forall fun ω => (hνS ω).symm),
      (lintegral_congr fun ω => hνS ω).trans (h.2.trans hρS.symm)⟩
  have key := aemeasurable_and_lintegral_eq_of_forall_measurableSet (P := P) ν ρ'
    (aemeasurable_and_lintegral_eq_of_isPiSystem (P := P) ν ρ' hgen hpi huniv hbase) f hf
  refine ⟨key.1.congr (Filter.Eventually.of_forall fun ω => hνg f hf ω), ?_⟩
  rw [← hρg f hf, ← key.2]
  exact lintegral_congr fun ω => (hνg f hf ω).symm

end IsWholePlaneGFF

end LatticeProb.Gauss
