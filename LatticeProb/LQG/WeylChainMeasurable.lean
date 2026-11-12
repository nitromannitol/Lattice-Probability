import Mathlib
import LatticeProb.LQG.WeylChainFormula

/-!
# Measurability of the internal metric of a Weyl-scaled random length metric

Let `D_ω` be a random Euclidean length metric on `ℂ` and `E_ω = e^{ξ f} · D_ω` its Weyl scaling by a deterministic
continuous function `f` (Gwynne-Miller, arXiv:1905.00383, (1.7)-(1.8)), with `ξ f` bounded above and uniformly
continuous. By the chain formula `internalMetric_weylScaling_eq_iInf_weightedChainInf`, the internal metric of `E_ω` on
an open set `U` is a countable infimum of finite weighted sums of internal metrics of `D_ω` on small balls intersected
with `U`, with deterministic weights. Hence:

* `exists_oscillation_scales_of_uniformContinuous`: a uniformly continuous `g` has scales `δ_n > 0` and oscillation
  bounds `η_n → 0` with `|g a - g b| ≤ η_n` whenever `dist a b < δ_n`.
* `aemeasurable_weightedChainInf`: for countable `Q`, the weighted chain infimum of `D_ω` is a.e.-measurable in `ω` if
  the local internal metrics `D_ω(a, b; B(a, δ) ∩ U)` are, for `a ∈ {x} ∪ Q` and `b ∈ {y} ∪ Q`.
* `aemeasurable_internalMetric_weylScaling`: if the internal metrics `D_ω(a, b; B(a, r) ∩ U)` are a.e.-measurable in `ω`
  for all `a, b` and `r > 0`, and almost surely `D_ω` and `E_ω` are Euclidean length metrics with
  `E_ω = e^{ξ f} · D_ω`, then `ω ↦ E_ω(x, y; U)` is a.e.-measurable.
-/

namespace LatticeProb.LQG

open Set Filter Topology MeasureTheory
open scoped ENNReal

/-- A uniformly continuous function on `ℂ` has scales `δ_n > 0` and oscillation bounds `η_n → 0`: `|g a - g b| ≤ η_n`
whenever `dist a b < δ_n`. -/
theorem exists_oscillation_scales_of_uniformContinuous {g : ℂ → ℝ} (hg : UniformContinuous g) :
    ∃ δ η : ℕ → ℝ, (∀ n, 0 < δ n) ∧ (∀ n a b, dist a b < δ n → |g a - g b| ≤ η n) ∧
      Tendsto η atTop (𝓝 0) := by
  have h : ∀ n : ℕ, ∃ δ > 0, ∀ a b : ℂ, dist a b < δ → dist (g a) (g b) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hg (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨δ, hδ, fun a b hab => hδg hab⟩
  choose δ hδ hδg using h
  refine ⟨δ, fun n => 1 / ((n : ℝ) + 1), hδ, fun n a b hab => ?_,
    tendsto_one_div_add_atTop_nhds_zero_nat⟩
  have := hδg n a b hab
  rw [Real.dist_eq] at this
  exact this.le

theorem chainPoint_mem_insert_left {Q : Set ℂ} (x y : ℂ) (m : ℕ) (w : Fin m → Q) {i : ℕ} (hi : i < m) :
    chainPoint x y m w i ∈ insert x Q := by
  unfold chainPoint
  split_ifs with h0
  · exact mem_insert x Q
  · exact mem_insert_of_mem x (w ⟨i, hi⟩).2

theorem chainPoint_mem_insert_right {Q : Set ℂ} (x y : ℂ) (m : ℕ) (w : Fin m → Q) {i : ℕ} (hi : 0 < i) :
    chainPoint x y m w i ∈ insert y Q := by
  unfold chainPoint
  split_ifs with h0 h1
  · exact absurd h0 hi.ne'
  · exact mem_insert_of_mem y (w ⟨i, h1⟩).2
  · exact mem_insert y Q

/-- For countable `Q`, the weighted chain infimum `C_δ(x, y)` of a random length metric `D_ω` is a.e.-measurable in
`ω` when the local internal metrics `D_ω(a, b; B(a, δ) ∩ U)` are, for `a ∈ {x} ∪ Q` and `b ∈ {y} ∪ Q`. -/
theorem aemeasurable_weightedChainInf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : Ω → ℂ → ℂ → ℝ)
    (g : ℂ → ℝ) (U : Set ℂ) {Q : Set ℂ} (hQ : Q.Countable) (δ : ℝ) (x y : ℂ)
    (hloc : ∀ a ∈ insert x Q, ∀ b ∈ insert y Q,
      AEMeasurable (fun ω => internalMetric (D ω) (Metric.ball a δ ∩ U) a b) μ) :
    AEMeasurable (fun ω => weightedChainInf (D ω) g U Q δ x y) μ := by
  have := hQ.to_subtype
  unfold weightedChainInf weightedChainSum
  refine AEMeasurable.iInf fun m => AEMeasurable.iInf fun w => ?_
  apply Finset.aemeasurable_fun_sum
  intro i hi
  have hi' : i < m + 1 := Finset.mem_range.mp hi
  exact (hloc _ (chainPoint_mem_insert_left x y (m + 1) w hi') _
    (chainPoint_mem_insert_right x y (m + 1) w (Nat.succ_pos i))).const_mul _

/-- The internal metric of a set `U` is infinite at points off `U`: if `x ∉ U`, no path in `U` starts at `x`, so
`D(x, y; U) = ∞`. -/
theorem internalMetric_eq_top_of_not_mem (D : ℂ → ℂ → ℝ) {U : Set ℂ} {x : ℂ} (hx : x ∉ U) (y : ℂ) :
    internalMetric D U x y = ⊤ := by
  unfold internalMetric
  refine iInf_eq_top.mpr fun P => iInf_eq_top.mpr fun hPU => absurd ?_ hx
  simpa using hPU 0

/-- Measurability of the internal metric of a Weyl scaling of a random length metric: if the internal metrics
`D_ω(a, b; B(a, r) ∩ U)` of the open set `U` are a.e.-measurable in `ω` for all `a, b ∈ ℂ` and `r > 0`, `f` is
continuous with `ξ f ≤ K` and `ξ f` uniformly continuous, and almost surely `D_ω` and `E_ω` are Euclidean length metrics
with `E_ω ≥ 0` and `E_ω = e^{ξ f} · D_ω`, then `ω ↦ E_ω(x, y; U)` is a.e.-measurable. -/
theorem aemeasurable_internalMetric_weylScaling {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D E : Ω → ℂ → ℂ → ℝ} {ξ K : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (hK : ∀ z, ξ * f z ≤ K)
    (hg : UniformContinuous fun z => ξ * f z) {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ (a b : ℂ) (r : ℝ), 0 < r →
      AEMeasurable (fun ω => internalMetric (D ω) (Metric.ball a r ∩ U) a b) μ)
    (hD : ∀ᵐ ω ∂μ, IsEuclideanLengthMetric (D ω)) (hE : ∀ᵐ ω ∂μ, IsEuclideanLengthMetric (E ω))
    (hE0 : ∀ᵐ ω ∂μ, ∀ x y, 0 ≤ E ω x y)
    (hscale : ∀ᵐ ω ∂μ, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (D ω) ξ f x y) (x y : ℂ) :
    AEMeasurable (fun ω => internalMetric (E ω) U x y) μ := by
  by_cases hx : x ∈ U
  swap
  · simp_rw [internalMetric_eq_top_of_not_mem _ hx y]
    exact aemeasurable_const
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  obtain ⟨δ, η, hδ, hη, hη0⟩ := exists_oscillation_scales_of_uniformContinuous hg
  have hmeas : AEMeasurable (fun ω => ⨅ n, ENNReal.ofReal (Real.exp (η n)) *
      weightedChainInf (D ω) (fun z => ξ * f z) U Q (δ n) x y) μ :=
    AEMeasurable.iInf fun n => (aemeasurable_weightedChainInf D _ U hQc (δ n) x y
      fun a _ b _ => hloc a b (δ n) (hδ n)).const_mul _
  refine hmeas.congr ?_
  filter_upwards [hD, hE, hE0, hscale] with ω hDω hEω hE0ω hsω
  exact (internalMetric_weylScaling_eq_iInf_weightedChainInf hDω hEω hE0ω hf hK hsω hU hQd hδ hη hη0 hx
    y).symm

end LatticeProb.LQG
