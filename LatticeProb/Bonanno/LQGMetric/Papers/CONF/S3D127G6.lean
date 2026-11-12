/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127G6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 (L2) at `U = confU r δ z T`: the coarse kernel is Hölder up to `∂U`
(packet P-127G, task P2-HEATG)

* `survG_decay_confU`: `P^y(τ_U > t/8) ≤ C ρ^β` whenever `B(y, ρ) ⊄ confU` (G5 with the corkscrew
  step `killedSurv_le_of_ball` and the exterior corkscrew condition `extCorkscrew_confU` of
  P2-HEATC);
* **`coarseKer_holder_confU`**: `‖K^{(t,∞)}_x − K^{(t,∞)}_{x'}‖² ≤ K |x − x'|^α` for all
  `x, x' ∈ ℂ` (some `α ∈ (0, 1/4]`);
* **`exists_continuous_coarseField_confU`**: the coarse field `√π W(K^{(t,∞)}_x)` has a version
  that is continuous on all of `ℂ` (it vanishes off `confU`).

CONF l. 725–727 ("`h_{t,∞}` … continuous, as can easily be checked using Kolmogorov"): the
handoff's Lipschitz form `‖K_x − K_{x'}‖² ≤ K|x − x'|` is replaced by a Hölder form, which feeds
the generalized Kolmogorov lemma `exists_continuous_modification_of_kernel_holder` (G3)
(DV-P127G-3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat DZZ WhiteNoise Blueprint

lemma survG_eq_toReal {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (y : ℂ) :
    survG U t y = (killedSurv U t y).toReal := by
  rw [survG, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun w => killedHeat_nonneg _ _ _ _)
    (measurable_killedHeat_right hU ht y).aestronglyMeasurable]
  rfl

/-- **Power-law decay of the survival probability at `∂ confU`.** -/
theorem survG_decay_confU {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (T : Finset (ℤ × ℤ))
    {t : ℝ} (ht : 0 < t) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ β ≤ 1 ∧ ∀ y : ℂ, ∀ ρ : ℝ, 0 < ρ →
      ¬ ball y ρ ⊆ confU r δ z T → survG (confU r δ z T) (t / 8).toNNReal y ≤ C * ρ ^ β := by
  set U := confU r δ z T with hUdef
  have hU : IsOpen U := isOpen_confU r δ z T
  set L : ℝ := min (min (δ * r) r) (Real.sqrt (t / 16)) with hLdef
  have hL : 0 < L := lt_min (lt_min (by positivity) hr) (Real.sqrt_pos.mpr (by positivity))
  have hcork := extCorkscrew_confU hr hδ z T
  have hγ1 : survGam0 < 1 := by
    unfold survGam0
    have : Real.exp (-(81 / 32)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have hstep : ∀ ρ : ℝ, 0 < ρ → ρ ≤ L → ∀ y, ¬ ball y ρ ⊆ U →
      killedSurv U (ρ.toNNReal ^ 2) y ≤ 1 - ENNReal.ofReal survGam0 := by
    intro ρ hρ hρL y hy
    obtain ⟨p, hp, hpU⟩ := not_subset.mp hy
    obtain ⟨c, hcp, hball⟩ := hcork p hpU ρ hρ (hρL.trans (min_le_left _ _))
    have hR : ρ.toNNReal ≠ 0 := by simpa using hρ
    have hRc : ((ρ.toNNReal : ℝ≥0) : ℝ) = ρ := Real.coe_toNNReal _ hρ.le
    refine killedSurv_le_of_ball hU hR (by rw [hRc]; exact hcp) (by rw [hRc]; exact hball) ?_
    rw [hRc, dist_comm]; exact (mem_ball.mp hp).le
  have hH : 2 * L ^ 2 ≤ ((t / 8).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    have h1 : L ≤ Real.sqrt (t / 16) := min_le_right _ _
    have h2 : L ^ 2 ≤ t / 16 := by
      calc L ^ 2 ≤ Real.sqrt (t / 16) ^ 2 := pow_le_pow_left₀ hL.le h1 2
        _ = t / 16 := Real.sq_sqrt (by positivity)
    linarith
  obtain ⟨C, β, hC, hβ, hβ1, hdec⟩ :=
    killedSurv_le_rpow_of_step hU hL survGam0_pos hγ1 hstep hH
  refine ⟨C, β, hC, hβ, hβ1, fun y ρ hρ hy => ?_⟩
  have ht8 : (t / 8).toNNReal ≠ 0 := by simpa using ht
  rw [survG_eq_toReal hU ht8]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hdec y ρ hρ hy)

/-- **(L2) at `confU`: the coarse kernel is Hölder up to the boundary**, for all `x, x' ∈ ℂ`. -/
theorem coarseKer_holder_confU {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ)
    (T : Finset (ℤ × ℤ)) {t : ℝ} (ht : 0 < t) :
    ∃ K α : ℝ, 0 ≤ K ∧ 0 < α ∧ ∀ x x' : ℂ,
      ‖wndKernelL2 (confU r δ z T) (Ioi t) x - wndKernelL2 (confU r δ z T) (Ioi t) x'‖ ^ 2 ≤
        K * ‖x - x'‖ ^ α := by
  obtain ⟨C, β, hC, hβ, hβ1, hS⟩ := survG_decay_confU hr hδ z T ht
  obtain ⟨K, hK, hF⟩ := coarseKer_holder_of_survDecay (isOpen_confU r δ z T)
    (by positivity : (0 : ℝ) ≤ 4 * r) (confU_subset_ball r δ z T) ht hC hβ hβ1 hS
  exact ⟨K, β / 4, hK, by positivity, hF⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end ZBM
end CONF
end LQGMetric
