/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.CircleKernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.Plane
import LatticeProb.Bonanno.HigherDimLFPP.Field.LogCov
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-!
# Circle kernels of the κ-white-noise representation (packet P-X10, target T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2 (Lemma A.1, two-dimensional part);
planning audit HA5 (`planning/audits/HA5-inputs-appendixA-DGZ.md`), finding A2-1 and Details D12,
Claim 1; ruling H12.

In `d = 2` the circle average of the all-scale field `h` of (3.2) over `σ_{r,z} - σ_{1,0}`
(`σ_{r,z}` the uniform probability measure on the circle `∂B(z, r)`) is the white-noise pairing
with the kernel `k_η(t, y) = 1_{t > 0} ∫ K_t(u - y) η(du)`, `η = σ_{r,z} - σ_{1,0}`.  In the
measure-level notation of packet P-F2 this kernel is `bandFun κ (Ioi 0) σ_{r,z} -
bandFun κ (Ioi 0) σ_{1,0}`, and its `L²` class is `circVec κ r z = bandVecM κ (Ioi 0) σ_{r,z}
σ_{1,0}` (HA5's `circKerL2`; the representative is `coeFn_circVec`).

**Claim 1** (`circVec_spec`, `inner_circVec`): for `r, r' > 0` the kernel is square integrable
(`IsPairable`), and
`⟪k_η, k_η'⟫ = ∫∫ log|u - v|⁻¹ η(du) η'(dv) = LQGDimension.gffCircleCov r z r' z'`.

Proof: (3.2) for finite measures (`scaleCov_eq_logCov`, P-F2: Frullani for the profile of
`C = κ ⋆ κ`), applied to circle measures, which are atomless and have finite logarithmic energy
(`LQGDimension.Coupling.circMeas_singleton`, `integrable_log_circ_prod`); the logarithmic pairings
of circles are LQGMetric's `circCov` (`LQGMetric.CircleAvg.circCov_eq_lPair`), and the resulting
`incCov z r 0 1 z' r' 0 1` is `gffCircleCov r z r' z'`
(`LQGMetric.CircleAvg.gffCircleCov_eq_incCov`, Newton's theorem for circle averages of `log`).

The circles live in `ℂ` in the 2D libraries; `ℝ² = Rd 2` is identified with `ℂ` by the linear
isometry `cToR2 : ℂ ≃ₗᵢ[ℝ] Rd 2` of `TwoD/Plane.lean`, and `circMeasR z r` is the image of
`LQGDimension.Coupling.circMeas z r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

/-! ### Circle measures on `ℝ²` -/

/-- The uniform probability measure `σ_{r,z}` on the circle `∂B(z, r)`, as a measure on `ℝ²`
(image of `LQGDimension.Coupling.circMeas z r` under `cToR2`). -/
def circMeasR (z : ℂ) (r : ℝ) : Measure (Rd 2) := (LQGDimension.Coupling.circMeas z r).map cToR2

instance (z : ℂ) (r : ℝ) : IsProbabilityMeasure (circMeasR z r) := by
  unfold circMeasR
  infer_instance

theorem circMeasR_eq_map_equiv (z : ℂ) (r : ℝ) :
    circMeasR z r = (LQGDimension.Coupling.circMeas z r).map cToR2Meas := rfl

/-- Circle measures with nonzero radius have no atoms. -/
theorem nullSingletonClass_circMeasR (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    NullSingletonClass (circMeasR z r) := by
  refine ⟨fun x => ?_⟩
  rw [circMeasR, Measure.map_apply cToR2.continuous.measurable (measurableSet_singleton x)]
  have e : cToR2 ⁻¹' {x} = {cToR2.symm x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => by rw [← h, LinearIsometryEquiv.symm_apply_apply],
      fun h => by rw [h, LinearIsometryEquiv.apply_symm_apply]⟩
  rw [e]
  exact LQGDimension.Coupling.circMeas_singleton hr _

/-- Almost every point of `σ_{r,z}` lies on the circle `‖u - z‖ = |r|`. -/
theorem ae_circMeasR (z : ℂ) (r : ℝ) : ∀ᵐ u ∂circMeasR z r, ‖u - cToR2 z‖ = |r| := by
  rw [circMeasR_eq_map_equiv, cToR2Meas.measurableEmbedding.ae_map_iff]
  filter_upwards [LQGDimension.Coupling.ae_circMeas z r] with y hy
  rw [coe_cToR2Meas, norm_cToR2_sub, hy]

/-- Products of circle measures on `ℝ²` are images of products of circle measures on `ℂ`. -/
theorem circMeasR_prod (z w : ℂ) (r s : ℝ) :
    (circMeasR z r).prod (circMeasR w s) =
      ((LQGDimension.Coupling.circMeas z r).prod (LQGDimension.Coupling.circMeas w s)).map
        (cToR2Meas.prodCongr cToR2Meas) :=
  Measure.map_prod_map _ _ cToR2.continuous.measurable cToR2.continuous.measurable

/-- Integrals of functions of the distance against products of circle measures are the same in
`ℝ²` and in `ℂ`. -/
theorem integral_circMeasR_prod (g : ℝ → ℝ) (z w : ℂ) (r s : ℝ) :
    ∫ p, g ‖p.1 - p.2‖ ∂((circMeasR z r).prod (circMeasR w s)) =
      ∫ p, g ‖p.1 - p.2‖ ∂((LQGDimension.Coupling.circMeas z r).prod
        (LQGDimension.Coupling.circMeas w s)) := by
  rw [circMeasR_prod, integral_map_equiv]
  congr 1
  funext p
  show g ‖cToR2 p.1 - cToR2 p.2‖ = g ‖p.1 - p.2‖
  rw [norm_cToR2_sub]

/-- `log ‖u - v‖` is integrable for products of circle measures (second radius positive). -/
theorem integrable_log_circMeasR_prod (z w : ℂ) (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : Rd 2 × Rd 2 => Real.log ‖p.1 - p.2‖)
      ((circMeasR z r).prod (circMeasR w s)) := by
  rw [circMeasR_prod, integrable_map_equiv]
  refine (LQGDimension.Coupling.integrable_log_circ_prod z w r hs).congr
    (Filter.Eventually.of_forall fun p => ?_)
  show Real.log ‖p.1 - p.2‖ = Real.log ‖cToR2 p.1 - cToR2 p.2‖
  rw [norm_cToR2_sub]

/-- `∫∫ -log ‖u - v‖ dσ_{r,z}(u) dσ_{s,w}(v) = -lPair σ_{r,z} σ_{s,w}`. -/
theorem integral_neg_log_circMeasR_prod (z w : ℂ) (r s : ℝ) :
    ∫ p, -Real.log ‖p.1 - p.2‖ ∂((circMeasR z r).prod (circMeasR w s)) =
      -LQGDimension.Coupling.lPair (LQGDimension.Coupling.circMeas z r)
        (LQGDimension.Coupling.circMeas w s) := by
  rw [integral_circMeasR_prod (fun x => -Real.log x), integral_neg]
  rfl

/-! ### Logarithmic energy of sums of circle measures -/

section LogEnergy

/-- Right factors `β` for which `log ‖u - v‖` is integrable against every circle on the left. -/
private def GoodRight (β : Measure (Rd 2)) : Prop :=
  ∀ (z : ℂ) (r : ℝ), Integrable (fun p : Rd 2 × Rd 2 => Real.log ‖p.1 - p.2‖)
    ((circMeasR z r).prod β)

private theorem goodRight_circ (w : ℂ) {s : ℝ} (hs : 0 < s) : GoodRight (circMeasR w s) :=
  fun z r => integrable_log_circMeasR_prod z w r hs

private theorem GoodRight.add {β β' : Measure (Rd 2)} [SFinite β] [SFinite β'] (h : GoodRight β)
    (h' : GoodRight β') : GoodRight (β + β') := fun z r => by
  rw [Measure.prod_add]
  exact (h z r).add_measure (h' z r)

/-- `log ‖u - v‖` is integrable for `(σ₁ + σ₂ + σ₃ + σ₄) ⊗ (σ₁ + σ₂ + σ₃ + σ₄)` when the `σᵢ` are
circle measures of positive radii. -/
theorem integrable_log_four_circ (z₁ z₂ z₃ z₄ : ℂ) {r₁ r₂ r₃ r₄ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h₃ : 0 < r₃) (h₄ : 0 < r₄) :
    Integrable (fun p : Rd 2 × Rd 2 => Real.log ‖p.1 - p.2‖)
      ((circMeasR z₁ r₁ + circMeasR z₂ r₂ + circMeasR z₃ r₃ + circMeasR z₄ r₄).prod
        (circMeasR z₁ r₁ + circMeasR z₂ r₂ + circMeasR z₃ r₃ + circMeasR z₄ r₄)) := by
  set S := circMeasR z₁ r₁ + circMeasR z₂ r₂ + circMeasR z₃ r₃ + circMeasR z₄ r₄ with hS
  have hR : GoodRight S :=
    (((goodRight_circ z₁ h₁).add (goodRight_circ z₂ h₂)).add (goodRight_circ z₃ h₃)).add
      (goodRight_circ z₄ h₄)
  rw [hS, Measure.add_prod, Measure.add_prod, Measure.add_prod, ← hS]
  exact (((hR z₁ r₁).add_measure (hR z₂ r₂)).add_measure (hR z₃ r₃)).add_measure (hR z₄ r₄)

/-- Circle measures with positive radii are log-pairable (`LogPairable`, P-F2). -/
theorem logPairable_circ (z z' : ℂ) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    LogPairable (circMeasR z r) (circMeasR 0 1) (circMeasR z' r') (circMeasR 0 1) :=
  ⟨nullSingletonClass_circMeasR z hr.ne', nullSingletonClass_circMeasR 0 one_ne_zero,
    nullSingletonClass_circMeasR z' hr'.ne', nullSingletonClass_circMeasR 0 one_ne_zero,
    integrable_log_four_circ z 0 z' 0 hr one_pos hr' one_pos⟩

end LogEnergy

/-! ### The log covariance of circle averages -/

/-- **Newton's theorem for the normalized circle averages**:
`∫∫ log|u - v|⁻¹ (σ_{r,z} - σ_{1,0})(du) (σ_{r',z'} - σ_{1,0})(dv) = gffCircleCov r z r' z'`. -/
theorem logCov_circMeasR (z z' : ℂ) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    logCov (circMeasR z r) (circMeasR 0 1) (circMeasR z' r') (circMeasR 0 1) =
      LQGDimension.gffCircleCov r z r' z' := by
  rw [logCov, integral_neg_log_circMeasR_prod, integral_neg_log_circMeasR_prod,
    integral_neg_log_circMeasR_prod, integral_neg_log_circMeasR_prod,
    LQGMetric.CircleAvg.gffCircleCov_eq_incCov hr hr', LQGMetric.CircleAvg.incCov,
    LQGMetric.CircleAvg.circCov_eq_lPair z r z' hr',
    LQGMetric.CircleAvg.circCov_eq_lPair z r 0 one_pos,
    LQGMetric.CircleAvg.circCov_eq_lPair 0 1 z' hr',
    LQGMetric.CircleAvg.circCov_eq_lPair 0 1 0 one_pos]
  ring

/-! ### The circle kernel -/

/-- The white-noise vector of the normalized circle average `⟨h, σ_{r,z} - σ_{1,0}⟩` of the
all-scale field: the `L²` class of `k_η(t, y) = 1_{t > 0} ∫ K_t(u - y) η(du)`,
`η = σ_{r,z} - σ_{1,0}` (HA5's `circKerL2`). -/
def circVec (κ : Rd 2 → ℝ) (r : ℝ) (z : ℂ) : WN 2 :=
  bandVecM κ (Ioi 0) (circMeasR z r) (circMeasR 0 1)

variable {κ : Rd 2 → ℝ}

/-- **HA5 D12, Claim 1** (target T1): for `r, r' > 0`, the kernels `k_η`, `k_η'` are square
integrable, `⟪k_η, k_η'⟫ = ∫∫ log|u - v|⁻¹ η(du) η'(dv)` (`logCov`), and this is
`LQGDimension.gffCircleCov r z r' z'`. -/
theorem circVec_spec (hκ : IsLFPPKernel κ) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (z z' : ℂ) :
    IsPairable κ (Ioi 0) (circMeasR z r) (circMeasR 0 1) ∧
      IsPairable κ (Ioi 0) (circMeasR z' r') (circMeasR 0 1) ∧
      scaleCov κ (Ioi 0) (circMeasR z r) (circMeasR 0 1) (circMeasR z' r') (circMeasR 0 1) =
        logCov (circMeasR z r) (circMeasR 0 1) (circMeasR z' r') (circMeasR 0 1) ∧
      logCov (circMeasR z r) (circMeasR 0 1) (circMeasR z' r') (circMeasR 0 1) =
        LQGDimension.gffCircleCov r z r' z' := by
  have hmass : ∀ (w : ℂ) (s : ℝ), (circMeasR w s).real univ = (circMeasR 0 1).real univ :=
    fun w s => by rw [probReal_univ, probReal_univ]
  obtain ⟨h1, h2, h3⟩ := scaleCov_eq_logCov hκ (hmass z r) (hmass z' r')
    (logPairable_circ z z' hr hr')
  exact ⟨h1, h2, h3, logCov_circMeasR z z' hr hr'⟩

/-- The circle kernel is square integrable. -/
theorem isPairable_circ (hκ : IsLFPPKernel κ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsPairable κ (Ioi 0) (circMeasR z r) (circMeasR 0 1) :=
  (circVec_spec hκ hr hr z z).1

/-- **Covariance of the circle kernels** (target T1):
`⟪circVec κ r z, circVec κ r' z'⟫ = gffCircleCov r z r' z'` for `r, r' > 0`. -/
theorem inner_circVec (hκ : IsLFPPKernel κ) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (z z' : ℂ) :
    ⟪circVec κ r z, circVec κ r' z'⟫ = LQGDimension.gffCircleCov r z r' z' := by
  obtain ⟨-, -, h3, h4⟩ := circVec_spec hκ hr hr' z z'
  exact h3.trans h4

/-- `‖circVec κ r z‖² = gffCircleCov r z r z`. -/
theorem norm_circVec_sq (hκ : IsLFPPKernel κ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖circVec κ r z‖ ^ 2 = LQGDimension.gffCircleCov r z r z := by
  rw [← real_inner_self_eq_norm_sq, inner_circVec hκ hr hr]

/-- **Increments of the circle kernels**: `‖k_{r,z} - k_{r,w}‖² ≤ 2 ‖z - w‖ / r`
(`LQGDimension.Osc37.gffCircleCov_incr_le`). -/
theorem norm_circVec_sub_sq_le (hκ : IsLFPPKernel κ) {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    ‖circVec κ r z - circVec κ r w‖ ^ 2 ≤ 2 * ‖z - w‖ / r := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_circVec hκ hr hr, inner_circVec hκ hr hr, inner_circVec hκ hr hr]
  exact LQGDimension.Osc37.gffCircleCov_incr_le hr z w

end HigherDimLFPP
