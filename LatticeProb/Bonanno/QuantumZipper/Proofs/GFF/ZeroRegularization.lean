/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.ZeroRegularization at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegPotential
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible

/-!
# Regularization of the zero-boundary GFF on `ℍ` (task RG-0)

Zero-boundary ports of REG-A/B/C, for `X` with `IsZeroBoundaryGFFH X P`:

* **REG-A** (`exists_continuous_circleAvg_zero`): the folded-circle averages
  `z ↦ X(foldedCircle z 2^{-k})` have a modification continuous on `Hbar`, and a.s.
  `avgReg (X ω) k z` equals it at every `z ∈ Hbar`. The increment variance bound
  `Var(X(c z) − X(c w)) ≤ 8‖z − w‖/r` comes from the Lipschitz bound on folded-circle
  potentials of `greenH` (`ZeroRegPotential`).
* **REG-B** (`integral_avgReg_ae_eq_bind_zero`): stochastic Fubini
  `∫ avgReg (X ω) k dν = X ω (ν.bind (foldedCircle · 2^{-k}))` a.s., for finite `ν` carried by a
  compact subset of `Hbar`.
* **REG-C** (`integral_sq_smoothed_sub_le_zero`, `ae_tendsto_smoothed_zero`,
  `evalReg_ae_eq_zero`): for a bounded-density `ν` with bounded support at height `> δ`,
  `E(X νk − X ν)² ≤ 4π M ν(ℂ) 4^{-k}` once `2^{-k} ≤ δ`, hence `X νk → X ν` and
  `evalReg (X ω) ν = X ω ν` almost surely.

The kernel-generic refactor suggested by the blueprint was not done: the proofs are direct ports.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate

namespace QuantumZipper
namespace ZeroReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Second moments of the zero-boundary GFF -/

theorem zero_mem_Hbar_zr : (0 : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (0 : ℂ).im
  simp

theorem isProbabilityMeasure_of_zeroGFF (hX : IsZeroBoundaryGFFH X P) : IsProbabilityMeasure P :=
  (hX.gaussian.hasGaussianLaw_eval
    ⟨foldedCircle 0 1, isAdmissibleH_foldedCircle zero_mem_Hbar_zr one_pos⟩).isProbabilityMeasure

theorem zg_memLp (hX : IsZeroBoundaryGFFH X P) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    MemLp (fun ω => X ω μ) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval ⟨μ, hμ⟩).memLp_two

theorem zg_integral_mul (hX : IsZeroBoundaryGFFH X P) {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) : ∫ ω, X ω μ * X ω ν ∂P = kernelCov greenH μ ν := by
  have := isProbabilityMeasure_of_zeroGFF hX
  have h := hX.covariance_eq μ ν hμ hν
  rw [covariance_eq_sub (zg_memLp hX hμ) (zg_memLp hX hν), hX.centered μ hμ,
    hX.centered ν hν] at h
  simpa using h

theorem kernelCov_greenH_symm {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    kernelCov greenH μ ν = kernelCov greenH ν μ := by
  have := hμ.1
  have := hν.1
  unfold kernelCov
  rw [integral_integral_swap (f := fun x y => greenH x y) (integrable_greenH_prod hμ hν)]
  congr 1; funext y; congr 1; funext x; exact greenH_symm x y

/-! ## REG-A: continuity of circle averages -/

theorem ae_mem_Hbar_foldedCircle_zr (z : ℂ) (r : ℝ) : ∀ᵐ x ∂foldedCircle z r, x ∈ Hbar := by
  rw [foldedCircle]
  exact (ae_map_iff measurable_foldH.aemeasurable isClosed_Hbar.measurableSet).2
    (ae_of_all _ CircleFubini.foldH_mem_Hbar')

theorem integrable_pot_zr {a b : ℂ} (ha : a ∈ Hbar) (hb : b ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => ∫ y, greenH x y ∂foldedCircle a r) (foldedCircle b r) :=
  (integrable_greenH_prod (isAdmissibleH_foldedCircle hb hr)
    (isAdmissibleH_foldedCircle ha hr)).integral_prod_left

theorem abs_kernelCov_circle_sub_right_le {b z w : ℂ} (hb : b ∈ Hbar) (hz : z ∈ Hbar)
    (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    |kernelCov greenH (foldedCircle b r) (foldedCircle z r) -
      kernelCov greenH (foldedCircle b r) (foldedCircle w r)| ≤ 4 * ‖z - w‖ / r := by
  unfold kernelCov
  rw [← integral_sub (integrable_pot_zr hz hb hr) (integrable_pot_zr hw hb hr)]
  have hbd : ∀ᵐ x ∂foldedCircle b r, ‖(∫ y, greenH x y ∂foldedCircle z r) -
      ∫ y, greenH x y ∂foldedCircle w r‖ ≤ 4 * ‖z - w‖ / r :=
    (ae_mem_Hbar_foldedCircle_zr b r).mono fun x hx => by
      rw [Real.norm_eq_abs]; exact abs_integral_greenH_foldedCircle_sub_le hx z w hr
  have := norm_integral_le_of_norm_le_const hbd
  simpa [Real.norm_eq_abs] using this

theorem abs_kernelCov_circle_self_sub_le {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar) {r : ℝ}
    (hr : 0 < r) :
    |kernelCov greenH (foldedCircle z r) (foldedCircle z r) -
      kernelCov greenH (foldedCircle w r) (foldedCircle w r)| ≤ 8 * ‖z - w‖ / r := by
  have h1 := abs_le.1 (abs_kernelCov_circle_sub_right_le hz hz hw hr)
  have h2 := abs_kernelCov_circle_sub_right_le hw hz hw hr
  rw [kernelCov_greenH_symm (isAdmissibleH_foldedCircle hw hr)
    (isAdmissibleH_foldedCircle hz hr)] at h2
  have h2 := abs_le.1 h2
  have e : 8 * ‖z - w‖ / r = 4 * ‖z - w‖ / r + 4 * ‖z - w‖ / r := by ring
  rw [abs_le, e]; constructor <;> linarith

theorem kernelCov_circle_diff_le {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar) {r : ℝ}
    (hr : 0 < r) :
    kernelCov greenH (foldedCircle z r) (foldedCircle z r) -
      kernelCov greenH (foldedCircle z r) (foldedCircle w r) -
      kernelCov greenH (foldedCircle w r) (foldedCircle z r) +
      kernelCov greenH (foldedCircle w r) (foldedCircle w r) ≤ 8 * ‖z - w‖ / r := by
  have h1 := abs_le.1 (abs_kernelCov_circle_sub_right_le hz hz hw hr)
  have h2 := abs_le.1 (abs_kernelCov_circle_sub_right_le hw hz hw hr)
  have e : 8 * ‖z - w‖ / r = 4 * ‖z - w‖ / r + 4 * ‖z - w‖ / r := by ring
  rw [e]; linarith

/-- The increment of folded-circle averages of the zero-boundary GFF is a centered Gaussian. -/
theorem map_circleDiff_eq_gaussianReal_zero (hX : IsZeroBoundaryGFFH X P) {r : ℝ} (hr : 0 < r)
    {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar) :
    P.map (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) =
      gaussianReal 0 (kernelCov greenH (foldedCircle z r) (foldedCircle z r) -
        kernelCov greenH (foldedCircle z r) (foldedCircle w r) -
        kernelCov greenH (foldedCircle w r) (foldedCircle z r) +
        kernelCov greenH (foldedCircle w r) (foldedCircle w r)).toNNReal := by
  have := isProbabilityMeasure_of_zeroGFF hX
  have hadz := isAdmissibleH_foldedCircle hz hr
  have hadw := isAdmissibleH_foldedCircle hw hr
  have hG : HasGaussianLaw (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) P :=
    hX.gaussian.hasGaussianLaw_fun_sub (s := ⟨_, hadz⟩) (t := ⟨_, hadw⟩)
  have hm : AEMeasurable (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hA := zg_memLp hX hadz
  have hB := zg_memLp hX hadw
  have hc : P[fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)] = 0 := by
    show ∫ ω, (X ω (foldedCircle z r) - X ω (foldedCircle w r)) ∂P = 0
    rw [integral_sub (hA.integrable one_le_two) (hB.integrable one_le_two), hX.centered _ hadz,
      hX.centered _ hadw, sub_zero]
  have hcov : cov[fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r),
      fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r); P] =
      kernelCov greenH (foldedCircle z r) (foldedCircle z r) -
        kernelCov greenH (foldedCircle z r) (foldedCircle w r) -
        kernelCov greenH (foldedCircle w r) (foldedCircle z r) +
        kernelCov greenH (foldedCircle w r) (foldedCircle w r) := by
    rw [covariance_fun_sub_fun_sub hA hB hA hB, hX.covariance_eq _ _ hadz hadz,
      hX.covariance_eq _ _ hadz hadw, hX.covariance_eq _ _ hadw hadz,
      hX.covariance_eq _ _ hadw hadw]
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- **Eighth-moment Kolmogorov bound** for folded-circle averages of the zero-boundary GFF. -/
theorem momentBound_circle_zero (hX : IsZeroBoundaryGFFH X P) {r : ℝ} (hr : 0 < r) :
    CircleCont.MomentBound (fun z ω => X ω (foldedCircle z r)) P
      ((8 / r) ^ 4 * gaussianAbsMoment 8) := by
  intro z hz w hw
  beta_reduce
  rw [CircleCont.lintegral_pow8_of_map_eq
    (U := fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r))
    ((hX.measurable_coord _).sub (hX.measurable_coord _))
    (map_circleDiff_eq_gaussianReal_zero hX hr hz hw)]
  apply ENNReal.ofReal_le_ofReal
  have hkb := kernelCov_circle_diff_le hz hw hr
  rw [mul_div_right_comm] at hkb
  have hnn : 0 ≤ 8 / r * ‖z - w‖ :=
    mul_nonneg (div_nonneg (by norm_num) hr.le) (norm_nonneg _)
  have hv : ((kernelCov greenH (foldedCircle z r) (foldedCircle z r) -
      kernelCov greenH (foldedCircle z r) (foldedCircle w r) -
      kernelCov greenH (foldedCircle w r) (foldedCircle z r) +
      kernelCov greenH (foldedCircle w r) (foldedCircle w r)).toNNReal : ℝ) ≤
      8 / r * ‖z - w‖ := by
    rw [Real.coe_toNNReal']; exact max_le hkb hnn
  have h4 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 4
  calc _ ≤ (8 / r * ‖z - w‖) ^ 4 * gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right h4 (gaussianAbsMoment_nonneg 8)
    _ = (8 / r) ^ 4 * gaussianAbsMoment 8 * ‖z - w‖ ^ 4 := by ring

/-- **REG-A for the zero-boundary GFF.** At radius `radius k`, the folded-circle averages
`z ↦ X(foldedCircle z)` have a modification `Y` continuous on `Hbar` for every `ω`, and almost
surely `avgReg (X ω) k z = Y z ω` at every point of `Hbar`. -/
theorem exists_continuous_circleAvg_zero (hX : IsZeroBoundaryGFFH X P) (k : ℕ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun z => Y z ω) Hbar) ∧
      (∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] fun ω => X ω (foldedCircle z (radius k))) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ Hbar, avgReg (X ω) k z = Y z ω) := by
  have hr := radius_pos k
  obtain ⟨Y, hc, hae, hlim⟩ := CircleCont.exists_continuous_modification
    (Z := fun z ω => X ω (foldedCircle z (radius k)))
    (fun z => (hX.measurable_coord _).aemeasurable)
    (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hr.le) 4) (gaussianAbsMoment_nonneg 8))
    (momentBound_circle_zero hX hr)
  refine ⟨Y, hc, hae, ?_⟩
  filter_upwards [hlim] with ω hω z hz
  unfold avgReg
  exact (hω z hz).limUnder_eq

/-- Almost surely, `z ↦ avgReg (X ω) k z` is continuous on `Hbar`. -/
theorem ae_continuousOn_avgReg_zero (hX : IsZeroBoundaryGFFH X P) (k : ℕ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun z => avgReg (X ω) k z) Hbar := by
  obtain ⟨Y, hc, -, hlim⟩ := exists_continuous_circleAvg_zero hX k
  filter_upwards [hlim] with ω hω
  exact (hc ω).congr fun z hz => hω z hz

/-! ## REG-B: stochastic Fubini -/

/-- **Stochastic Fubini for folded-circle averages of the zero-boundary GFF**, for any version
`Y` continuous in the centre. -/
theorem integral_circleAvg_ae_eq_bind_zero (hX : IsZeroBoundaryGFFH X P) (k : ℕ)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] fun ω => X ω (foldedCircle z (radius k)))
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, Y z ω ∂ν) =ᵐ[P]
      fun ω => X ω (ν.bind fun w => foldedCircle w (radius k)) := by
  have := isProbabilityMeasure_of_zeroGFF hX
  set r := radius k with hr_def
  have hr : 0 < r := radius_pos k
  set νk := ν.bind fun w => foldedCircle w r with hνk_def
  have : IsFiniteMeasure νk := CircleFubini.isFiniteMeasure_bind_circle ν
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR₀ hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set Cc : ℝ≥0∞ := 2 * ENNReal.ofReal (CircleFubini.potConst r) with hCc_def
  have hCct : Cc ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hcP : ∀ z y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle z r ≤ Cc :=
    fun z y => CircleFubini.foldedCircle_pot_le hr z y
  have hmCt : ν Set.univ * Cc ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) hCct
  have hkS : νk (CircleFubini.ballH (R₀ + r))ᶜ = 0 :=
    CircleFubini.bind_circle_support ν hr.le hνK hKR (le_refl _)
  have hkA : IsAdmissibleH νk :=
    CircleFubini.admissible_of_bounds hkS hmCt (CircleFubini.bind_circle_pot ν hcP)
  have hcA : ∀ z ∈ Hbar, IsAdmissibleH (foldedCircle z r) := fun z hz =>
    isAdmissibleH_foldedCircle hz hr
  set W : ℂ → Ω → ℝ := fun z ω => X ω (foldedCircle z r) with hW_def
  set D : Ω → ℝ := fun ω => X ω νk with hD_def
  have hWm : ∀ z, Measurable (W z) := fun z => hX.measurable_coord _
  have hDm : Measurable D := hX.measurable_coord _
  have hWL2 : ∀ z ∈ Hbar, MemLp (W z) 2 P := fun z hz => zg_memLp hX (hcA z hz)
  have hDL2 : MemLp D 2 P := zg_memLp hX hkA
  obtain ⟨Z, hZm, hZc, hZY, hZW⟩ := CircleFubini.exists_measurable_version hYc hWm hY
  have hZL2 : ∀ z ∈ K, MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z (hKH hz)).ae_eq (hZW z (hKH hz)).symm
  -- the uniform variance bound
  set b := kernelCov greenH (foldedCircle 0 r) (foldedCircle 0 r) + 8 * R₀ / r with hb_def
  have hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ b := by
    intro z hz
    have e1 : ∫ ω, Z z ω ^ 2 ∂P = kernelCov greenH (foldedCircle z r) (foldedCircle z r) := by
      rw [← zg_integral_mul hX (hcA z (hKH hz)) (hcA z (hKH hz))]
      refine integral_congr_ae ?_
      filter_upwards [hZW z (hKH hz)] with ω hω
      rw [hω, sq]
    rw [e1]
    have h1 := abs_le.1 (abs_kernelCov_circle_self_sub_le (hKH hz) zero_mem_Hbar_zr hr)
    have h2 : 8 * ‖z - 0‖ / r ≤ 8 * R₀ / r := by
      rw [sub_zero]; gcongr; exact hKR z hz
    linarith [h1.2]
  have hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P := fun z hz =>
    (hZL2 z hz).integrable_sq
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  -- linearity of the covariance under `bind`
  have hlin : ∀ a : Measure ℂ, IsAdmissibleH a →
      ∫ w, kernelCov greenH (foldedCircle w r) a ∂ν = kernelCov greenH νk a := by
    intro a ha
    have := ha.1
    have hint : Integrable (fun x => ∫ y, greenH x y ∂a) νk :=
      (integrable_greenH_prod hkA ha).integral_prod_left
    exact (CircleFubini.integral_bind_circle ν hint).2.symm
  obtain ⟨hLm, hLL2⟩ := CircleFubini.memLp_integral (B := b) hZm hνK hK hZc hmom hB
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂ν with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z ∈ K, ∫ ω, Z z ω * D ω ∂P = kernelCov greenH (foldedCircle z r) νk := by
    intro z hz
    rw [← zg_integral_mul hX (hcA z (hKH hz)) hkA]
    refine integral_congr_ae ?_
    filter_upwards [hZW z (hKH hz)] with ω hω
    rw [hω]
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov greenH νk νk := zg_integral_mul hX hkA hkA
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov greenH νk νk := by
    rw [CircleFubini.fubini_mul hZm hνK hmom hB hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂ν
        = ∫ z, kernelCov greenH (foldedCircle z r) νk ∂ν :=
          integral_congr_ae (hae.mono fun z hz => hZD z hz)
      _ = _ := hlin νk hkA
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [CircleFubini.fubini_mul hZm hνK hmom hB hLm hLL2,
      CircleFubini.fubini_mul hZm hνK hmom hB hDm hDL2]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, CircleFubini.fubini_mul hZm hνK hmom hB (hZmz z) (hZL2 z hz)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂ν
        = ∫ z', kernelCov greenH (foldedCircle z' r) (foldedCircle z r) ∂ν := by
          refine integral_congr_ae (hae.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P =
            kernelCov greenH (foldedCircle z' r) (foldedCircle z r)
          rw [← zg_integral_mul hX (hcA z' (hKH hz')) (hcA z (hKH hz))]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz), hZW z' (hKH hz')] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov greenH νk (foldedCircle z r) := hlin _ (hcA z (hKH hz))
      _ = ∫ ω, Z z ω * D ω ∂P := by
          rw [← zg_integral_mul hX hkA (hcA z (hKH hz))]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz)] with ω hω
          rw [hω, mul_comm]
  -- conclusion: `E[(L - D)²] = 0`
  have hsq : ∫ ω, (L ω - D ω) ^ 2 ∂P = 0 := by
    have : ∀ ω, (L ω - D ω) ^ 2 = (L ω * L ω - 2 * (L ω * D ω)) + D ω * D ω := fun ω => by
      ring
    simp_rw [this]
    have iLL := CircleFubini.integrable_mul_of_memLp_two hLL2 hLL2
    have iLD := CircleFubini.integrable_mul_of_memLp_two hLL2 hDL2
    have iDD := CircleFubini.integrable_mul_of_memLp_two hDL2 hDL2
    rw [integral_add (f := fun ω => L ω * L ω - 2 * (L ω * D ω)) (g := fun ω => D ω * D ω)
        (iLL.sub (iLD.const_mul 2)) iDD,
      integral_sub (f := fun ω => L ω * L ω) (g := fun ω => 2 * (L ω * D ω)) iLL
        (iLD.const_mul 2),
      integral_const_mul, E2, E1, hEDD]
    ring
  have hint : Integrable (fun ω => (L ω - D ω) ^ 2) P := (hLL2.sub hDL2).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (L ω - D ω)) hint).1 hsq
  filter_upwards [h0, hZY] with ω hω hωY
  have hLD : L ω = D ω := by
    have h2 : (L ω - D ω) ^ 2 = 0 := hω
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
    linarith
  show ∫ z, Y z ω ∂ν = D ω
  rw [← hLD]
  exact integral_congr_ae (hae.mono fun z hz => (hωY z (hKH hz)).symm)

/-- **REG-B for the zero-boundary GFF**: for a finite measure `ν` carried by a compact subset
of `Hbar`, `∫ avgReg (X ω) k dν = X ω (ν.bind (foldedCircle · 2^{-k}))` almost surely. -/
theorem integral_avgReg_ae_eq_bind_zero (hX : IsZeroBoundaryGFFH X P) (k : ℕ)
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, avgReg (X ω) k z ∂ν) =ᵐ[P]
      fun ω => X ω (ν.bind fun w => foldedCircle w (radius k)) := by
  obtain ⟨Y, hYc, hY, hlim⟩ := exists_continuous_circleAvg_zero hX k
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  filter_upwards [integral_circleAvg_ae_eq_bind_zero hX k hYc hY ν hK hKH hνK, hlim]
    with ω h1 h2
  rw [← h1]
  exact integral_congr_ae (hae.mono fun z hz => h2 z (hKH hz))

/-! ## REG-C: interior convergence with rate -/

end ZeroReg
end QuantumZipper
