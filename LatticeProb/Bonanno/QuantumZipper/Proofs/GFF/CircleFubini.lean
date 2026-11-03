/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CircleFubini at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: use MemLp.aestronglyMeasurable in place of conjunction projections.
   v4.35 port: silence unused-section-variable and unused-variable linters. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Stochastic Fubini for folded-circle averages (task REG-B)

For a free-boundary GFF modulo constants `X`, a continuous version `Y z` of the circle-average
increments `X (c z) - X (c z₀)` (`c z = foldedCircle z (radius k)`), and a finite measure `ν`
supported in a compact `K ⊆ Hbar`, we show
`∫ Y z dν = X (ν.bind c) - X ((ν ℂ) • c z₀)` almost surely.

The proof shows `E[(L - D)²] = 0` by a Fubini argument in `(z, ω)` and bilinearity of the
kernel covariance under `Measure.bind`. Circle measures are admissible uniformly in the centre
(a uniform bound on their logarithmic potentials, from the mean-value formula
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper

namespace CircleFubini

/-! ## Folding -/

theorem foldH_eq_mk (w : ℂ) : foldH w = (w.re : ℂ) + ((|w.im| : ℝ) : ℂ) * Complex.I := by
  unfold foldH
  split_ifs with h
  · apply Complex.ext <;> simp [abs_of_nonneg h]
  · apply Complex.ext <;> simp [abs_of_neg (not_le.mp h)]

theorem continuous_foldH' : Continuous foldH := by
  have : foldH = fun w : ℂ => (w.re : ℂ) + ((|w.im| : ℝ) : ℂ) * Complex.I := funext foldH_eq_mk
  rw [this]; fun_prop

theorem foldH_mem_Hbar' (w : ℂ) : foldH w ∈ Hbar := by
  show 0 ≤ (foldH w).im
  rw [foldH_eq_mk]; simp

theorem foldH_of_mem' {w : ℂ} (hw : w ∈ Hbar) : foldH w = w := by
  unfold foldH; simp [show 0 ≤ w.im from hw]

theorem norm_foldH' (w : ℂ) : ‖foldH w‖ = ‖w‖ := by
  unfold foldH; split_ifs <;> simp

/-! ## The circle kernel -/

theorem measurable_foldedCircle' (r : ℝ) : Measurable (fun z : ℂ => foldedCircle z r) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hcont : Continuous (fun p : ℂ × ℝ => circleMap p.1 r p.2) := by
    unfold circleMap; fun_prop
  have hg : Measurable (fun p : ℂ × ℝ => foldH (circleMap p.1 r p.2)) :=
    measurable_foldH.comp hcont.measurable
  have h := (measurable_measure_prodMk_left (ν := volume.restrict (Set.Ico 0 (2 * π))) (hg hs))
  convert h.const_mul ((ENNReal.ofReal (2 * π))⁻¹) using 1
  funext z
  rw [foldedCircle, Measure.map_apply measurable_foldH hs, circleUnif, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap z r) (measurable_foldH hs), smul_eq_mul]
  rfl

/-- The folded-circle kernel `z ↦ foldedCircle z r`. -/
def circleKernel (r : ℝ) : Kernel ℂ ℂ where
  toFun z := foldedCircle z r
  measurable' := measurable_foldedCircle' r

instance (r : ℝ) : IsMarkovKernel (circleKernel r) :=
  ⟨fun z => by show IsProbabilityMeasure (foldedCircle z r); infer_instance⟩

theorem circleKernel_apply (r : ℝ) (z : ℂ) : circleKernel r z = foldedCircle z r := rfl

/-! ## Uniform logarithmic potential bound for circles -/

/-- The constant of the uniform potential bound for circles of radius `r`. -/
def potConst (r : ℝ) : ℝ := Real.log 2 + 2 * Real.posLog r - Real.log r

theorem measurable_logPot (y : ℂ) :
    Measurable fun x : ℂ => ENNReal.ofReal (-Real.log ‖x - y‖) :=
  ((Real.measurable_log.comp (measurable_id.sub_const y).norm).neg).ennreal_ofReal

theorem circleUnif_pot_le {r : ℝ} (hr : 0 < r) (z y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif z r) ≤ ENNReal.ofReal (potConst r) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [circleUnif, lintegral_smul_measure, lintegral_map (measurable_logPot y)
    (measurable_circleMap z r), smul_eq_mul]
  set g : ℝ → ℝ := fun θ => Real.posLog ‖circleMap z r θ - y‖ - Real.log ‖circleMap z r θ - y‖
    with hg_def
  have hle : ∀ θ, ENNReal.ofReal (-Real.log ‖circleMap z r θ - y‖) ≤ ENNReal.ofReal (g θ) :=
    fun θ => ENNReal.ofReal_le_ofReal (by
      simp only [hg_def]; linarith [Real.posLog_nonneg (x := ‖circleMap z r θ - y‖)])
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => by
    simp only [hg_def]
    have := Real.posLog_sub_posLog_inv (x := ‖circleMap z r θ - y‖)
    linarith [Real.posLog_nonneg (x := ‖circleMap z r θ - y‖⁻¹)]
  have hlogint : IntervalIntegrable (fun θ => Real.log ‖circleMap z r θ - y‖) volume 0 (2 * π) :=
    (circleIntegrable_log_norm_sub_const (a := y) (c := z) r)
  have hposint : IntervalIntegrable (fun θ => Real.posLog ‖circleMap z r θ - y‖) volume 0
      (2 * π) := by
    apply Continuous.intervalIntegrable
    have : Continuous (circleMap z r) := continuous_circleMap z r
    fun_prop
  have hint : IntervalIntegrable g volume 0 (2 * π) := hposint.sub hlogint
  -- the value of the log integral
  have hlog : ∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap z r θ - y‖
      = 2 * π * (Real.log r + Real.posLog (r⁻¹ * ‖z - y‖)) := by
    rw [← circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne', Real.circleAverage_def,
      smul_eq_mul]
    field_simp
  -- the bound on the posLog integral
  have hpos : ∫ θ in (0 : ℝ)..2 * π, Real.posLog ‖circleMap z r θ - y‖
      ≤ 2 * π * Real.posLog (‖z - y‖ + r) := by
    have := intervalIntegral.integral_mono_on h2π.le hposint
      (intervalIntegrable_const (c := Real.posLog (‖z - y‖ + r))) (fun θ _ => by
        apply Real.posLog_le_posLog (by linarith [norm_nonneg (circleMap z r θ - y)])
        calc ‖circleMap z r θ - y‖ = ‖(circleMap z r θ - z) + (z - y)‖ := by ring_nf
          _ ≤ ‖circleMap z r θ - z‖ + ‖z - y‖ := norm_add_le _ _
          _ = ‖z - y‖ + r := by
            rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]; ring)
    simpa using this
  have hkey : Real.posLog (‖z - y‖ + r) - (Real.log r + Real.posLog (r⁻¹ * ‖z - y‖))
      ≤ potConst r := by
    have h1 := Real.posLog_add (x := ‖z - y‖) (y := r)
    have h2 := Real.posLog_mul (x := r) (y := r⁻¹ * ‖z - y‖)
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at h2
    unfold potConst; linarith
  have hgint : ∫ θ in (0 : ℝ)..2 * π, g θ ≤ 2 * π * potConst r := by
    rw [hg_def, intervalIntegral.integral_sub hposint hlogint, hlog]
    nlinarith [hkey, hpos]
  calc (ENNReal.ofReal (2 * π))⁻¹ *
        ∫⁻ θ in Set.Ico 0 (2 * π), ENNReal.ofReal (-Real.log ‖circleMap z r θ - y‖)
      ≤ (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ θ in Set.Ico 0 (2 * π), ENNReal.ofReal (g θ) := by
        exact mul_le_mul' le_rfl (lintegral_mono hle)
    _ = (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, g θ) := by
        rw [Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc, intervalIntegral.integral_of_le h2π.le,
          ofReal_integral_eq_lintegral_ofReal hint.1 (ae_of_all _ hg0)]
    _ ≤ (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (2 * π * potConst r) := by
        gcongr
    _ = ENNReal.ofReal (potConst r) := by
        rw [ENNReal.ofReal_mul h2π.le, ← mul_assoc,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr h2π).ne' ENNReal.ofReal_ne_top, one_mul]

theorem foldedCircle_pot_le {r : ℝ} (hr : 0 < r) (z y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(foldedCircle z r)
      ≤ 2 * ENNReal.ofReal (potConst r) := by
  rw [foldedCircle, lintegral_map (measurable_logPot y) measurable_foldH]
  calc ∫⁻ w, ENNReal.ofReal (-Real.log ‖foldH w - y‖) ∂circleUnif z r
      ≤ ∫⁻ w, (ENNReal.ofReal (-Real.log ‖w - y‖) + ENNReal.ofReal (-Real.log ‖w - conj y‖))
          ∂circleUnif z r := by
        refine lintegral_mono fun w => ?_
        unfold foldH
        split_ifs
        · exact le_self_add
        · have : conj w - y = conj (w - conj y) := by simp
          rw [this, Complex.norm_conj]; exact le_add_self
    _ = ∫⁻ w, ENNReal.ofReal (-Real.log ‖w - y‖) ∂circleUnif z r
          + ∫⁻ w, ENNReal.ofReal (-Real.log ‖w - conj y‖) ∂circleUnif z r :=
        lintegral_add_left (measurable_logPot y) _
    _ ≤ ENNReal.ofReal (potConst r) + ENNReal.ofReal (potConst r) :=
        add_le_add (circleUnif_pot_le hr z y) (circleUnif_pot_le hr z (conj y))
    _ = 2 * ENNReal.ofReal (potConst r) := (two_mul _).symm

/-- The compact set `closedBall 0 R ∩ Hbar`. -/
def ballH (R : ℝ) : Set ℂ := closedBall (0 : ℂ) R ∩ Hbar

theorem isCompact_ballH (R : ℝ) : IsCompact (ballH R) :=
  (isCompact_closedBall _ _).inter_right isClosed_Hbar

theorem measurableSet_ballH (R : ℝ) : MeasurableSet (ballH R) :=
  (isCompact_ballH R).isClosed.measurableSet

theorem foldedCircle_support {r : ℝ} (hr : 0 ≤ r) {z : ℂ} {R : ℝ} (hzR : ‖z‖ + r ≤ R) :
    foldedCircle z r (ballH R)ᶜ = 0 := by
  have hA : MeasurableSet (ballH R)ᶜ := (measurableSet_ballH R).compl
  rw [foldedCircle, Measure.map_apply measurable_foldH hA, circleUnif, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap z r) (measurable_foldH hA)]
  have : circleMap z r ⁻¹' (foldH ⁻¹' (ballH R)ᶜ) = ∅ := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    refine ⟨?_, foldH_mem_Hbar' _⟩
    rw [mem_closedBall, dist_zero_right, norm_foldH']
    calc ‖circleMap z r θ‖ = ‖z + (circleMap z r θ - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖circleMap z r θ - z‖ := norm_add_le _ _
      _ = ‖z‖ + r := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]
      _ ≤ R := hzR
  rw [this]; simp

/-! ## Integrability of the Neumann kernel -/

theorem abs_log_le_of_le {t R : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 * R) :
    |Real.log t| ≤ Real.log (max (2 * R) 1) + max 0 (-Real.log t) := by
  have hM : 0 ≤ Real.log (max (2 * R) 1) := Real.log_nonneg (le_max_right _ _)
  have hup : Real.log t ≤ Real.log (max (2 * R) 1) := by
    rcases ht0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact hM
    · exact Real.log_le_log h (ht.trans (le_max_left _ _))
  rw [abs_le]
  constructor
  · linarith [le_max_right 0 (-Real.log t)]
  · linarith [le_max_left 0 (-Real.log t)]

theorem ofReal_max_zero (u : ℝ) : ENNReal.ofReal (max 0 u) = ENNReal.ofReal u := by
  rcases le_total 0 u with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

theorem ofReal_norm_neumannH_le {R : ℝ} {x y : ℂ} (hx : x ∈ ballH R) (hy : y ∈ ballH R) :
    ENNReal.ofReal ‖neumannH x y‖ ≤ ENNReal.ofReal (2 * Real.log (max (2 * R) 1))
      + ENNReal.ofReal (-Real.log ‖y - x‖) + ENNReal.ofReal (-Real.log ‖y - conj x‖) := by
  have hxR : ‖x‖ ≤ R := by simpa using hx.1
  have hyR : ‖y‖ ≤ R := by simpa using hy.1
  have hM : 0 ≤ Real.log (max (2 * R) 1) := Real.log_nonneg (le_max_right _ _)
  have ha : ‖x - y‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have hb : ‖x - conj y‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
  have h1 := abs_log_le_of_le (norm_nonneg _) ha
  have h2 := abs_log_le_of_le (norm_nonneg _) hb
  have hN : ‖neumannH x y‖ ≤ (Real.log (max (2 * R) 1) + max 0 (-Real.log ‖x - y‖))
      + (Real.log (max (2 * R) 1) + max 0 (-Real.log ‖x - conj y‖)) := by
    rw [Real.norm_eq_abs, neumannH]
    calc |-Real.log ‖x - y‖ - Real.log ‖x - conj y‖|
        = |Real.log ‖x - y‖ + Real.log ‖x - conj y‖| := by
          rw [← abs_neg]; ring_nf
      _ ≤ |Real.log ‖x - y‖| + |Real.log ‖x - conj y‖| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  calc ENNReal.ofReal ‖neumannH x y‖
      ≤ ENNReal.ofReal ((Real.log (max (2 * R) 1) + max 0 (-Real.log ‖x - y‖))
      + (Real.log (max (2 * R) 1) + max 0 (-Real.log ‖x - conj y‖))) :=
        ENNReal.ofReal_le_ofReal hN
    _ = ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) + ENNReal.ofReal (max 0 (-Real.log ‖x - y‖))
          + ENNReal.ofReal (max 0 (-Real.log ‖x - conj y‖)) := by
        rw [← ENNReal.ofReal_add (by positivity) (le_max_left _ _),
          ← ENNReal.ofReal_add (by positivity) (le_max_left _ _)]
        congr 1; ring
    _ = _ := by
        rw [ofReal_max_zero, ofReal_max_zero, norm_sub_rev x y, norm_sub_conj_comm x y]

theorem lintegral_norm_neumannH_le {μ μ' : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {R : ℝ} (hμ : μ (ballH R)ᶜ = 0) (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞}
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    ∫⁻ p, ENNReal.ofReal ‖neumannH p.1 p.2‖ ∂(μ.prod μ')
      ≤ μ Set.univ * (ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ + 2 * C) := by
  have hae : ∀ᵐ x ∂μ, x ∈ ballH R := mem_ae_iff.mpr hμ
  have hae' : ∀ᵐ y ∂μ', y ∈ ballH R := mem_ae_iff.mpr hμ'
  rw [lintegral_prod _ (measurable_neumannH.norm.ennreal_ofReal.aemeasurable)]
  have hin : ∀ x ∈ ballH R, ∫⁻ y, ENNReal.ofReal ‖neumannH x y‖ ∂μ'
      ≤ ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ + 2 * C := by
    intro x hx
    calc ∫⁻ y, ENNReal.ofReal ‖neumannH x y‖ ∂μ'
        ≤ ∫⁻ y, (ENNReal.ofReal (2 * Real.log (max (2 * R) 1))
            + ENNReal.ofReal (-Real.log ‖y - x‖) + ENNReal.ofReal (-Real.log ‖y - conj x‖)) ∂μ' :=
          lintegral_mono_ae (hae'.mono fun y hy => ofReal_norm_neumannH_le hx hy)
      _ = ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ
            + ∫⁻ y, ENNReal.ofReal (-Real.log ‖y - x‖) ∂μ'
            + ∫⁻ y, ENNReal.ofReal (-Real.log ‖y - conj x‖) ∂μ' := by
          rw [lintegral_add_right _ (measurable_logPot _), lintegral_add_left measurable_const,
            lintegral_const]
      _ ≤ ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ + C + C :=
          add_le_add (add_le_add le_rfl (hC x)) (hC (conj x))
      _ = _ := by rw [add_assoc, ← two_mul]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal ‖neumannH (x, y).1 (x, y).2‖ ∂μ' ∂μ
      ≤ ∫⁻ _, (ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ + 2 * C) ∂μ :=
        lintegral_mono_ae (hae.mono fun x hx => hin x hx)
    _ = _ := by rw [lintegral_const, mul_comm]

/-- The bound of `lintegral_norm_neumannH_le`. -/
def nBound (μ μ' : Measure ℂ) (R : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  μ Set.univ * (ENNReal.ofReal (2 * Real.log (max (2 * R) 1)) * μ' Set.univ + 2 * C)

theorem nBound_ne_top {μ μ' : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (R : ℝ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) : nBound μ μ' R C ≠ ⊤ := by
  unfold nBound
  exact ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.mul_ne_top (by simp) hC⟩)

theorem integrable_neumannH {μ μ' : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {R : ℝ} (hμ : μ (ballH R)ᶜ = 0) (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2) (μ.prod μ') := by
  refine ⟨measurable_neumannH.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [← ofReal_norm]
  exact lt_of_le_of_lt (lintegral_norm_neumannH_le hμ hμ' hC)
    (lt_top_iff_ne_top.mpr (nBound_ne_top (μ := μ) (μ' := μ') R hCt))

theorem abs_kernelCov_le {μ μ' : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {R : ℝ} (hμ : μ (ballH R)ᶜ = 0) (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    |kernelCov neumannH μ μ'| ≤ (nBound μ μ' R C).toReal := by
  have hint := integrable_neumannH hμ hμ' hCt hC
  unfold kernelCov
  rw [← integral_prod _ hint, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  exact ENNReal.toReal_mono (nBound_ne_top R hCt) (lintegral_norm_neumannH_le hμ hμ' hC)

/-! ## Integrals against `ν.bind c` -/

theorem integral_bind_circle {r : ℝ} (ν : Measure ℂ) [IsFiniteMeasure ν] {F : ℂ → ℝ}
    (hF : Integrable F (ν.bind fun w => foldedCircle w r)) :
    Integrable (fun w => ∫ x, F x ∂foldedCircle w r) ν ∧
      ∫ x, F x ∂(ν.bind fun w => foldedCircle w r) = ∫ w, ∫ x, F x ∂foldedCircle w r ∂ν := by
  change Integrable F (circleKernel r ∘ₘ ν) at hF
  change Integrable (fun w => ∫ x, F x ∂circleKernel r w) ν ∧
    ∫ x, F x ∂(circleKernel r ∘ₘ ν) = ∫ w, ∫ x, F x ∂circleKernel r w ∂ν
  rw [Measure.comp_eq_comp_const_apply] at hF ⊢
  refine ⟨?_, ?_⟩
  · simpa using hF.integral_comp
  · rw [ProbabilityTheory.Kernel.integral_comp hF]; simp

/-! ## Properties of `ν.bind c` and of `a • c z₀` -/

section BindProps

variable {r : ℝ} (ν : Measure ℂ) [IsFiniteMeasure ν]

theorem bind_circle_apply {A : Set ℂ} (hA : MeasurableSet A) :
    (ν.bind fun w => foldedCircle w r) A = ∫⁻ w, foldedCircle w r A ∂ν :=
  Measure.bind_apply hA (measurable_foldedCircle' r).aemeasurable

theorem bind_circle_univ : (ν.bind fun w => foldedCircle w r) Set.univ = ν Set.univ := by
  rw [bind_circle_apply ν MeasurableSet.univ]; simp

theorem isFiniteMeasure_bind_circle : IsFiniteMeasure (ν.bind fun w => foldedCircle w r) :=
  ⟨by rw [bind_circle_univ]; exact measure_lt_top _ _⟩

theorem bind_circle_support (hr : 0 ≤ r) {K : Set ℂ} (hνK : ν Kᶜ = 0) {R₀ R : ℝ}
    (hKR : ∀ z ∈ K, ‖z‖ ≤ R₀) (hR : R₀ + r ≤ R) :
    (ν.bind fun w => foldedCircle w r) (ballH R)ᶜ = 0 := by
  rw [bind_circle_apply ν (measurableSet_ballH R).compl]
  have hae : ∀ᵐ w ∂ν, w ∈ K := mem_ae_iff.mpr hνK
  have : ∀ᵐ w ∂ν, foldedCircle w r (ballH R)ᶜ = 0 :=
    hae.mono fun w hw => foldedCircle_support hr (by linarith [hKR w hw])
  rw [lintegral_congr_ae this, lintegral_zero]

theorem bind_circle_pot {C : ℝ≥0∞} (hC : ∀ z y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖)
    ∂foldedCircle z r ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(ν.bind fun w => foldedCircle w r)
      ≤ ν Set.univ * C := by
  rw [Measure.lintegral_bind (measurable_foldedCircle' r).aemeasurable
    (measurable_logPot y).aemeasurable]
  calc ∫⁻ w, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle w r ∂ν
      ≤ ∫⁻ _, C ∂ν := lintegral_mono fun w => hC w y
    _ = ν Set.univ * C := by rw [lintegral_const, mul_comm]

end BindProps

theorem isFiniteMeasure_smul' (a : ℝ≥0∞) (ha : a ≠ ⊤) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (a • μ) :=
  ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ha.lt_top (measure_lt_top _ _)⟩

theorem smul_pot {a : ℝ≥0∞} {μ : Measure ℂ} {C : ℝ≥0∞}
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(a • μ) ≤ a * C := by
  rw [lintegral_smul_measure, smul_eq_mul]; exact mul_le_mul' le_rfl (hC y)

theorem admissible_of_bounds {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ} (hS : μ (ballH R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ⊤) (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤ C) :
    IsAdmissibleH μ :=
  ⟨inferInstance, ⟨ballH R, isCompact_ballH R, Set.inter_subset_right, hS⟩,
    ⟨C, lt_top_iff_ne_top.mpr hCt, hC⟩⟩

/-- Linearity of `kernelCov neumannH` in the first measure under `bind`. -/
theorem kernelCov_bind {r : ℝ} (ν : Measure ℂ) [IsFiniteMeasure ν] {R : ℝ}
    (hS : (ν.bind fun w => foldedCircle w r) (ballH R)ᶜ = 0)
    {μ' : Measure ℂ} [IsFiniteMeasure μ'] (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    Integrable (fun w => kernelCov neumannH (foldedCircle w r) μ') ν ∧
      ∫ w, kernelCov neumannH (foldedCircle w r) μ' ∂ν
        = kernelCov neumannH (ν.bind fun w => foldedCircle w r) μ' := by
  have := isFiniteMeasure_bind_circle (r := r) ν
  have hint := integrable_neumannH hS hμ' hCt hC
  have hF : Integrable (fun x => ∫ y, neumannH x y ∂μ') (ν.bind fun w => foldedCircle w r) :=
    hint.integral_prod_left
  obtain ⟨h1, h2⟩ := integral_bind_circle ν hF
  exact ⟨h1, h2.symm⟩

/-! ## A Cauchy–Schwarz inequality and products of `L²` functions -/

theorem sq_integral_le' {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → ℝ} (h1 : Integrable f ν) (h2 : Integrable (fun z => f z ^ 2) ν) :
    (∫ z, f z ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ z, f z ^ 2 ∂ν := by
  set m := (ν Set.univ).toReal with hm_def
  set a := ∫ z, f z ∂ν with ha_def
  have h0 : 0 ≤ ∫ z, (m * f z - a) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ z, (m * f z - a) ^ 2 ∂ν = m * (m * ∫ z, f z ^ 2 ∂ν - a ^ 2) := by
    have : ∀ z, (m * f z - a) ^ 2 = (m ^ 2 * f z ^ 2 - (2 * m * a) * f z) + a ^ 2 :=
      fun z => by ring
    simp_rw [this]
    rw [integral_add (f := fun z => m ^ 2 * f z ^ 2 - 2 * m * a * f z) (g := fun _ => a ^ 2)
        ((h2.const_mul _).sub (h1.const_mul _)) (integrable_const _),
      integral_sub (f := fun z => m ^ 2 * f z ^ 2) (g := fun z => 2 * m * a * f z)
        (h2.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul,
      integral_const, smul_eq_mul, measureReal_def, ← ha_def, ← hm_def]
    ring
  rcases (ENNReal.toReal_nonneg (a := ν Set.univ)).eq_or_lt with hm | hm
  · have hν0 : ν Set.univ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 hm.symm with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have : ν = 0 := Measure.measure_univ_eq_zero.mp hν0
    subst this
    simp [a]
  · rw [hexp] at h0
    have := (mul_nonneg_iff_of_pos_left hm).1 h0
    linarith

theorem integrable_mul_of_memLp_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine Integrable.mono' ((hf.integrable_sq.add hg.integrable_sq).div_const 2)
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]

/-! ## A jointly measurable version of `Y` -/

theorem exists_measurable_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y W : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hW : ∀ z, Measurable (W z)) (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] W z) :
    ∃ Z : ℂ → Ω → ℝ, Measurable (Function.uncurry Z) ∧ (∀ ω, Continuous fun z => Z z ω) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ Hbar, Z z ω = Y z ω) ∧ (∀ z ∈ Hbar, Z z =ᵐ[P] W z) := by
  obtain ⟨S, hSc, hSH, hHS⟩ := TopologicalSpace.exists_countable_dense_subset Hbar
  have hall : ∀ᵐ ω ∂P, ∀ s ∈ S, Y s ω = W s ω :=
    (eventually_countable_ball hSc).2 fun s hs => hY s (hSH hs)
  set N := {ω | ¬ ∀ s ∈ S, Y s ω = W s ω} with hN_def
  have hN : P N = 0 := ae_iff.1 hall
  set Ω₁ := (toMeasurable P N)ᶜ with hΩ₁_def
  have hΩ₁m : MeasurableSet Ω₁ := (measurableSet_toMeasurable P N).compl
  have hΩ₁ : ∀ ω ∈ Ω₁, ∀ s ∈ S, Y s ω = W s ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable P N h)
  have hΩ₁ae : ∀ᵐ ω ∂P, ω ∈ Ω₁ := by
    rw [ae_iff]
    have : {a | ¬ a ∈ Ω₁} = toMeasurable P N := by ext; simp [Ω₁]
    rw [this, measure_toMeasurable, hN]
  have hcont : ∀ ω, Continuous fun z => Ω₁.indicator (fun ω => Y (foldH z) ω) ω := by
    intro ω
    by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]
      exact (hYc ω).comp_continuous continuous_foldH' foldH_mem_Hbar'
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]
      exact continuous_const
  have hmeas : ∀ z, Measurable (fun ω => Ω₁.indicator (fun ω => Y (foldH z) ω) ω) := by
    intro z
    have hz : foldH z ∈ closure S := hHS (foldH_mem_Hbar' z)
    obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hz
    refine measurable_of_tendsto_metrizable (f := fun n ω => Ω₁.indicator (W (u n)) ω)
      (fun n => (hW (u n)).indicator hΩ₁m) ?_
    rw [tendsto_pi_nhds]; intro ω
    by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]
      have : ∀ n, W (u n) ω = Y (u n) ω := fun n => (hΩ₁ ω hω (u n) (huS n)).symm
      simp_rw [this]
      exact ((hYc ω) (foldH z) (foldH_mem_Hbar' z)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall fun n => hSH (huS n)⟩)
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]
      exact tendsto_const_nhds
  refine ⟨fun z ω => Ω₁.indicator (fun ω => Y (foldH z) ω) ω,
    measurable_uncurry_of_continuous_of_measurable hcont hmeas, hcont, ?_, ?_⟩
  · filter_upwards [hΩ₁ae] with ω hω z hz
    simp only [Set.indicator_of_mem hω, foldH_of_mem' hz]
  · intro z hz
    filter_upwards [hΩ₁ae, hY z hz] with ω hω h2
    simp only [Set.indicator_of_mem hω, foldH_of_mem' hz]
    exact h2

/-! ## Abstract Fubini lemmas -/

section AbstractFubini

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ} {Z : ℂ → Ω → ℝ} {B : ℝ}

theorem integrable_sq_prod (hZ : Measurable (Function.uncurry Z)) (hνK : ν Kᶜ = 0)
    (hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ B) :
    Integrable (fun p : ℂ × Ω => Z p.1 p.2 ^ 2) (ν.prod P) := by
  have hm : Measurable (fun p : ℂ × Ω => Z p.1 p.2 ^ 2) := hZ.pow_const 2
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  refine ⟨hae.mono fun z hz => hmom z hz, ?_⟩
  refine Integrable.of_bound hm.norm.aestronglyMeasurable.integral_prod_right' B
    (hae.mono fun z hz => ?_)
  have h1 : ∀ ω, ‖Z z ω ^ 2‖ = Z z ω ^ 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [h1]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  exact hB z hz

theorem fubini_mul (hZ : Measurable (Function.uncurry Z)) (hνK : ν Kᶜ = 0)
    (hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ B) {g : Ω → ℝ} (hg : Measurable g) (hg2 : MemLp g 2 P) :
    ∫ ω, (∫ z, Z z ω ∂ν) * g ω ∂P = ∫ z, ∫ ω, Z z ω * g ω ∂P ∂ν := by
  have hsq := integrable_sq_prod (B := B) (ν := ν) hZ hνK hmom hB
  have hgsq : Integrable (fun ω => g ω ^ 2) P := hg2.integrable_sq
  have hg2' : Integrable (fun p : ℂ × Ω => g p.2 ^ 2) (ν.prod P) := by
    have hm : Measurable (fun p : ℂ × Ω => g p.2 ^ 2) := (hg.comp measurable_snd).pow_const 2
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    exact ⟨ae_of_all _ fun _ => hgsq, integrable_const (∫ y, ‖g y ^ 2‖ ∂P)⟩
  have hint : Integrable (fun p : ℂ × Ω => Z p.1 p.2 * g p.2) (ν.prod P) := by
    refine Integrable.mono' ((hsq.add hg2').div_const 2)
      ((hZ.mul (hg.comp measurable_snd)).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|Z p.1 p.2| - |g p.2|), sq_abs (Z p.1 p.2), sq_abs (g p.2)]
  calc ∫ ω, (∫ z, Z z ω ∂ν) * g ω ∂P = ∫ ω, ∫ z, Z z ω * g ω ∂ν ∂P := by
        congr 1; funext ω; rw [integral_mul_const]
    _ = ∫ z, ∫ ω, Z z ω * g ω ∂P ∂ν :=
        (integral_integral_swap (f := fun z ω => Z z ω * g ω) hint).symm

theorem memLp_integral (hZ : Measurable (Function.uncurry Z)) (hνK : ν Kᶜ = 0)
    (hK : IsCompact K) (hZc : ∀ ω, Continuous fun z => Z z ω)
    (hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ B) :
    Measurable (fun ω => ∫ z, Z z ω ∂ν) ∧ MemLp (fun ω => ∫ z, Z z ω ∂ν) 2 P := by
  have hsq := integrable_sq_prod (B := B) (ν := ν) hZ hνK hmom hB
  have hLm : Measurable (fun ω => ∫ z, Z z ω ∂ν) :=
    (hZ.stronglyMeasurable.integral_prod_left (μ := ν)).measurable
  refine ⟨hLm, ?_⟩
  rw [memLp_two_iff_integrable_sq hLm.aestronglyMeasurable]
  have hbound : Integrable (fun ω => (ν Set.univ).toReal * ∫ z, Z z ω ^ 2 ∂ν) P :=
    hsq.integral_prod_right.const_mul _
  refine Integrable.mono' hbound (hLm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hνK' : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hνK)
  have h1 : Integrable (fun z => Z z ω) ν := by
    rw [← hνK']; exact (hZc ω).continuousOn.integrableOn_compact hK
  have h2 : Integrable (fun z => Z z ω ^ 2) ν := by
    rw [← hνK']; exact ((hZc ω).pow 2).continuousOn.integrableOn_compact hK
  exact sq_integral_le' h1 h2

end AbstractFubini

/-! ## GFF second moments -/

section GFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem gff_memLp (hX : IsFreeGFFModConstH X P) {p : Measure ℂ × Measure ℂ}
    (h1 : IsAdmissibleH p.1) (h2 : IsAdmissibleH p.2) (h3 : p.1 Set.univ = p.2 Set.univ) :
    MemLp (fun ω => X ω p.1 - X ω p.2) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval ⟨p, h1, h2, h3⟩).memLp_two

theorem gff_integral_mul (hX : IsFreeGFFModConstH X P) {p q : Measure ℂ × Measure ℂ}
    (h1 : IsAdmissibleH p.1) (h2 : IsAdmissibleH p.2) (h3 : p.1 Set.univ = p.2 Set.univ)
    (g1 : IsAdmissibleH q.1) (g2 : IsAdmissibleH q.2) (g3 : q.1 Set.univ = q.2 Set.univ) :
    ∫ ω, (X ω p.1 - X ω p.2) * (X ω q.1 - X ω q.2) ∂P = kernelCov2 neumannH p q := by
  have h := hX.covariance_eq p q h1 h2 h3 g1 g2 g3
  rw [covariance_eq_sub (gff_memLp hX h1 h2 h3) (gff_memLp hX g1 g2 g3),
    hX.centered _ _ h1 h2 h3, hX.centered _ _ g1 g2 g3] at h
  simpa using h

end GFF

end CircleFubini

open CircleFubini

/-- **Stochastic Fubini for folded-circle averages** (general mass). For a free-boundary GFF
modulo constants `X`, a version `Y` of the circle-average increments that is continuous in the
centre on `Hbar`, and a finite measure `ν` carried by a compact `K ⊆ Hbar`,
`∫ Y z dν = X (ν.bind c) - X ((ν ℂ) • c z₀)` almost surely, where `c z = foldedCircle z 2^{-k}`.
The right-hand side pairs `X` with two measures of equal mass, which is what the free field
modulo constants can see. -/
theorem integral_circleAvg_ae_eq_bind
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (k : ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ Hbar)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P]
      fun ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle z₀ (radius k)))
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    (fun ω => ∫ z, Y z ω ∂ν) =ᵐ[P] fun ω =>
      X ω (ν.bind fun w => foldedCircle w (radius k))
        - X ω (ν Set.univ • foldedCircle z₀ (radius k)) := by
  set r := radius k with hr_def
  have hr : 0 < r := radius_pos k
  set νk := ν.bind fun w => foldedCircle w r with hνk_def
  set μ₀ := ν Set.univ • foldedCircle z₀ r with hμ₀_def
  have : IsFiniteMeasure νk := isFiniteMeasure_bind_circle ν
  have : IsFiniteMeasure μ₀ := isFiniteMeasure_smul' _ (measure_ne_top _ _) _
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R₀ := max R₁ ‖z₀‖ with hR₀_def
  set R := R₀ + r with hR_def
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR₁ hz
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hz₀R : ‖z₀‖ ≤ R₀ := le_max_right _ _
  set Cc : ℝ≥0∞ := 2 * ENNReal.ofReal (potConst r) with hCc_def
  have hCct : Cc ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hcP : ∀ z y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle z r ≤ Cc :=
    fun z y => foldedCircle_pot_le hr z y
  have hcS : ∀ z, ‖z‖ ≤ R₀ → foldedCircle z r (ballH R)ᶜ = 0 := fun z hz =>
    foldedCircle_support hr.le (by linarith)
  have hcA : ∀ z, ‖z‖ ≤ R₀ → IsAdmissibleH (foldedCircle z r) := fun z hz =>
    admissible_of_bounds (hcS z hz) hCct (hcP z)
  have hmCt : ν Set.univ * Cc ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) hCct
  have hkS : νk (ballH R)ᶜ = 0 := bind_circle_support ν hr.le hνK hKR (le_refl _)
  have hkP : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂νk ≤ ν Set.univ * Cc :=
    bind_circle_pot ν hcP
  have hkA : IsAdmissibleH νk := admissible_of_bounds hkS hmCt hkP
  have hkU : νk Set.univ = ν Set.univ := bind_circle_univ ν
  have h0S : μ₀ (ballH R)ᶜ = 0 := by
    rw [hμ₀_def, Measure.smul_apply, hcS z₀ hz₀R, smul_zero]
  have h0P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ₀ ≤ ν Set.univ * Cc :=
    smul_pot (hcP z₀)
  have h0A : IsAdmissibleH μ₀ := admissible_of_bounds h0S hmCt h0P
  have h0U : μ₀ Set.univ = ν Set.univ := by
    rw [hμ₀_def, Measure.smul_apply, measure_univ (μ := foldedCircle z₀ r), smul_eq_mul, mul_one]
  -- the random variables
  set W : ℂ → Ω → ℝ := fun z ω => X ω (foldedCircle z r) - X ω (foldedCircle z₀ r) with hW_def
  set D : Ω → ℝ := fun ω => X ω νk - X ω μ₀ with hD_def
  have hWm : ∀ z, Measurable (W z) := fun z =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hDm : Measurable D := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have h11 : ∀ z : ℂ, (foldedCircle z r) Set.univ = (foldedCircle z₀ r) Set.univ := by
    intro z; simp
  have hqU : νk Set.univ = μ₀ Set.univ := by rw [hkU, h0U]
  have hWL2 : ∀ z ∈ K, MemLp (W z) 2 P := fun z hz =>
    gff_memLp (p := (foldedCircle z r, foldedCircle z₀ r)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z)
  have hDL2 : MemLp D 2 P := gff_memLp (p := (νk, μ₀)) hX hkA h0A hqU
  have hEWW : ∀ z ∈ K, ∀ z' ∈ K, ∫ ω, W z ω * W z' ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r)
          (foldedCircle z' r, foldedCircle z₀ r) :=
    fun z hz z' hz' => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r))
      (q := (foldedCircle z' r, foldedCircle z₀ r)) hX (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
      (hcA z' (hKR z' hz')) (hcA z₀ hz₀R) (h11 z')
  have hEWD : ∀ z ∈ K, ∫ ω, W z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) :=
    fun z hz => gff_integral_mul (p := (foldedCircle z r, foldedCircle z₀ r)) (q := (νk, μ₀)) hX (hcA z (hKR z hz))
      (hcA z₀ hz₀R) (h11 z) hkA h0A hqU
  have hEDW : ∀ z ∈ K, ∫ ω, D ω * W z ω ∂P
      = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
    fun z hz => gff_integral_mul (p := (νk, μ₀)) (q := (foldedCircle z r, foldedCircle z₀ r)) hX hkA h0A hqU (hcA z (hKR z hz)) (hcA z₀ hz₀R) (h11 z)
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) :=
    gff_integral_mul (p := (νk, μ₀)) (q := (νk, μ₀)) hX hkA h0A hqU hkA h0A hqU
  -- a jointly measurable version of `Y`
  obtain ⟨Z, hZm, hZc, hZY, hZW⟩ := exists_measurable_version hYc hWm hY
  have hZL2 : ∀ z ∈ K, MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z hz).ae_eq (hZW z (hKH hz)).symm
  -- the uniform variance bound
  set b := (nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc).toReal with hb_def
  have hkc : ∀ z z', ‖z‖ ≤ R₀ → ‖z'‖ ≤ R₀ →
      |kernelCov neumannH (foldedCircle z r) (foldedCircle z' r)| ≤ b := by
    intro z z' hz hz'
    have := abs_kernelCov_le (hcS z hz) (hcS z' hz') hCct (hcP z')
    have he : nBound (foldedCircle z r) (foldedCircle z' r) R Cc
        = nBound (foldedCircle z₀ r) (foldedCircle z₀ r) R Cc := by
      simp only [nBound, measure_univ]
    rwa [he] at this
  have hB : ∀ z ∈ K, ∫ ω, Z z ω ^ 2 ∂P ≤ 4 * b := by
    intro z hz
    have e1 : ∫ ω, Z z ω ^ 2 ∂P = ∫ ω, W z ω * W z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZW z (hKH hz)] with ω hω
      rw [hω, sq]
    rw [e1, hEWW z hz z hz]
    simp only [kernelCov2]
    have a1 := abs_le.1 (hkc z z (hKR z hz) (hKR z hz))
    have a2 := abs_le.1 (hkc z z₀ (hKR z hz) hz₀R)
    have a3 := abs_le.1 (hkc z₀ z hz₀R (hKR z hz))
    have a4 := abs_le.1 (hkc z₀ z₀ hz₀R hz₀R)
    linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hmom : ∀ z ∈ K, Integrable (fun ω => Z z ω ^ 2) P := fun z hz =>
    (hZL2 z hz).integrable_sq
  -- linearity of the covariance under `bind`
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.mpr hνK
  have hsmul : ∀ μ' : Measure ℂ, kernelCov neumannH μ₀ μ'
      = (ν Set.univ).toReal * kernelCov neumannH (foldedCircle z₀ r) μ' := by
    intro μ'; simp only [kernelCov, hμ₀_def, integral_smul_measure, smul_eq_mul]
  have hlin2 : ∀ (a b' : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b'],
      a (ballH R)ᶜ = 0 → b' (ballH R)ᶜ = 0 → ∀ {C C' : ℝ≥0∞}, C ≠ ⊤ → C' ≠ ⊤ →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ C) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b' ≤ C') →
      ∫ w, kernelCov2 neumannH (foldedCircle w r, foldedCircle z₀ r) (a, b') ∂ν
        = kernelCov2 neumannH (νk, μ₀) (a, b') := by
    intro a b' _ _ ha hb' C C' hC hC' hCa hCb
    obtain ⟨ia, ea⟩ := kernelCov_bind ν hkS ha hC hCa
    obtain ⟨ib, eb⟩ := kernelCov_bind ν hkS hb' hC' hCb
    simp only [kernelCov2]
    rw [integral_add (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b' - kernelCov neumannH (foldedCircle z₀ r) a)
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) b')
        ((ia.sub ib).sub (integrable_const _)) (integrable_const _),
      integral_sub (f := fun w => kernelCov neumannH (foldedCircle w r) a
          - kernelCov neumannH (foldedCircle w r) b')
        (g := fun _ => kernelCov neumannH (foldedCircle z₀ r) a) (ia.sub ib) (integrable_const _),
      integral_sub ia ib, ea, eb,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hsmul, hsmul]
  -- the second moments of `L = ∫ Z z dν`
  obtain ⟨hLm, hLL2⟩ := memLp_integral (B := 4 * b) hZm hνK hK hZc hmom hB
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂ν with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z ∈ K, ∫ ω, Z z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) := by
    intro z hz
    rw [← hEWD z hz]
    refine integral_congr_ae ?_
    filter_upwards [hZW z (hKH hz)] with ω hω
    rw [hω]
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov2 neumannH (νk, μ₀) (νk, μ₀) := by
    rw [fubini_mul hZm hνK hmom hB hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂ν
        = ∫ z, kernelCov2 neumannH (foldedCircle z r, foldedCircle z₀ r) (νk, μ₀) ∂ν :=
          integral_congr_ae (hae.mono fun z hz => hZD z hz)
      _ = _ := hlin2 νk μ₀ hkS h0S hmCt hmCt hkP h0P
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [fubini_mul hZm hνK hmom hB hLm hLL2, fubini_mul hZm hνK hmom hB hDm hDL2]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, fubini_mul hZm hνK hmom hB (hZmz z) (hZL2 z hz)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂ν
        = ∫ z', kernelCov2 neumannH (foldedCircle z' r, foldedCircle z₀ r)
            (foldedCircle z r, foldedCircle z₀ r) ∂ν := by
          refine integral_congr_ae (hae.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P = _
          beta_reduce
          rw [← hEWW z' hz' z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz), hZW z' (hKH hz')] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov2 neumannH (νk, μ₀) (foldedCircle z r, foldedCircle z₀ r) :=
          hlin2 _ _ (hcS z (hKR z hz)) (hcS z₀ hz₀R) hCct hCct (hcP z) (hcP z₀)
      _ = ∫ ω, Z z ω * D ω ∂P := by
          rw [← hEDW z hz]
          refine integral_congr_ae ?_
          filter_upwards [hZW z (hKH hz)] with ω hω
          rw [hω, mul_comm]
  -- conclusion: `E[(L - D)²] = 0`
  have hsq : ∫ ω, (L ω - D ω) ^ 2 ∂P = 0 := by
    have : ∀ ω, (L ω - D ω) ^ 2 = (L ω * L ω - 2 * (L ω * D ω)) + D ω * D ω := fun ω => by
      ring
    simp_rw [this]
    have iLL := integrable_mul_of_memLp_two hLL2 hLL2
    have iLD := integrable_mul_of_memLp_two hLL2 hDL2
    have iDD := integrable_mul_of_memLp_two hDL2 hDL2
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

end QuantumZipper
