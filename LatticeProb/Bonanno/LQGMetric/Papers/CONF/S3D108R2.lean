/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108R2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108R1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K1
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentKer

/-!
# CONF Lemma 2.10, white-noise model on a bounded open `U`: the pairing process and the split

CONF (arXiv:1905.00381, `confluence-final.tex`) C:722–731: `h^U = h_{0,t} + h_{t,∞}` with
`h_{s,t} = √π ∫_{s²}^{t²} ∫_U p^U_{r/2} W`; the two pieces are independent (white noise on
disjoint time windows).

* `zbProcU W U φ = √π W(K^{(0,∞)}_U (φ 1_U))`: CONF's `(h^U, φ)` (Rhodes–Vargas Lemma 5.4).
* **`cov_zbProcU`**: `Cov((h^U, φ), (h^U, ψ)) = ∫∫ φ 1_U(y) ψ 1_U(y') G_U(y, y')` with
  `G_U = π ∫₀^∞ p_U(s; ·, ·) ds` (`KilledHeat.killedGreen`), for every bounded open `U`.
* `ZBHeatRepr U`: the identification `G_U = π ∫ p_U` of D39 (handoff/P2-KILLED.md item 1) at `U`,
  in pairing form; proved so far only for squares (`GMCIdent2.killedGreen_openSquare`,
  `HeatSq.zeroGFFTestCov_sqOpen_eq_heat_gen`). Under it, `zbProcU` has the covariance of
  `IsZBExtField` (`cov_zbProcU_of_heatRepr`) and is a centred Gaussian process.
* `uKer_split`, `uKerL2_split`, `supportedIn_uKerL2`: `K^{(0,∞)} = K^{(0,c]} + K^{(c,∞)}`, the
  pieces supported in disjoint time windows (generalising `GMCIdent.measKerL2_split` to signed
  densities), hence `indep_fine_coarse`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- CONF's pairing `(h^U, φ) = √π ∫∫ (∫ φ 1_U p^U_{s/2}) W` (C:722–724) -/
def zbProcU (W : WNSpace → Ω → ℝ) (U : Set ℂ) (φ : TestC) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (uKerL2 U (Ioi 0) (U.indicator φ)) ω

/-- D39 at `U` (`G_U = π ∫₀^∞ p_U`, pairing form): the Dirichlet-form covariance of the
zero-boundary GFF equals the killed-Green-function covariance -/
def ZBHeatRepr (U : Set ℂ) : Prop :=
  ∀ φ ψ : TestC, QuantumZipper.zeroGFFTestCov U (U.indicator φ) (U.indicator ψ) =
    ∫ q : ℂ × ℂ, U.indicator φ q.1 * U.indicator ψ q.2 * killedGreen U q.1 q.2

lemma testC_abs_le (φ : TestC) : ∃ C, ∀ z : ℂ, |φ z| ≤ C := by
  obtain ⟨C, hC⟩ := (φ.continuous.norm.bddAbove_range_of_hasCompactSupport
    φ.hasCompactSupport.norm)
  exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC ⟨z, rfl⟩⟩

lemma indicator_props (hU : IsOpen U) (φ : TestC) {C : ℝ} (hC : ∀ z, |φ z| ≤ C) :
    Measurable (U.indicator φ) ∧ (∀ z, |U.indicator φ z| ≤ C) ∧ Integrable (U.indicator φ) := by
  refine ⟨φ.continuous.measurable.indicator hU.measurableSet, fun z => ?_,
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).indicator
      hU.measurableSet⟩
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz]; exact hC z
  · rw [indicator_of_notMem hz, abs_zero]; exact (abs_nonneg _).trans (hC z)

/-- **the covariance of the white-noise pairing process** on a bounded open `U` -/
theorem cov_zbProcU (hW : IsWhiteNoise P W) (hU : IsOpen U) (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) (φ ψ : TestC) :
    cov[zbProcU W U φ, zbProcU W U ψ; P] =
      ∫ q : ℂ × ℂ, U.indicator φ q.1 * U.indicator ψ q.2 * killedGreen U q.1 q.2 := by
  obtain ⟨C₁, h₁⟩ := testC_abs_le φ
  obtain ⟨C₂, h₂⟩ := testC_abs_le ψ
  obtain ⟨m1, b1, i1⟩ := indicator_props hU φ (C := max C₁ C₂)
    (fun z => (h₁ z).trans (le_max_left _ _))
  obtain ⟨m2, b2, i2⟩ := indicator_props hU ψ (C := max C₁ C₂)
    (fun z => (h₂ z).trans (le_max_right _ _))
  have e : zbProcU W U φ = fun ω => Real.sqrt Real.pi * W (uKerL2 U (Ioi 0) (U.indicator φ)) ω :=
    rfl
  have e' : zbProcU W U ψ = fun ω => Real.sqrt Real.pi * W (uKerL2 U (Ioi 0) (U.indicator ψ)) ω :=
    rfl
  rw [e, e', covariance_const_mul_left, covariance_const_mul_right, hW.cov_eq,
    inner_uKerL2 hU hR hUR measurableSet_Ioi subset_rfl m1 m2 b1 b2 i1 i2, ← mul_assoc,
    Real.mul_self_sqrt Real.pi_pos.le, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [killedGreen]
  ring

/-- under `ZBHeatRepr U`, the white-noise pairing has the zero-boundary covariance -/
theorem cov_zbProcU_of_heatRepr (hW : IsWhiteNoise P W) (hU : IsOpen U) (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) (hH : ZBHeatRepr U) (φ ψ : TestC) :
    cov[zbProcU W U φ, zbProcU W U ψ; P] =
      QuantumZipper.zeroGFFTestCov U (U.indicator φ) (U.indicator ψ) := by
  rw [cov_zbProcU hW hU hR hUR, hH]

lemma isGaussianProcess_zbProcU (hW : IsWhiteNoise P W) (U : Set ℂ) :
    IsGaussianProcess (fun (φ : TestC) ω => zbProcU W U φ ω) P :=
  isGaussianProcess_sqrtPi hW (fun φ : TestC => uKerL2 U (Ioi 0) (U.indicator φ))

lemma integral_zbProcU (hW : IsWhiteNoise P W) (U : Set ℂ) (φ : TestC) :
    ∫ ω, zbProcU W U φ ω ∂P = 0 :=
  integral_sqrtPi hW _

/-! ## The coarse/fine split of the kernel (C:722–731) -/

lemma integrable_mul_wnd (hU : IsOpen U) {I : Set ℝ} (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0)
    {ρ : ℂ → ℝ} (hρi : Integrable ρ) (p : ℝ × ℂ) :
    Integrable (fun y => ρ y * wndKernel U I y p) := by
  by_cases hp : p.1 ∈ I
  · have hb : ∀ y, ‖wndKernel U I y p‖ ≤ (Real.pi * p.1)⁻¹ := fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
      exact GMCIdent.wndKernel_le U I y p (hI0 hp)
    have := hρi.bdd_mul (measurable_wndKernel_comp hU hI measurable_id
      measurable_const).aestronglyMeasurable (Eventually.of_forall hb)
    exact this.congr (Eventually.of_forall fun y => mul_comm _ _)
  · have : (fun y => ρ y * wndKernel U I y p) = fun _ => 0 := by
      funext y; simp [wndKernel, hp]
    rw [this]; exact integrable_zero _ _ _

/-- `K^{(0,∞)} ρ = K^{(0,c]} ρ + K^{(c,∞)} ρ` -/
lemma uKer_split (hU : IsOpen U) {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ} (hρi : Integrable ρ) :
    uKer U (Ioi 0) ρ = uKer U (Ioc 0 t) ρ + uKer U (Ioi t) ρ := by
  funext p
  simp only [uKer, Pi.add_apply]
  rw [← integral_add (integrable_mul_wnd hU measurableSet_Ioc Ioc_subset_Ioi_self hρi p)
    (integrable_mul_wnd hU measurableSet_Ioi (Ioi_subset_Ioi ht.le) hρi p)]
  exact integral_congr_ae (Eventually.of_forall fun y => by
    show ρ y * _ = ρ y * _ + ρ y * _
    rw [GMCIdent.wndKernel_split U ht y p]; ring)

lemma uKerL2_split (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R) {t : ℝ}
    (ht : 0 < t) {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (hρi : Integrable ρ) :
    uKerL2 U (Ioi 0) ρ = uKerL2 U (Ioc 0 t) ρ + uKerL2 U (Ioi t) ρ := by
  have h₀ := memLp_uKer hU hR hUR measurableSet_Ioi subset_rfl hρ hC hρi
  have h₁ := memLp_uKer (I := Ioc 0 t) hU hR hUR measurableSet_Ioc Ioc_subset_Ioi_self hρ hC hρi
  have h₂ := memLp_uKer hU hR hUR measurableSet_Ioi (Ioi_subset_Ioi ht.le) hρ hC hρi
  rw [uKerL2, uKerL2, uKerL2, dite_eq_left_of_eq_true (eq_true h₀),
    dite_eq_left_of_eq_true (eq_true h₁), dite_eq_left_of_eq_true (eq_true h₂),
    ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => by rw [uKer_split hU ht hρi])

/-- `K^I ρ` is supported in the time window `I` -/
lemma supportedIn_uKerL2 {I : Set ℝ} (hI : MeasurableSet I) (ρ : ℂ → ℝ) :
    SupportedIn (I ×ˢ univ) (uKerL2 U I ρ) := by
  unfold uKerL2
  split_ifs with h
  · unfold SupportedIn
    filter_upwards [ae_restrict_of_ae h.coeFn_toLp,
      ae_restrict_mem (hI.prod MeasurableSet.univ).compl] with p h1 h2
    rw [h1]
    have : p.1 ∉ I := fun h3 => h2 ⟨h3, trivial⟩
    simp [uKer, wndKernel, this]
  · unfold SupportedIn
    exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 volume)

end LQGMetric.CONF.ZBM
