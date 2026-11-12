/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu2

/-!
# `hmeas` of DZZ Lemma 5.3 at `μIn`: `ω ↦ M^W(B(c,r))` is a.e.-measurable (P2-DZZ53b)

DZZ (arXiv:1807.00422) treat measurability of `ω ↦ M_γ^{h̃}(A)` implicitly. Own elementary glue,
following the proof of `DG.aemeasurable_qArea_open_circ` (itself the proof of
`GMCIdent4.aemeasurable_qAreaMeasureOn_ball_circ`):

* for an open bounded `U ⊆ 𝕍`, `CR^{−γ²/2}μ(U) = ⨆ₙ ∫ φₙ · CR^{−γ²/2} dμ` with the cut-offs
  `φₙ = LQGMeas.openBump U n` (monotone convergence); each `φₙ · CR^{−γ²/2}` is continuous with
  compact support in `𝕍` (`hS(z,z)` is continuous on `𝕍`, `GMCIdent4.continuousOn_hS_diag`), so on
  the good samples its integral is the measurable limit `Prop16Area.Meas.Psi`;
* the circle-law statement is transferred to the white noise by `map_circVec_eq`, as in
  `DG.ae_muHU_null`;
* `M^W(B(c,r)) = M^W(B(c,r) ∩ 𝕍)` (`wickArea_compl`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent3

/-- the cut-off integrands `φₙ · CR^{−γ²/2}` -/
def wickBump (γ : ℝ) (U : Set ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  LQGMeas.openBump U n z * Real.exp (-(γ ^ 2 / 2) * hS z z)

lemma continuous_wickBump (γ : ℝ) {U : Set ℂ} (hUU : U ⊆ openSquare) (n : ℕ) :
    Continuous (wickBump γ U n) := by
  refine continuous_of_tsupport fun x hx => ?_
  have hxS : x ∈ openSquare :=
    hUU (LQGMeas.tsupport_openBump_subset U n (tsupport_mul_subset_left hx))
  have he : ContinuousAt (fun z => Real.exp (-(γ ^ 2 / 2) * hS z z)) x :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
      GMCIdent4.continuousOn_hS_diag)).continuousAt (isOpen_openSquare.mem_nhds hxS)
  exact (LQGMeas.continuous_openBump U n).continuousAt.mul he

lemma tsupport_wickBump (γ : ℝ) (U : Set ℂ) (n : ℕ) : tsupport (wickBump γ U n) ⊆ U :=
  (tsupport_mul_subset_left).trans (LQGMeas.tsupport_openBump_subset U n)

lemma hasCompactSupport_wickBump (γ : ℝ) {U : Set ℂ} (hUb : Bornology.IsBounded U) (n : ℕ) :
    HasCompactSupport (wickBump γ U n) :=
  (LQGMeas.hasCompactSupport_openBump hUb n).mul_right

lemma wickBump_nonneg (γ : ℝ) (U : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ wickBump γ U n z :=
  mul_nonneg (LQGMeas.openBump_nonneg U n z) (Real.exp_pos _).le

/-- `CR^{−γ²/2}μ(U) = ⨆ₙ ∫ φₙ CR^{−γ²/2} dμ` (monotone convergence) -/
lemma wickArea_open_eq_iSup (γ : ℝ) (μ : Measure ℂ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : Uᶜ.Nonempty) :
    wickArea γ μ U = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (wickBump γ U n z) ∂μ := by
  have e1 : ∀ n z, ENNReal.ofReal (wickBump γ U n z) =
      ENNReal.ofReal (LQGMeas.openBump U n z) * wickDens γ z := fun n z => by
    rw [wickBump, ENNReal.ofReal_mul (LQGMeas.openBump_nonneg U n z), wickDens]
  simp only [e1]
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (LQGMeas.openBump U n z) * wickDens γ z)
    (fun n => (ENNReal.measurable_ofReal.comp
      (LQGMeas.continuous_openBump U n).measurable).mul (measurable_wickDens γ))
    (fun m n hmn z => mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (LQGMeas.openBump_mono U z hmn)) _)]
  simp only [← ENNReal.iSup_mul, LQGMeas.iSup_openBump hUo hUc]
  rw [wickArea, withDensity_apply _ hUo.measurableSet, ← lintegral_indicator hUo.measurableSet]
  congr 1
  funext z
  by_cases hz : z ∈ U <;> simp [hz]

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {X : Ω₀ → Measure ℂ → ℝ}

/-- open-set Wick masses are a.e.-measurable under the circle law -/
theorem aemeasurable_wickArea_open_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {U : Set ℂ}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUU : U ⊆ openSquare) :
    AEMeasurable (fun v => wickArea γ (qAreaMeasureOn γ (circExt v) openSquare) U)
      (circLaw P₀ X) := by
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by have := hUU h; simp [openSquare] at this⟩
  let F : (CircIdx → ℝ) → ℝ≥0∞ := fun v =>
    ⨆ n, ENNReal.ofReal (Prop16Area.Meas.Psi γ circExt (fun _ z => wickBump γ U n z) v)
  have hF : Measurable F := Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (Prop16Area.Meas.measurable_Psi γ measurable_circExt
      ((continuous_wickBump γ hUU n).measurable.comp measurable_snd))
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_isVagueLimitOn_circExt hX hγ hγ2] with v hm
  set μ := qAreaMeasureOn γ (circExt v) openSquare
  have hts : ∀ n, tsupport (wickBump γ U n) ⊆ openSquare := fun n =>
    (tsupport_wickBump γ U n).trans hUU
  have ePsi : ∀ n, Prop16Area.Meas.Psi γ circExt (fun _ z => wickBump γ U n z) v =
      ∫ z, wickBump γ U n z ∂μ := fun n =>
    (hm.2.2 _ (continuous_wickBump γ hUU n) (hasCompactSupport_wickBump γ hUb n)
      (hts n)).limUnder_eq
  have eL : ∀ n, ENNReal.ofReal (∫ z, wickBump γ U n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (wickBump γ U n z) ∂μ := fun n =>
    ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (continuous_wickBump γ hUU n)
        (hasCompactSupport_wickBump γ hUb n) (hts n))
      (ae_of_all _ (wickBump_nonneg γ U n))
  simp only [F, ePsi, eL]
  rw [← wickArea_open_eq_iSup γ μ hUo hUc]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`hmeas`** of `dzzLem53Exp_dzzMuIn_of_subadd`: `ω ↦ M^W(B(c,r))` is a.e.-measurable -/
theorem aemeasurable_wickQArea_ball (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (c : ℂ) (r : ℝ) :
    AEMeasurable (fun ω => wickQArea γ W ω (ball c r)) P := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  set U := ball c r ∩ openSquare
  have hU : ∀ ω, wickQArea γ W ω (ball c r) = wickQArea γ W ω U := fun ω => by
    have h0 : wickQArea γ W ω openSquareᶜ = 0 :=
      wickArea_compl γ (qAreaMeasureOn_openSquare_compl γ _)
    rw [← measure_inter_add_sdiff₀ (s := ball c r) (t := openSquare)
      isOpen_openSquare.measurableSet.nullMeasurableSet,
      measure_mono_null (sdiff_subset_compl _ _) h0, add_zero]
  simp only [hU]
  have hg := aemeasurable_wickArea_open_circ hX hγ hγ2 (isOpen_ball.inter isOpen_openSquare)
    (isBounded_ball.subset inter_subset_left) (inter_subset_right (s := ball c r))
  rw [circLaw, map_circVec_eq hX hW] at hg
  exact hg.comp_measurable (measurable_wnCircVec hW)

end DZZ
end LQGMetric
