/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32X
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPosGreen
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass

/-!
# D97, packet P-1: the Wick-normalised chaos `M^W = CR^{−γ²/2} · M_γ` and the `CR` bounds

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-M-eta), l. 1209–1213) work with the chaos
`M_γ^{h̃}` of the white-noise field `h̃`, normalised by `E h̃_{2^{-n}}(z)²` (Wick). The
Duplantier–Sheffield measure `M_γ = qAreaMeasureOn γ h openSquare` carries the extra factor
`CR(z)^{γ²/2} = e^{γ²/2 hS(z,z)}` (GMCIdentMain, `wnWeight`; GMCIdent4Fact, `cDens`). Decision D97
(decisions/DEC-97.md §3, §6 P-1):

* `wickArea γ μ := CR^{−γ²/2} · μ`, `wickQArea γ W ω := wickArea γ (M_γ(wnField W ω))`, and DZZ's
  internal measure `dzzMuIn γ W ω := dzzWall dzzV (wickQArea γ W ω)`;
* `withDensity_wickArea`: `μ = CR^{γ²/2} · wickArea γ μ`;
* **`le_wickArea`** (`hup` of `lgd_sandwich_dzzWall`): `μ(A) ≤ 3^{γ²/2} · wickArea γ μ (A)` when
  `μ` lives on `𝕍` (`hS ≤ log 3`, `GMCPos.hS_le_log_three`);
* **`wickArea_le_of_compact`** (`hlow`): for a compact `K ⊆ (0,1)²` there is `b` with
  `wickArea γ μ (A) ≤ e^b μ(A)` for `A ⊆ K` (`hS(z,z)` continuous on `(0,1)²`,
  `GMCIdent4.continuousOn_hS_diag`).

Own elementary glue (D97).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- `CR(z)^{−γ²/2} = e^{−γ²/2 hS(z,z)}` -/
def wickDens (γ : ℝ) (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(γ ^ 2 / 2) * hS z z))

/-- `CR(z)^{γ²/2} = e^{γ²/2 hS(z,z)}` -/
def crDens (γ : ℝ) (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * hS z z))

lemma measurable_wickDens (γ : ℝ) : Measurable (wickDens γ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (GMCIdent.measurable_hS_diag.const_mul _))

lemma measurable_crDens (γ : ℝ) : Measurable (crDens γ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (GMCIdent.measurable_hS_diag.const_mul _))

/-- the Wick-normalised measure `CR^{−γ²/2} · μ` -/
def wickArea (γ : ℝ) (μ : Measure ℂ) : Measure ℂ := μ.withDensity (wickDens γ)

/-- DZZ's `M_γ^{h̃}` (eq-def-M-eta) for the white-noise field: `CR^{−γ²/2} M_γ` -/
def wickQArea {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (W : WNSpace → Ω → ℝ) (ω : Ω) :
    Measure ℂ :=
  wickArea γ (qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare)

/-- **DZZ's internal measure for §§3–5** (D97): balls inside `𝕍`, Wick mass. -/
def dzzMuIn {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (W : WNSpace → Ω → ℝ) (ω : Ω) :
    Measure ℂ :=
  dzzWall dzzV (wickQArea γ W ω)

lemma withDensity_wickArea (γ : ℝ) (μ : Measure ℂ) :
    (wickArea γ μ).withDensity (crDens γ) = μ := by
  unfold wickArea
  rw [← withDensity_mul _ (measurable_wickDens γ) (measurable_crDens γ)]
  conv_rhs => rw [← withDensity_one (μ := μ)]
  congr 1
  funext z
  simp only [Pi.mul_apply, Pi.one_apply, wickDens, crDens]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_mul, neg_add_cancel,
    Real.exp_zero, ENNReal.ofReal_one]

lemma wickArea_compl (γ : ℝ) {μ : Measure ℂ} {S : Set ℂ} (h : μ Sᶜ = 0) :
    wickArea γ μ Sᶜ = 0 :=
  withDensity_absolutelyContinuous μ _ h

/-- **`hup`**: `μ(A) ≤ 3^{γ²/2} · CR^{−γ²/2}μ(A)` for `μ` living on `(0,1)²`. -/
theorem le_wickArea (γ : ℝ) {μ : Measure ℂ} (hμ : μ openSquareᶜ = 0) {A : Set ℂ}
    (hA : MeasurableSet A) :
    μ A ≤ ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * Real.log 3)) * wickArea γ μ A := by
  conv_lhs => rw [← withDensity_wickArea γ μ]
  rw [withDensity_apply _ hA, ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  have h1 : ∀ᵐ z ∂(wickArea γ μ), z ∈ openSquare :=
    (mem_ae_iff).2 (wickArea_compl γ hμ)
  filter_upwards [ae_restrict_of_ae h1] with z hz
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_left (GMCPos.hS_le_log_three hz hz) (by positivity)

lemma le_wickQArea {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (W : WNSpace → Ω → ℝ) (ω : Ω)
    {A : Set ℂ} (hA : MeasurableSet A) :
    qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare A ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * Real.log 3)) * wickQArea γ W ω A :=
  le_wickArea γ (qAreaMeasureOn_openSquare_compl γ _) hA

/-- **`hlow`**: on a compact `K ⊆ (0,1)²`, `CR^{−γ²/2}μ(A) ≤ e^b μ(A)` for `A ⊆ K`. -/
theorem wickArea_le_of_compact (γ : ℝ) {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ openSquare) :
    ∃ b : ℝ, ∀ (μ : Measure ℂ) (A : Set ℂ), MeasurableSet A → A ⊆ K →
      wickArea γ μ A ≤ ENNReal.ofReal (Real.exp b) * μ A := by
  obtain ⟨m, hm⟩ : BddBelow ((fun z => hS z z) '' K) :=
    (hK.image_of_continuousOn (GMCIdent4.continuousOn_hS_diag.mono hKV)).bddBelow
  refine ⟨-(γ ^ 2 / 2) * m, fun μ A hA hAK => ?_⟩
  rw [wickArea, withDensity_apply _ hA, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun z hz => ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hm ⟨z, hAK hz, rfl⟩
  have h2 : (0 : ℝ) ≤ γ ^ 2 / 2 := by positivity
  nlinarith

end DZZ
end LQGMetric
