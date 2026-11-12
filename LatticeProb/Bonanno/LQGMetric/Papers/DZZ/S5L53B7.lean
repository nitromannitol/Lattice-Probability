/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B6

/-!
# The law of `D̃_δ(u,v)` does not depend on the white noise (P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) use throughout that quantities built from the field
`h̃` have a law determined by that of `h̃` (e.g. l. 2318–2322: the coupled copies
`ζ⁽ⁱ⁾` "have the same law as the η-process", and comparisons of expectations across couplings).
Here: `M^W = CR^{−γ²/2} M_γ(circExt (wnCircVec W))` is a function of the white-noise circle family,
whose law is that of any zero-boundary GFF on `𝕍` (`map_circVec_eq`). Hence for any two white noises
`W₁, W₂` (on any probability spaces) `E log D̃_δ(u,v)[W₁] = E log D̃_δ(u,v)[W₂]`
(`integral_logTilde_eq`). Own glue (measurability at the level of the circle law, from
`aemeasurable_wickArea_open_circ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent3

/-- DZZ's internal measure as a function of the circle family -/
def muInOfCirc (γ : ℝ) (c : CircIdx → ℝ) : Measure ℂ :=
  dzzWall dzzV (wickArea γ (qAreaMeasureOn γ (circExt c) openSquare))

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {X : Ω₀ → Measure ℂ → ℝ}

/-- ball masses of the Wick measure are a.e.-measurable under the circle law -/
theorem aemeasurable_wickArea_ball_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ)
    (r : ℝ) :
    AEMeasurable (fun c => wickArea γ (qAreaMeasureOn γ (circExt c) openSquare) (ball z r))
      (circLaw P₀ X) := by
  have hU : ∀ c, wickArea γ (qAreaMeasureOn γ (circExt c) openSquare) (ball z r) =
      wickArea γ (qAreaMeasureOn γ (circExt c) openSquare) (ball z r ∩ openSquare) := fun c => by
    have h0 : wickArea γ (qAreaMeasureOn γ (circExt c) openSquare) openSquareᶜ = 0 :=
      wickArea_compl γ (qAreaMeasureOn_openSquare_compl γ _)
    rw [← measure_inter_add_sdiff₀ (s := ball z r) (t := openSquare)
      isOpen_openSquare.measurableSet.nullMeasurableSet,
      measure_mono_null (sdiff_subset_compl _ _) h0, add_zero]
  simp only [hU]
  exact aemeasurable_wickArea_open_circ hX hγ hγ2 (isOpen_ball.inter isOpen_openSquare)
    (isBounded_ball.subset inter_subset_left) (inter_subset_right (s := ball z r))

/-- `c ↦ log D̃_δ(u,v)` is a.e.-measurable under the circle law -/
theorem aemeasurable_logTilde_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (K : Set ℂ)
    (δ : ℝ) (u v : ℂ) :
    AEMeasurable (fun c => logMinLGD (dzzWall K (muInOfCirc γ c)) δ {u} {v}) (circLaw P₀ X) := by
  have hbm : ∀ (z : ℂ) (r : ℝ), AEMeasurable
      (fun c => dzzWall K (muInOfCirc γ c) (ball z r)) (circLaw P₀ X) := fun z r => by
    simp only [dzzWall, muInOfCirc, Measure.add_apply, Measure.smul_apply]
    exact ((aemeasurable_wickArea_ball_circ hX hγ hγ2 z r).add aemeasurable_const).add
      aemeasurable_const
  simp only [logMinLGD_singleton]
  exact measurable_log_toNat.comp_aemeasurable (aemeasurable_lgdDZZ hbm δ u v)

/-- `E log D̃_δ(u,v)[W]` is the integral under the circle law -/
theorem integral_logTilde_eq_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (δ : ℝ) (u v : ℂ) :
    ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ {u} {v} ∂P =
      ∫ c, logMinLGD (dzzWall K (muInOfCirc γ c)) δ {u} {v} ∂(circLaw P₀ X) := by
  have hG := aemeasurable_logTilde_circ hX hγ hγ2 K δ u v
  rw [circLaw, map_circVec_eq hX hW] at hG ⊢
  rw [integral_map (measurable_wnCircVec hW).aemeasurable hG.aestronglyMeasurable]
  rfl

/-- **The law of `log D̃_δ(u,v)` does not depend on the white noise**: for any two white noises,
`E log D̃_δ(u,v)` is the same. -/
theorem integral_logTilde_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {W₁ : WNSpace → Ω₁ → ℝ} {W₂ : WNSpace → Ω₂ → ℝ}
    (hW₁ : IsWhiteNoise P₁ W₁) (hW₂ : IsWhiteNoise P₂ W₂) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (δ : ℝ) (u v : ℂ) :
    ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W₁ ω)) δ {u} {v} ∂P₁ =
      ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W₂ ω)) δ {u} {v} ∂P₂ := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  rw [integral_logTilde_eq_circ hX hW₁ hγ hγ2, integral_logTilde_eq_circ hX hW₂ hγ hγ2]

end DZZ
end LQGMetric
