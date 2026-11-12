/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117E1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117D2
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4LGD

/-!
# D117, packet P-DIH, part 3: the law of `ballMassQ (dzzMuIn γ W)` does not depend on `W`

The law transfer behind DZZ (eq-translation-invariant) (arXiv:1807.00422, l. 2271): equalities in
law of the field give equalities of probabilities of LGD events only if those are functions of
countably many coordinates of the measure (`ballMassQ`). Here:

* `aemeasurable_ballMassQ_dzzWall_circ`: under the circle law of a zero-boundary GFF, all
  rational ball masses of the walled measure are a.e.-measurable (from
  `aemeasurable_wickArea_ball_circ`, S5L53B7);
* **`map_ballMassQ_dzzMuIn_eq`**, **`prob_ballMassQ_dzzMuIn_eq`**: the law of
  `ballMassQ (dzzMuIn γ W)` is the same for every white noise `W` (on any probability space)
  (`GMCIdent4.map_qArea_eq_wn`).

Own elementary glue (DZZ use the equality in law implicitly).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent3 GMCIdent4

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {X : Ω₀ → Measure ℂ → ℝ}

/-- the rational ball masses of the walled Wick measure are a.e.-measurable under the circle law -/
theorem aemeasurable_ballMassQ_dzzWall_circ [IsProbabilityMeasure P₀]
    (hX : IsZeroBoundaryGFFOn openSquare X P₀) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    AEMeasurable (fun v => ballMassQ (dzzWall dzzV
      (wickArea γ (qAreaMeasureOn γ (circExt v) openSquare)))) (circLaw P₀ X) := by
  refine AEMeasurable.of_eval fun c => AEMeasurable.of_eval fun q => ?_
  simp only [ballMassQ, dzzWall_apply_ball]
  exact (aemeasurable_wickArea_ball_circ hX hγ hγ2 _ _).add aemeasurable_const

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- `ballMassQ (dzzMuIn γ W)` is a.e.-measurable -/
theorem aemeasurable_ballMassQ_dzzMuIn {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : AEMeasurable (fun ω => ballMassQ (dzzMuIn γ W ω)) P := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₁, _, P₁, X₁, hP₁, hX₁⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hF := aemeasurable_ballMassQ_dzzWall_circ hX₁ hγ hγ2
  rw [circLaw, map_circVec_eq hX₁ hW] at hF
  exact hF.comp_aemeasurable (measurable_wnCircVec hW).aemeasurable

/-- **the law of `ballMassQ (dzzMuIn γ W)` does not depend on the white noise** -/
theorem map_ballMassQ_dzzMuIn_eq {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    P.map (fun ω => ballMassQ (dzzMuIn γ W ω)) = P'.map (fun ω => ballMassQ (dzzMuIn γ W' ω)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₁, _, P₁, X₁, hP₁, hX₁⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hF := aemeasurable_ballMassQ_dzzWall_circ hX₁ hγ hγ2
  have h1 := map_qArea_eq_wn hX₁ hW γ
    (F := fun μ => ballMassQ (dzzWall dzzV (wickArea γ μ))) hF
  have h2 := map_qArea_eq_wn hX₁ hW' γ
    (F := fun μ => ballMassQ (dzzWall dzzV (wickArea γ μ))) hF
  exact h1.symm.trans h2

/-- **probabilities of ball-mass events of `dzzMuIn` do not depend on the white noise** -/
theorem prob_ballMassQ_dzzMuIn_eq {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : Set (ℚ × ℚ → ℚ → ℝ≥0∞)} (hS : MeasurableSet S) :
    P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S} = P' {ω | ballMassQ (dzzMuIn γ W' ω) ∈ S} := by
  have e1 := Measure.map_apply_of_aemeasurable (aemeasurable_ballMassQ_dzzMuIn hW hγ hγ2) hS
  have e2 := Measure.map_apply_of_aemeasurable (aemeasurable_ballMassQ_dzzMuIn hW' hγ hγ2) hS
  rw [map_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2, e2] at e1
  exact e1.symm

end DZZ
end LQGMetric
