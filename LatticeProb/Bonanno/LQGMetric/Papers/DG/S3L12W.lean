/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L12W at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L20B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W7

/-!
# DG Lemmas 3.12 and 3.20 at DZZ's internal measure `μIn = dzzMuIn γ W` (P2-DG105h, D105 P9)

`dg_lemma312` and `dg_lemma320` with DZZ's measure `ν = dzzMuIn γ W = dzzWall 𝕍̄ (CR^{−γ²/2} μ_{h^𝕍})`
(decision D97; the measure of `DZZ.DZZProp317` in D105 N9): the comparisons `hν` are discharged by
`DZZ.le_wickQArea` / `DZZ.le_dzzWall` (L3.12) and `DZZ.wickArea_le_of_compact` /
`DZZ.dzzWall_ball_of_subset` (L3.20). The only remaining inputs are the DZZ statements
`DZZL53Whp P (dzzMuIn γ W) χ` and `DZZL61Whp P (dzzMuIn γ W) α χ u`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DG Lemma 3.12 at `μIn`** (DG:1204–1216) -/
theorem dg_lemma312_muIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {y : ℂ} {b : ℝ}
    (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    {c : ℂ} {s : ℝ} (hs : 0 < s) (hmid : l312Mids c s ⊆ l312Vbar)
    (hS : l312Sq1 c s ⊆ ferniqueBox y b) {ζ : ℝ} (hζ : 0 < ζ) (hζd : ζ < 2 / χ) :
    Tendsto (fun ε => P {ω | ¬ ∀ u ∈ l312Mids c s, ∀ v ∈ l312Mids c s,
      ((dgLGD (muTr hW γ hb hK ω) ε (l312Sq1 c s) u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-(1 / (2 / χ - ζ))))}) (𝓝[>] 0) (𝓝 0) :=
  dg_lemma312 hW hγ hb hK (ν := DZZ.dzzMuIn γ W) (a := γ ^ 2 / 2 * Real.log 3)
    (fun ω x r => (DZZ.le_wickQArea γ W ω measurableSet_ball).trans
      (by gcongr; exact DZZ.le_dzzWall _ _)) hχ hDZZ hs hmid hS hζ hζd

/-- **DG Lemma 3.20 at `μIn`** (DG:1625–1636) -/
theorem dg_lemma320_muIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {u : ℂ} (hR : closedBall u (1 / 10) ⊆ ferniqueBox y b)
    {α χ : ℝ} (hα : α < 1) (hχ : 0 < χ) (hDZZ : DZZL61Whp P (DZZ.dzzMuIn γ W) α χ u)
    {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ε => P {ω | ¬ ∀ z ∈ l312Box u (α / 20), ∀ w ∈ frontier (l312Box u (1 / 20)),
      ENNReal.ofReal (ε ^ (-(1 / (2 / χ + ζ)))) ≤
        ((dgLGD (muTr hW γ hb hK ω) ε univ z w : ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0) := by
  have hRV : closedBall u (1 / 10) ⊆ openSquare := hR.trans (ferniqueBox_subset hK)
  obtain ⟨b', hb'⟩ := DZZ.wickArea_le_of_compact γ (isCompact_closedBall u (1 / 10)) hRV
  refine dg_lemma320 hW hγ hγ2 hb hK hR (b' := b') (fun ω x r hsub => ?_) hα hχ hDZZ hζ
  rw [DZZ.dzzMuIn, DZZ.dzzWall_ball_of_subset _
    ((hsub.trans hRV).trans DZZ.openSquare_subset_dzzV)]
  exact hb' _ _ measurableSet_ball hsub

end DG
end LQGMetric
