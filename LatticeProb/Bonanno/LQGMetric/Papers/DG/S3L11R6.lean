/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11R6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R5
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc5

/-!
# DG Lemma 3.11 at `μ = μ_ĥ` without the locality hypothesis (P2-DG105r)

Node 2(a) (`L311TrLocal`, S3L11R1, DG:1267–1268) follows from P2-DGLOC's `dgLocTr_proved`
(S3L11Loc5) at the unit-frame square `sqOne (1/32) l311UnitB (0,0) ⊆ K₀` (`l311_unit_sub`).
So the single-square inputs of DG Lemma 3.11 at `μ = μ_ĥ` hold for horizontal
(`l311LevelInput_muHat`, S3L11R3) and vertical (`l311LevelInputV_muHat`, S3L11R5) rectangles
with DZZ Lemma 5.3 (`hDZZ`) as the only input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **node 2(a)** (DG:1267–1268), from P2-DGLOC's `dgLocTr_proved` -/
theorem l311TrLocal_proved (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), Metric.ball z (1 / 10) ⊆ openSquare) :
    L311TrLocal P hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK := fun j c ε M =>
  dgLocTr_proved hγ hγ2 _ hK j c (dgN5_wnScaleDy hW j c).1 l311_unit_sub ε M

/-- **the single-square inputs of DG Lemma 3.11 at `μ = μ_ĥ`**, given DZZ Lemma 5.3 only -/
theorem l311LevelInput_muHat' (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hd : 1 ≤ 2 / χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    {Q : Set ℂ} (hQ : Q ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    L311LevelInput P W (fun ω => muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK ω) γ (2 / χ) Q :=
  l311LevelInput_muHat hW hγ hγ2 hK hχ hd hDZZ (l311TrLocal_proved hW hγ hγ2 hK) hQ

/-- **the single-square inputs of DG Lemma 3.11 for vertical rectangles at `μ = μ_ĥ`**, given
DZZ Lemma 5.3 only -/
theorem l311LevelInputV_muHat' (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), Metric.ball z (1 / 10) ⊆ openSquare)
    {χ : ℝ} (hχ : 0 < χ) (hd : 1 ≤ 2 / χ) (hDZZ : DZZL53Whp P (DZZ.dzzMuIn γ W) χ)
    {Q : Set ℂ} (hQ : Q ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    L311LevelInputV P W (fun ω => muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK ω) γ (2 / χ)
      Q :=
  l311LevelInputV_muHat hW hγ hγ2 hK hχ hd hDZZ (l311TrLocal_proved hW hγ hγ2 hK) hQ

end DG
end LQGMetric
