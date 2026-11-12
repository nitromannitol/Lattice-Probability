/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim6D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6C

/-!
# P-317K-SIM, part 6D: the walled P3.17 at every wall of `dgWalls`

DZZ (arXiv:1807.00422) Proposition 3.17 (l. 1505–1517) for the walled distances (Remark 5.2,
l. 2281–2284) at the walls of the DG chain (`dgWalls`, D128), from the walled
(Eq.boundDprime) `L32UpperCrossInside γ B₀ ξ` at the fixed dyadic box `B̄₀ = [1/4,1/2]²`.
Every wall is `θ(B̄₀)` (`wsim_wall_image`); DZZ's proof of P3.17 (l. 1526–1530) is run at
`θB̄₀` through the similarity coupling of `B̄₀` (`dzzSimCoupleU_of_norm_le`, DZZ
lem-scaling-coupling, l. 611–624) with the dyadic inputs at `B̄₀` on the coupling space:
walled P3.2 (`dzz_prop32UOn_of`), walled Cor 3.9 (`cor39_boundOn`), `DZZConcApproxOn`
(`dzzConcApproxOn_inside`) for the reindexed pairs, and the target's crude moments
(`dzzCrudeMomentsEvOn_dzzMuIn`): `wsim_prop317In_image`, **`dzzProp317Walls_dzzMuIn_of`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **Walled DZZ P3.17 at `θB̄₀`** (`0 < ‖a‖ ≤ 1`, `θB̄₀ ⊆ 𝕍^ξ`). -/
theorem wsim_prop317In_image {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80) (h2ξ : 2 * ξ < dzzCMc γ)
    (hX : L32UpperCrossInside γ wsimB₀ ξ) {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1)
    (hKV : simMap a b '' wsimB₀.closedBox ⊆ dzzVXi ξ) :
    DZZProp317In P (fun ω => dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω))
      (simMap a b '' wsimB₀.closedBox) ξ := by
  have hξc : ξ < dzzCMc γ := by linarith
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le hγ hγ2 hξ (by linarith)
    (isClosed_closedBox wsimB₀) (wsimB₀_subset_dzzVXi hξ.le (by linarith)) ha ha1
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hcp⟩ := hcpl b hKV
  have h32 := dzz_prop32UOn_of hW₁ hγ hγ2 hξ h2ξ (l32BallCoverOn_inside_dzzMuIn hW₁ hγ hγ2 wsimB₀)
    (hX hW₁ (2 * ξ) h2ξ) (fun _ h => dzz_lemma35UOn_wall hW₁ hγ hγ2 wsimB₀ hξ h)
  obtain ⟨c', hc', δc, hδc, -, hcor⟩ := cor39_boundOn (by positivity) h32
    (dzz_lemma35UOn_wall hW₁ hγ hγ2 wsimB₀ hξ h2ξ)
  obtain ⟨c₃, hc₃, δ3, hδ3, h32b⟩ := h32
  obtain ⟨c, hc, hconc⟩ := dzzConcApproxOn_inside hW₁ hγ hγ2 wsimB₀ hξ hξc hX
  have hmom := dzzCrudeMomentsEvOn_dzzMuIn hW hγ hγ2
    (wsim_convex_image (convex_closedBox wsimB₀) a b) (cellsInside wsimB₀) hξ
  refine ⟨min (min c₃ (c / 64)) c' / 2 / 2, by positivity, fun A B hAB hKin => ?_⟩
  obtain ⟨hAB', hin'⟩ := wsimPull_isXiAdmissible ha ha1 hξ hξ1 hAB hKin
  obtain ⟨hc1, c₂, hc₂, δ5, hδ5, hc2⟩ := hconc _ _ hAB' hin'
  obtain ⟨K₁, δ6, hδ6, hK₁⟩ := hmom A B hAB hKin
  exact ⟨wsim_conc1 hW hW₁ hW₂ hγ hγ2 ha ha1 hC hcp hξ hξ1 hc₃ hc' hc hδ3 hδc hδ6 h32b hcor
      hAB hKin (fun δ hδ => (hK₁ δ hδ).1) hc1,
    wsim_conc2 hW hW₁ hW₂ hγ hγ2 ha ha1 hC hcp hξ hξ1 hc₃ hc' hc₂ hδ3 hδ5 hδc hδ6 h32b hcor
      hAB hKin (fun δ hδ => (hK₁ δ hδ).1) hc2⟩

/-- **Walled DZZ Proposition 3.17 at every wall of the DG chain** from the walled
(Eq.boundDprime) at the fixed dyadic box `B̄₀ = [1/4,1/2]²`. -/
theorem dzzProp317Walls_dzzMuIn_of {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80) (h2ξ : 2 * ξ < dzzCMc γ)
    (hX : L32UpperCrossInside γ wsimB₀ ξ) :
    DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls := by
  intro K hK
  have hKV : K ⊆ dzzVXi ξ := (wsim_wall_subset_dzzVXi hK).trans (dzzVXi_anti (by linarith))
  obtain ⟨a, b, ha, ha1, rfl⟩ := wsim_wall_image hK
  exact wsim_prop317In_image hW hγ hγ2 hξ hξ1 h2ξ hX ha ha1 hKV

end DZZ
end LQGMetric
