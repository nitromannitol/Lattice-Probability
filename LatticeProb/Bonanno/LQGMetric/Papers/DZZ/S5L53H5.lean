/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53H5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6E

/-!
# DZZ Lemma 5.3, the `d_i` comparison, part 5: the hypothesis `hd` (P2-DZZ53H)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2380–2391 ((Eq.calD1)): the `d_i` comparison
for all `u ≠ v ∈ 𝕍̄` and the nine boxes, in the exact form of the hypothesis `hd` of
`dzzLem53Exp_dzzMuIn_of_nodes` (S5L53F4):
* **`l53_hd_of_walls`**: from the walled P3.17 at the DG walls for small `ξ` (any `Ω`);
* **`l53_hd_holds`**: unconditional for `Ω : Type`, with `dzzProp317Walls_dzzMuIn` (S5WallSim6E);
* **`dzzLem53Exp_dzzMuIn_of_reg_bad`**: `dzzLem53Exp_dzzMuIn_of_nodes` with `hd` discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **The `d_i` comparison** (`hd` of `dzzLem53Exp_dzzMuIn_of_nodes`) from the walled P3.17 at
the walls `dgWalls` for small `ξ`. -/
theorem l53_hd_of_walls {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) :
    ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i < 9,
      P (l53DiEvent γ W ((2 : ℝ)⁻¹ ^ k) u v i
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
          ((k : ℝ) * Real.log 2) ^ (0.96 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))) := by
  intro u hu v hv huv
  obtain ⟨ξ₂, hξ₂, hw⟩ := hwalls
  have hd : 0 < dist u v := dist_pos.2 huv
  set ξ := min (ξ₂ / 2) (min (dist u v / 2) (1 / 4)) with hξ
  have hξ0 : 0 < ξ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hξ1 : ξ < ξ₂ := (min_le_left _ _).trans_lt (by linarith)
  have hξu : 2 * ξ ≤ dist u v := by
    have := (min_le_right (ξ₂ / 2) _).trans (min_le_left (dist u v / 2) (1 / 4)); linarith
  have hξ4 : ξ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have h317 := dzzProp317In_tildeBox_of_walls (hw ξ hξ0 hξ1) hu hv huv
  choose k₀ hk₀ using fun (i : Fin 9) => l53h_di_one hW hγ hγ2 hu hv huv hξ0 hξu hξ4 h317 i.2
  refine ⟨Finset.univ.sup k₀, fun k hk i hi => hk₀ ⟨i, hi⟩ k ?_⟩
  exact le_trans (Finset.le_sup (f := k₀) (Finset.mem_univ (⟨i, hi⟩ : Fin 9))) hk

/-- **The `d_i` comparison, unconditional** (DZZ l. 2380–2391), for `Ω : Type`. -/
theorem l53_hd_holds {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i < 9,
      P (l53DiEvent γ W ((2 : ℝ)⁻¹ ^ k) u v i
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
          ((k : ℝ) * Real.log 2) ^ (0.96 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))) :=
  l53_hd_of_walls hW hγ hγ2 (dzzProp317WallsAll_holds P W hW γ hγ hγ2)

end DZZ
end LQGMetric
