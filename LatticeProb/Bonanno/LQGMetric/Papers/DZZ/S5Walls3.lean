/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Walls3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G0
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2

/-!
# The leg walls are DG walls; DZZ Lemma 5.4 at `μIn` from `DZZProp317Walls` (P-317K-ADAPT)

DEC-123 §2 (`legWalls u ⊆ dgWalls` for `u ∈ 𝕍̄`: squares of side `1/10` centred within `1/40` of
`u`, inside `𝕍`) and §4 rows P-54LEG / P-317K-ADAPT. DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`,
Lemma 5.4 l. 2299–2304, proof l. 2550–2578, with Proposition 3.17 for the walled distances
(Remark 5.2, l. 2281–2284).

* **`legWalls_subset_dgWalls`**;
* `dzzProp317Leg_of_walls`: `DZZProp317Leg` from `DZZProp317Walls … dgWalls`
  (`dzzProp317Leg_of_In`, S5L54G0);
* **`dzzLem54Exp_dzzMuIn_walls`**: `dzzLem54Exp_dzzMuInQ` (S5L54F2) with both walled P3.17
  hypotheses supplied by `DZZProp317Walls P μIn ξ dgWalls`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

lemma legWalls_subset_dgWalls {u : ℂ} (hu : u ∈ dzzVbar) : legWalls u ⊆ dgWalls := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  rw [abs_le] at h1 h2
  rintro K (rfl | ⟨j, rfl⟩)
  · exact sqBox_mem_dgWalls (abs_le.2 ⟨by linarith, by linarith⟩)
      (abs_le.2 ⟨by linarith, by linarith⟩)
  · rw [legSq, show (2 * (1 / 20) : ℝ) = 1 / 10 by norm_num]
    apply sqBox_mem_dgWalls <;>
    fin_cases j <;> simp only [legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] <;>
      rw [abs_le] <;> constructor <;> nlinarith

lemma dzzProp317Leg_of_walls {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ} (hξ : 0 < ξ)
    (hξ' : ξ ≤ 1 / 40) (h : DZZProp317Walls P μ ξ dgWalls) {u : ℂ} (hu : u ∈ dzzVbar) :
    DZZProp317Leg P μ ξ u :=
  dzzProp317Leg_of_In hξ hξ' hu fun K hK => h K (legWalls_subset_dgWalls hu hK)

/-- **DZZ Lemma 5.4 at `μIn`** (`dzzLem54Exp_dzzMuInQ`, S5L54F2) with the walled P3.17 at
`𝕍_{u,1/10}` and at the leg walls from `DZZProp317Walls P μIn ξ dgWalls`. -/
theorem dzzLem54Exp_dzzMuIn_walls {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hmeas : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => wickQArea γ W ω (Metric.ball c r)) P)
    {χ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 40) (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    (hbig : DZZBigBalls P (dzzMuIn γ W) (1 / 80))
    (hseg : DZZLem54SegQ P (dzzMuIn γ W) χ) : DZZLem54Exp P (dzzMuIn γ W) χ :=
  dzzLem54Exp_dzzMuInQ hW hγ hγ2 hmeas hξ hξ1 hL
    (fun _ hu => dzzProp317In_sqBox_of_walls h317 hu)
    (fun _ hu => dzzProp317Leg_of_walls hξ hξ1 h317 hu) hbig hseg

end DZZ
end LQGMetric
