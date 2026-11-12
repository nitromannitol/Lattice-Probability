/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32K5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K2

/-!
# Walled P3.2, K5: the lower-half input for a dyadic wall and the cells inside it (P2-DZZ317K)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1160–1168 with Remark 5.2 (l. 2281–2284), D117 §3,
for the wall `K = B̄` (the closed dyadic box of `B`) and the cell family `cellsInside B` (the
cells contained in `B̄`). For this family the walled `D'` is the `D'` of the dyadic partition of
`B̄` itself (all cells of level `≥ B.n` meeting the interior of `B̄` lie in `B̄`), which is the
family recommended in `handoff/P2-DZZ317K.md` for the open upper half (grid-aligned walls, as
for `𝕍` in D102).

* `closedBox_sub_of_ball`: a dyadic box of level `≥ B.n` meeting a ball inside `B̄` lies in `B̄`;
* **`l32BallCoverOn_inside_dzzMuIn`**:
  `L32BallCoverOn P γ W (cellsInside B) (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω))`,
  unconditional (on Lemma 3.1 at `δ'` every cell has level `≥ B.n` for small `δ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

universe u

/-- The dyadic boxes contained in the closed box of `B`. -/
def cellsInside (B : DyBox) : Set DyBox := {b | b.closedBox ⊆ B.closedBox}

/-- A dyadic box of level `≥ B.n` containing a point of an open ball inside `B̄` lies in `B̄`. -/
lemma closedBox_sub_of_ball {B T : DyBox} (hn : B.n ≤ T.n) {x z : ℂ} {ρ : ℝ}
    (hball : Metric.ball x ρ ⊆ B.closedBox) (hz : z ∈ Metric.ball x ρ)
    (hzT : z ∈ T.closedBox) : T.closedBox ⊆ B.closedBox := by
  set T' := T.anc B.n with hT'
  have hT'n : T'.n = B.n := anc_n_of_le hn
  have hzT' : z ∈ T'.closedBox := closedBox_sub_anc T B.n hzT
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 (Metric.isOpen_ball.mem_nhds hz)
  have hs : T'.side = B.side := by unfold DyBox.side; rw [hT'n]
  set s := B.side with hsdef
  have hs0 : 0 < s := by rw [hsdef]; unfold DyBox.side; positivity
  have mem : ∀ w : ℂ, ‖w‖ < ε → z + w ∈ B.closedBox := fun w hw =>
    hball (hεb (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hw))
  have he2 : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  have he2' : ‖-((ε / 2 : ℝ) : ℂ)‖ < ε := by rw [norm_neg]; exact he2
  have he3 : ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ < ε := by
    rw [norm_mul, Complex.norm_I, mul_one]; exact he2
  have he3' : ‖-(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ < ε := by rw [norm_neg]; exact he3
  obtain ⟨-, a2, -, -⟩ := mem _ he2
  obtain ⟨b1, -, -, -⟩ := mem _ he2'
  obtain ⟨-, -, -, c2⟩ := mem _ he3
  obtain ⟨-, -, d1, -⟩ := mem _ he3'
  simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero] at a2 b1 c2 d1
  obtain ⟨t1, t2, t3, t4⟩ := hzT'
  rw [hs] at t1 t2 t3 t4
  have hj1 : (T'.j : ℝ) < B.j + 1 := lt_of_mul_lt_mul_right (by linarith) hs0.le
  have hj2 : (B.j : ℝ) < T'.j + 1 := lt_of_mul_lt_mul_right (by linarith) hs0.le
  have hk1 : (T'.k : ℝ) < B.k + 1 := lt_of_mul_lt_mul_right (by linarith) hs0.le
  have hk2 : (B.k : ℝ) < T'.k + 1 := lt_of_mul_lt_mul_right (by linarith) hs0.le
  have ej : T'.j = B.j := by
    have h1 : T'.j < B.j + 1 := by exact_mod_cast hj1
    have h2 : B.j < T'.j + 1 := by exact_mod_cast hj2
    omega
  have ek : T'.k = B.k := by
    have h1 : T'.k < B.k + 1 := by exact_mod_cast hk1
    have h2 : B.k < T'.k + 1 := by exact_mod_cast hk2
    omega
  have hTB : T' = B := DyBox.ext hT'n ej ek
  rw [← hTB]
  exact closedBox_sub_anc T B.n

/-- Cells of side `≤ B.side` have level `≥ B.n`. -/
lemma level_ge_of_side_le {B b : DyBox} (h : b.side ≤ B.side) : B.n ≤ b.n := by
  by_contra hlt
  push Not at hlt
  have : B.side < b.side := by
    unfold DyBox.side; exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
  linarith

variable {Ω : Type u} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The walled ball-cover inclusion for the cells inside `B̄`, when all `δ'`-cells have side
`≤ B.side`. -/
theorem ballCover_inter_cellSize_subsetInside (B : DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ)
    (ν : Ω → Measure ℂ) {δ : ℝ} (hδ : 0 < p32Up δ) (hsm : p32Up δ ^ dzzCMc γ ≤ B.side) :
    ballCoverEvent γ W ν δ ∩ cellSizeEvent γ W (p32Up δ) ⊆
      {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        approxLGDOn (cellsInside B) γ W (p32Up δ) u v ω ≤
          4 * lgdDZZ (dzzWall B.closedBox (dzzWall dzzV (ν ω))) δ u v} := by
  rintro ω ⟨hcov, hpart, hside⟩ u hu v hv
  obtain ⟨N₀, hN₀⟩ := exists_level_bound (Real.rpow_pos_of_pos hδ (dzzCmc γ))
    fun b hb => (hside b hb).1
  have hK : IsClosed B.closedBox := by
    have : B.closedBox = (fun z : ℂ => z.re) ⁻¹' Icc (B.j * B.side) ((B.j + 1) * B.side) ∩
        (fun z : ℂ => z.im) ⁻¹' Icc (B.k * B.side) ((B.k + 1) * B.side) := by
      ext z; simp only [DyBox.closedBox, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc]
      tauto
    rw [this]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  exact approxDistOn_le_four_mul_lgd hK (cellsInside B)
    (fun T hT _ _ z hK' hz hzT => closedBox_sub_of_ball
      (level_ge_of_side_le ((hside T hT).2.trans hsm)) hK' hz hzT) hpart hN₀ (hcov · ·) hu hv

/-- **The lower-half input of the walled P3.2 at `μIn` for a dyadic wall**, with the cells inside
the wall, unconditional. -/
theorem l32BallCoverOn_inside_dzzMuIn {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (B : DyBox) :
    L32BallCoverOn P γ W (cellsInside B) (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω)) := by
  have hcmp := highProb_cellCompare' hW hγ hγ2
    (l32CellCompareBox_of_lower hW hγ hγ2 (l32TildeMLower_wickQArea hW hγ hγ2))
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ :=
    (hcmp.inter (highProb_cellSize_p32Up hW hγ hγ2)).inter (highProb_cellSize_p32Up hW hγ hγ2)
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := 1) (b := 0) one_pos
  have hCM : 0 < dzzCMc γ := dzzCMc_pos γ
  have hB0 : 0 < B.side := by unfold DyBox.side; positivity
  set δb : ℝ := B.side ^ (2 / dzzCMc γ) with hδb
  have hδb0 : 0 < δb := Real.rpow_pos_of_pos hB0 _
  refine ⟨c, hc, min δ₀ (min δa δb), lt_min hδ₀ (lt_min hδa hδb0), fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδ₀' : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδa' : δ < δa := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδb' : δ < δb := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsq := p32Up_le_sqrt hδ0 (hasym δ ⟨hδ0, hδa'⟩).1
  have hsm : p32Up δ ^ dzzCMc γ ≤ B.side := by
    calc p32Up δ ^ dzzCMc γ ≤ (δ ^ (1 / 2 : ℝ)) ^ dzzCMc γ :=
          Real.rpow_le_rpow (p32Up_pos hδ0).le hsq hCM.le
      _ = δ ^ (dzzCMc γ / 2) := by rw [← Real.rpow_mul hδ0.le]; ring_nf
      _ ≤ δb ^ (dzzCMc γ / 2) := Real.rpow_le_rpow hδ0.le hδb'.le (by positivity)
      _ = B.side := by
          rw [hδb, ← Real.rpow_mul hB0.le, show 2 / dzzCMc γ * (dzzCMc γ / 2) = 1 by
            field_simp, Real.rpow_one]
  refine (measure_mono (compl_subset_compl.2 ?_)).trans (h δ ⟨hδ0, hδ₀'⟩)
  rintro ω ⟨hω1, hω2⟩
  exact ballCover_inter_cellSize_subsetInside B γ W (wickQArea γ W) (p32Up_pos hδ0) hsm
    ⟨cellCompare'_inter_subset γ W _ δ hω1, hω2⟩

end DZZ
end LQGMetric
