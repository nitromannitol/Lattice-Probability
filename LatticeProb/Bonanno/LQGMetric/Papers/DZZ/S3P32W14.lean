/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W14 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12

/-!
# D97, packet P-3: (eq-cell-LQG-compare) only for boxes of side `≥ δ'^{C_mc}`

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1185–1186): "one can check (eq-cell-LQG-compare),
noting that the event there is not empty only for `s ≥ (δ')^{C_Mc}`". On the event of Lemma 3.1
at `δ'` every cell has side `≥ δ'^{C_mc}`, so a dyadic box of smaller side lies inside a cell and
needs no mass comparison. Here:

* `ballInCells_of_sqCell` (deterministic): a ball is covered by 4 cells as soon as every closed
  level-`n` box meeting it (`2^{-n} ∈ [2r, 4r)`) lies inside a cell (`IsSqCell`);
* `cellCompareEvent'`: (eq-cell-LQG-compare) for boxes of side `≥ δ'^{C_mc}`;
* **`l32BallCover_of_cellCompare'`**: `cellCompareEvent'` w.h.p. gives `L32BallCover` at
  `dzzWall dzzV ν`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- A ball is covered by 4 cells if every level-`n` box meeting it lies inside a cell. -/
theorem ballInCells_of_sqCell {m : DyBox → ℝ} {δ' : ℝ} {x : ℂ} {ρ : ℝ} (hV : ball x ρ ⊆ dzzV)
    (hsq : ∀ B : DyBox, B.side / 4 < ρ → ρ ≤ B.side / 2 → (B.closedBox ∩ ball x ρ).Nonempty →
      ∃ T, IsSqCell m δ' B T) :
    BallInCells m δ' (ball x ρ) := by
  classical
  rcases le_or_gt ρ 0 with hρ | hρ
  · refine ⟨∅, by simp, 0, fun t _ hne => ?_⟩
    obtain ⟨z, -, hz⟩ := hne
    rw [ball_eq_empty.2 hρ] at hz
    exact absurd hz (notMem_empty z)
  have hρ2 := radius_le_half hV
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 1 / (2 * ρ)) (y := 2)
    (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num)
  set s : ℝ := (2 : ℝ)⁻¹ ^ n with hsdef
  have hs0 : 0 < s := by positivity
  have hs2 : (2 : ℝ) ^ n * s = 1 := by rw [hsdef, inv_pow, mul_inv_cancel₀ (by positivity)]
  have hsa : 2 * ρ ≤ s := by
    rw [le_div_iff₀ (by positivity)] at hn1
    nlinarith
  have hsb : s / 4 < ρ := by
    rw [div_lt_iff₀ (by positivity), pow_succ] at hn2
    nlinarith
  set Bs : Finset DyBox := (finite_level n).toFinset.filter
    fun B => (B.closedBox ∩ ball x ρ).Nonempty with hBs
  have memBs : ∀ B ∈ Bs, B.n = n ∧ (B.closedBox ∩ ball x ρ).Nonempty := by
    intro B hB
    rw [hBs, Finset.mem_filter, Set.Finite.mem_toFinset] at hB
    exact hB
  have hside : ∀ B ∈ Bs, B.side = s := fun B hB => by
    rw [hsdef, DyBox.side, (memBs B hB).1]
  -- at most 4 boxes
  set F : ℤ := ⌊(x.re - ρ) / s⌋
  set G : ℤ := ⌊(x.im - ρ) / s⌋
  have hcard : Bs.card ≤ 4 := by
    have hT : (({F, F + 1} : Finset ℤ) ×ˢ ({G, G + 1} : Finset ℤ)).card ≤ 4 := by
      rw [Finset.card_product]
      have h1 := Finset.card_le_two (a := F) (b := F + 1)
      have h2 := Finset.card_le_two (a := G) (b := G + 1)
      nlinarith
    refine le_trans (Finset.card_le_card_of_injOn (fun B : DyBox => ((B.j : ℤ), (B.k : ℤ)))
      ?_ ?_) hT
    · intro B hB
      obtain ⟨hBn, z, ⟨z1, z2, z3, z4⟩, hz⟩ := memBs B hB
      rw [hside B hB] at z1 z2 z3 z4
      have hzx : ‖z - x‖ < ρ := by rw [mem_ball, dist_eq_norm] at hz; exact hz
      have hre := abs_lt.1 ((Complex.abs_re_le_norm _).trans_lt hzx)
      have him := abs_lt.1 ((Complex.abs_im_le_norm _).trans_lt hzx)
      simp only [Complex.sub_re, Complex.sub_im] at hre him
      obtain ⟨c1, c2⟩ := col_mem (c := x.re) hs0 hsa z1 z2 (by linarith) (by linarith)
      obtain ⟨c3, c4⟩ := col_mem (c := x.im) hs0 hsa z3 z4 (by linarith) (by linarith)
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton]
      constructor <;> omega
    · intro B hB B' hB' h
      simp only [Prod.mk.injEq, Nat.cast_inj] at h
      exact DyBox.ext ((memBs B hB).1.trans (memBs B' hB').1.symm) h.1 h.2
  have hcov : ∀ B ∈ Bs, ∃ T, IsSqCell m δ' B T := fun B hB =>
    hsq B (by rw [hside B hB]; exact hsb) (by rw [hside B hB]; linarith) (memBs B hB).2
  set cellOf : DyBox → DyBox := fun B =>
    if h : ∃ T, IsSqCell m δ' B T then h.choose else B with hcellOf
  refine ⟨Bs.image cellOf, Finset.card_image_le.trans hcard, n, fun t ht hne T hT => ?_⟩
  set B := t.anc n with hBdef
  have hBn : B.n = n := anc_n_of_le ht
  have hB : B ∈ Bs := by
    rw [hBs, Finset.mem_filter, Set.Finite.mem_toFinset]
    obtain ⟨z, hz1, hz2⟩ := hne
    exact ⟨hBn, z, closedBox_sub_anc t n hz1, hz2⟩
  have h := hcov B hB
  obtain ⟨hc, hTn, hTa⟩ := h.choose_spec
  have hT' : IsSqCell m δ' t h.choose := by
    refine ⟨hc, by omega, ?_⟩
    calc t.anc h.choose.n = (t.anc n).anc h.choose.n := (anc_anc t (by omega)).symm
      _ = h.choose := hTa
  rw [isSqCell_unique hT hT']
  refine Finset.mem_image.2 ⟨B, hB, ?_⟩
  simp only [hcellOf, h, dite_true]

omit [MeasurableSpace Ω] in
/-- a box below a cell -/
lemma exists_isSqCell_of_light {m : DyBox → ℝ} {δ : ℝ} (B : DyBox) (hB : m B < δ ^ 2) :
    ∃ T, IsSqCell m δ B T := by
  classical
  have h : ∃ i, m (B.anc i) < δ ^ 2 := ⟨B.n, by rw [anc_self le_rfl]; exact hB⟩
  obtain ⟨hle, hcell⟩ := isCell_anc_find B h hB
  exact ⟨B.anc (Nat.find h), hcell, by rw [anc_n_of_le hle]; exact hle,
    by rw [anc_n_of_le hle]⟩

omit [MeasurableSpace Ω] in
/-- a box smaller than every cell lies inside a cell -/
lemma exists_isSqCell_of_small {m : DyBox → ℝ} {δ x : ℝ}
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) (hside : ∀ b, IsCell m δ b → x ≤ b.side)
    {B : DyBox} (hB : B.side < x) : ∃ T, IsSqCell m δ B T := by
  refine exists_isSqCell hpart (N₀ := B.n) (fun b hb => ?_) le_rfl
  by_contra hlt
  push Not at hlt
  have : b.side ≤ B.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
  linarith [hside b hb]

/-- DZZ (eq-cell-LQG-compare) for the boxes of side `≥ δ'^{C_mc}` (l. 1185–1186). -/
def cellCompareEvent' (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) (δ : ℝ) : Set Ω :=
  {ω | ∀ (B : DyBox) (a b : ℕ), a < 4096 → b < 4096 → p32Up δ ^ dzzCmc γ ≤ B.side →
    p32Up δ ^ 2 ≤ approxLQG γ W ω B → sqSB B a b ⊆ dzzV →
      ENNReal.ofReal (δ ^ 2) < ν ω (sqSB B a b)}

omit [MeasurableSpace Ω] in
theorem cellCompare'_inter_subset (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) (δ : ℝ) :
    cellCompareEvent' γ W ν δ ∩ cellSizeEvent γ W (p32Up δ) ⊆ ballCoverEvent γ W ν δ := by
  rintro ω ⟨hcmp, hpart, hsz⟩ c ρ hV hν
  refine ballInCells_of_sqCell hV fun B h1 h2 hne => ?_
  rcases lt_or_ge B.side (p32Up δ ^ dzzCmc γ) with hs | hs
  · exact exists_isSqCell_of_small hpart (fun b hb => (hsz b hb).1) hs
  · refine exists_isSqCell_of_light B ?_
    by_contra hm
    push Not at hm
    obtain ⟨a, b, ha, hb, hsub⟩ := exists_sqSB_sub_ball h1 h2 hne
    have := hcmp B a b ha hb hs hm (hsub.trans hV)
    exact absurd ((measure_mono hsub).trans hν) (not_le.2 this)

/-- Lemma 3.1 at `δ' = δ e^{(log δ⁻¹)^{0.8}}` holds with high probability (in `δ`). -/
theorem highProb_cellSize_p32Up {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    HighProb P fun δ => cellSizeEvent γ W (p32Up δ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := 1) (b := 0) one_pos
  set K := l31const γ with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; unfold l31const; positivity
  refine ⟨1 / 4, by norm_num, min δa (min (1 / 4) ((1 / (1 + K)) ^ (4 : ℝ))), by positivity,
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδa' : δ < δa := hδ.trans_le (min_le_left _ _)
  have hδq : δ < 1 / 4 := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδK : δ < (1 / (1 + K)) ^ (4 : ℝ) := hδ.trans_le ((min_le_right _ _).trans
    (min_le_right _ _))
  have hs := p32Up_le_sqrt hδ0 (hasym δ ⟨hδ0, hδa'⟩).1
  have hsq : δ ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    calc δ ^ (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hδ0.le hδq.le (by norm_num)
      _ = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have p2 := dzz_lemma31_bound hW hγ hγ2 (p32Up_pos hδ0) (hs.trans hsq)
  have h4 : δ ^ (1 / 4 : ℝ) ≤ 1 / (1 + K) := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_mul (by positivity), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  have hsplit : δ ^ (1 / 2 : ℝ) = δ ^ (1 / 4 : ℝ) * δ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hδ0]; norm_num
  have hp0 : 0 ≤ l31const γ * p32Up δ := mul_nonneg hK (p32Up_pos hδ0).le
  refine ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp0).2 p2).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ δ ^ (1 / 4 : ℝ) := by positivity
  have hKq : K * δ ^ (1 / 4 : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h4 hK
    rw [mul_one_div] at this
    exact this.trans ((div_le_one (by positivity)).2 (by linarith))
  calc l31const γ * p32Up δ ≤ K * δ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hs hK
    _ = (K * δ ^ (1 / 4 : ℝ)) * δ ^ (1 / 4 : ℝ) := by rw [hsplit]; ring
    _ ≤ 1 * δ ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hKq h0
    _ = δ ^ (1 / 4 : ℝ) := one_mul _

/-- **P-3 (DZZ l. 1160–1186)**: (eq-cell-LQG-compare) for the boxes of side `≥ δ'^{C_mc}`, with
high probability, gives `L32BallCover` for the internal measure `dzzWall dzzV ν`. -/
theorem l32BallCover_of_cellCompare' {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Ω → Measure ℂ}
    (hcmp : HighProb P (cellCompareEvent' γ W ν)) :
    L32BallCover P γ W (fun ω => dzzWall dzzV (ν ω)) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := hcmp.inter (highProb_cellSize_p32Up hW hγ hγ2)
  exact l32BallCover_of_ballCover hW hγ hγ2 ⟨c, hc, δ₀, hδ₀, fun δ hδ =>
    (measure_mono (compl_subset_compl.2 (cellCompare'_inter_subset γ W ν δ))).trans (h δ hδ)⟩

end DZZ
end LQGMetric
