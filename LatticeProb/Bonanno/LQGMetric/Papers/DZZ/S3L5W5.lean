/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCells

/-!
# Walled DZZ Lemma 3.5, W5: enclosures relative to the wall around all `δ`-cells (P2-DZZL35W)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1047–1049) with Remark 5.2 (l. 2281–2284): with high
probability every `δ`-cell inside the dyadic wall `B̄w` has an enclosure relative to the wall.
Copy of `l37_cells_enc` (S3L7FinCells, P2-DZZ3G): the union bound runs over the pulled-back boxes
`b` (`1 ≤ b.n`, real level `n_{wEmb Bw b} ≤ C_mc log₂ δ⁻¹`), with `dzz_lemma37_percW` (S3L5W4).

* `allCellsEncW`, **`l37_cells_encW`** (uniform in the wall `Bw`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The event that, if the wall `Bw` is split at `δ`, every `δ`-cell inside `B̄w` has an enclosure
relative to the wall (`𝓔_{δ',𝖢,ε,λ}` of Def 3.6 with Remark 5.2), in pulled-back form. -/
def allCellsEncW (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' : ℝ) (Bw : DyBox) : Set Ω :=
  {ω | WSplit (approxLQG γ W ω) δ Bw → ∀ b, IsCell (fun c => approxLQG γ W ω (wEmb Bw c)) δ b →
    ω ∈ encEventPsiW γ W δ' Bw b (kL37 γ δ) (lamL37 δ δ')}

/-- **Walled DZZ l. 1047–1049** (copy of `l37_cells_enc`): the union bound of the walled
(eq-B-percolation-Phi) over all cells inside the wall, uniformly in the wall. -/
theorem l37_cells_encW (hW : IsWhiteNoise P W) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 4 * dzzCmc γ < α) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ Bw : DyBox,
      P.real (allCellsEncW γ W δ δ' Bw ∩ eventEFine γ W α δ)ᶜ ≤
        δ + P.real (eventEFine γ W α δ)ᶜ := by
  have := hW.isProbabilityMeasure
  obtain ⟨δ₁, hδ₁, hperc⟩ := dzz_lemma37_percW hW hγ hγ2 hα
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  refine ⟨min δ₁ (1 / 2), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ δ' hδ' Bw
  have hδa : δ < δ₁ := hδ.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := by linarith [hδ.trans_le (min_le_right _ _)]
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL0 : 0 < L := by
    rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hKr : 0 ≤ C * Real.logb 2 δ⁻¹ := by
    rw [Real.logb, ← hLdef]; positivity
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  have hK : (K : ℝ) ≤ C * L / Real.log 2 := by
    calc (K : ℝ) ≤ C * Real.logb 2 δ⁻¹ := Nat.floor_le hKr
      _ = C * L / Real.log 2 := by rw [Real.logb, ← hLdef, mul_div_assoc]
  set Bad : DyBox → Set Ω := fun b => if (wEmb Bw b).n ≤ K then
    {ω | approxLQG γ W ω (wEmb Bw b) ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      (encEventPsiW γ W δ' Bw b (kL37 γ δ) (lamL37 δ δ'))ᶜ else ∅ with hBad
  have hsub : (allCellsEncW γ W δ δ' Bw ∩ eventEFine γ W α δ)ᶜ ⊆ (eventEFine γ W α δ)ᶜ ∪
      ⋃ n ∈ Finset.Icc 1 K, {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad b} := by
    intro ω hω
    by_cases hE : ω ∈ eventEFine γ W α δ
    · right
      have hn : ¬ (WSplit (approxLQG γ W ω) δ Bw → ∀ b,
          IsCell (fun c => approxLQG γ W ω (wEmb Bw c)) δ b →
          ω ∈ encEventPsiW γ W δ' Bw b (kL37 γ δ) (lamL37 δ δ')) := fun h => hω ⟨h, hE⟩
      push Not at hn
      obtain ⟨hsp, b', hb', hnot⟩ := hn
      have hn1 : 1 ≤ b'.n := not_isCell_root_of_split hsp b' hb'
      have hb := (isCell_wEmb_iff hsp).2 hb'
      set b := wEmb Bw b' with hbdef
      obtain ⟨hs1, hs2⟩ := hE.1.2 b hb
      have hnK : b.n ≤ K := by
        rw [hKdef]; apply Nat.le_floor
        have h1 := Real.log_le_log (by positivity) hs1
        rw [Real.log_rpow hδ0, hlogδ] at h1
        have h2 : Real.log b.side = -(b.n * Real.log 2) := by
          unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
        rw [h2] at h1
        rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
        linarith
      have hnK' : b'.n ≤ K := by have : b.n = Bw.n + b'.n := rfl; omega
      refine mem_iUnion₂.2 ⟨b'.n, Finset.mem_Icc.2 ⟨hn1, hnK'⟩, b', rfl, ?_⟩
      show ω ∈ Bad b'
      simp only [Bad]; rw [if_pos hnK]
      exact ⟨⟨hb.1.le, hE⟩, hnot⟩
    · left; exact hE
  have hlevel : ∀ n ∈ Finset.Icc 1 K,
      P.real {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad b} ≤ ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) := by
    intro n hn
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
    refine measureReal_level_le n Bad fun b hb => ?_
    by_cases hbK0 : (wEmb Bw b).n ≤ K
    · have hbK : ((wEmb Bw b).n : ℝ) ≤ C * Real.logb 2 δ⁻¹ :=
        (Nat.cast_le.2 hbK0).trans (Nat.floor_le hKr)
      simp only [Bad]; rw [if_pos hbK0]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hperc δ ⟨hδ0, hδa⟩ δ' hδ' Bw b (hb ▸ hn1) hbK)
    · simp only [Bad]; rw [if_neg hbK0, measureReal_empty]
      positivity
  have hterm : ∀ n ∈ Finset.Icc 1 K, ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤
      Real.exp (-((8 * C + 10) * L)) := by
    intro n hn
    have hnK := (Finset.mem_Icc.1 hn).2
    have hnL : (n : ℝ) * Real.log 2 ≤ C * L := by
      have : (n : ℝ) ≤ K := by exact_mod_cast hnK
      have := mul_le_mul_of_nonneg_right (this.trans hK) hlog2.le
      rwa [div_mul_cancel₀ _ hlog2.ne'] at this
    rw [two_pow_sq_eq, Real.rpow_def_of_pos hδ0, hlogδ, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hsum : ∑ n ∈ Finset.Icc 1 K, ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤ δ := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show K + 1 - 1 = K by omega]
    have hKL : (K : ℝ) ≤ 2 * C * L := by
      refine hK.trans ?_
      rw [div_le_iff₀ hlog2]
      have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
      linarith
    have hex : 2 * C * L ≤ Real.exp ((8 * C + 9) * L) := by
      have := Real.add_one_le_exp ((8 * C + 9) * L); nlinarith
    have hδe : δ = Real.exp (-L) := by rw [← hlogδ, Real.exp_log hδ0]
    calc (K : ℝ) * Real.exp (-((8 * C + 10) * L)) ≤
          Real.exp ((8 * C + 9) * L) * Real.exp (-((8 * C + 10) * L)) :=
          mul_le_mul_of_nonneg_right (hKL.trans hex) (Real.exp_pos _).le
      _ = δ := by rw [← Real.exp_add, hδe]; congr 1; ring
  calc P.real (allCellsEncW γ W δ δ' Bw ∩ eventEFine γ W α δ)ᶜ
      ≤ P.real ((eventEFine γ W α δ)ᶜ ∪
          ⋃ n ∈ Finset.Icc 1 K, {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad b}) := measureReal_mono hsub
    _ ≤ P.real (eventEFine γ W α δ)ᶜ +
          P.real (⋃ n ∈ Finset.Icc 1 K, {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad b}) :=
        measureReal_union_le _ _
    _ ≤ P.real (eventEFine γ W α δ)ᶜ + δ := by
        gcongr
        exact (measureReal_biUnion_finset_le _ _).trans
          ((Finset.sum_le_sum hlevel).trans hsum)
    _ = δ + P.real (eventEFine γ W α δ)ᶜ := add_comm _ _

end DZZ
end LQGMetric
