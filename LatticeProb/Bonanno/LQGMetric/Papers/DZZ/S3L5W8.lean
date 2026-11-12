/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W7

/-!
# Walled DZZ Lemma 3.5, W8: the walled start pieces and the walled Lemma 3.5 (P2-DZZSTW)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1058–1066) for the walled
approximate distance at a dyadic wall `K = B̄w`, `S = cellsInside Bw` (Remark 5.2,
l. 2281–2284; D117/D123), in the pulled-back form `startGoodW` (S3L5W6).

**Near-miss reuse**: `l35_start_hpW` is a copy of `l35_start_hp` (S3L5Start, P2-DZZ3G): the
union bound of (eq-B-good-Phi) over the `9 ⌊C_mc log₂ δ⁻¹⌋` pulled-back boxes `b` with
`ψ⁻¹x ∈ b_large`, now with `dzz_lemma37_goodW` (S3L5W7). On `𝓔_{δ,α}` and `δ^{C_Mc} < s_{Bw}`,
`Bw` and its ancestors are split (`wsplit_of_side`), so a pulled-back cell `b` is a cell
`wEmb Bw b` (`isCell_wEmb_iff`), whose side bounds from `𝓔_{δ,α}` give
`1 ≤ m_b` and `m_{wEmb Bw b} ≤ C_mc log₂ δ⁻¹`.

* **`l35_start_hpW`**: `L35StartW`-type bound at every `x ∈ B̄w`;
* **`l35StartW_holds`**: `L35StartW P γ W α ι ξ Bw` for `α, ι > 0`;
* **`dzz_lemma35UOn_wall`**: the walled DZZ Lemma 3.5 `DZZLemma35UOn P γ W B̄w (cellsInside Bw) ξ ξd`
  for every dyadic wall, `0 < ξ`, `ξd < C_Mc`, with no open hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma wHom_symm_mem_dzzV {Bw : DyBox} {x : ℂ} (hx : x ∈ Bw.closedBox) :
    (wHom Bw).symm x ∈ dzzV := by
  have h : wHom Bw ((wHom Bw).symm x) ∈ (wEmb Bw DyBox.root).closedBox := by
    rw [wEmb_root]; simpa using hx
  rw [wHom_mem_closedBox, closedBox_root] at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ l. 1058–1066 at a dyadic wall** (copy of `l35_start_hp`): with high probability, for
all pulled-back cells `b` with `ψ⁻¹x ∈ b_large`, the pulled-back
`D'_{δ'}(ψ⁻¹x, ∂b_large ∩ 𝕍) ≤ δ^{-ι}(δ/δ')³`, uniformly in `x ∈ B̄w`. -/
theorem l35_start_hpW (hW : IsWhiteNoise P W) {γ α ι : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hι : 0 < ι) (Bw : DyBox) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ x ∈ Bw.closedBox,
      P.real (startGoodW γ W δ δ' ι Bw x ∩ eventEFine γ W α δ)ᶜ ≤
        δ ^ (ι / 20) + P.real (eventEFine γ W α δ)ᶜ := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨δ₁, hδ₁, hgood⟩ := dzz_lemma37_goodW hW hγ hγ2 hα hι
  set c := dzzCMc γ with hcdef
  have hc : 0 < c := dzzCMc_pos γ
  have hBs := wside_pos Bw
  set δ₄ := (Bw.side / 2) ^ (1 / c) with hδ₄def
  have hδ₄ : 0 < δ₄ := Real.rpow_pos_of_pos (by positivity) _
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set M := 14400 * C / ι ^ 2 + 1 with hMdef
  refine ⟨min (min δ₁ δ₄) (min (1 / 2) (Real.exp (-M))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ δ' hδ' x' hx'
  set x := (wHom Bw).symm x' with hxdef
  have hxV : x ∈ dzzV := wHom_symm_mem_dzzV hx'
  have hδa : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ4' : δ < δ₄ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := by linarith [hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))]
  have hδM : δ < Real.exp (-M) := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδc : δ ^ c < Bw.side := by
    have h1 := Real.rpow_lt_rpow hδ0.le hδ4' hc
    rw [hδ₄def, ← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at h1
    linarith
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLM : M < L := by
    have := Real.log_lt_log hδ0 hδM
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hLM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hKr : 0 ≤ C * Real.logb 2 δ⁻¹ := by
    rw [Real.logb, ← hLdef]; positivity
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  have hK : (K : ℝ) ≤ C * L / Real.log 2 := by
    calc (K : ℝ) ≤ C * Real.logb 2 δ⁻¹ := Nat.floor_le hKr
      _ = C * L / Real.log 2 := by rw [Real.logb, ← hLdef, mul_div_assoc]
  set Bad : DyBox → Set Ω := fun b => if x ∈ b.largeBox ∧ (wEmb Bw b).n ≤ K then
    {ω | approxLQG γ W ω (wEmb Bw b) ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
        ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
          (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞)} else ∅
    with hBad
  set cb : ℕ → Fin 3 × Fin 3 → DyBox := fun n ac =>
    clampBox n (idx n x.re - 1 + ac.1) (idx n x.im - 1 + ac.2) with hcb
  have hsub : (startGoodW γ W δ δ' ι Bw x' ∩ eventEFine γ W α δ)ᶜ ⊆ (eventEFine γ W α δ)ᶜ ∪
      ⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac) := by
    intro ω hω
    by_cases hE : ω ∈ eventEFine γ W α δ
    · right
      have hn : ¬ ∀ b, IsCell (fun c => approxLQG γ W ω (wEmb Bw c)) δ b → x ∈ b.largeBox →
          ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
            (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) := fun h => hω ⟨h, hE⟩
      push Not at hn
      obtain ⟨b0, hb0, hxb, hlt⟩ := hn
      have hsp : WSplit (approxLQG γ W ω) δ Bw :=
        wsplit_of_side hE.1.1 fun b hb => (hE.1.2 b hb).2.trans_lt hδc
      set b := wEmb Bw b0 with hbdef
      have hb : IsCell (approxLQG γ W ω) δ b := (isCell_wEmb_iff hsp).2 hb0
      obtain ⟨hs1, hs2⟩ := hE.1.2 b hb
      have hn1 : 1 ≤ b0.n := by
        by_contra h0
        have h0' : b0.n = 0 := by omega
        have : b0.side = 1 := by unfold DyBox.side; rw [h0', pow_zero]
        have hbs : b.side = Bw.side := by rw [hbdef, side_wEmb, this, mul_one]
        linarith
      have hnK : b.n ≤ K := by
        rw [hKdef]; apply Nat.le_floor
        have h1 := Real.log_le_log (by positivity) hs1
        rw [Real.log_rpow hδ0, hlogδ] at h1
        have h2 : Real.log b.side = -(b.n * Real.log 2) := by
          unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
        rw [h2] at h1
        rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
        linarith
      have hnK0 : b0.n ≤ K := by
        have : b.n = Bw.n + b0.n := rfl
        omega
      obtain ⟨ac, hac⟩ := eq_clampBox_of_mem_largeBox hxb hxV
      refine mem_iUnion₂.2 ⟨b0.n, Finset.mem_Icc.2 ⟨hn1, hnK0⟩, mem_iUnion.2 ⟨ac, ?_⟩⟩
      have hb' : cb b0.n ac = b0 := hac.symm
      rw [hb']
      simp only [Bad]
      rw [if_pos ⟨hxb, hnK⟩]
      exact ⟨⟨hb.1.le, hE⟩, hlt⟩
    · left; exact hE
  have hlevel : ∀ n ∈ Finset.Icc 1 K, ∀ ac : Fin 3 × Fin 3,
      P.real (Bad (cb n ac)) ≤ δ ^ (ι / 10) := by
    intro n hn ac
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
    have hbn : (cb n ac).n = n := rfl
    simp only [Bad]
    split_ifs with hxb
    · have hbK : ((wEmb Bw (cb n ac)).n : ℝ) ≤ C * Real.logb 2 δ⁻¹ :=
        (Nat.cast_le.2 hxb.2).trans (Nat.floor_le hKr)
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hgood δ ⟨hδ0, hδa⟩ δ' hδ' Bw (cb n ac) (hbn ▸ hn1) hbK x ⟨hxb.1, hxV⟩)
    · simp only [measureReal_empty]; positivity
  have hsum : ∑ n ∈ Finset.Icc 1 K, ∑ ac : Fin 3 × Fin 3, δ ^ (ι / 10) ≤ δ ^ (ι / 20) := by
    have e : ∑ n ∈ Finset.Icc 1 K, ∑ ac : Fin 3 × Fin 3, δ ^ (ι / 10) =
        (K : ℝ) * (9 * δ ^ (ι / 10)) := by
      simp [Finset.sum_const, Nat.card_Icc]
    rw [e]
    have hKL : (K : ℝ) ≤ 2 * C * L := by
      refine hK.trans ?_
      rw [div_le_iff₀ hlog2]
      have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
      linarith
    have hy : (ι * L / 20) ^ 2 / 2 ≤ Real.exp (ι * L / 20) := by
      have := Real.pow_div_factorial_le_exp (ι * L / 20) (by positivity) 2
      rwa [Nat.factorial_two, Nat.cast_ofNat] at this
    have hM' : 14400 * C ≤ ι ^ 2 * L := by
      have : 14400 * C / ι ^ 2 < L := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      linarith [mul_comm L (ι ^ 2)]
    have h18 : 18 * C * L ≤ Real.exp (ι * L / 20) := by
      refine le_trans ?_ hy
      have : 18 * C * L * 800 ≤ ι ^ 2 * L * L := by nlinarith
      nlinarith
    rw [Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hδ0, hlogδ]
    calc (K : ℝ) * (9 * Real.exp (-L * (ι / 10))) ≤
          (18 * C * L) * Real.exp (-L * (ι / 10)) := by
          have := Real.exp_pos (-L * (ι / 10))
          nlinarith
      _ ≤ Real.exp (ι * L / 20) * Real.exp (-L * (ι / 10)) :=
          mul_le_mul_of_nonneg_right h18 (Real.exp_pos _).le
      _ = Real.exp (-L * (ι / 20)) := by rw [← Real.exp_add]; congr 1; ring
  calc P.real (startGoodW γ W δ δ' ι Bw x' ∩ eventEFine γ W α δ)ᶜ
      ≤ P.real ((eventEFine γ W α δ)ᶜ ∪
          ⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac)) := measureReal_mono hsub
    _ ≤ P.real (eventEFine γ W α δ)ᶜ +
          P.real (⋃ n ∈ Finset.Icc 1 K, ⋃ ac : Fin 3 × Fin 3, Bad (cb n ac)) :=
        measureReal_union_le _ _
    _ ≤ P.real (eventEFine γ W α δ)ᶜ + δ ^ (ι / 20) := by
        gcongr
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun n hn =>
          (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun ac _ =>
            hlevel n hn ac)) hsum
    _ = δ ^ (ι / 20) + P.real (eventEFine γ W α δ)ᶜ := add_comm _ _

/-- **The walled start pieces** `L35StartW` (S3L5W6) hold, for every dyadic wall. -/
theorem l35StartW_holds (hW : IsWhiteNoise P W) {γ α ι : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hι : 0 < ι) (Bw : DyBox) {ξ : ℝ} (hξ : 0 < ξ) :
    L35StartW P γ W α ι ξ Bw := by
  obtain ⟨δ₀, hδ₀, h⟩ := l35_start_hpW (P := P) hW hγ hγ2 hα hι Bw
  exact ⟨δ₀, hδ₀, fun δ hδ δ' hδ' x hx =>
    h δ hδ δ' hδ' x (interior_subset (kXi_sub_interior hξ hx))⟩

/-- **Walled DZZ Lemma 3.5** (l. 907–916, proof l. 1037–1083; Remark 5.2) at every dyadic wall
`K = B̄w` with `S = cellsInside Bw`, for `0 < ξ`, `ξd < C_Mc`: no open hypotheses. -/
theorem dzz_lemma35UOn_wall (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    DZZLemma35UOn P γ W Bw.closedBox (cellsInside Bw) ξ ξd := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  exact dzz_lemma35UOn_of_start hW hγ hγ2 Bw hξ hξd
    (l35StartW_holds hW hγ hγ2 (by linarith) (by have := dzzCMc_pos γ; positivity) Bw hξ)

end DZZ
end LQGMetric
