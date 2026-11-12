/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W6

/-!
# Walled DZZ Lemma 3.5, W7: (eq-B-good-Phi) for the pulled-back boxes of a wall (P2-DZZSTW)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 963–965, proof l. 1017–1035),
Lemma 3.7 (eq-B-good-Phi), for the pulled-back mass `c ↦ M(wEmb Bw c)` of a dyadic wall `Bw`
(DZZ Remark 5.2, l. 2281–2284; D117/D123).

**Near-miss reuse**: `dzz_lemma37_goodW` is a copy of `dzz_lemma37_good` (S3L7FinGood, P2-DZZ3G)
in which the row of boxes from `y` to `∂b_large ∩ 𝕍` is taken in the pulled-back grid (so it
stays inside the wall), while the mass estimate `approxLQG_fine_le_of_mem` and the union bound
`tail_bandNorm_finset` are applied to the actual boxes `wEmb Bw ·` (side and centre transfer by
`side_wEmb`, `center_wEmb`). The level condition is on the actual box `wEmb Bw b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma wEmb_center_near (Bw b bt : DyBox) (h : ‖b.center - bt.center‖ ≤ 8 * b.side) :
    ‖(wEmb Bw b).center - (wEmb Bw bt).center‖ ≤ 8 * (wEmb Bw b).side := by
  rw [center_wEmb, center_wEmb, wHom_apply, wHom_apply, side_wEmb,
    show (Bw.side : ℂ) * b.center + wOff Bw - ((Bw.side : ℂ) * bt.center + wOff Bw) =
      (Bw.side : ℂ) * (b.center - bt.center) by ring, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (wside_pos Bw)]
  calc Bw.side * ‖b.center - bt.center‖ ≤ Bw.side * (8 * b.side) :=
        mul_le_mul_of_nonneg_left h (wside_pos Bw).le
    _ = 8 * (Bw.side * b.side) := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- **DZZ Lemma 3.7, (eq-B-good-Phi)** (l. 963–965, proof l. 1017–1035) for the pulled-back
boxes of a wall `Bw` (copy of `dzz_lemma37_good`): uniformly in `Bw`, the pulled-back box `b`
(`1 ≤ m_b`, `m_{wEmb Bw b} ≤ C_mc log₂ δ⁻¹`) and the point `x ∈ b_large ∩ 𝕍`, the pulled-back
`D'_{δ'}(x, ∂b_large ∩ 𝕍)` exceeds `δ^{-ι}(δ/δ')³` on `{M(wEmb Bw b) ≤ δ²} ∩ 𝓔_{δ,α}` with
probability at most `δ^{ι/10}`. -/
theorem dzz_lemma37_goodW (hW : IsWhiteNoise P W) {γ α ι : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hι : 0 < ι) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ Bw b : DyBox, 1 ≤ b.n →
      ((wEmb Bw b).n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ → ∀ x ∈ b.largeBox ∩ dzzV,
      P ({ω | approxLQG γ W ω (wEmb Bw b) ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
        {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
          ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
            (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞)}) ≤
        ENNReal.ofReal (δ ^ (ι / 10)) := by
  have := hW.isProbabilityMeasure
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  obtain ⟨U, hU1, hU⟩ := l37g_ev (dzzCmc γ) γ α ι hι hα
  refine ⟨Real.exp (-(U ^ 10)), Real.exp_pos _, ?_⟩
  rintro δ ⟨hδ0, hδ1⟩ δ' ⟨hδ'0, hδ'δ⟩ Bw b hb1 hbn x hx
  set b' := wEmb Bw b with hb'def
  set C := dzzCmc γ with hCdef
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL : U ^ 10 < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this; linarith
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  set u := L ^ ((1 : ℝ) / 10) with hudef
  have hu10 : u ^ 10 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have huU : U ≤ u := by
    have h1 : (U ^ 10) ^ ((1 : ℝ) / 10) = U := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
    rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL.le (by norm_num)
  obtain ⟨E1, E2, E3, E4⟩ := hU u huU
  rw [hu10] at E1 E2 E3 E4
  have hu1 : 1 ≤ u := hU1.trans huU
  have hsqrt : Real.sqrt L = u ^ 5 := by
    rw [← hu10, show u ^ 10 = (u ^ 5) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hlogL : Real.log L ≤ 10 * u := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 10 by norm_num)
    rw [← hudef] at this
    calc Real.log L ≤ u / (1 / 10) := this
      _ = 10 * u := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the scale `t = 2^{-r}`: `log X < τ = r log 2 ≤ log X + log 2`
  set ρ := Real.log δ - Real.log δ' with hρdef
  have hρ0 : 0 ≤ ρ := by have := Real.log_le_log hδ'0 hδ'δ; linarith
  set X := Real.exp (9 / 10 * ι * L + 3 * ρ) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_exp (by positivity)
  have hX0 : 0 < X := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Nat.log 2 ⌊X⌋₊ := ⟨_, rfl⟩
  have hfl2 : ⌊X⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 hX1; omega
  have hℓ1 : (2 : ℝ) ^ ℓ ≤ X := by
    have h1 := Nat.pow_log_le_self 2 hfl2
    rw [← hℓdef] at h1
    have h2 : ((2 ^ ℓ : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le hX0.le)
  have hℓ2 : X < (2 : ℝ) ^ (ℓ + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊X⌋₊
    rw [← hℓdef] at h1
    have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one X]
  set r := ℓ + 1 with hrdef
  set τ := (r : ℝ) * Real.log 2 with hτdef
  have hτ1 : 9 / 10 * ι * L + 3 * ρ < τ := by
    have := Real.log_lt_log hX0 hℓ2
    rwa [hXdef, Real.log_exp, Real.log_pow] at this
  have h2r : (2 : ℝ) ^ r = Real.exp τ := two_pow_eq_exp r
  have h2r2 : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2rX : (2 : ℝ) ^ r ≤ 2 * X := by rw [hrdef, pow_succ]; linarith
  set a := 6 / 5 * τ with hadef
  -- the exponent `E` of `approxLQG_fine_le_of_mem`
  have hbn' : (b'.n : ℝ) * Real.log 2 ≤ C * L := by
    rw [Real.logb, ← hLdef] at hbn
    rw [← le_div_iff₀ hlog2]
    calc (b'.n : ℝ) ≤ C * (L / Real.log 2) := hbn
      _ = C * L / Real.log 2 := by ring
  have hside : Real.log b'.side⁻¹ = b'.n * Real.log 2 := by
    rw [show b'.side⁻¹ = (2 : ℝ) ^ b'.n by unfold DyBox.side; rw [inv_pow, inv_inv]]
    exact Real.log_pow _ _
  have hsq1 : Real.sqrt 8608 ≤ 93 := by
    calc Real.sqrt 8608 ≤ Real.sqrt (93 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 93 := Real.sqrt_sq (by norm_num)
  have hsq2 : Real.sqrt (Real.log b'.side⁻¹ + 4) ≤ (C + 4) * u ^ 5 := by
    calc Real.sqrt (Real.log b'.side⁻¹ + 4) ≤ Real.sqrt (((C + 4) * u ^ 5) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hside, show ((C + 4) * u ^ 5) ^ 2 = (C + 4) ^ 2 * L by rw [← hu10]; ring]
          have hL1 : 1 ≤ L := by rw [← hu10]; exact one_le_pow₀ hu1
          have : (C + 4) * L ≤ (C + 4) ^ 2 * L :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by norm_num)) hL0.le
          linarith
      _ = (C + 4) * u ^ 5 := Real.sqrt_sq (by positivity)
  have hE : γ * (α * Real.sqrt L * Real.log L) +
      γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b'.side⁻¹ + 4)) ≤
      γ * α * 10 * u ^ 6 + γ ^ 2 * 93 * (C + 4) * u ^ 5 := by
    have t1 : α * Real.sqrt L * Real.log L ≤ α * u ^ 5 * (10 * u) := by
      rw [hsqrt]; exact mul_le_mul_of_nonneg_left hlogL (mul_nonneg hα.le (by positivity))
    have t2 : 2 * Real.sqrt 8608 * Real.sqrt (Real.log b'.side⁻¹ + 4) ≤
        2 * 93 * ((C + 4) * u ^ 5) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by norm_num)) hsq2 (Real.sqrt_nonneg _)
        (by norm_num)
    have t1' := mul_le_mul_of_nonneg_left t1 hγ.le
    have t2' := mul_le_mul_of_nonneg_left t2 (show 0 ≤ γ ^ 2 / 2 by positivity)
    linarith
  have hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ r) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b'.side⁻¹ + 4))) * Real.exp a <
      δ' ^ 2 := by
    have e1 : δ ^ 2 = Real.exp (2 * Real.log δ) := by rw [← exp_sq_eq, Real.exp_log hδ0]
    have e2 : δ' ^ 2 = Real.exp (2 * Real.log δ') := by rw [← exp_sq_eq, Real.exp_log hδ'0]
    rw [inv_two_pow_eq_exp, exp_sq_eq, e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.exp_lt_exp, ← hLdef]
    rw [← hτdef]
    linarith
  -- the geometry: the row from `x` to a point `v ∈ ∂B_large ∩ 𝕍`
  obtain ⟨v, hv, hvim⟩ := exists_frontier_row b hb1 hx
  have hvL : v ∈ b.largeBox ∩ dzzV := ⟨(isClosed_largeBox b).frontier_subset hv.1, hv.2⟩
  obtain ⟨p, q, hp, hq, hpq, hpqi, hD⟩ : ∃ p q : ℂ, p ∈ b.largeBox ∩ dzzV ∧
      q ∈ b.largeBox ∩ dzzV ∧ p.re ≤ q.re ∧ p.im = q.im ∧
      ∀ m' : DyBox → ℝ, approxDist m' δ' x v = approxDist m' δ' p q := by
    rcases le_total x.re v.re with h | h
    · exact ⟨x, v, hx, hvL, h, hvim.symm, fun _ => rfl⟩
    · exact ⟨v, x, hvL, hx, h, hvim, fun _ => approxDist_comm _ _⟩
  set N := b.n + r with hNdef
  set S : Finset DyBox := (Finset.Icc (idx N p.re) (idx N q.re)).image
    (rowBox N (idx N p.im) (idx_lt _ _)) with hSdef
  have hmono := idx_mono N hpq
  -- the count `|S| ≤ (idx q − idx p) + 1 ≤ 2 · 2^r + 2`
  have hs2N : b.side * 2 ^ N = 2 ^ r := by
    unfold DyBox.side; rw [hNdef, pow_add, ← mul_assoc, pow_inv_mul_pow, one_mul]
  have hD1 : (((idx N q.re - idx N p.re : ℕ) : ℝ)) + 1 ≤ 2 * 2 ^ r + 2 := by
    rw [Nat.cast_sub hmono]
    obtain ⟨-, p2⟩ := idx_bounds (n := N) hp.2.1 hp.2.2.1
    obtain ⟨q1, -⟩ := idx_bounds (n := N) hq.2.1 hq.2.2.1
    have ap := abs_le.1 hp.1.1
    have aq := abs_le.1 hq.1.1
    have hqp : (q.re - p.re) * 2 ^ N ≤ 2 * b.side * 2 ^ N :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have : 2 * b.side * 2 ^ N = 2 * 2 ^ r := by rw [mul_assoc, hs2N]
    nlinarith
  have hcard : (S.card : ℝ) ≤ 2 * 2 ^ r + 2 := by
    have h1 : S.card ≤ idx N q.re + 1 - idx N p.re :=
      Finset.card_image_le.trans (Nat.card_Icc _ _).le
    have h2 : ((idx N q.re + 1 - idx N p.re : ℕ) : ℝ) = ((idx N q.re - idx N p.re : ℕ) : ℝ) + 1 := by
      rw [show idx N q.re + 1 - idx N p.re = (idx N q.re - idx N p.re) + 1 by omega]; push_cast
      ring
    have h3 : (S.card : ℝ) ≤ ((idx N q.re + 1 - idx N p.re : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  -- the bad event
  set S' : Finset DyBox := S.image (wEmb Bw) with hS'def
  have hcard' : (S'.card : ℝ) ≤ 2 * 2 ^ r + 2 :=
    le_trans (by exact_mod_cast Finset.card_image_le) hcard
  set T : Set Ω := {ω | ∃ bt ∈ S', a ≤ bandNorm γ W bt b'.n ω} with hTdef
  have hdec0 : P (decompEvent W)ᶜ = 0 := by
    have := ae_iff.1 (ae_decompEvent (P := P) hW)
    simpa [compl_def] using this
  have hm' : (2 : ℝ) ^ b'.n ≤ δ ^ (-C) := by
    rw [two_pow_eq_exp, Real.rpow_def_of_pos hδ0, hlogδ, Real.exp_le_exp]; linarith
  have hjY : (2 : ℝ) ^ 0 ≤ (α * Real.log δ⁻¹) ^ 2 := by
    rw [pow_zero, ← hLdef]; nlinarith
  have hq3 : (δ / δ') ^ 3 = Real.exp (3 * ρ) := by
    rw [show (3 : ℝ) * ρ = (3 : ℕ) * ρ by norm_num, Real.exp_nat_mul, hρdef,
      ← Real.log_div hδ0.ne' hδ'0.ne', Real.exp_log (div_pos hδ0 hδ'0)]
  have hratio : δ ^ (-ι) * (δ / δ') ^ 3 = X * Real.exp (ι / 10 * L) := by
    rw [hq3, Real.rpow_def_of_pos hδ0, hlogδ, hXdef, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have h9 : 9 ≤ Real.exp (ι / 10 * L) := by
    have := Real.add_one_le_exp (ι / 10 * L); linarith
  have hbound : 2 * 2 ^ r + 2 ≤ δ ^ (-ι) * (δ / δ') ^ 3 := by
    rw [hratio]; nlinarith
  -- on the good event, `D' ≤ (idx q − idx p) + 1 ≤ δ^{-ι} (δ/δ')³`
  have hsub : {ω | approxLQG γ W ω b' ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
        ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
          (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞)} ⊆
      (decompEvent W)ᶜ ∪ T := by
    rintro ω ⟨⟨hM, hEv⟩, hbig⟩
    by_cases hdec : ω ∈ decompEvent W
    swap
    · exact Or.inl hdec
    by_contra hT
    have hgood : ∀ bt ∈ S', bandNorm γ W bt b'.n ω < a := fun bt hbt =>
      lt_of_not_ge fun h => hT (Or.inr ⟨bt, hbt, h⟩)
    have hmass : ∀ i, idx N p.re ≤ i → i ≤ idx N q.re →
        approxLQG γ W ω (wEmb Bw (rowBox N (idx N p.im) (idx_lt _ _) i)) < δ' ^ 2 := by
      intro i hi1 hi2
      set bt0 := rowBox N (idx N p.im) (idx_lt _ _) i with hbt0def
      set bt := wEmb Bw bt0 with hbtdef
      have hbtS : bt ∈ S' := Finset.mem_image.2
        ⟨bt0, Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hi2⟩, rfl⟩, rfl⟩
      have hbtn : bt.n = b'.n + r := by
        show Bw.n + (b.n + r) = Bw.n + b.n + r; omega
      have hc := wEmb_center_near Bw b bt0
        (rowBox_center_near b (N := N) (by omega) hp hq hi1 hi2)
      have h := approxLQG_fine_le_of_mem hW hγ hEv.2 hdec (j := 0) hm' hjY
        (by rw [hbtn]; omega) hc hM (a := a) (hgood bt hbtS).le
      have hrat : bt.side / b'.side = (2 : ℝ)⁻¹ ^ r := by
        rw [side_eq_pow_mul (b := b') (b' := bt) (k' := r) hbtn]
        push_cast
        rw [div_mul_cancel_right₀ (side_pos' bt).ne', inv_pow]
      rw [hrat] at h
      exact h.trans_lt hsmall
    have hrow := approxDist_row_le (m := fun c => approxLQG γ W ω (wEmb Bw c)) (δ := δ') (N := N)
      hp.2 hq.2 hpq hpqi hmass
    have hset : approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
        (frontier b.largeBox ∩ dzzV) ≤ ((idx N q.re - idx N p.re : ℕ) : ℕ∞) + 1 := by
      unfold approxDistSet
      refine (iInf₂_le x (mem_singleton x)).trans ((iInf₂_le v hv).trans ?_)
      rw [hD]; exact hrow
    have hle : ((approxDistSet (fun c => approxLQG γ W ω (wEmb Bw c)) δ' {x}
        (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) := by
      refine (ENat.toENNReal_le.2 hset).trans ?_
      rw [show ((idx N q.re - idx N p.re : ℕ) : ℕ∞) + 1 =
          ((idx N q.re - idx N p.re + 1 : ℕ) : ℕ∞) by push_cast; rfl,
        ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)
    exact not_lt.2 hle hbig
  -- the union bound
  have hT := tail_bandNorm_finset hW S' b'.n γ a
  have h4 : 4 ≤ Real.exp (2 / 25 * ι * L) := by
    have := Real.add_one_le_exp (2 / 25 * ι * L); linarith
  calc _ ≤ P ((decompEvent W)ᶜ ∪ T) := measure_mono hsub
    _ ≤ P (decompEvent W)ᶜ + P T := measure_union_le _ _
    _ = ENNReal.ofReal (P.real T) := by rw [hdec0, zero_add, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (δ ^ (ι / 10)) := by
      refine ENNReal.ofReal_le_ofReal (hT.trans ?_)
      rw [Real.rpow_def_of_pos hδ0, hlogδ]
      calc (S'.card : ℝ) * Real.exp (-a) ≤ (4 * Real.exp τ) * Real.exp (-a) :=
            mul_le_mul_of_nonneg_right (by rw [← h2r]; linarith) (Real.exp_pos _).le
        _ = 4 * Real.exp (-(τ / 5)) := by
            rw [mul_assoc, ← Real.exp_add, hadef]; congr 2; ring
        _ ≤ Real.exp (2 / 25 * ι * L) * Real.exp (-(τ / 5)) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ = Real.exp (2 / 25 * ι * L + -(τ / 5)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-L * (ι / 10)) := Real.exp_le_exp.2 (by linarith)

end DZZ
end LQGMetric
