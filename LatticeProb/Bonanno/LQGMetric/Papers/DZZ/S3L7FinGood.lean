/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinRow
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinAsym

/-!
# DZZ Lemma 3.7, (eq-B-good-Phi) (P2-DZZ3G)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 963–965, proof l. 1017–1035):
for `x ∈ B_large` and `ι > 0`,
`P({M_s(B) ≤ δ²} ∩ 𝓔_{δ,α} ∩ {D'_{γ,δ'}(x, ∂B_large) > δ^{-ι} (δ/δ')³}) ≤ δ^{ι/10}`.

Proof as in DZZ: `t = 2^{-r}` with `δ^{0.9ι}(δ'/δ)³/2 ≤ t < δ^{0.9ι}(δ'/δ)³` (DZZ:
`t = max {2^{-r} : 2^{-r} ≤ δ^{0.9 ι}(δ'/δ)³}`); the boxes of side `t s` of the horizontal row
through `x`, from `x` to a point of `∂B_large ∩ 𝕍`, are at most `4/t`; on
`{M_s(B) ≤ δ²} ∩ 𝓔_{δ,α}` a box with band exponent `< a = 1.2 log t⁻¹` has mass `< δ'²`
(`approxLQG_fine_le_of_mem`, the normalized form of DZZ's `η ≤ 1.5 log t⁻¹`), and then
`D' ≤ 4/t ≤ δ^{-ι}(δ/δ')³` (`approxDist_row_le`); the union bound gives `(4/t) t^{1.2}`.
Deviation (see the report): the band is `η^{s}_{ts}` (level `j = 0` in
`approxLQG_fine_le_of_mem`) instead of DZZ's `η^{ε² s}_{ts}`; no independence is needed here.
Stated for every `α > 0` (DZZ: `α > max {α₀, 4 C_mc}`), uniformly in `B` and `x ∈ B_large ∩ 𝕍`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- The boxes of the row between `p` and `q` are within `8 s_B` of `c_B`. -/
lemma rowBox_center_near (B : DyBox) {N : ℕ} (hN : B.n ≤ N) {p q : ℂ}
    (hp : p ∈ B.largeBox ∩ dzzV) (hq : q ∈ B.largeBox ∩ dzzV) {i : ℕ} (h1 : idx N p.re ≤ i)
    (h2 : i ≤ idx N q.re) :
    ‖B.center - (rowBox N (idx N p.im) (idx_lt _ _) i).center‖ ≤ 8 * B.side := by
  obtain ⟨⟨hpr, hpi⟩, hp0, hp1, hp2, hp3⟩ := hp
  obtain ⟨⟨hqr, -⟩, hq0, hq1, -, -⟩ := hq
  set sN : ℝ := (2 : ℝ)⁻¹ ^ N with hsNdef
  have hsN : sN ≤ B.side := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have hsN0 : 0 < sN := by positivity
  have hiq := idx_lt N q.re
  have hmin : min i (2 ^ N - 1) = i := min_eq_left (by omega)
  have hre : (rowBox N (idx N p.im) (idx_lt _ _) i).center.re = ((i : ℝ) + 1 / 2) * sN := by
    show (((min i (2 ^ N - 1) : ℕ) : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ N = _
    rw [hmin]
  have him : (rowBox N (idx N p.im) (idx_lt _ _) i).center.im =
      ((idx N p.im : ℝ) + 1 / 2) * sN := rfl
  obtain ⟨-, p2⟩ := idx_bounds (n := N) hp0 hp1
  obtain ⟨q1, -⟩ := idx_bounds (n := N) hq0 hq1
  obtain ⟨x1, x2⟩ := idx_bounds (n := N) hp2 hp3
  have ep := scale_hi N p2
  have eq := scale_lo N q1
  have ex1 := scale_lo N x1
  have ex2 := scale_hi N x2
  rw [← hsNdef] at ep eq ex1 ex2
  have hi1 : ((idx N p.re : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
  have hi2 : (i : ℝ) ≤ idx N q.re := by exact_mod_cast h2
  have m1 := mul_le_mul_of_nonneg_right hi1 hsN0.le
  have m2 := mul_le_mul_of_nonneg_right hi2 hsN0.le
  have ap := abs_le.1 hpr
  have aq := abs_le.1 hqr
  have ai := abs_le.1 hpi
  have a1 : |(B.center - (rowBox N (idx N p.im) (idx_lt _ _) i).center).re| ≤ 2 * B.side := by
    rw [Complex.sub_re, hre, abs_le]; constructor <;> linarith
  have a2 : |(B.center - (rowBox N (idx N p.im) (idx_lt _ _) i).center).im| ≤ 2 * B.side := by
    rw [Complex.sub_im, him, abs_le]; constructor <;> linarith
  calc _ ≤ _ := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * B.side + 2 * B.side := add_le_add a1 a2
    _ ≤ 8 * B.side := by linarith [side_pos' B]

lemma isClosed_largeBox (B : DyBox) : IsClosed B.largeBox := by
  have cr : Continuous fun w : ℂ => |w.re - B.center.re| :=
    continuous_abs.comp (Complex.continuous_re.sub continuous_const)
  have ci : Continuous fun w : ℂ => |w.im - B.center.im| :=
    continuous_abs.comp (Complex.continuous_im.sub continuous_const)
  exact (isClosed_le cr continuous_const).inter (isClosed_le ci continuous_const)

/-- The polynomial requirements in `u = (log δ⁻¹)^{1/10}`. -/
lemma l37g_ev (C γ α ι : ℝ) (hι : 0 < ι) (hα : 0 < α) : ∃ U : ℝ, 1 ≤ U ∧ ∀ u ≥ U,
    γ * α * 10 * u ^ 6 + γ ^ 2 * 93 * (C + 4) * u ^ 5 ≤ 18 / 25 * ι * u ^ 10 ∧
    8 ≤ ι / 10 * u ^ 10 ∧ 3 ≤ 2 / 25 * ι * u ^ 10 ∧ 1 ≤ α * u ^ 10 := by
  have e1 := ev_pow_le (show 0 < 9 / 25 * ι by positivity) (γ * α * 10) (show 6 < 10 by norm_num)
  have e2 := ev_pow_le (show 0 < 9 / 25 * ι by positivity) (γ ^ 2 * 93 * (C + 4))
    (show 5 < 10 by norm_num)
  have e3 := ev_pow_le (show 0 < ι / 10 by positivity) 8 (show 0 < 10 by norm_num)
  have e4 := ev_pow_le (show 0 < 2 / 25 * ι by positivity) 3 (show 0 < 10 by norm_num)
  have e5 := ev_pow_le hα 1 (show 0 < 10 by norm_num)
  obtain ⟨U, hU⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max U 1, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hU u ((le_max_left _ _).trans hu)
  simp only [pow_zero, mul_one] at h3 h4 h5
  exact ⟨by linarith, h3, h4, h5⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- **DZZ Lemma 3.7, (eq-B-good-Phi)** (l. 963–965, proof l. 1017–1035), uniformly in the box
`B` (`1 ≤ m_B ≤ C_mc log₂ δ⁻¹`) and the point `x ∈ B_large ∩ 𝕍`. -/
theorem dzz_lemma37_good (hW : IsWhiteNoise P W) {γ α ι : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hι : 0 < ι) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ b : DyBox, 1 ≤ b.n →
      (b.n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ → ∀ x ∈ b.largeBox ∩ dzzV,
      P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
        {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
          ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞)}) ≤
        ENNReal.ofReal (δ ^ (ι / 10)) := by
  have := hW.isProbabilityMeasure
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  obtain ⟨U, hU1, hU⟩ := l37g_ev (dzzCmc γ) γ α ι hι hα
  refine ⟨Real.exp (-(U ^ 10)), Real.exp_pos _, ?_⟩
  rintro δ ⟨hδ0, hδ1⟩ δ' ⟨hδ'0, hδ'δ⟩ b hb1 hbn x hx
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
  have hbn' : (b.n : ℝ) * Real.log 2 ≤ C * L := by
    rw [Real.logb, ← hLdef] at hbn
    rw [← le_div_iff₀ hlog2]
    calc (b.n : ℝ) ≤ C * (L / Real.log 2) := hbn
      _ = C * L / Real.log 2 := by ring
  have hside : Real.log b.side⁻¹ = b.n * Real.log 2 := by
    rw [show b.side⁻¹ = (2 : ℝ) ^ b.n by unfold DyBox.side; rw [inv_pow, inv_inv]]
    exact Real.log_pow _ _
  have hsq1 : Real.sqrt 8608 ≤ 93 := by
    calc Real.sqrt 8608 ≤ Real.sqrt (93 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 93 := Real.sqrt_sq (by norm_num)
  have hsq2 : Real.sqrt (Real.log b.side⁻¹ + 4) ≤ (C + 4) * u ^ 5 := by
    calc Real.sqrt (Real.log b.side⁻¹ + 4) ≤ Real.sqrt (((C + 4) * u ^ 5) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hside, show ((C + 4) * u ^ 5) ^ 2 = (C + 4) ^ 2 * L by rw [← hu10]; ring]
          have hL1 : 1 ≤ L := by rw [← hu10]; exact one_le_pow₀ hu1
          have : (C + 4) * L ≤ (C + 4) ^ 2 * L :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by norm_num)) hL0.le
          linarith
      _ = (C + 4) * u ^ 5 := Real.sqrt_sq (by positivity)
  have hE : γ * (α * Real.sqrt L * Real.log L) +
      γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4)) ≤
      γ * α * 10 * u ^ 6 + γ ^ 2 * 93 * (C + 4) * u ^ 5 := by
    have t1 : α * Real.sqrt L * Real.log L ≤ α * u ^ 5 * (10 * u) := by
      rw [hsqrt]; exact mul_le_mul_of_nonneg_left hlogL (mul_nonneg hα.le (by positivity))
    have t2 : 2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4) ≤
        2 * 93 * ((C + 4) * u ^ 5) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by norm_num)) hsq2 (Real.sqrt_nonneg _)
        (by norm_num)
    have t1' := mul_le_mul_of_nonneg_left t1 hγ.le
    have t2' := mul_le_mul_of_nonneg_left t2 (show 0 ≤ γ ^ 2 / 2 by positivity)
    linarith
  have hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ r) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) * Real.exp a <
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
  set T : Set Ω := {ω | ∃ bt ∈ S, a ≤ bandNorm γ W bt b.n ω} with hTdef
  have hdec0 : P (decompEvent W)ᶜ = 0 := by
    have := ae_iff.1 (ae_decompEvent (P := P) hW)
    simpa [compl_def] using this
  have hm' : (2 : ℝ) ^ b.n ≤ δ ^ (-C) := by
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
  have hsub : {ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
      {ω | ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) <
        ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞)} ⊆
      (decompEvent W)ᶜ ∪ T := by
    rintro ω ⟨⟨hM, hEv⟩, hbig⟩
    by_cases hdec : ω ∈ decompEvent W
    swap
    · exact Or.inl hdec
    by_contra hT
    have hgood : ∀ bt ∈ S, bandNorm γ W bt b.n ω < a := fun bt hbt =>
      lt_of_not_ge fun h => hT (Or.inr ⟨bt, hbt, h⟩)
    have hmass : ∀ i, idx N p.re ≤ i → i ≤ idx N q.re →
        approxLQG γ W ω (rowBox N (idx N p.im) (idx_lt _ _) i) < δ' ^ 2 := by
      intro i hi1 hi2
      set bt := rowBox N (idx N p.im) (idx_lt _ _) i with hbtdef
      have hbtS : bt ∈ S := Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hi2⟩, rfl⟩
      have hbtn : bt.n = b.n + r := rfl
      have hc := rowBox_center_near b (N := N) (by omega) hp hq hi1 hi2
      have h := approxLQG_fine_le_of_mem hW hγ hEv.2 hdec (j := 0) hm' hjY
        (by rw [hbtn]; omega) hc hM (a := a) (hgood bt hbtS).le
      have hrat : bt.side / b.side = (2 : ℝ)⁻¹ ^ r := by
        rw [side_eq_pow_mul (b := b) (b' := bt) (k' := r) hbtn]
        push_cast
        rw [div_mul_cancel_right₀ (side_pos' bt).ne', inv_pow]
      rw [hrat] at h
      exact h.trans_lt hsmall
    have hrow := approxDist_row_le (m := approxLQG γ W ω) (δ := δ') (N := N) hp.2 hq.2 hpq hpqi
      hmass
    have hset : approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω ≤
        ((idx N q.re - idx N p.re : ℕ) : ℕ∞) + 1 := by
      unfold approxLGDSet approxDistSet
      refine (iInf₂_le x (mem_singleton x)).trans ((iInf₂_le v hv).trans ?_)
      rw [hD]; exact hrow
    have hle : ((approxLGDSet γ W δ' {x} (frontier b.largeBox ∩ dzzV) ω : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ (-ι) * (δ / δ') ^ 3) := by
      refine (ENat.toENNReal_le.2 hset).trans ?_
      rw [show ((idx N q.re - idx N p.re : ℕ) : ℕ∞) + 1 =
          ((idx N q.re - idx N p.re + 1 : ℕ) : ℕ∞) by push_cast; rfl,
        ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)
    exact not_lt.2 hle hbig
  -- the union bound
  have hT := tail_bandNorm_finset hW S b.n γ a
  have h4 : 4 ≤ Real.exp (2 / 25 * ι * L) := by
    have := Real.add_one_le_exp (2 / 25 * ι * L); linarith
  calc _ ≤ P ((decompEvent W)ᶜ ∪ T) := measure_mono hsub
    _ ≤ P (decompEvent W)ᶜ + P T := measure_union_le _ _
    _ = ENNReal.ofReal (P.real T) := by rw [hdec0, zero_add, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (δ ^ (ι / 10)) := by
      refine ENNReal.ofReal_le_ofReal (hT.trans ?_)
      rw [Real.rpow_def_of_pos hδ0, hlogδ]
      calc (S.card : ℝ) * Real.exp (-a) ≤ (4 * Real.exp τ) * Real.exp (-a) :=
            mul_le_mul_of_nonneg_right (by rw [← h2r]; linarith) (Real.exp_pos _).le
        _ = 4 * Real.exp (-(τ / 5)) := by
            rw [mul_assoc, ← Real.exp_add, hadef]; congr 2; ring
        _ ≤ Real.exp (2 / 25 * ι * L) * Real.exp (-(τ / 5)) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ = Real.exp (2 / 25 * ι * L + -(τ / 5)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-L * (ι / 10)) := Real.exp_le_exp.2 (by linarith)

end DZZ
end LQGMetric
