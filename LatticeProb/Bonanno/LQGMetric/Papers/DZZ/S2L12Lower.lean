/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L12Lower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Chain
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# DZZ Lemma 2.12, lower half: `D_{γ,δ}(u, v) ≥ δ^{-c}` with high probability (task P2-DZZPRE4)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 745–759 (proof of Lemma 2.12,
`lem-obvious-bounds`): with `2^{-k} ≈ δ^c`, a union bound over the grid `𝔠_k` shows that w.h.p.
every ball `B(w, 2^{-k})`, `w ∈ 𝔠_k`, has LQG mass `≥ δ²`; then every ball of mass `≤ δ²` is
small and a chain from `u` to `v` needs many balls (`S2L12Chain`).

DZZ obtain the per-ball lower tail from (eq-max-white-noise-process) and (eq-LQG-negative-moment)
for the white-noise chaos `M̃_{γ,δ}` (which needs the identification of `M_γ` with that chaos,
l. 648–658). Here this input is the explicit hypothesis `BallMassLowerTail`: a polynomial lower
tail `P(μ(B(w, s)) ≤ t) ≤ C t^p s^{-A}` uniformly for `w` in a compact set and small `s`
(what DZZ's two estimates give, and what Markov's inequality gives from a negative-moment bound
`E μ(B(w, s))^{-p} ≤ C s^{-A}`). The library has only the finiteness `E μ(B)^{-p} < ∞` for a
fixed ball (`lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg`), without the scaling in `s`.

`dzz_lemma212_lower_whp` is the union bound and the bookkeeping, for any random measure; we use
grid spacing `s = δ^{c₁}` (any real `s`) instead of DZZ's dyadic `2^{-k_δ}` (bookkeeping only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- **Polynomial lower tail of the mass of small balls** (the input of DZZ l. 750–755): for some
`p > 0`, `A ≥ 0`, `C`, `r₀ > 0`, `P(μ(B(w, s)) ≤ t) ≤ C t^p s^{-A}` for `w ∈ K`, `s ∈ (0, r₀]`,
`t > 0`. -/
def BallMassLowerTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (K : Set ℂ) : Prop :=
  ∃ p A C r₀ : ℝ, 0 < p ∧ 0 ≤ A ∧ 0 < r₀ ∧ ∀ w ∈ K, ∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ t : ℝ, 0 < t →
    P {ω | μ ω (ball w s) ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal (C * t ^ p * s ^ (-A))

/-- The grid points `(is, js)` near `u` have `|i|, |j| ≤ M`. -/
lemma grid_index_le {s R : ℝ} (hs : 0 < s) {u : ℂ} {i j : ℤ}
    (h : ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R) :
    |i| ≤ ⌈(‖u‖ + R) / s⌉ ∧ |j| ≤ ⌈(‖u‖ + R) / s⌉ := by
  have hw : ‖(⟨i * s, j * s⟩ : ℂ)‖ ≤ ‖u‖ + R := by
    have := norm_le_norm_add_norm_sub' (⟨i * s, j * s⟩ : ℂ) u
    linarith
  have h1 := (Complex.abs_re_le_norm (⟨i * s, j * s⟩ : ℂ)).trans hw
  have h2 := (Complex.abs_im_le_norm (⟨i * s, j * s⟩ : ℂ)).trans hw
  simp only at h1 h2
  rw [abs_mul, abs_of_pos hs, ← le_div_iff₀ hs] at h1 h2
  constructor
  · exact_mod_cast h1.trans (Int.le_ceil _)
  · exact_mod_cast h2.trans (Int.le_ceil _)

/-- **Union bound over the grid**: the probability that some grid ball `B(w, s)` with
`|w − u| ≤ R + 3s` has mass `≤ t` is at most `(2M + 1)² C t^p s^{-A}`. -/
theorem prob_grid_light_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {u : ℂ} {R s t p A C r₀ : ℝ} (hR : 0 ≤ R) (hs : 0 < s) (hsr : s ≤ r₀) (ht : 0 < t)
    (htail : ∀ w ∈ closedBall u (R + 3 * s), ∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ t : ℝ, 0 < t →
      P {ω | μ ω (ball w s) ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal (C * t ^ p * s ^ (-A))) :
    P {ω | ∃ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R + 3 * s ∧
        μ ω (ball ⟨i * s, j * s⟩ s) ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal ((2 * ⌈(‖u‖ + (R + 3 * s)) / s⌉ + 1) ^ 2 * (C * t ^ p * s ^ (-A))) := by
  set M := ⌈(‖u‖ + (R + 3 * s)) / s⌉
  set F : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  set E : ℤ × ℤ → Set Ω := fun q => if ‖(⟨q.1 * s, q.2 * s⟩ : ℂ) - u‖ ≤ R + 3 * s then
    {ω | μ ω (ball ⟨q.1 * s, q.2 * s⟩ s) ≤ ENNReal.ofReal t} else ∅
  have hsub : {ω | ∃ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R + 3 * s ∧
      μ ω (ball ⟨i * s, j * s⟩ s) ≤ ENNReal.ofReal t} ⊆ ⋃ q ∈ F, E q := by
    rintro ω ⟨i, j, hd, hm⟩
    obtain ⟨hi, hj⟩ := grid_index_le hs hd
    refine mem_biUnion (x := (i, j)) ?_ ?_
    · simp only [F, Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
      exact ⟨abs_le.1 hi, abs_le.1 hj⟩
    · simp only [E, hd, if_true]; exact hm
  have hE : ∀ q ∈ F, P (E q) ≤ ENNReal.ofReal (C * t ^ p * s ^ (-A)) := by
    intro q _
    simp only [E]
    split_ifs with hd
    · exact htail _ (by rw [mem_closedBall, dist_eq_norm]; exact hd) s hs hsr t ht
    · simp
  have hcard : (F.card : ℝ) = (2 * M + 1) ^ 2 := by
    have hM : 0 ≤ M := by
      apply Int.ceil_nonneg; exact div_nonneg (by linarith [norm_nonneg u]) hs.le
    simp only [F, Finset.card_product, Int.card_Icc]
    have h0 : 0 ≤ M + 1 - -M := by omega
    have h := Int.toNat_of_nonneg h0
    have h2 : ((((M + 1 - -M).toNat : ℕ) : ℤ) : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by rw [h]
    have h3 : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      push_cast at h2; rw [h2]; ring
    rw [Nat.cast_mul, h3]; ring
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le F E).trans ?_)
  refine (Finset.sum_le_sum hE).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← hcard]
  by_cases hC : 0 ≤ C * t ^ p * s ^ (-A)
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  · push_neg at hC
    rw [ENNReal.ofReal_of_nonpos hC.le, mul_zero]; exact zero_le

lemma tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => δ ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **DZZ Lemma 2.12, lower half, w.h.p. form** (l. 745–759), for any random measure `μ` with the
small-ball lower tail `BallMassLowerTail` on compact subsets of `𝕍`: for `u ∈ 𝕍`, `v ≠ u`, there
is `c > 0` with `P(D_δ(u, v) < δ^{-c}) → 0` as `δ → 0`. -/
theorem dzz_lemma212_lower_whp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {u v : ℂ} (hu : u ∈ openSquare) (huv : u ≠ v)
    (hT : ∀ K : Set ℂ, IsCompact K → K ⊆ openSquare → BallMassLowerTail P μ K) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun δ : ℝ =>
      P {ω | lgdDZZ (μ ω) δ u v < ((⌈δ ^ (-c)⌉₊ : ℕ) : ℕ∞)}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 isOpen_openSquare' u hu
  have hvu : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  set R := min (ε / 4) ‖v - u‖ with hRdef
  have hR : 0 < R := lt_min (by positivity) hvu
  have hRv : R ≤ ‖v - u‖ := min_le_right _ _
  have hRε : R ≤ ε / 4 := min_le_left _ _
  have hK : closedBall u (2 * R) ⊆ openSquare :=
    (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨p, A, C, r₀, hp, hA, hr₀, htail⟩ := hT _ (isCompact_closedBall u (2 * R)) hK
  set c₁ := p / (A + 2) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hc₁A : c₁ * (A + 2) = p := by rw [hc₁]; field_simp
  set c := c₁ / 2 with hc
  have hc0 : 0 < c := by positivity
  set L := 2 * ‖u‖ + 4 * R + 3 with hL
  have hL0 : 0 < L := by positivity
  refine ⟨c, hc0, ?_⟩
  have hup : Tendsto (fun δ : ℝ => ENNReal.ofReal (L ^ 2 * |C| * δ ^ p)) (𝓝[>] 0) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_rpow_nhdsGT_zero hp).const_mul (L ^ 2 * |C|)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  have e1 := (tendsto_rpow_nhdsGT_zero hc₁0).eventually (Iio_mem_nhds (show (0 : ℝ) <
    min (min 1 r₀) (R / 3) by positivity))
  have e2 := (tendsto_rpow_nhdsGT_zero hc0).eventually (Iio_mem_nhds (show (0 : ℝ) < R / 16 by
    positivity))
  have e3 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 := by
    have := (tendsto_rpow_nhdsGT_zero one_pos).eventually (Iio_mem_nhds one_pos)
    filter_upwards [this] with δ h; simpa using h
  filter_upwards [e1, e2, e3, self_mem_nhdsWithin] with δ h1 h2 h3 hδ
  simp only [mem_Iio, lt_min_iff] at h1 h2
  rw [mem_Ioi] at hδ
  set s := δ ^ c₁ with hs
  have hs0 : 0 < s := by positivity
  -- the bad event is contained in the event that some grid ball is light
  have hsub : {ω | lgdDZZ (μ ω) δ u v < ((⌈δ ^ (-c)⌉₊ : ℕ) : ℕ∞)} ⊆
      {ω | ∃ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R + 3 * s ∧
        μ ω (ball ⟨i * s, j * s⟩ s) ≤ ENNReal.ofReal (δ ^ 2)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_setOf_eq, not_exists, not_and, not_le] at hcon
    have hmass := large_ball_heavy_of_grid (μ := μ ω) (δ := δ) (R := R) (u := u) hs0 hcon
    have hge := lgdDZZ_ge_of_large_balls_heavy (μ := μ ω) (δ := δ) (r := 4 * s)
      (by positivity) hR.le hRv (fun c ρ hρ hne => hmass c ρ hρ hne)
      (n := ⌈δ ^ (-c)⌉₊) ?_
    · exact absurd hω (not_lt.2 hge)
    -- `⌈δ^{-c}⌉ ≤ R/(8 s)`
    have hx1 : 1 ≤ δ ^ (-c) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ h3.le (by linarith)
    have hceil : (⌈δ ^ (-c)⌉₊ : ℝ) ≤ 2 * δ ^ (-c) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ δ ^ (-c) by positivity); linarith
    refine hceil.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have hprod : δ ^ (-c) * s = δ ^ c := by
      rw [hs, ← Real.rpow_add hδ]; congr 1; rw [hc]; ring
    nlinarith [hprod]
  have hcount := prob_grid_light_le (P := P) (μ := μ) (u := u) (R := R) (t := δ ^ 2) (p := p)
    (A := A) (C := C) hR.le hs0 h1.1.2.le (by positivity)
    (fun w hw => htail w (closedBall_subset_closedBall (by linarith) hw))
  refine (measure_mono hsub).trans (hcount.trans (ENNReal.ofReal_le_ofReal ?_))
  -- the arithmetic
  set M := ⌈(‖u‖ + (R + 3 * s)) / s⌉
  have hM : (M : ℝ) ≤ (‖u‖ + (R + 3 * s)) / s + 1 := (Int.ceil_lt_add_one _).le
  have hM0 : (0 : ℝ) ≤ M := by
    have : 0 ≤ M := Int.ceil_nonneg (div_nonneg (by linarith [norm_nonneg u]) hs0.le)
    exact_mod_cast this
  have hs1 : s ≤ 1 := h1.1.1.le
  have h2M : 2 * (M : ℝ) + 1 ≤ L / s := by
    rw [le_div_iff₀ hs0]
    have : (M : ℝ) * s ≤ ‖u‖ + (R + 3 * s) + s := by
      have := mul_le_mul_of_nonneg_right hM hs0.le
      rw [add_mul, div_mul_cancel₀ _ hs0.ne', one_mul] at this; exact this
    nlinarith
  set X := C * (δ ^ 2) ^ p * s ^ (-A)
  have hX : X ≤ |C| * (δ ^ 2) ^ p * s ^ (-A) := by
    simp only [X]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C)
      (by positivity)) (by positivity)
  have hsq : (2 * (M : ℝ) + 1) ^ 2 ≤ (L / s) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have hkey : (L / s) ^ 2 * (|C| * (δ ^ 2) ^ p * s ^ (-A)) = L ^ 2 * |C| * δ ^ p := by
    have e1 : (δ ^ 2) ^ p = δ ^ (2 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num
    have e2 : s ^ (-A) = δ ^ (c₁ * -A) := by rw [hs, ← Real.rpow_mul hδ.le]
    have e3 : s ^ 2 = δ ^ (2 * c₁) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num; ring_nf
    have e4 : δ ^ (2 * p) * δ ^ (c₁ * -A) = δ ^ p * δ ^ (2 * c₁) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; linarith
    have hd : δ ^ (2 * c₁) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
    rw [e1, e2, div_pow, e3, div_mul_eq_mul_div, div_eq_iff hd]
    linear_combination (L ^ 2 * |C|) * e4
  calc (2 * (M : ℝ) + 1) ^ 2 * X ≤ (2 * (M : ℝ) + 1) ^ 2 * (|C| * (δ ^ 2) ^ p * s ^ (-A)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ (L / s) ^ 2 * (|C| * (δ ^ 2) ^ p * s ^ (-A)) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = L ^ 2 * |C| * δ ^ p := hkey

end DZZ
end LQGMetric
