/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Discounted occupation integrals of two paths that agree after random times

For a bounded function `f` and a path `x : ℝ≥0 → E` write
`discOcc λ f x = ∫₀^∞ e^{-λ t} f (x_t) dt`.  The resolvent of a path measure `μ` is the `μ`-mean of
`discOcc λ f`.

* `discOcc_sub_le`: if `x (a + s) = y (b + s)` for all `s ≥ 0`, with `a, b ≤ 2 ε`, then
  `|discOcc λ f x - discOcc λ f y| ≤ 4 M ε` for `|f| ≤ M`.
* `abs_integral_discOcc_sub_le`: for two processes defined on the same probability space and
  agreeing in the above sense outside an event of probability at most `5 ε`,
  the resolvents differ by at most `4 M ε + 10 M ε / λ`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {E : Type*}

/-- The discounted occupation integral `∫₀^∞ e^{-λ t} f (x_t) dt` of `f` along the path `x`. -/
def discOcc (lam : ℝ) (f : E → ℝ) (x : ℝ≥0 → E) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * f (x t.toNNReal)

/-- The integrand of `discOcc` is integrable on `(0, ∞)` for a bounded measurable `f ∘ x`. -/
theorem integrableOn_discOcc {f : E → ℝ} {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M)
    {x : ℝ≥0 → E} (hx : Measurable fun u : ℝ≥0 => f (x u)) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t) * f (x t.toNNReal)) (Ioi 0) := by
  refine Integrable.mono' (Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hlam) M) ?_ ?_
  · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (hx.comp measurable_real_toNNReal)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le

/-- The discounted occupation integral of a path is bounded by `M / λ`. -/
theorem abs_discOcc_le {f : E → ℝ} {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M)
    (x : ℝ≥0 → E) : |discOcc lam f x| ≤ M / lam := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-lam * t)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hlam) M
  have h1 : ‖discOcc lam f x‖ ≤ ∫ t in Ioi (0 : ℝ), M * Real.exp (-lam * t) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le
  have h2 : ∫ t in Ioi (0 : ℝ), M * Real.exp (-lam * t) = M / lam := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -lam < 0)]
    field_simp
    simp
  rw [← Real.norm_eq_abs]
  exact h1.trans h2.le

/-- Shifting the lower limit of an integral over a half line. -/
theorem setIntegral_Ioi_shift (g : ℝ → ℝ) (a : ℝ) :
    ∫ t in Ioi a, g t = ∫ s in Ioi (0 : ℝ), g (s + a) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun t => (Ioi a).indicator g t) a
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext s
  simp only [Set.indicator, Set.mem_Ioi, lt_add_iff_pos_left]

/-- The map `t ↦ e^{-λ t}` is `λ`-Lipschitz on `[0, ∞)`. -/
theorem abs_exp_neg_mul_sub_le {lam : ℝ} (hlam : 0 < lam) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-lam * a) - Real.exp (-lam * b)| ≤ lam * |a - b| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      0 ≤ Real.exp (-lam * a) - Real.exp (-lam * b) ∧
        Real.exp (-lam * a) - Real.exp (-lam * b) ≤ lam * (b - a) := by
    intro a b ha hab
    have h1 : Real.exp (-lam * b) = Real.exp (-lam * a) * Real.exp (-(lam * (b - a))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hu : 0 ≤ lam * (b - a) := mul_nonneg hlam.le (sub_nonneg.2 hab)
    have h2 : 1 - lam * (b - a) ≤ Real.exp (-(lam * (b - a))) := by
      linarith [Real.add_one_le_exp (-(lam * (b - a)))]
    have h3 : Real.exp (-(lam * (b - a))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h4 : 0 < Real.exp (-lam * a) := Real.exp_pos _
    have h5 : Real.exp (-lam * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h6 : 0 < Real.exp (-(lam * (b - a))) := Real.exp_pos _
    rw [h1]
    constructor
    · nlinarith
    · nlinarith
  rcases le_total a b with hab | hab
  · obtain ⟨k1, k2⟩ := key a b ha hab
    rw [abs_of_nonneg k1, abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · obtain ⟨k1, k2⟩ := key b a hb hab
    rw [abs_sub_comm, abs_of_nonneg k1, abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith

/-- A path decomposes at a time `a ≥ 0` into the occupation integral up to `a` and the discounted
occupation integral of the path after `a`. -/
theorem discOcc_split {f : E → ℝ} {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M)
    {x : ℝ≥0 → E} (hx : Measurable fun u : ℝ≥0 => f (x u)) (a : ℝ≥0) :
    discOcc lam f x = (∫ t in Ioc (0 : ℝ) a, Real.exp (-lam * t) * f (x t.toNNReal)) +
      Real.exp (-lam * a) * discOcc lam f (fun u => x (a + u)) := by
  have hI := integrableOn_discOcc hlam hM hx
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  unfold discOcc
  have hsplit := setIntegral_union (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) a) (t := Ioi (a : ℝ))
    (Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2)) measurableSet_Ioi
    (hI.mono_set (fun t ht => ht.1)) (hI.mono_set (fun t ht => lt_of_le_of_lt ha ht))
  rw [Ioc_union_Ioi_eq_Ioi ha] at hsplit
  rw [hsplit, setIntegral_Ioi_shift _ (a : ℝ), ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have e1 : (s + a).toNNReal = a + s.toNNReal := by
    rw [Real.toNNReal_add hs0 ha, Real.toNNReal_coe, add_comm]
  simp only [e1]
  rw [show -lam * (s + a) = -lam * s + -lam * a by ring, Real.exp_add]
  ring

/-- **Two paths that agree after times `a, b ≤ 2 ε` have discounted occupation integrals within
`4 M ε`.** -/
theorem discOcc_sub_le {f : E → ℝ} {M lam ε : ℝ} (hlam : 0 < lam) (hM0 : 0 ≤ M)
    (hM : ∀ e, |f e| ≤ M) {x y : ℝ≥0 → E} (hx : Measurable fun u : ℝ≥0 => f (x u))
    (hy : Measurable fun u : ℝ≥0 => f (y u)) {a b : ℝ≥0} (ha : (a : ℝ) ≤ 2 * ε)
    (hb : (b : ℝ) ≤ 2 * ε) (hxy : ∀ s, x (a + s) = y (b + s)) :
    |discOcc lam f x - discOcc lam f y| ≤ 4 * M * ε := by
  have hxs : discOcc lam f (fun u => y (b + u)) = discOcc lam f (fun u => x (a + u)) := by
    unfold discOcc
    simp only [hxy]
  have hJ := abs_discOcc_le hlam hM (fun u => x (a + u))
  have hbound : ∀ (z : ℝ≥0 → E) (c : ℝ≥0),
      |∫ t in Ioc (0 : ℝ) c, Real.exp (-lam * t) * f (z t.toNNReal)| ≤ M * c := by
    intro z c
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) c) (C := M)
      (f := fun t : ℝ => Real.exp (-lam * t) * f (z t.toNNReal)) measure_Ioc_lt_top (by
        intro t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
        calc Real.exp (-lam * t) * |f (z t.toNNReal)| ≤ 1 * M :=
              mul_le_mul h1 (hM _) (abs_nonneg _) zero_le_one
          _ = M := one_mul M)
    rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    simp [Measure.real]
  have hPx := hbound x a
  have hPy := hbound y b
  rw [discOcc_split hlam hM hx a, discOcc_split hlam hM hy b, hxs]
  set P := ∫ t in Ioc (0 : ℝ) a, Real.exp (-lam * t) * f (x t.toNNReal)
  set Q := ∫ t in Ioc (0 : ℝ) b, Real.exp (-lam * t) * f (y t.toNNReal)
  set J := discOcc lam f (fun u => x (a + u))
  have hexp := abs_exp_neg_mul_sub_le hlam a.coe_nonneg b.coe_nonneg
  have hmain : |(P + Real.exp (-lam * a) * J) - (Q + Real.exp (-lam * b) * J)| ≤
      |P| + |Q| + |Real.exp (-lam * a) - Real.exp (-lam * b)| * |J| := by
    have : (P + Real.exp (-lam * a) * J) - (Q + Real.exp (-lam * b) * J) =
        P - Q + (Real.exp (-lam * a) - Real.exp (-lam * b)) * J := by ring
    rw [this]
    calc _ ≤ |P - Q| + |(Real.exp (-lam * a) - Real.exp (-lam * b)) * J| := abs_add_le _ _
      _ ≤ (|P| + |Q|) + |Real.exp (-lam * a) - Real.exp (-lam * b)| * |J| := by
          rw [abs_mul]
          linarith [abs_sub P Q]
      _ = _ := by ring
  have hprod : |Real.exp (-lam * a) - Real.exp (-lam * b)| * |J| ≤ M * |(a : ℝ) - b| := by
    calc _ ≤ (lam * |(a : ℝ) - b|) * (M / lam) :=
          mul_le_mul hexp hJ (abs_nonneg _) (by positivity)
      _ = M * |(a : ℝ) - b| := by field_simp
  have hab : |(a : ℝ) - b| ≤ 2 * ε := by
    rw [abs_le]
    constructor <;> nlinarith [a.coe_nonneg, b.coe_nonneg]
  have hsum : (a : ℝ) + b + |(a : ℝ) - b| ≤ 4 * ε := by
    rcases le_total (a : ℝ) b with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  calc _ ≤ |P| + |Q| + |Real.exp (-lam * a) - Real.exp (-lam * b)| * |J| := hmain
    _ ≤ M * a + M * b + M * |(a : ℝ) - b| := by linarith
    _ = M * ((a : ℝ) + b + |(a : ℝ) - b|) := by ring
    _ ≤ M * (4 * ε) := mul_le_mul_of_nonneg_left hsum hM0
    _ = 4 * M * ε := by ring

/-- **Resolvents of two coupled processes.**  Two processes `X, Y` on a probability space such that,
outside an event of probability at most `5 ε`, the paths agree after times `a, b ≤ 2 ε` have
`λ`-resolvents of a bounded function `f` (`|f| ≤ M`) that differ by at most
`4 M ε + 10 M ε / λ`. -/
theorem abs_integral_discOcc_sub_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] {f : E → ℝ} {M lam ε : ℝ} (hlam : 0 < lam) (hM0 : 0 ≤ M)
    (hM : ∀ e, |f e| ≤ M) (hε : 0 ≤ ε) {X Y : Ω → ℝ≥0 → E}
    (hX : Measurable fun p : Ω × ℝ≥0 => f (X p.1 p.2))
    (hY : Measurable fun p : Ω × ℝ≥0 => f (Y p.1 p.2))
    {a b : Ω → ℝ≥0} {Ev : Set Ω} (hEv : MeasurableSet Ev) (hQ : Q Evᶜ ≤ ENNReal.ofReal (5 * ε))
    (hEq : ∀ ω ∈ Ev, (a ω : ℝ) ≤ 2 * ε ∧ (b ω : ℝ) ≤ 2 * ε ∧
      ∀ s, X ω (a ω + s) = Y ω (b ω + s)) :
    |(∫ ω, discOcc lam f (X ω) ∂Q) - ∫ ω, discOcc lam f (Y ω) ∂Q| ≤
      4 * M * ε + 10 * ε * (M / lam) := by
  have hmeas : ∀ {Z : Ω → ℝ≥0 → E}, (Measurable fun p : Ω × ℝ≥0 => f (Z p.1 p.2)) →
      Measurable fun ω => discOcc lam f (Z ω) := by
    intro Z hZ
    have h : Measurable fun p : Ω × ℝ => Real.exp (-lam * p.2) * f (Z p.1 p.2.toNNReal) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
        (hZ.comp (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd)))
    exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  have hpath : ∀ {Z : Ω → ℝ≥0 → E}, (Measurable fun p : Ω × ℝ≥0 => f (Z p.1 p.2)) →
      ∀ ω, Measurable fun u : ℝ≥0 => f (Z ω u) := fun hZ ω => hZ.comp measurable_prodMk_left
  have hbd : ∀ {Z : Ω → ℝ≥0 → E}, (Measurable fun p : Ω × ℝ≥0 => f (Z p.1 p.2)) →
      Integrable (fun ω => discOcc lam f (Z ω)) Q := by
    intro Z hZ
    refine Integrable.of_bound (hmeas hZ).aestronglyMeasurable (M / lam) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_discOcc_le hlam hM (Z ω)
  have hc : 0 ≤ 4 * M * ε := mul_nonneg (mul_nonneg (by norm_num) hM0) hε
  have hd : 0 ≤ 2 * (M / lam) := by positivity
  have hrhs : Integrable (fun ω => 4 * M * ε + Evᶜ.indicator (fun _ => 2 * (M / lam)) ω) Q :=
    (integrable_const _).add ((integrable_const _).indicator hEv.compl)
  have hpt : ∀ ω, ‖discOcc lam f (X ω) - discOcc lam f (Y ω)‖ ≤
      4 * M * ε + Evᶜ.indicator (fun _ => 2 * (M / lam)) ω := by
    intro ω
    by_cases hω : ω ∈ Ev
    · obtain ⟨h1, h2, h3⟩ := hEq ω hω
      rw [Real.norm_eq_abs, indicator_of_notMem (by simpa using hω), add_zero]
      exact discOcc_sub_le hlam hM0 hM (hpath hX ω) (hpath hY ω) h1 h2 h3
    · rw [Real.norm_eq_abs, indicator_of_mem (show ω ∈ Evᶜ from hω)]
      have h1 := abs_discOcc_le hlam hM (X ω)
      have h2 := abs_discOcc_le hlam hM (Y ω)
      calc _ ≤ |discOcc lam f (X ω)| + |discOcc lam f (Y ω)| := abs_sub _ _
        _ ≤ 2 * (M / lam) := by linarith
        _ ≤ 4 * M * ε + 2 * (M / lam) := le_add_of_nonneg_left hc
  have hqr : Q.real Evᶜ ≤ 5 * ε := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
    rw [ENNReal.toReal_ofReal (by linarith)] at h
    exact h
  calc |(∫ ω, discOcc lam f (X ω) ∂Q) - ∫ ω, discOcc lam f (Y ω) ∂Q|
      = ‖∫ ω, (discOcc lam f (X ω) - discOcc lam f (Y ω)) ∂Q‖ := by
        rw [integral_sub (hbd hX) (hbd hY), Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖discOcc lam f (X ω) - discOcc lam f (Y ω)‖ ∂Q := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (4 * M * ε + Evᶜ.indicator (fun _ => 2 * (M / lam)) ω) ∂Q :=
        integral_mono ((hbd hX).sub (hbd hY)).norm hrhs hpt
    _ = 4 * M * ε + 2 * (M / lam) * Q.real Evᶜ := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hEv.compl),
          integral_const, integral_indicator_const _ hEv.compl]
        simp [smul_eq_mul, mul_comm]
    _ ≤ 4 * M * ε + 10 * ε * (M / lam) := by
        have := mul_le_mul_of_nonneg_left hqr hd
        linarith

end LatticeProb

end
