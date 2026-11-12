/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Polar

/-!
# GM Lemma 5.6: planar tools for the paths `π₋`, `π₊` (task P2-M2L56c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6, l. 2963–2966 ("We can choose a path `π₋` … and a path `π₊` …"). GM give no
construction; these are the elementary planar facts used for ours (own elementary arguments):

* `l56_exists_arc_avoid`: two points of the unit circle at distance `≥ δ` from a point `c` are
  joined by an arc of the unit circle all of whose points are at distance `≥ δ` from `c`
  (the arc of `circle ∖ {c}`; `|e^{iθ} − e^{iφ}| = 2 sin((θ − φ)/2)` is quasi-concave on
  `[φ, φ + 2π]`);
* `l56_rad_sep`: `|t x − s y| ≥ (S/4) |x − y|` for unit `x, y`, `t ≥ 0`, `s ≥ S > 0`;
* `l56_rad_hp_sep`: a ray in a direction `g` with `Re g ≤ −1/2` stays `α/4` away from
  `{|h| ≥ α, Re h ≥ 0}`;
* `l56_exists_dir`: for every `c` there is a unit `g` with `Re g ≤ −1/2` and `|g − c| ≥ 1/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex Real

namespace LQGMetric.GM

/-- `|e^{iθ} − e^{iφ}| = 2 |sin((θ − φ)/2)|` -/
lemma l56_arc_norm_sub (φ θ : ℝ) :
    ‖polPt 1 θ - polPt 1 φ‖ = 2 * |Real.sin ((θ - φ) / 2)| := by
  rw [← dist_eq_norm, dist_comm, dist_polPt]
  have e : ((1 : ℝ) : ℂ) - ((1 : ℝ) : ℂ) * exp (((θ - φ : ℝ) : ℂ) * I) =
      -(exp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by rw [mul_comm I]; push_cast; ring
  rw [e, norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]

/-- `sin` is quasi-concave on `[0, π]` -/
lemma l56_sin_ge {s1 s s2 d : ℝ} (h1 : 0 ≤ s1) (h1s : s1 ≤ s) (hs2 : s ≤ s2) (h2 : s2 ≤ π)
    (hd1 : d ≤ Real.sin s1) (hd2 : d ≤ Real.sin s2) : d ≤ Real.sin s := by
  rcases le_total s (π / 2) with h | h
  · exact hd1.trans (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h h1s)
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π - s2) (y := π - s)
      (by linarith) (by linarith) (by linarith)
    rw [Real.sin_pi_sub, Real.sin_pi_sub] at this
    linarith

lemma l56_arc_key {φ δ θ1 θ2 : ℝ} (h1 : θ1 ∈ Ico φ (φ + 2 * π)) (h2 : θ2 ∈ Ico φ (φ + 2 * π))
    (hd1 : δ ≤ ‖polPt 1 θ1 - polPt 1 φ‖) (hd2 : δ ≤ ‖polPt 1 θ2 - polPt 1 φ‖) :
    ∀ θ ∈ Icc θ1 θ2, δ ≤ ‖polPt 1 θ - polPt 1 φ‖ := by
  intro θ hθ
  rw [l56_arc_norm_sub] at hd1 hd2 ⊢
  have hs : ∀ t ∈ Icc φ (φ + 2 * π), |Real.sin ((t - φ) / 2)| = Real.sin ((t - φ) / 2) := by
    intro t ht
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2]))
  rw [hs θ1 (Ico_subset_Icc_self h1)] at hd1
  rw [hs θ2 (Ico_subset_Icc_self h2)] at hd2
  rw [hs θ ⟨by linarith [h1.1, hθ.1], by linarith [h2.2, hθ.2]⟩]
  have := l56_sin_ge (s1 := (θ1 - φ) / 2) (s := (θ - φ) / 2) (s2 := (θ2 - φ) / 2)
    (d := δ / 2) (by linarith [h1.1]) (by linarith [hθ.1]) (by linarith [hθ.2])
    (by linarith [h2.2]) (by linarith) (by linarith)
  linarith

/-- **arc avoiding a point**: two points of the unit circle `δ`-far from `c` are joined by a
preconnected subset of the unit circle all of whose points are `δ`-far from `c` -/
lemma l56_exists_arc_avoid {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) {δ : ℝ}
    (had : δ ≤ ‖a - c‖) (hbd : δ ≤ ‖b - c‖) :
    ∃ A : Set ℂ, IsPreconnected A ∧ a ∈ A ∧ b ∈ A ∧ ∀ x ∈ A, ‖x‖ = 1 ∧ δ ≤ ‖x - c‖ := by
  obtain ⟨φ, rfl⟩ : ∃ φ : ℝ, c = polPt 1 φ := ⟨arg c, by
    rw [polPt, ← hc]; exact (norm_mul_exp_arg_mul_I c).symm⟩
  have hrep : ∀ x : ℂ, ‖x‖ = 1 → ∃ θ ∈ Ico φ (φ + 2 * π), x = polPt 1 θ := fun x hx =>
    ⟨_, toIcoMod_mem_Ico Real.two_pi_pos φ (arg x), by
      have := eq_polPt_toIcoMod x φ; rwa [hx] at this⟩
  obtain ⟨θa, hθa, rfl⟩ := hrep a ha
  obtain ⟨θb, hθb, rfl⟩ := hrep b hb
  refine ⟨(fun θ => polPt 1 θ) '' uIcc θa θb,
    isPreconnected_uIcc.image _ (continuous_polPt_angle 1).continuousOn,
    ⟨θa, left_mem_uIcc, rfl⟩, ⟨θb, right_mem_uIcc, rfl⟩, ?_⟩
  rintro _ ⟨θ, hθ, rfl⟩
  refine ⟨norm_polPt zero_le_one θ, ?_⟩
  rcases le_total θa θb with h | h
  · rw [uIcc_of_le h] at hθ; exact l56_arc_key hθa hθb had hbd θ hθ
  · rw [uIcc_of_ge h] at hθ; exact l56_arc_key hθb hθa hbd had θ hθ

lemma l56_norm_ofReal_mul {x : ℂ} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 ≤ t) : ‖(t : ℂ) * x‖ = t := by
  rw [norm_mul, hx, Complex.norm_real, Real.norm_of_nonneg ht, mul_one]

/-- points at separated distances from `0` are apart -/
lemma l56_nsep {p q : ℂ} {a d : ℝ} (hp : ‖p‖ ≤ a) (hq : a + d ≤ ‖q‖) : d ≤ ‖p - q‖ := by
  have := norm_sub_norm_le q p; rw [norm_sub_rev] at this; linarith

lemma l56_nsep' {p q : ℂ} {a d : ℝ} (hp : ‖p‖ ≤ a) (hq : a + d ≤ ‖q‖) : d ≤ ‖q - p‖ := by
  rw [norm_sub_rev]; exact l56_nsep hp hq

/-- **two rays**: `|t x − s y| ≥ (S/4) |x − y|` for unit `x, y`, `t ≥ 0`, `s ≥ S > 0` -/
lemma l56_rad_sep {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {t s S : ℝ} (ht : 0 ≤ t) (hS : 0 < S)
    (hs : S ≤ s) : S / 4 * ‖x - y‖ ≤ ‖(t : ℂ) * x - (s : ℂ) * y‖ := by
  have hxy : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by rw [hx, hy]; norm_num)
  rcases le_total t (S / 2) with h | h
  · have h1 := l56_nsep' (p := (t : ℂ) * x) (q := (s : ℂ) * y) (a := t) (d := s - t)
      (l56_norm_ofReal_mul hx ht).le (by rw [l56_norm_ofReal_mul hy (by linarith)]; linarith)
    rw [norm_sub_rev] at h1
    nlinarith
  · have hx2 : x.re * x.re + x.im * x.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hx]; norm_num
    have hy2 : y.re * y.re + y.im * y.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hy]; norm_num
    have key : (S / 2 * ‖x - y‖) ^ 2 ≤ ‖(t : ℂ) * x - (s : ℂ) * y‖ ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      have e : (t * x.re - s * y.re) * (t * x.re - s * y.re) +
          (t * x.im - s * y.im) * (t * x.im - s * y.im) = (t - s) ^ 2 + t * s *
          ((x.re - y.re) * (x.re - y.re) + (x.im - y.im) * (x.im - y.im)) := by
        linear_combination (t ^ 2 - t * s) * hx2 + (s ^ 2 - t * s) * hy2
      rw [e]
      have hQ : 0 ≤ (x.re - y.re) * (x.re - y.re) + (x.im - y.im) * (x.im - y.im) := by
        nlinarith
      have hts : (S / 2) ^ 2 ≤ t * s := by nlinarith
      nlinarith [sq_nonneg (t - s)]
    have := le_of_sq_le_sq key (norm_nonneg _)
    nlinarith [norm_nonneg (x - y)]

/-- **ray against the closed half annulus** -/
lemma l56_rad_hp_sep {g h : ℂ} (hg : ‖g‖ = 1) (hgre : g.re ≤ -1 / 2) {t α : ℝ} (ht : 0 ≤ t)
    (hh : α ≤ ‖h‖) (hre : 0 ≤ h.re) : α / 4 ≤ ‖(t : ℂ) * g - h‖ := by
  rcases le_total t (α / 2) with h1 | h1
  · have := l56_nsep (p := (t : ℂ) * g) (q := h) (a := t) (d := α - t)
      (l56_norm_ofReal_mul hg ht).le (by linarith)
    linarith
  · have hr := Complex.re_le_norm (h - (t : ℂ) * g)
    rw [Complex.sub_re, Complex.re_ofReal_mul, norm_sub_rev] at hr
    nlinarith

/-- a unit direction in the left half plane far from a given point -/
lemma l56_exists_dir (c : ℂ) : ∃ g : ℂ, ‖g‖ = 1 ∧ g.re ≤ -1 / 2 ∧ 1 / 2 ≤ ‖g - c‖ := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3' : 1 ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hn : ∀ σ : ℝ, σ ^ 2 = 1 → ‖(⟨-1 / 2, σ * √3 / 2⟩ : ℂ)‖ = 1 := by
    intro σ hσ
    have h2 : ‖(⟨-1 / 2, σ * √3 / 2⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith
    nlinarith [norm_nonneg (⟨-1 / 2, σ * √3 / 2⟩ : ℂ)]
  have hd : 1 ≤ ‖(⟨-1 / 2, 1 * √3 / 2⟩ : ℂ) - ⟨-1 / 2, -1 * √3 / 2⟩‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [Complex.sub_im, abs_of_nonneg (by simp only; linarith)]
    simp only; linarith
  by_cases h : 1 / 2 ≤ ‖(⟨-1 / 2, 1 * √3 / 2⟩ : ℂ) - c‖
  · exact ⟨_, hn 1 (by norm_num), le_refl _, h⟩
  · refine ⟨_, hn (-1) (by norm_num), le_refl _, ?_⟩
    have := norm_sub_le_norm_sub_add_norm_sub (⟨-1 / 2, 1 * √3 / 2⟩ : ℂ) c
      (⟨-1 / 2, -1 * √3 / 2⟩ : ℂ)
    rw [norm_sub_rev c] at this
    linarith

end LQGMetric.GM
