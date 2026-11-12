/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepArc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepSeg
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DFGPS Proposition 4.1: elementary facts for the tube around a circle or an arc

For `L ⊆ ∂B_ρ(z)` (an arc of a circle or a whole circle, DFGPS T:2445): points of the tube
`B_{ε𝕣}(𝕣L)` have `||y − 𝕣z| − 𝕣ρ| < ε𝕣`; the argument of `γ(t) − 𝕣z` along a path in the
tube lifts to a continuous real function (path lifting for the covering map `exp : ℂ → ℂ∖{0}`,
mathlib `Complex.isCoveringMap_exp`, `IsCoveringMap.exists_path_lifts`); chords versus angles:
`(2/π)|a − b| ≤ |e^{ia} − e^{ib}| ≤ |a − b|` for `|a − b| ≤ π` (Jordan's inequality,
`Real.mul_le_sin`). Own elementary write-up of the geometry DFGPS leave to the reader (T:2486).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex

namespace LQGMetric.DFGPS.P41

open Blueprint

/-- `e^{iθ}` -/
def cis' (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

lemma norm_cis' (θ : ℝ) : ‖cis' θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma cis'_sub (a b : ℝ) : cis' a - cis' b = cis' b * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
  unfold cis'
  rw [mul_sub, mul_one, ← Complex.exp_add]
  congr 2
  push_cast; ring

lemma norm_cis'_sub_le (a b : ℝ) : ‖cis' a - cis' b‖ ≤ |a - b| := by
  rw [cis'_sub, norm_mul, norm_cis', one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma norm_cis'_sub_ge (a b : ℝ) (hab : |a - b| ≤ Real.pi) :
    2 / Real.pi * |a - b| ≤ ‖cis' a - cis' b‖ := by
  rw [cis'_sub, norm_mul, norm_cis', one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have h1 : 2 / Real.pi * (|a - b| / 2) ≤ Real.sin (|a - b| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have h2 : Real.sin (|a - b| / 2) ≤ |Real.sin ((a - b) / 2)| := by
    rcases le_total 0 (a - b) with h | h
    · rw [abs_of_nonneg h]; exact le_abs_self _
    · rw [abs_of_nonpos h, show -(a - b) / 2 = -((a - b) / 2) by ring, Real.sin_neg]
      exact neg_le_abs _
  have : 2 / Real.pi * |a - b| = 2 * (2 / Real.pi * (|a - b| / 2)) := by ring
  rw [this]
  linarith

/-- points of the tube around `𝕣L ⊆ ∂B_{𝕣ρ}(𝕣z)` -/
lemma tube_circle {z : ℂ} {ρ : ℝ} {L : Set ℂ} (hL : L ⊆ sphere z ρ) {r ε : ℝ} (hr : 0 < r)
    {y : ℂ} (hy : y ∈ thickening (ε * r) (scaleSet r 0 L)) :
    |‖y - r * z‖ - r * ρ| < ε * r := by
  rw [mem_thickening_iff] at hy
  obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := hy
  have hx' : ‖x - z‖ = ρ := by simpa [dist_eq_norm] using hL hx
  rw [dist_eq_norm] at hd
  simp only [add_zero] at hd
  have : ‖(r : ℂ) * x - r * z‖ = r * ρ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hx']
  rw [← this]
  calc |‖y - r * z‖ - ‖(r : ℂ) * x - r * z‖| ≤ ‖(y - r * z) - (r * x - r * z)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖y - r * x‖ := by ring_nf
    _ < ε * r := hd

/-- a point at angle `ψ` around `c` is at distance `||y − c| − R|` from `c + R e^{iψ}` -/
lemma dist_polar {c y : ℂ} {ψ R : ℝ} (hy : y - c = ‖y - c‖ * cis' ψ) :
    ‖y - (c + R * cis' ψ)‖ = |‖y - c‖ - R| := by
  calc ‖y - (c + R * cis' ψ)‖ = ‖((‖y - c‖ - R : ℝ) : ℂ) * cis' ψ‖ := by
        congr 1
        rw [show y - (c + R * cis' ψ) = (y - c) - R * cis' ψ by ring]
        conv_lhs => rw [hy]
        push_cast; ring
    _ = |‖y - c‖ - R| := by
        rw [norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- polar form from a logarithm -/
lemma polar_of_exp {w Γ : ℂ} (h : Complex.exp Γ = w) : w = ‖w‖ * cis' Γ.im := by
  rw [← h, Complex.norm_exp, cis', Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im Γ]

/-- **continuous argument along a path** avoiding `c` (path lifting for `exp`) -/
lemma exists_arg_lift (γ : ℝ → ℂ) (hγ : Continuous γ) (c : ℂ) (hc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ c) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ φ 0 = (Complex.log (γ 0 - c)).im ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t - c = ‖γ t - c‖ * cis' (φ t) := by
  let γI : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨γ t - c, sub_ne_zero.2 (hc t t.2)⟩,
      (hγ.comp continuous_subtype_val).sub continuous_const |>.subtype_mk _⟩
  have h0 : γ 0 - c ≠ 0 := sub_ne_zero.2 (hc 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨Γ, hΓ, hΓ0⟩ := Complex.isCoveringMap_exp.exists_path_lifts γI (Complex.log (γ 0 - c))
    (by ext; simp [γI, Complex.exp_log h0])
  refine ⟨IccExtend zero_le_one fun t => (Γ t).im, ?_, ?_, ?_⟩
  · exact continuous_IccExtend_iff.2 (Complex.continuous_im.comp Γ.continuous)
  · rw [IccExtend_left]
    show (Γ 0).im = _
    rw [hΓ0]
  · intro t ht
    rw [IccExtend_of_mem _ _ ht]
    have := congrArg Subtype.val (congrFun hΓ ⟨t, ht⟩)
    exact polar_of_exp this

end LQGMetric.DFGPS.P41
