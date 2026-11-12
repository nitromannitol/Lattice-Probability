/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18T4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Law transfer for functionals that are multiplicatively stable under sup-norm perturbations

A general form of the law step of DG:1774–1777 / DG:1593–1595 (used for `DGProp3_17Sq`, whose
event involves `D^δ(K, ∂U)` with paths in a non-convex `Ū`, where the chain argument of
`S3P18T3` is not available).

Let `X ⊂ ℂ` be bounded and `F : (ℂ → ℝ) → [0,∞]` satisfy the LFPP comparison
`φ ≤ ψ + η` on `X` ⇒ `F φ ≤ e^{ξη} F ψ` (for measurable `φ, ψ`, `ψ` bounded on `X`). Then:

* `F φ_n`, `φ_n = g ∘ (grid rounding at mesh 1/(n+1))`, depends on finitely many coordinates
  `g q`, and is upper semicontinuous in them, hence measurable (`t18_measurable_Fn`);
* for continuous `φ`, `F φ_n → F φ` (uniform continuity on a compact set) (`t18_tendsto_Fn`);
* hence **`t18_repr`**: `F φ = Φ (φ|_{ℚ²})` with `Φ` measurable, and
  **`t18_lower_eq`**: `P{¬ t ≤ F(hc δ ·)}` does not depend on the process `hc`.

Own elementary argument (DG uses the measurability without comment).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- the Gaussian rational point `q₁ + q₂ i` -/
def t18pt0 (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- rounding down to the grid of mesh `1/(n+1)` -/
def t18gq (n : ℕ) (x : ℂ) : ℚ × ℚ :=
  ((⌊((n : ℝ) + 1) * x.re⌋ : ℚ) / ((n : ℚ) + 1), (⌊((n : ℝ) + 1) * x.im⌋ : ℚ) / ((n : ℚ) + 1))

lemma t18_floor_err {m a : ℝ} (hm : 0 < m) : |(⌊m * a⌋ : ℝ) / m - a| ≤ 1 / m := by
  have h1 := Int.floor_le (m * a)
  have h2 := Int.lt_floor_add_one (m * a)
  have e : (⌊m * a⌋ : ℝ) / m - a = ((⌊m * a⌋ : ℝ) - m * a) / m := by field_simp
  rw [e, abs_div, abs_of_pos hm, div_le_div_iff_of_pos_right hm, abs_le]
  constructor <;> linarith

lemma t18_gq_err (n : ℕ) (x : ℂ) : ‖t18pt0 (t18gq n x) - x‖ ≤ 2 / ((n : ℝ) + 1) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (t18pt0 (t18gq n x) - x).re = (⌊((n : ℝ) + 1) * x.re⌋ : ℝ) / ((n : ℝ) + 1) - x.re := by
    simp only [t18pt0, t18gq, Complex.sub_re, Complex.add_re, Complex.ratCast_re, Complex.mul_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im]
    push_cast; ring
  have e2 : (t18pt0 (t18gq n x) - x).im = (⌊((n : ℝ) + 1) * x.im⌋ : ℝ) / ((n : ℝ) + 1) - x.im := by
    simp only [t18pt0, t18gq, Complex.sub_im, Complex.add_im, Complex.ratCast_re, Complex.mul_im,
      Complex.ratCast_im, Complex.I_re, Complex.I_im]
    push_cast; ring
  rw [e1, e2]
  have := t18_floor_err (a := x.re) hm
  have := t18_floor_err (a := x.im) hm
  rw [show (2 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) by ring]
  linarith

lemma t18_floor_mem {m a R : ℝ} (hm : 0 < m) (ha : |a| ≤ R) :
    ⌊m * a⌋ ∈ Finset.Icc (-(⌈m * R⌉ + 1)) (⌈m * R⌉ + 1) := by
  rw [Finset.mem_Icc]
  have h1 := Int.floor_le (m * a)
  have h2 := Int.lt_floor_add_one (m * a)
  have h3 := Int.le_ceil (m * R)
  rw [abs_le] at ha
  have h4 : m * a ≤ m * R := mul_le_mul_of_nonneg_left ha.2 hm.le
  have h5 : m * (-R) ≤ m * a := mul_le_mul_of_nonneg_left ha.1 hm.le
  constructor
  · have : ((-(⌈m * R⌉ + 1) : ℤ) : ℝ) ≤ ⌊m * a⌋ := by push_cast; nlinarith
    exact_mod_cast this
  · have : ((⌊m * a⌋ : ℤ) : ℝ) ≤ ((⌈m * R⌉ + 1 : ℤ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this

lemma t18_gq_finite {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R) (n : ℕ) :
    (t18gq n '' X).Finite := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set K : ℤ := ⌈((n : ℝ) + 1) * R⌉ + 1
  refine ((((Finset.Icc (-K) K) ×ˢ (Finset.Icc (-K) K)).image
    (fun p : ℤ × ℤ => ((p.1 : ℚ) / ((n : ℚ) + 1), (p.2 : ℚ) / ((n : ℚ) + 1)))).finite_toSet).subset
    ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hX hx
  rw [mem_closedBall, dist_zero_right] at hx'
  simp only [Finset.coe_image, Finset.coe_product, mem_image, mem_prod, Finset.mem_coe]
  exact ⟨(⌊((n : ℝ) + 1) * x.re⌋, ⌊((n : ℝ) + 1) * x.im⌋),
    ⟨t18_floor_mem hm ((Complex.abs_re_le_norm x).trans hx'),
      t18_floor_mem hm ((Complex.abs_im_le_norm x).trans hx')⟩, rfl⟩

lemma t18_measurable_gq (n : ℕ) : Measurable (t18gq n) := by
  have h : ∀ f : ℂ → ℝ, Measurable f → Measurable fun x => ((⌊((n : ℝ) + 1) * f x⌋ : ℚ) /
      ((n : ℚ) + 1)) := fun f hf =>
    (measurable_of_countable (fun k : ℤ => (k : ℚ) / ((n : ℚ) + 1))).comp
      (Int.measurable_floor.comp (hf.const_mul _))
  exact (h _ Complex.measurable_re).prodMk (h _ Complex.measurable_im)

/-- the step approximant `x ↦ g(grid point of x)` -/
def t18step (n : ℕ) (g : ℚ × ℚ → ℝ) : ℂ → ℝ := fun x => g (t18gq n x)

lemma t18_measurable_step (n : ℕ) (g : ℚ × ℚ → ℝ) : Measurable (t18step n g) :=
  (measurable_of_countable g).comp (t18_measurable_gq n)

lemma t18_step_bdd {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R) (n : ℕ) (g : ℚ × ℚ → ℝ) :
    ∃ B, ∀ x ∈ X, |t18step n g x| ≤ B := by
  obtain ⟨B, hB⟩ := ((t18_gq_finite hX n).image (fun q => |g q|)).bddAbove
  exact ⟨B, fun x hx => hB ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩

/-- the comparison property of an LFPP-type functional on `X` -/
def T18Cmp (ξ : ℝ) (X : Set ℂ) (F : (ℂ → ℝ) → ℝ≥0∞) : Prop :=
  ∀ φ ψ : ℂ → ℝ, Measurable φ → Measurable ψ → (∃ B, ∀ x ∈ X, |ψ x| ≤ B) →
    ∀ η : ℝ, 0 ≤ η → (∀ x ∈ X, φ x ≤ ψ x + η) → F φ ≤ ENNReal.ofReal (Real.exp (ξ * η)) * F ψ

lemma t18_tendsto_expfac (ξ : ℝ) (a : ℝ≥0∞) (ha : a ≠ ∞) :
    Tendsto (fun η : ℝ => ENNReal.ofReal (Real.exp (ξ * η)) * a) (𝓝 0) (𝓝 a) := by
  have h : Tendsto (fun η : ℝ => ENNReal.ofReal (Real.exp (ξ * η))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun η : ℝ => Real.exp (ξ * η) := by fun_prop
    have := ENNReal.tendsto_ofReal (hc.tendsto (0 : ℝ))
    simpa using this
  simpa using ENNReal.Tendsto.mul_const h (Or.inr ha)

/-- `∃ η > 0` with `e^{ξη} a < b`, for `a < b` -/
lemma t18_exists_eta {ξ : ℝ} {a b : ℝ≥0∞} (hab : a < b) :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (Real.exp (ξ * η)) * a < b := by
  have hev := (t18_tendsto_expfac ξ a hab.ne_top).eventually (gt_mem_nhds hab)
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨ε / 2, by positivity, h (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)⟩

lemma t18_measurable_Fn {ξ : ℝ} {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R)
    {F : (ℂ → ℝ) → ℝ≥0∞} (hF : T18Cmp ξ X F) (n : ℕ) :
    Measurable fun g : ℚ × ℚ → ℝ => F (t18step n g) := by
  refine measurable_of_Iio fun a => IsOpen.measurableSet ?_
  refine isOpen_iff_forall_mem_open.2 fun g hg => ?_
  obtain ⟨η, hη, hlt⟩ := t18_exists_eta (ξ := ξ) (show F (t18step n g) < a from hg)
  refine ⟨{g' | ∀ q ∈ t18gq n '' X, |g' q - g q| < η}, fun g' hg' => ?_, ?_, fun q _ => ?_⟩
  · refine lt_of_le_of_lt ?_ hlt
    refine hF _ _ (t18_measurable_step n g') (t18_measurable_step n g) (t18_step_bdd hX n g) η
      hη.le fun x hx => ?_
    have := hg' _ ⟨x, hx, rfl⟩
    rw [abs_lt] at this
    simp only [t18step]; linarith
  · have e : {g' : ℚ × ℚ → ℝ | ∀ q ∈ t18gq n '' X, |g' q - g q| < η} =
        ⋂ q ∈ t18gq n '' X, {g' : ℚ × ℚ → ℝ | |g' q - g q| < η} := by ext; simp
    rw [e]
    exact (t18_gq_finite hX n).isOpen_biInter fun q _ =>
      isOpen_lt ((continuous_apply q : Continuous fun g : ℚ × ℚ → ℝ => g q).sub
        continuous_const).abs continuous_const
  · simpa using hη

lemma t18_tendsto_Fn {ξ : ℝ} {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R)
    {F : (ℂ → ℝ) → ℝ≥0∞} (hF : T18Cmp ξ X F) {φ : ℂ → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => F (t18step n (fun q => φ (t18pt0 q)))) atTop (𝓝 (F φ)) := by
  have huc := (isCompact_closedBall (0 : ℂ) (R + 2)).uniformContinuousOn_of_continuous
    hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hφ.continuousOn
  have hφB : ∃ B, ∀ x ∈ X, |φ x| ≤ B := ⟨B, fun x hx => hB x (hX hx)⟩
  -- eventually the step function is `η`-close to `φ` on `X`
  have hclose : ∀ η > 0, ∀ᶠ n in atTop, ∀ x ∈ X, |φ (t18pt0 (t18gq n x)) - φ x| ≤ η := by
    intro η hη
    obtain ⟨ρ, hρ, hu⟩ := huc η hη
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ρ)
    refine eventually_atTop.2 ⟨N, fun n hn x hx => ?_⟩
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have herr := t18_gq_err n x
    have h2 : 2 / ((n : ℝ) + 1) < ρ := by
      rw [div_lt_iff₀ hm]
      rw [div_lt_iff₀ hρ] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have h2' : 2 / ((n : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hm]; nlinarith
    have hx' := hX hx
    rw [mem_closedBall, dist_zero_right] at hx'
    have hxB : x ∈ closedBall (0 : ℂ) (R + 2) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have hyB : t18pt0 (t18gq n x) ∈ closedBall (0 : ℂ) (R + 2) := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_le_norm_add_norm_sub' (t18pt0 (t18gq n x)) x
      linarith
    have := hu _ hyB _ hxB (by rw [dist_eq_norm]; linarith)
    rw [Real.dist_eq] at this
    exact this.le
  have hup : ∀ η > 0, ∀ᶠ n in atTop, F (t18step n (fun q => φ (t18pt0 q))) ≤
      ENNReal.ofReal (Real.exp (ξ * η)) * F φ := fun η hη =>
    (hclose η hη).mono fun n hn => hF _ _ (t18_measurable_step _ _) hφ.measurable hφB η hη.le
      fun x hx => by have := (abs_le.1 (hn x hx)).2; simp only [t18step]; linarith
  have hlo : ∀ η > 0, ∀ᶠ n in atTop, F φ ≤
      ENNReal.ofReal (Real.exp (ξ * η)) * F (t18step n (fun q => φ (t18pt0 q))) := fun η hη =>
    (hclose η hη).mono fun n hn => hF _ _ hφ.measurable (t18_measurable_step _ _)
      (t18_step_bdd hX n _) η hη.le
      fun x hx => by have := (abs_le.1 (hn x hx)).1; simp only [t18step]; linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨η, hη, hlt⟩ := t18_exists_eta (ξ := ξ) ha
    refine (hlo η hη).mono fun n hn => lt_of_not_ge fun hle => ?_
    exact absurd (hn.trans (by gcongr)) (not_le.2 hlt)
  · obtain ⟨η, hη, hlt⟩ := t18_exists_eta (ξ := ξ) ha
    exact (hup η hη).mono fun n hn => hn.trans_lt hlt

/-- **`F` is a measurable function of the rational values of a continuous `φ`** -/
theorem t18_repr {ξ : ℝ} {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R)
    {F : (ℂ → ℝ) → ℝ≥0∞} (hF : T18Cmp ξ X F) :
    ∃ Φ : (ℚ × ℚ → ℝ) → ℝ≥0∞, Measurable Φ ∧
      ∀ φ : ℂ → ℝ, Continuous φ → Φ (fun q => φ (t18pt0 q)) = F φ :=
  ⟨fun g => liminf (fun n => F (t18step n g)) atTop,
    Measurable.liminf fun n => t18_measurable_Fn hX hF n,
    fun _ hφ => (t18_tendsto_Fn hX hF hφ).liminf_eq⟩

lemma t18_lower_set {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) {δ : ℝ} (hδ : 0 < δ) {F : (ℂ → ℝ) → ℝ≥0∞}
    {Φ : (ℚ × ℚ → ℝ) → ℝ≥0∞} (hΦF : ∀ φ : ℂ → ℝ, Continuous φ → Φ (fun q => φ (t18pt0 q)) = F φ)
    (t : ℝ≥0∞) :
    {ω | ¬ t ≤ F (fun x => hc δ x ω)} = {ω | t18Coord hc δ t18pt0 ω ∈ {g | ¬ t ≤ Φ g}} := by
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [← hΦF _ (hG.continuous δ hδ ω)]
  rfl

/-- **law transfer of the lower-bound event `{t ≤ F(hc δ ·)}`** -/
theorem t18_lower_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hc : ℝ → ℂ → Ω → ℝ} {hc' : ℝ → ℂ → Ω' → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) (hG' : LQGDimension.IsGFFCircleAverage hc' P')
    {δ : ℝ} (hδ : 0 < δ) {ξ : ℝ} {X : Set ℂ} {R : ℝ} (hX : X ⊆ closedBall 0 R)
    {F : (ℂ → ℝ) → ℝ≥0∞} (hF : T18Cmp ξ X F) (t : ℝ≥0∞) :
    P {ω | ¬ t ≤ F (fun x => hc δ x ω)} = P' {ω | ¬ t ≤ F (fun x => hc' δ x ω)} := by
  obtain ⟨Φ, hΦ, hΦF⟩ := t18_repr hX hF
  rw [t18_lower_set hG hδ hΦF t, t18_lower_set hG' hδ hΦF t]
  exact t18T_measure_eq hG hG' hδ _ (measurableSet_le measurable_const hΦ).compl

end LQGMetric.DG
