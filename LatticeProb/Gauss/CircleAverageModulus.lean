import LatticeProb.Gauss.CircleAverageIncrement

/-!
# Moments of increments of the rescaled circle-average process

Two ingredients for a quantitative modulus of continuity of the circle-average process
`(r, z) ↦ h_r(z)` of the whole-plane Gaussian free field, uniform over scales.

* Absolute moments of a centred Gaussian variable: `E|X|^p = Var[X]^{p/2} E|Z|^p` with `Z` a
  standard Gaussian (`integral_abs_rpow_of_hasGaussianLaw`).
* The circle-average process rescaled around a centre `z₀` at scale `ε`,
  `x ↦ h_{ε x₀}(z₀ + ε (x₁ + i x₂))` on the box `[1/2, 1] × [0, 1]²`, satisfies the
  Kolmogorov–Chentsov moment bound
  `E|X_x - X_y|^p ≤ E|Z|^p · 12^{p/2} · dist(x, y)^{p/2}`,
  with a constant independent of `ε` and `z₀` (`integral_abs_rpow_circleRescaled_sub_le`). This
  follows from the increment variance bound `Var[h_s(z) - h_{s'}(z')] ≤ 2 (|s - s'| + |z - z'|) / min(s, s')`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- Absolute moments of a centred Gaussian law: `∫ |x|^p d N(0, v) = v^{p/2} ∫ |x|^p d N(0, 1)`. -/
theorem integral_abs_rpow_gaussianReal_zero (v : ℝ≥0) {p : ℝ} (hp : 0 ≤ p) :
    ∫ x, |x| ^ p ∂(gaussianReal 0 v) = (v : ℝ) ^ (p / 2) * ∫ x, |x| ^ p ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (Real.sqrt v * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  rw [← integral_const_mul]
  congr 1
  ext x
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul (NNReal.coe_nonneg v)]
  ring_nf

/-- Absolute moments of a centred random variable with a Gaussian law:
`E|X|^p = Var[X]^{p/2} E|Z|^p` with `Z` a standard Gaussian. -/
theorem integral_abs_rpow_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasGaussianLaw X P) (h0 : ∫ ω, X ω ∂P = 0) {p : ℝ} (hp : 0 ≤ p) :
    ∫ ω, |X ω| ^ p ∂P = Var[X; P] ^ (p / 2) * ∫ x, |x| ^ p ∂(gaussianReal 0 1) := by
  have hmap := hX.map_eq_gaussianReal
  rw [h0] at hmap
  rw [← integral_map (f := fun x : ℝ => |x| ^ p) hX.aemeasurable (by fun_prop), hmap,
    integral_abs_rpow_gaussianReal_zero _ hp, Real.coe_toNNReal _ (variance_nonneg X P)]

/-- A random variable with a Gaussian law has integrable absolute moments of every order. -/
theorem integrable_abs_rpow_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => |X ω| ^ p) P := by
  have h := (hX.memLp (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp] using h

/-- The circle-average process rescaled around the centre `z₀` at scale `ε`:
`x ↦ h_{ε x₀}(z₀ + ε (x₁ + i x₂))` for `x ∈ ℝ³`. -/
def circleRescaled {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (ε : ℝ) (z₀ : ℂ) (x : Fin 3 → ℝ)
    (ω : Ω) : ℝ :=
  hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)

/-- The lower corner `(1/2, 0, 0)` of the box of radii ratios and rescaled centres. -/
def circleBoxLower : Fin 3 → ℝ := ![1 / 2, 0, 0]

/-- The upper corner `(1, 1, 1)` of the box of radii ratios and rescaled centres. -/
def circleBoxUpper : Fin 3 → ℝ := ![1, 1, 1]

theorem le_coord_zero_of_mem_circleBox {x : Fin 3 → ℝ}
    (hx : x ∈ Set.Icc circleBoxLower circleBoxUpper) : 1 / 2 ≤ x 0 := by
  simpa [circleBoxLower] using hx.1 0

theorem abs_coord_le_one_of_mem_circleBox {x : Fin 3 → ℝ}
    (hx : x ∈ Set.Icc circleBoxLower circleBoxUpper) (i : Fin 3) : |x i| ≤ 1 := by
  have h1 : circleBoxLower i ≤ x i := hx.1 i
  have h2 : x i ≤ circleBoxUpper i := hx.2 i
  have h0 : 0 ≤ circleBoxLower i := by
    fin_cases i <;> norm_num [circleBoxLower]
  have h3 : circleBoxUpper i ≤ 1 := by
    fin_cases i <;> norm_num [circleBoxUpper]
  rw [abs_le]
  constructor <;> linarith

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The increment variance of the rescaled circle-average process on the box
`[1/2, 1] × [0, 1]²` is at most `12 dist(x, y)` (sup distance), for every scale `ε > 0` and every
centre `z₀`. -/
theorem variance_circleRescaled_sub_le (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (z₀ : ℂ) {x y : Fin 3 → ℝ} (hx : x ∈ Set.Icc circleBoxLower circleBoxUpper)
    (hy : y ∈ Set.Icc circleBoxLower circleBoxUpper) :
    Var[fun ω => circleRescaled hcirc ε z₀ x ω - circleRescaled hcirc ε z₀ y ω; P]
      ≤ 12 * dist x y := by
  have hx0 := le_coord_zero_of_mem_circleBox hx
  have hy0 := le_coord_zero_of_mem_circleBox hy
  have hs : 0 < ε * x 0 := mul_pos hε (by linarith)
  have hs' : 0 < ε * y 0 := mul_pos hε (by linarith)
  have hV := hh.variance_circle_sub_le hs hs' (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
    (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)
  refine (show Var[fun ω => circleRescaled hcirc ε z₀ x ω - circleRescaled hcirc ε z₀ y ω; P]
      = Var[fun ω => hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
          - hcirc ω (ε * y 0) (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩); P] from rfl) ▸ hV.trans ?_
  have hd : ∀ i, |x i - y i| ≤ dist x y := fun i => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
  have hrad : |ε * x 0 - ε * y 0| ≤ ε * dist x y := by
    rw [← mul_sub, abs_mul, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (hd 0) hε.le
  have hcen : ‖(z₀ + (ε : ℂ) * ⟨x 1, x 2⟩) - (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)‖ ≤ ε * (2 * dist x y) := by
    have heq : (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩) - (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)
        = (ε : ℂ) * ⟨x 1 - y 1, x 2 - y 2⟩ := by
      apply Complex.ext <;> simp <;> ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only
    linarith [hd 1, hd 2]
  have hmin : ε / 2 ≤ min (ε * x 0) (ε * y 0) :=
    le_min (by nlinarith) (by nlinarith)
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hε2 : 0 < ε / 2 := by linarith
  calc 2 * ((|ε * x 0 - ε * y 0| + ‖(z₀ + (ε : ℂ) * ⟨x 1, x 2⟩) - (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)‖)
        / min (ε * x 0) (ε * y 0))
      ≤ 2 * ((ε * dist x y + ε * (2 * dist x y)) / (ε / 2)) := by
        gcongr
    _ = 12 * dist x y := by
        field_simp
        ring

/-- **Kolmogorov–Chentsov moment bound for the rescaled circle-average process.** On the box
`[1/2, 1] × [0, 1]²`, for every scale `ε > 0`, every centre `z₀` and every `p ≥ 0`,
`E|X_x - X_y|^p ≤ E|Z|^p · 12^{p/2} · dist(x, y)^{p/2}` with `Z` a standard Gaussian. -/
theorem integral_abs_rpow_circleRescaled_sub_le (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (z₀ : ℂ) {p : ℝ} (hp : 0 ≤ p) {x y : Fin 3 → ℝ}
    (hx : x ∈ Set.Icc circleBoxLower circleBoxUpper)
    (hy : y ∈ Set.Icc circleBoxLower circleBoxUpper) :
    ∫ ω, |circleRescaled hcirc ε z₀ x ω - circleRescaled hcirc ε z₀ y ω| ^ p ∂P
      ≤ (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * dist x y ^ (p / 2) := by
  have hx0 := le_coord_zero_of_mem_circleBox hx
  have hy0 := le_coord_zero_of_mem_circleBox hy
  have hs : 0 < ε * x 0 := mul_pos hε (by linarith)
  have hs' : 0 < ε * y 0 := mul_pos hε (by linarith)
  have hG := hh.hasGaussianLaw_circle_sub hs hs' (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
    (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)
  have h0 := hh.integral_circle_sub hs hs' (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
    (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)
  have hmom := integral_abs_rpow_of_hasGaussianLaw hG h0 hp
  have hV := hh.variance_circleRescaled_sub_le hε z₀ hx hy
  have hC0 : 0 ≤ ∫ t, |t| ^ p ∂(gaussianReal 0 1) :=
    integral_nonneg (fun t => Real.rpow_nonneg (abs_nonneg t) p)
  have hp2 : 0 ≤ p / 2 := by linarith
  change ∫ ω, |hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
      - hcirc ω (ε * y 0) (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)| ^ p ∂P ≤ _
  rw [hmom]
  have hVr : Var[fun ω => hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
      - hcirc ω (ε * y 0) (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩); P] ^ (p / 2)
      ≤ 12 ^ (p / 2) * dist x y ^ (p / 2) := by
    rw [← Real.mul_rpow (by norm_num) dist_nonneg]
    exact Real.rpow_le_rpow (variance_nonneg _ _) hV hp2
  calc Var[fun ω => hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
        - hcirc ω (ε * y 0) (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩); P] ^ (p / 2)
        * ∫ t, |t| ^ p ∂(gaussianReal 0 1)
      ≤ (12 ^ (p / 2) * dist x y ^ (p / 2)) * ∫ t, |t| ^ p ∂(gaussianReal 0 1) :=
        mul_le_mul_of_nonneg_right hVr hC0
    _ = (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * dist x y ^ (p / 2) := by ring

/-- The increments of the rescaled circle-average process have integrable absolute moments of
every order. -/
theorem integrable_abs_rpow_circleRescaled_sub (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (z₀ : ℂ) {p : ℝ} (hp : 0 ≤ p) {x y : Fin 3 → ℝ}
    (hx : x ∈ Set.Icc circleBoxLower circleBoxUpper)
    (hy : y ∈ Set.Icc circleBoxLower circleBoxUpper) :
    Integrable (fun ω => |circleRescaled hcirc ε z₀ x ω - circleRescaled hcirc ε z₀ y ω| ^ p) P := by
  have := hh.isProbabilityMeasure
  have hx0 := le_coord_zero_of_mem_circleBox hx
  have hy0 := le_coord_zero_of_mem_circleBox hy
  have hs : 0 < ε * x 0 := mul_pos hε (by linarith)
  have hs' : 0 < ε * y 0 := mul_pos hε (by linarith)
  have h := integrable_abs_rpow_of_hasGaussianLaw (P := P)
    (X := fun ω => hcirc ω (ε * x 0) (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
      - hcirc ω (ε * y 0) (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩))
    (hh.hasGaussianLaw_circle_sub hs hs' (z₀ + (ε : ℂ) * ⟨x 1, x 2⟩)
      (z₀ + (ε : ℂ) * ⟨y 1, y 2⟩)) hp
  exact h

end IsWholePlaneGFF

end LatticeProb.Gauss
