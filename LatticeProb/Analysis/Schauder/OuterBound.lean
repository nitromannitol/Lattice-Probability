import LatticeProb.Analysis.Schauder.IBPTwice
import LatticeProb.Analysis.Schauder.DirDerivComm
import LatticeProb.Analysis.Schauder.ChainDeriv
import LatticeProb.Analysis.Schauder.BoundedDerivsCompact

/-!
# A kernel cut off near the origin absorbs a Laplacian

Let `χ` be a smooth bump function centred at the origin, equal to `1` on the ball of radius
`χ.rIn`, and let `K` be a `C²` kernel whose values and first two directional derivatives are
dominated, away from that ball, by a fixed integrable profile `G`. The cut-off kernel
`K' = (1 - χ) K` vanishes near the origin, so the singularity of `K` at the origin plays no role,
and by the Leibniz rule `K'` and its derivatives up to order two are dominated everywhere by `G`,
with constants that depend only on `χ` (through the sup norms of its first two derivatives).

Two integrations by parts then move the Laplacian from a bounded `C²` function `w` onto `K'`:
`∫ K'(y) Δw(x - y) dy = Σ_i ∫ ∂_i²K'(y) w(x - y) dy`, which is bounded by
`C · M · sup |w| · ∫ G`, where `C` depends only on `χ` and the dimension. The companion bound
`|∫ (1 - χ) K| ≤ M ∫ G` involves no derivatives.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A directional derivative of a `C²` function is `C¹`. -/
private theorem contDiff_one_dirDeriv {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (e : Euc d) :
    ContDiff ℝ 1 (dirDeriv e f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- A directional derivative of a `C²` function is differentiable. -/
private theorem differentiable_dirDeriv_of_contDiff_two {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (e : Euc d) : Differentiable ℝ (dirDeriv e f) :=
  (contDiff_one_dirDeriv hf e).differentiable one_ne_zero

/-- The directional derivative of a sum of differentiable functions. -/
private theorem dirDeriv_fun_add {f g : Euc d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (e : Euc d) :
    dirDeriv e (fun y => f y + g y) = fun y => dirDeriv e f y + dirDeriv e g y := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_fun_add (hf y) (hg y)]
  rfl

/-- The Leibniz rule for the directional derivative of a product of differentiable functions. -/
private theorem dirDeriv_fun_mul {f g : Euc d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (e : Euc d) :
    dirDeriv e (fun y => f y * g y) = fun y => dirDeriv e f y * g y + f y * dirDeriv e g y := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_fun_mul (hf y) (hg y)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The directional derivative of the negative of a function. -/
private theorem dirDeriv_fun_neg (f : Euc d → ℝ) (e : Euc d) :
    dirDeriv e (fun y => -f y) = fun y => -dirDeriv e f y := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_fun_neg]
  rfl

/-- The directional derivative of `1 - f`. -/
private theorem dirDeriv_fun_one_sub (f : Euc d → ℝ) (e : Euc d) :
    dirDeriv e (fun y => 1 - f y) = fun y => -dirDeriv e f y := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_const_sub]
  rfl

/-- The first directional derivative of `(1 - f) K`. -/
private theorem dirDeriv_one_sub_mul {f K : Euc d → ℝ} (hf : Differentiable ℝ f)
    (hK : Differentiable ℝ K) (e : Euc d) :
    dirDeriv e (fun z => (1 - f z) * K z) =
      fun z => -dirDeriv e f z * K z + (1 - f z) * dirDeriv e K z := by
  rw [dirDeriv_fun_mul (hf.const_sub 1) hK e, dirDeriv_fun_one_sub]

/-- The second directional derivative of `(1 - f) K`. -/
private theorem dirDeriv_dirDeriv_one_sub_mul {f K : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hK : ContDiff ℝ 2 K) (e e' : Euc d) (y : Euc d) :
    dirDeriv e' (dirDeriv e (fun z => (1 - f z) * K z)) y =
      -dirDeriv e' (dirDeriv e f) y * K y + -dirDeriv e f y * dirDeriv e' K y +
        -dirDeriv e' f y * dirDeriv e K y + (1 - f y) * dirDeriv e' (dirDeriv e K) y := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hfe := differentiable_dirDeriv_of_contDiff_two hf e
  have hKe := differentiable_dirDeriv_of_contDiff_two hK e
  have hneg : Differentiable ℝ fun z => -dirDeriv e f z := hfe.neg
  have hone : Differentiable ℝ fun z => 1 - f z := hfd.const_sub 1
  have hA : Differentiable ℝ fun z => -dirDeriv e f z * K z := hneg.mul hKd
  have hB : Differentiable ℝ fun z => (1 - f z) * dirDeriv e K z := hone.mul hKe
  rw [dirDeriv_one_sub_mul hfd hKd e, dirDeriv_fun_add hA hB e', dirDeriv_fun_mul hneg hKd e',
    dirDeriv_fun_mul hone hKe e', dirDeriv_fun_neg, dirDeriv_fun_one_sub]
  ring

/-- A function vanishing on an open set has vanishing directional derivatives there. -/
private theorem dirDeriv_eq_zero_of_forall_mem {f : Euc d → ℝ} {s : Set (Euc d)}
    (hs : IsOpen s) (hf : ∀ z ∈ s, f z = 0) (e : Euc d) : ∀ z ∈ s, dirDeriv e f z = 0 := by
  intro z hz
  have h : f =ᶠ[nhds z] fun _ => 0 := Filter.eventually_of_mem (hs.mem_nhds hz) hf
  simp only [dirDeriv]
  rw [h.fderiv_eq]
  simp

/-- The factor `1 - χ` vanishes inside the ball where the bump equals `1`. -/
private theorem one_sub_bump_eq_zero (χ : ContDiffBump (0 : Euc d)) {y : Euc d}
    (hy : ‖y‖ < χ.rIn) : 1 - χ y = 0 := by
  have hy' : y ∈ Metric.closedBall (0 : Euc d) χ.rIn :=
    Metric.ball_subset_closedBall (mem_ball_zero_iff.2 hy)
  rw [χ.one_of_mem_closedBall hy', sub_self]

/-- The first two directional derivatives of `(1 - χ) K` vanish inside the ball where the bump
equals `1`. -/
private theorem dirDeriv_one_sub_bump_mul_eq_zero (χ : ContDiffBump (0 : Euc d))
    (K : Euc d → ℝ) {y : Euc d} (hy : ‖y‖ < χ.rIn) (e e' : Euc d) :
    dirDeriv e (fun z => (1 - χ z) * K z) y = 0 ∧
      dirDeriv e' (dirDeriv e (fun z => (1 - χ z) * K z)) y = 0 := by
  have hs : IsOpen (Metric.ball (0 : Euc d) χ.rIn) := Metric.isOpen_ball
  have h0 : ∀ z ∈ Metric.ball (0 : Euc d) χ.rIn, (1 - χ z) * K z = 0 := fun z hz => by
    rw [one_sub_bump_eq_zero χ (mem_ball_zero_iff.1 hz), zero_mul]
  have h1 := dirDeriv_eq_zero_of_forall_mem hs h0 e
  have h2 := dirDeriv_eq_zero_of_forall_mem hs h1 e'
  have hy' : y ∈ Metric.ball (0 : Euc d) χ.rIn := mem_ball_zero_iff.2 hy
  exact ⟨h1 y hy', h2 y hy'⟩

/-- The absolute value of a product is bounded by the product of bounds. -/
private theorem abs_mul_le_mul_of_abs_le' {a b p q : ℝ} (ha : |a| ≤ p) (hb : |b| ≤ q) :
    |a * b| ≤ p * q := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The triangle inequality for four terms. -/
private theorem abs_add_four_le (a b c e : ℝ) : |a + b + c + e| ≤ |a| + |b| + |c| + |e| := by
  have h1 := abs_add_le (a + b + c) e
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- The first two derivatives of a smooth bump function are bounded by constants times the norms
of the directions. -/
private theorem exists_bump_dirDeriv_bounds (χ : ContDiffBump (0 : Euc d)) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ (∀ y e, |dirDeriv e (fun z => χ z) y| ≤ M₁ * ‖e‖) ∧
      ∀ y e e', |dirDeriv e' (dirDeriv e (fun z => χ z)) y| ≤ M₂ * ‖e‖ * ‖e'‖ := by
  have hb := boundedDerivs_bump 2 χ
  obtain ⟨M₁, hM₁⟩ := hb.exists_norm_fderiv_le
  obtain ⟨M₂, hM₂⟩ := hb.2 2 le_rfl
  have hχ2 : ContDiff ℝ 2 (fun z => χ z) := χ.contDiff
  refine ⟨M₁, M₂, (norm_nonneg _).trans (hM₁ 0), (norm_nonneg _).trans (hM₂ 0),
    fun y e => ?_, fun y e e' => ?_⟩
  · calc |dirDeriv e (fun z => χ z) y| = ‖fderiv ℝ (fun z => χ z) y e‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fun z => χ z) y‖ * ‖e‖ := (fderiv ℝ (fun z => χ z) y).le_opNorm e
      _ ≤ M₁ * ‖e‖ := mul_le_mul_of_nonneg_right (hM₁ y) (norm_nonneg e)
  · calc |dirDeriv e' (dirDeriv e (fun z => χ z)) y|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => χ z) y‖ * (‖e'‖ * ‖e‖) := abs_dirDeriv_two_le hχ2 y e' e
      _ ≤ M₂ * (‖e'‖ * ‖e‖) := mul_le_mul_of_nonneg_right (hM₂ y) (by positivity)
      _ = M₂ * ‖e‖ * ‖e'‖ := by ring

/-- The cut-off kernel `(1 - χ) K` is dominated by `M G` everywhere. -/
private theorem abs_one_sub_bump_mul_le (χ : ContDiffBump (0 : Euc d)) {K G : Euc d → ℝ}
    {M : ℝ} (hG0 : ∀ y, 0 ≤ G y) (hM : 0 ≤ M)
    (hKG : ∀ y, χ.rIn ≤ ‖y‖ → |K y| ≤ M * G y) (y : Euc d) :
    |(1 - χ y) * K y| ≤ M * G y := by
  by_cases hy : ‖y‖ < χ.rIn
  · rw [one_sub_bump_eq_zero χ hy, zero_mul, abs_zero]
    exact mul_nonneg hM (hG0 y)
  · have h1 : |1 - χ y| ≤ 1 := abs_le.2 ⟨by linarith [χ.le_one (x := y)],
      by linarith [χ.nonneg (x := y)]⟩
    calc |(1 - χ y) * K y| ≤ 1 * (M * G y) :=
          abs_mul_le_mul_of_abs_le' h1 (hKG y (not_lt.1 hy))
      _ = M * G y := one_mul _

/-- The first derivative of the cut-off kernel `(1 - χ) K` is dominated by `G`. -/
private theorem abs_dirDeriv_one_sub_bump_mul_le (χ : ContDiffBump (0 : Euc d))
    {K G : Euc d → ℝ} {M M₁ : ℝ} (hK : ContDiff ℝ 2 K) (hG0 : ∀ y, 0 ≤ G y) (hM : 0 ≤ M)
    (hM₁ : 0 ≤ M₁) (hχ₁ : ∀ y e, |dirDeriv e (fun z => χ z) y| ≤ M₁ * ‖e‖)
    (hK0 : ∀ y, χ.rIn ≤ ‖y‖ → |K y| ≤ M * G y)
    (hK1 : ∀ y e, χ.rIn ≤ ‖y‖ → |dirDeriv e K y| ≤ M * ‖e‖ * G y) (y e : Euc d) :
    |dirDeriv e (fun z => (1 - χ z) * K z) y| ≤ (1 + M₁) * M * ‖e‖ * G y := by
  by_cases hy : ‖y‖ < χ.rIn
  · rw [(dirDeriv_one_sub_bump_mul_eq_zero χ K hy e e).1, abs_zero]
    have := hG0 y
    positivity
  · have hy' := not_lt.1 hy
    have h1 : |1 - χ y| ≤ 1 := abs_le.2 ⟨by linarith [χ.le_one (x := y)],
      by linarith [χ.nonneg (x := y)]⟩
    rw [dirDeriv_one_sub_mul ((χ.contDiff (n := 2)).differentiable (by norm_num))
      (hK.differentiable (by norm_num)) e]
    have ha : |-dirDeriv e (fun z => χ z) y| ≤ M₁ * ‖e‖ := by rw [abs_neg]; exact hχ₁ y e
    calc |-dirDeriv e (fun z => χ z) y * K y + (1 - χ y) * dirDeriv e K y|
        ≤ |-dirDeriv e (fun z => χ z) y * K y| + |(1 - χ y) * dirDeriv e K y| := abs_add_le _ _
      _ ≤ M₁ * ‖e‖ * (M * G y) + 1 * (M * ‖e‖ * G y) :=
          add_le_add (abs_mul_le_mul_of_abs_le' ha (hK0 y hy'))
            (abs_mul_le_mul_of_abs_le' h1 (hK1 y e hy'))
      _ = (1 + M₁) * M * ‖e‖ * G y := by ring

/-- The second derivative of the cut-off kernel `(1 - χ) K` is dominated by `G`. -/
private theorem abs_dirDeriv_dirDeriv_one_sub_bump_mul_le (χ : ContDiffBump (0 : Euc d))
    {K G : Euc d → ℝ} {M M₁ M₂ : ℝ} (hK : ContDiff ℝ 2 K) (hG0 : ∀ y, 0 ≤ G y) (hM : 0 ≤ M)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hχ₁ : ∀ y e, |dirDeriv e (fun z => χ z) y| ≤ M₁ * ‖e‖)
    (hχ₂ : ∀ y e e', |dirDeriv e' (dirDeriv e (fun z => χ z)) y| ≤ M₂ * ‖e‖ * ‖e'‖)
    (hK0 : ∀ y, χ.rIn ≤ ‖y‖ → |K y| ≤ M * G y)
    (hK1 : ∀ y e, χ.rIn ≤ ‖y‖ → |dirDeriv e K y| ≤ M * ‖e‖ * G y)
    (hK2 : ∀ y e e', χ.rIn ≤ ‖y‖ → |dirDeriv e' (dirDeriv e K) y| ≤ M * ‖e‖ * ‖e'‖ * G y)
    (y e e' : Euc d) :
    |dirDeriv e' (dirDeriv e (fun z => (1 - χ z) * K z)) y| ≤
      (1 + 2 * M₁ + M₂) * M * ‖e‖ * ‖e'‖ * G y := by
  by_cases hy : ‖y‖ < χ.rIn
  · rw [(dirDeriv_one_sub_bump_mul_eq_zero χ K hy e e').2, abs_zero]
    have := hG0 y
    positivity
  · have hy' := not_lt.1 hy
    have h1 : |1 - χ y| ≤ 1 := abs_le.2 ⟨by linarith [χ.le_one (x := y)],
      by linarith [χ.nonneg (x := y)]⟩
    rw [dirDeriv_dirDeriv_one_sub_mul (χ.contDiff (n := 2)) hK e e' y]
    have ha : |-dirDeriv e' (dirDeriv e (fun z => χ z)) y| ≤ M₂ * ‖e‖ * ‖e'‖ := by
      rw [abs_neg]; exact hχ₂ y e e'
    have hb : |-dirDeriv e (fun z => χ z) y| ≤ M₁ * ‖e‖ := by rw [abs_neg]; exact hχ₁ y e
    have hc : |-dirDeriv e' (fun z => χ z) y| ≤ M₁ * ‖e'‖ := by rw [abs_neg]; exact hχ₁ y e'
    calc |-dirDeriv e' (dirDeriv e (fun z => χ z)) y * K y +
          -dirDeriv e (fun z => χ z) y * dirDeriv e' K y +
          -dirDeriv e' (fun z => χ z) y * dirDeriv e K y +
          (1 - χ y) * dirDeriv e' (dirDeriv e K) y|
        ≤ |-dirDeriv e' (dirDeriv e (fun z => χ z)) y * K y| +
          |-dirDeriv e (fun z => χ z) y * dirDeriv e' K y| +
          |-dirDeriv e' (fun z => χ z) y * dirDeriv e K y| +
          |(1 - χ y) * dirDeriv e' (dirDeriv e K) y| := abs_add_four_le _ _ _ _
      _ ≤ M₂ * ‖e‖ * ‖e'‖ * (M * G y) + M₁ * ‖e‖ * (M * ‖e'‖ * G y) +
          M₁ * ‖e'‖ * (M * ‖e‖ * G y) + 1 * (M * ‖e‖ * ‖e'‖ * G y) :=
          add_le_add (add_le_add (add_le_add
            (abs_mul_le_mul_of_abs_le' ha (hK0 y hy'))
            (abs_mul_le_mul_of_abs_le' hb (hK1 y e' hy')))
            (abs_mul_le_mul_of_abs_le' hc (hK1 y e hy')))
            (abs_mul_le_mul_of_abs_le' h1 (hK2 y e e' hy'))
      _ = (1 + 2 * M₁ + M₂) * M * ‖e‖ * ‖e'‖ * G y := by ring

/-- Moving the Laplacian onto a `C²` kernel with integrable derivatives dominated by a profile `G`
costs a constant times `sup |w| · ∫ G`: the sum over the coordinate directions of two integrations
by parts, each bounded using the domination of the second derivatives of the kernel. -/
private theorem abs_integral_mul_laplacianSum_le {K G w : Euc d → ℝ} {B₀ B₁ B₂ A : ℝ}
    (hK : ContDiff ℝ 2 K) (hG : Integrable G) (h0 : ∀ y, |K y| ≤ B₀ * G y)
    (h1 : ∀ y e, |dirDeriv e K y| ≤ B₁ * ‖e‖ * G y)
    (h2 : ∀ y e e', |dirDeriv e' (dirDeriv e K) y| ≤ B₂ * ‖e‖ * ‖e'‖ * G y)
    (hw : BoundedDerivs 2 w) (hA : ∀ y, |w y| ≤ A) (x : Euc d) :
    |∫ y, K y * laplacianSum w (x - y)| ≤ d * (B₂ * A * ∫ y, G y) := by
  have hK1d : ∀ e, ContDiff ℝ 1 (dirDeriv e K) := fun e => contDiff_one_dirDeriv hK e
  have hI0 : Integrable K :=
    Integrable.mono' (hG.const_mul B₀) hK.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h0 y)
  have hI1 : ∀ e, Integrable (dirDeriv e K) := fun e =>
    Integrable.mono' (hG.const_mul (B₁ * ‖e‖)) (hK1d e).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h1 y e)
  have hI2 : ∀ e e', Integrable (dirDeriv e' (dirDeriv e K)) := fun e e' =>
    Integrable.mono' (hG.const_mul (B₂ * ‖e‖ * ‖e'‖))
      (((hK1d e).continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h2 y e e')
  have hw2 : ContDiff ℝ 2 w := by exact_mod_cast hw.1
  have hsub : Continuous fun y : Euc d => x - y := continuous_const.sub continuous_id
  -- the second derivatives of `w` are bounded and continuous
  have hwd : ∀ e e' : Euc d, BoundedDerivs 0 (dirDeriv e' (dirDeriv e w)) := fun e e' =>
    (hw.dirDeriv e).dirDeriv e'
  have hint : ∀ i : Fin d, Integrable (fun y => K y *
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) w) (x - y)) := by
    intro i
    obtain ⟨B, hB⟩ := (hwd (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)).exists_abs_le
    refine hI0.mul_bdd (c := B) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((hwd (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)).continuous.comp
        hsub).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hB _
  have hlap : ∀ y, K y * laplacianSum w (x - y) = ∑ i : Fin d, K y *
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) w) (x - y) :=
    fun y => by rw [laplacianSum_eq_sum_dirDeriv_of_contDiff hw2, Finset.mul_sum]
  have hibp : ∀ i : Fin d, ∫ y, K y *
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) w) (x - y) =
        ∫ y, dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) K) y *
          w (x - y) :=
    fun i => integral_mul_dirDeriv_dirDeriv_comp_sub hK hI0 hI1 hI2 hw x _ _
  have hbd : ∀ i : Fin d, |∫ y, dirDeriv (EuclideanSpace.single i 1)
      (dirDeriv (EuclideanSpace.single i 1) K) y * w (x - y)| ≤ B₂ * A * ∫ y, G y := by
    intro i
    have hpt : ∀ y, ‖dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) K) y * w (x - y)‖ ≤ B₂ * A * G y := by
      intro y
      have hy := h2 y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
      rw [Real.norm_eq_abs, abs_mul]
      calc |dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) K) y| *
            |w (x - y)|
          ≤ (B₂ * ‖(EuclideanSpace.single i 1 : Euc d)‖ * ‖(EuclideanSpace.single i 1 : Euc d)‖ *
              G y) * A :=
            mul_le_mul hy (hA _) (abs_nonneg _) ((abs_nonneg _).trans hy)
        _ = B₂ * A * G y := by simp; ring
    have h := norm_integral_le_of_norm_le (hG.const_mul (B₂ * A))
      (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul] at h
    rwa [Real.norm_eq_abs] at h
  simp_rw [hlap]
  rw [integral_finsetSum _ fun i _ => hint i]
  simp_rw [hibp]
  calc |∑ i : Fin d, ∫ y, dirDeriv (EuclideanSpace.single i 1)
          (dirDeriv (EuclideanSpace.single i 1) K) y * w (x - y)|
      ≤ ∑ i : Fin d, |∫ y, dirDeriv (EuclideanSpace.single i 1)
          (dirDeriv (EuclideanSpace.single i 1) K) y * w (x - y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, B₂ * A * ∫ y, G y := Finset.sum_le_sum fun i _ => hbd i
    _ = d * (B₂ * A * ∫ y, G y) := by simp

/-- Away from the origin a kernel with dominated derivatives can absorb a Laplacian: if `K` is
`C²` and, outside the ball of radius `χ.rIn`, `K` and its first two directional derivatives are
dominated by `M G` (with the factors `‖e‖`, `‖e'‖` for the directions) for an integrable `G ≥ 0`,
then for every bounded `C²` function `w` with bounded derivatives and `|w| ≤ A`, the integral of
`(1 - χ) K` against `Δw (x - ·)` is at most `C M A ∫ G` in absolute value, with `C` depending only
on `χ` and the dimension. -/
theorem exists_abs_integral_one_sub_bump_mul_laplacianSum_le (χ : ContDiffBump (0 : Euc d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K G w : Euc d → ℝ) (M A : ℝ), ContDiff ℝ 2 K → Integrable G →
      (∀ y, 0 ≤ G y) → 0 ≤ M →
      (∀ y, χ.rIn ≤ ‖y‖ → |K y| ≤ M * G y) →
      (∀ y e, χ.rIn ≤ ‖y‖ → |dirDeriv e K y| ≤ M * ‖e‖ * G y) →
      (∀ y e e', χ.rIn ≤ ‖y‖ → |dirDeriv e' (dirDeriv e K) y| ≤ M * ‖e‖ * ‖e'‖ * G y) →
      BoundedDerivs 2 w → (∀ y, |w y| ≤ A) → ∀ x : Euc d,
        |∫ y, (1 - χ y) * K y * laplacianSum w (x - y)| ≤ C * M * A * ∫ y, G y := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hχ₁, hχ₂⟩ := exists_bump_dirDeriv_bounds χ
  refine ⟨d * (1 + 2 * M₁ + M₂), by positivity, ?_⟩
  intro K G w M A hK hG hG0 hM hK0 hK1 hK2 hw hA x
  have hK' : ContDiff ℝ 2 (fun z => (1 - χ z) * K z) :=
    (contDiff_const.sub (χ.contDiff (n := 2))).mul hK
  have h := abs_integral_mul_laplacianSum_le (K := fun z => (1 - χ z) * K z) (G := G) (w := w)
    (B₀ := M) (B₁ := (1 + M₁) * M) (B₂ := (1 + 2 * M₁ + M₂) * M) (A := A) hK' hG
    (abs_one_sub_bump_mul_le χ hG0 hM hK0)
    (fun y e => abs_dirDeriv_one_sub_bump_mul_le χ hK hG0 hM hM₁ hχ₁ hK0 hK1 y e)
    (fun y e e' => abs_dirDeriv_dirDeriv_one_sub_bump_mul_le χ hK hG0 hM hM₁ hM₂ hχ₁ hχ₂
      hK0 hK1 hK2 y e e')
    hw hA x
  calc |∫ y, (1 - χ y) * K y * laplacianSum w (x - y)|
      ≤ d * ((1 + 2 * M₁ + M₂) * M * A * ∫ y, G y) := h
    _ = d * (1 + 2 * M₁ + M₂) * M * A * ∫ y, G y := by ring

/-- The companion bound without the Laplacian: the integral of the cut-off kernel `(1 - χ) K` is
at most `M ∫ G` in absolute value when `K` is dominated by `M G` away from the origin. -/
theorem abs_integral_one_sub_bump_mul_le (χ : ContDiffBump (0 : Euc d)) {K G : Euc d → ℝ}
    {M : ℝ} (hG : Integrable G) (hG0 : ∀ y, 0 ≤ G y) (hM : 0 ≤ M)
    (hKG : ∀ y, χ.rIn ≤ ‖y‖ → |K y| ≤ M * G y) :
    |∫ y, (1 - χ y) * K y| ≤ M * ∫ y, G y := by
  have h := norm_integral_le_of_norm_le (f := fun y => (1 - χ y) * K y) (hG.const_mul M)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_one_sub_bump_mul_le χ hG0 hM hKG y)
  rw [integral_const_mul] at h
  rwa [Real.norm_eq_abs] at h

end

end LatticeProb.Analysis.Schauder
