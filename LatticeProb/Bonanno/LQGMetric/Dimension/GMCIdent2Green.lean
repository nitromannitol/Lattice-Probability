/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent2Green at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqKer
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Field.GreenFn
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqKer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
**`GMCIdent2.killedGreen_openSquare`**: for `x ≠ y` in `𝕍 = (0,1)²`,

  `π ∫₀^∞ p_𝕍(s; x, y) ds = −log‖x − y‖ + hS x y  (= G_ℍ(φ x, φ y) = G_𝕍(x, y))`,

DZZ (`LBM_LGDarXiv.tex` l. 400–403, eq. (eq:Green_fxn)). Inputs:

* R1 `HeatSq.zeroGFFTestCov_sqOpen_eq_heat_gen` (`Cov = π ∫₀^∞ ∫∫ ρ p^D_s σ` for bounded `ρ, σ`),
* G1 `KilledHeatSq.killedHeat_sqOpen` (`p_𝕍 = p^D`, the image-series kernel),
* the kernel form `zeroGFFTestCov_eq_green` (`Cov = ∫∫ ρ σ G_ℍ(φ ·, φ ·)` for test functions).

Applied to normalized bumps `ρ_n, σ_n` concentrating at `x`, `y`, both sides converge: the
right side by continuity of `G_ℍ(φ ·, φ ·)` off the diagonal, the left side by dominated
convergence in `s` (for fixed `s > 0`, `p^D_s` is continuous — its sine series converges
uniformly — and `p_𝕍(s; ·, ·) ≤ min((π d²)⁻¹, 4/(π s²))` at distance `≥ d`). Own elementary
assembly (approximate identities), recorded in DEVIATIONS.
-/

noncomputable section

open MeasureTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent2

open KilledHeat HeatSq KilledHeatSq

/-! ## Approximate identities on `ℂ × ℂ` -/

lemma integrable_bump_mul {ρ σ : ℂ → ℝ} (hρ : Integrable ρ) (hσ : Integrable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x) {F : ℂ × ℂ → ℝ}
    (hFm : AEStronglyMeasurable F (volume.prod volume)) {C : ℝ}
    (hC : ∀ p : ℂ × ℂ, ρ p.1 ≠ 0 → σ p.2 ≠ 0 → |F p| ≤ C) :
    Integrable (fun p : ℂ × ℂ => ρ p.1 * σ p.2 * F p) (volume.prod volume) := by
  have hi : Integrable (fun p : ℂ × ℂ => ρ p.1 * σ p.2) (volume.prod volume) := hρ.mul_prod hσ
  refine (hi.mul_const C).mono' (hi.aestronglyMeasurable.mul hFm) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hρ0 _) (hσ0 _))]
  by_cases h1 : ρ p.1 = 0
  · simp [h1]
  by_cases h2 : σ p.2 = 0
  · simp [h2]
  exact mul_le_mul_of_nonneg_left (hC p h1 h2) (mul_nonneg (hρ0 _) (hσ0 _))

/-- Normalized bumps shrinking to `p₀` average a function continuous at `p₀` to its value. -/
theorem tendsto_bump_prod {F : ℂ × ℂ → ℝ} {p₀ : ℂ × ℂ} (hF : ContinuousAt F p₀)
    (hFm : AEStronglyMeasurable F (volume.prod volume)) {ρ σ : ℕ → ℂ → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hρi : ∀ n, Integrable (ρ n)) (hσi : ∀ n, Integrable (σ n))
    (hρ0 : ∀ n x, 0 ≤ ρ n x) (hσ0 : ∀ n x, 0 ≤ σ n x) (hρ1 : ∀ n, ∫ x, ρ n x = 1)
    (hσ1 : ∀ n, ∫ x, σ n x = 1) (hρs : ∀ n x, ρ n x ≠ 0 → dist x p₀.1 ≤ r n)
    (hσs : ∀ n x, σ n x ≠ 0 → dist x p₀.2 ≤ r n) :
    Tendsto (fun n => ∫ p, ρ n p.1 * σ n p.2 * F p ∂(volume.prod volume)) atTop (𝓝 (F p₀)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hFδ⟩ := Metric.continuousAt_iff.1 hF (η / 2) (half_pos hη)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have := hN n hn; rw [Real.dist_eq, sub_zero] at this; exact (le_abs_self _).trans_lt this
  have hclose : ∀ p : ℂ × ℂ, ρ n p.1 ≠ 0 → σ n p.2 ≠ 0 → |F p - F p₀| < η / 2 := by
    intro p h1 h2
    have : dist p p₀ < δ := by
      rw [Prod.dist_eq]; exact max_lt ((hρs n _ h1).trans_lt hrn) ((hσs n _ h2).trans_lt hrn)
    have := hFδ this; rwa [Real.dist_eq] at this
  have hi : Integrable (fun p : ℂ × ℂ => ρ n p.1 * σ n p.2) (volume.prod volume) :=
    (hρi n).mul_prod (hσi n)
  have hiF := integrable_bump_mul (hρi n) (hσi n) (hρ0 n) (hσ0 n) hFm (C := |F p₀| + η / 2)
    fun p h1 h2 => by
      have := hclose p h1 h2
      calc |F p| = |(F p - F p₀) + F p₀| := by ring_nf
        _ ≤ |F p - F p₀| + |F p₀| := abs_add_le _ _
        _ ≤ |F p₀| + η / 2 := by linarith
  have h1 : ∫ p, ρ n p.1 * σ n p.2 ∂(volume.prod volume) = 1 := by
    have := integral_prod_mul (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (ρ n) (σ n)
    rw [this, hρ1, hσ1, one_mul]
  have hsplit : ∫ p, ρ n p.1 * σ n p.2 * F p ∂(volume.prod volume) - F p₀ =
      ∫ p, ρ n p.1 * σ n p.2 * (F p - F p₀) ∂(volume.prod volume) := by
    simp_rw [mul_sub]
    rw [integral_sub hiF (hi.mul_const _), integral_mul_const, h1, one_mul]
  rw [Real.dist_eq, hsplit]
  have hb : ‖∫ p, ρ n p.1 * σ n p.2 * (F p - F p₀) ∂(volume.prod volume)‖ ≤ η / 2 := by
    have := norm_integral_le_of_norm_le
      (f := fun p : ℂ × ℂ => ρ n p.1 * σ n p.2 * (F p - F p₀)) (hi.mul_const (η / 2))
      (ae_of_all _ fun p => ?_)
    · rwa [integral_mul_const, h1, one_mul] at this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hρ0 n _) (hσ0 n _))]
    by_cases h1 : ρ n p.1 = 0
    · simp [h1]
    by_cases h2 : σ n p.2 = 0
    · simp [h2]
    exact mul_le_mul_of_nonneg_left (hclose p h1 h2).le (mul_nonneg (hρ0 n _) (hσ0 n _))
  rw [← Real.norm_eq_abs]; linarith

/-! ## Continuity of the square kernel -/

lemma continuous_intervalDirKernel {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) :
    Continuous fun p : ℝ × ℝ => intervalDirKernel a L s p.1 p.2 := by
  have he : (fun p : ℝ × ℝ => intervalDirKernel a L s p.1 p.2) = fun p =>
      ∑' k : ℕ, 2 / L * (modeDecay L s k * (sinMode a L k p.1 * sinMode a L k p.2)) := by
    funext p; exact ((hasSum_intervalDirKernel_sine hs hL p.1 p.2).tsum_eq).symm
  rw [he]
  refine continuous_tsum (u := fun k => 2 / L * modeDecay L s k) (fun k => ?_)
    ((summable_modeDecay hs hL).mul_left _) (fun k p => ?_)
  · unfold sinMode; fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (modeDecay_pos _ _ _),
      abs_of_pos (by positivity : (0:ℝ) < 2 / L)]
    refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (modeDecay_pos _ _ _).le ?_)
      (by positivity)
    exact abs_mul_le_one_of (abs_sinMode_le _ _ _ _) (abs_sinMode_le _ _ _ _)

lemma continuous_sqDirKernel {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) :
    Continuous fun p : ℂ × ℂ => sqDirKernel a L s p.1 p.2 := by
  have h := continuous_intervalDirKernel (a := a) hs hL
  show Continuous fun p : ℂ × ℂ =>
    intervalDirKernel a L s p.1.re p.2.re * intervalDirKernel a L s p.1.im p.2.im
  have h1 : Continuous fun p : ℂ × ℂ => intervalDirKernel a L s p.1.re p.2.re :=
    h.comp (f := fun p : ℂ × ℂ => (p.1.re, p.2.re)) (by fun_prop)
  have h2 : Continuous fun p : ℂ × ℂ => intervalDirKernel a L s p.1.im p.2.im :=
    h.comp (f := fun p : ℂ × ℂ => (p.1.im, p.2.im)) (by fun_prop)
  exact h1.mul h2

lemma openSquare_eq_sqOpen : openSquare = sqOpen 0 1 := by
  ext z; simp [openSquare, sqOpen]

/-- for `s > 0` the killed kernel of `𝕍` is continuous at points of `𝕍 × 𝕍` -/
lemma continuousAt_killedHeat {s : ℝ} (hs : 0 < s) {p₀ : ℂ × ℂ} (h1 : p₀.1 ∈ openSquare)
    (h2 : p₀.2 ∈ openSquare) :
    ContinuousAt (fun p : ℂ × ℂ => killedHeat openSquare s.toNNReal p.1 p.2) p₀ := by
  have hU : (openSquare ×ˢ openSquare : Set (ℂ × ℂ)) ∈ 𝓝 p₀ :=
    (isOpen_openSquare.prod isOpen_openSquare).mem_nhds ⟨h1, h2⟩
  refine ((continuous_sqDirKernel (a := 0) hs one_pos).continuousAt).congr ?_
  filter_upwards [hU] with p hp
  have ht : s.toNNReal ≠ 0 := by simpa using hs
  rw [openSquare_eq_sqOpen] at hp ⊢
  rw [killedHeat_sqOpen one_pos _ ht _ _ hp.1 hp.2, Real.coe_toNNReal _ hs.le]

/-! ## R1 against the kernel form, for test functions -/

lemma coe_openSquareOpens : ((openSquareOpens : TopologicalSpace.Opens ℂ) : Set ℂ) = openSquare :=
  rfl

/-- a test function on `𝕍` as a bounded function on `sqOpen 0 1` -/
def toBdd (φ : TestOn openSquareOpens) : BddOn (sqOpen 0 1) :=
  ⟨φ, (TestOn.toBddOn φ).2.1, (TestOn.toBddOn φ).2.2.1, fun z hz =>
    φ.zero_on_compl (by rw [coe_openSquareOpens, openSquare_eq_sqOpen]; exact hz)⟩

lemma measurable_killedHeat_param :
    Measurable fun r : (ℝ × ℂ) × ℂ => killedHeat openSquare r.1.1.toNNReal r.1.2 r.2 :=
  (measurable_killedHeat isOpen_openSquare).comp
    ((measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- R1 and the kernel form of the zero-boundary covariance, combined:
`π ∫₀^∞ ∫∫ φ p_𝕍(s) ψ ds = ∫∫ φ ψ G_ℍ(φ ·, φ ·)`. -/
theorem heat_eq_green (φ ψ : TestOn openSquareOpens) :
    Real.pi * ∫ s in Ioi (0 : ℝ), ∫ x', ∫ y', φ x' * killedHeat openSquare s.toNNReal x' y' * ψ y' =
      ∫ p, φ p.1 * ψ p.2 * greenH (sqM p.1) (sqM p.2) ∂(volume.prod volume) := by
  have e1 := zeroGFFTestCov_eq_green openSquare_subset_H isConformalOnto_sqMap φ ψ
  have e2 := zeroGFFTestCov_sqOpen_eq_heat_gen (a := 0) (L := 1) one_pos (toBdd φ) (toBdd ψ)
  have hset : ((sqOpens 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ) =
      ((openSquareOpens : TopologicalSpace.Opens ℂ) : Set ℂ) := openSquare_eq_sqOpen.symm
  rw [hset] at e2
  have hφ0 : ∀ z ∉ openSquare, φ z = 0 := fun z hz => φ.zero_on_compl hz
  have hψ0 : ∀ z ∉ openSquare, ψ z = 0 := fun z hz => ψ.zero_on_compl hz
  have hL : ∫ s in Ioi (0 : ℝ), ∫ x', ∫ y', φ x' * killedHeat openSquare s.toNNReal x' y' * ψ y' =
      ∫ s in Ioi (0 : ℝ), ∫ x', ∫ y', (toBdd φ).1 x' * sqDirKernel 0 1 s x' y' * (toBdd ψ).1 y' := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    refine integral_congr_ae (ae_of_all _ fun x' => integral_congr_ae (ae_of_all _ fun y' => ?_))
    show φ x' * killedHeat openSquare s.toNNReal x' y' * ψ y' = φ x' * sqDirKernel 0 1 s x' y' * ψ y'
    by_cases hx' : x' ∈ openSquare
    · by_cases hy' : y' ∈ openSquare
      · have ht : s.toNNReal ≠ 0 := by simpa using (mem_Ioi.1 hs)
        rw [openSquare_eq_sqOpen] at hx' hy' ⊢
        rw [killedHeat_sqOpen one_pos _ ht _ _ hx' hy', Real.coe_toNNReal _ (mem_Ioi.1 hs).le]
      · simp [hψ0 y' hy']
    · simp [hφ0 x' hx']
  have hR : ∫ p, φ p.1 * ψ p.2 * greenH (sqM p.1) (sqM p.2) ∂(volume.prod volume) =
      ∫ p, φ p.1 * ψ p.2 * greenH (sqMap p.1) (sqMap p.2) ∂(volume.prod volume) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    by_cases h1 : p.1 ∈ openSquare
    · by_cases h2 : p.2 ∈ openSquare
      · simp only; rw [sqM_eq h1, sqM_eq h2]
      · simp [hψ0 _ h2]
    · simp [hφ0 _ h1]
  rw [hL, hR, ← e1, ← e2]
  rfl

/-! ## The pointwise identity -/

lemma openSquare_subset_ball2 : openSquare ⊆ Metric.ball (0 : ℂ) 2 := by
  intro z ⟨h1, h2, h3, h4⟩
  rw [Metric.mem_ball, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans_lt ?_
  rw [abs_of_pos h1, abs_of_pos h3]; linarith

/-- the time bound `p_𝕍(s; u, v) ≤ g(s)` at distance `‖u − v‖ ≥ e` -/
def timeBound (e s : ℝ) : ℝ := if s ≤ 1 then (Real.pi * e ^ 2)⁻¹ else 2 ^ 2 / Real.pi * s ^ (-2 : ℝ)

lemma integrableOn_timeBound (e : ℝ) : IntegrableOn (timeBound e) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.congr_fun (f := fun _ => (Real.pi * e ^ 2)⁻¹)
      (integrableOn_const (by simp)) (fun s hs => ?_) measurableSet_Ioc
    simp [timeBound, hs.2]
  · refine IntegrableOn.congr_fun (f := fun s : ℝ => 2 ^ 2 / Real.pi * s ^ (-2 : ℝ))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
      (2 ^ 2 / Real.pi)) (fun s hs => ?_) measurableSet_Ioi
    simp [timeBound, not_le.2 (mem_Ioi.1 hs)]

lemma killedHeat_le_timeBound {e s : ℝ} (he : 0 < e) (hs : 0 < s) {u v : ℂ} (huv : e ≤ ‖u - v‖) :
    killedHeat openSquare s.toNNReal u v ≤ timeBound e s := by
  unfold timeBound
  split_ifs with h
  · have hne : u ≠ v := fun h' => by rw [h', sub_self, norm_zero] at huv; linarith
    refine (killedHeat_le_heatKernel _ _ _ _).trans ?_
    rw [Real.coe_toNNReal _ hs.le]
    refine (heatKernel_le_inv_sq s hs hne).trans (inv_anti₀ (by positivity) ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le huv 2) Real.pi_pos.le
  · exact killedHeat_le_rpow (by norm_num) openSquare_subset_ball2 hs u v

lemma continuousAt_greenH_sqM {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare)
    (hxy : x ≠ y) : ContinuousAt (fun p : ℂ × ℂ => greenH (sqM p.1) (sqM p.2)) (x, y) := by
  have hcx : ContinuousAt sqM x :=
    differentiableOn_sqM.continuousOn.continuousAt (isOpen_openSquare.mem_nhds hx)
  have hcy : ContinuousAt sqM y :=
    differentiableOn_sqM.continuousOn.continuousAt (isOpen_openSquare.mem_nhds hy)
  have h1 : ContinuousAt (fun p : ℂ × ℂ => sqM p.1) (x, y) := hcx.comp continuousAt_fst
  have h2 : ContinuousAt (fun p : ℂ × ℂ => sqM p.2) (x, y) := hcy.comp continuousAt_snd
  have hc : ContinuousAt (fun p : ℂ × ℂ => (starRingEnd ℂ) (sqM p.2)) (x, y) :=
    Complex.continuous_conj.continuousAt.comp h2
  have n1 : ‖sqM x - (starRingEnd ℂ) (sqM y)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ← norm_ne_zero_iff, norm_sub_conj_comm, norm_ne_zero_iff]
    exact sub_conj_ne_zero hx hy
  have n2 : ‖sqM x - sqM y‖ ≠ 0 :=
    norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => hxy (sqM_injOn hx hy e))
  unfold greenH
  exact ((h1.sub hc).norm.log n1).sub ((h1.sub h2).norm.log n2)

lemma measurable_greenH_sqM : Measurable fun p : ℂ × ℂ => greenH (sqM p.1) (sqM p.2) := by
  have h1 := measurable_sqM.comp (measurable_fst : Measurable (Prod.fst : ℂ × ℂ → ℂ))
  have h2 := measurable_sqM.comp (measurable_snd : Measurable (Prod.snd : ℂ × ℂ → ℂ))
  unfold greenH
  exact ((h1.sub (Complex.continuous_conj.measurable.comp h2)).norm.log).sub
    ((h1.sub h2).norm.log)

/-- **The Green function of the unit square** (DZZ (eq:Green_fxn), l. 400–403):
`π ∫₀^∞ p_𝕍(s; x, y) ds = −log‖x − y‖ + hS x y` for `x ≠ y` in `𝕍`. -/
theorem killedGreen_openSquare {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare)
    (hxy : x ≠ y) : killedGreen openSquare x y = -Real.log ‖x - y‖ + hS x y := by
  rw [← greenH_sqM hx hy hxy]
  set d := ‖x - y‖ with hd
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  obtain ⟨e1, he1, hb1⟩ := Metric.isOpen_iff.1 isOpen_openSquare x hx
  obtain ⟨e2, he2, hb2⟩ := Metric.isOpen_iff.1 isOpen_openSquare y hy
  set ε := min (min (e1 / 2) (e2 / 2)) (d / 4) with hε
  have hε0 : 0 < ε := lt_min (lt_min (half_pos he1) (half_pos he2)) (by positivity)
  have hεd : ε ≤ d / 4 := min_le_right _ _
  have hcb1 : closedBall x ε ⊆ openSquare := (closedBall_subset_ball
    ((min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self he1)))).trans hb1
  have hcb2 : closedBall y ε ⊆ openSquare := (closedBall_subset_ball
    ((min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (half_lt_self he2)))).trans hb2
  set r : ℕ → ℝ := fun n => ε / (n + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrε : ∀ n, r n ≤ ε := fun n => div_le_self hε0.le (by linarith [n.cast_nonneg (α := ℝ)])
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat ε |>.comp
    (tendsto_add_atTop_nat 1) |>.congr fun n => by simp [r]
  let bx : ℕ → ContDiffBump x := fun n => ⟨r n / 2, r n, half_pos (hr0 n), half_lt_self (hr0 n)⟩
  let by' : ℕ → ContDiffBump y := fun n => ⟨r n / 2, r n, half_pos (hr0 n), half_lt_self (hr0 n)⟩
  set ρ : ℕ → ℂ → ℝ := fun n => (bx n).normed volume with hρ
  set σ : ℕ → ℂ → ℝ := fun n => (by' n).normed volume with hσ
  have hρs : ∀ n z, ρ n z ≠ 0 → dist z x ≤ r n := fun n z h => by
    have : z ∈ Function.support (ρ n) := h
    rw [hρ, ContDiffBump.support_normed_eq] at this; exact (mem_ball.1 this).le
  have hσs : ∀ n z, σ n z ≠ 0 → dist z y ≤ r n := fun n z h => by
    have : z ∈ Function.support (σ n) := h
    rw [hσ, ContDiffBump.support_normed_eq] at this; exact (mem_ball.1 this).le
  let φ : ℕ → TestOn openSquareOpens := fun n => ⟨ρ n, (bx n).contDiff_normed,
    (bx n).hasCompactSupport_normed, by
      rw [(bx n).tsupport_normed_eq]; exact (closedBall_subset_closedBall (hrε n)).trans hcb1⟩
  let ψ : ℕ → TestOn openSquareOpens := fun n => ⟨σ n, (by' n).contDiff_normed,
    (by' n).hasCompactSupport_normed, by
      rw [(by' n).tsupport_normed_eq]; exact (closedBall_subset_closedBall (hrε n)).trans hcb2⟩
  have hρi : ∀ n, Integrable (ρ n) := fun n => (bx n).integrable_normed
  have hσi : ∀ n, Integrable (σ n) := fun n => (by' n).integrable_normed
  have hρ0 : ∀ n z, 0 ≤ ρ n z := fun n z => (bx n).nonneg_normed z
  have hσ0 : ∀ n z, 0 ≤ σ n z := fun n z => (by' n).nonneg_normed z
  have hρ1 : ∀ n, ∫ z, ρ n z = 1 := fun n => (bx n).integral_normed
  have hσ1 : ∀ n, ∫ z, σ n z = 1 := fun n => (by' n).integral_normed
  -- separation on the supports
  have hsep : ∀ n (p : ℂ × ℂ), ρ n p.1 ≠ 0 → σ n p.2 ≠ 0 → d / 2 ≤ ‖p.1 - p.2‖ := by
    intro n p h1 h2
    have a1 := (hρs n _ h1).trans (hrε n)
    have a2 := (hσs n _ h2).trans (hrε n)
    have := dist_triangle4 x p.1 p.2 y
    rw [dist_comm p.1 x] at a1
    have hxy' : d = dist x y := by rw [hd, dist_eq_norm]
    rw [← dist_eq_norm]; linarith
  -- the right side
  have hRt := tendsto_bump_prod (continuousAt_greenH_sqM hx hy hxy)
    measurable_greenH_sqM.aestronglyMeasurable hrt hρi hσi hρ0 hσ0 hρ1 hσ1 hρs hσs
  -- the left side, for fixed `s`
  set A : ℕ → ℝ → ℝ := fun n s =>
    ∫ x', ∫ y', ρ n x' * killedHeat openSquare s.toNNReal x' y' * σ n y' with hA
  have hKm : ∀ s : ℝ, AEStronglyMeasurable
      (fun p : ℂ × ℂ => killedHeat openSquare s.toNNReal p.1 p.2) (volume.prod volume) :=
    fun s => (measurable_killedHeat_param.comp
      (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd :
        Measurable fun p : ℂ × ℂ => ((s, p.1), p.2))).aestronglyMeasurable
  have hAprod : ∀ n, ∀ s, 0 < s → A n s =
      ∫ p, ρ n p.1 * σ n p.2 * killedHeat openSquare s.toNNReal p.1 p.2 ∂(volume.prod volume) := by
    intro n s hs
    rw [integral_prod _ (integrable_bump_mul (hρi n) (hσi n) (hρ0 n) (hσ0 n) (hKm s)
      (C := timeBound (d / 2) s) fun p h1 h2 => by
        rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
        exact killedHeat_le_timeBound (by positivity) hs (hsep n p h1 h2))]
    refine integral_congr_ae (ae_of_all _ fun x' => integral_congr_ae (ae_of_all _ fun y' => ?_))
    simp only; ring
  have hAlim : ∀ s, 0 < s → Tendsto (fun n => A n s) atTop
      (𝓝 (killedHeat openSquare s.toNNReal x y)) := fun s hs => by
    have := tendsto_bump_prod (p₀ := (x, y)) (continuousAt_killedHeat hs hx hy) (hKm s) hrt
      hρi hσi hρ0 hσ0 hρ1 hσ1 hρs hσs
    exact this.congr fun n => (hAprod n s hs).symm
  have hAb : ∀ n, ∀ s, 0 < s → ‖A n s‖ ≤ timeBound (d / 2) s := by
    intro n s hs
    rw [hAprod n s hs]
    have hi : Integrable (fun p : ℂ × ℂ => ρ n p.1 * σ n p.2) (volume.prod volume) :=
      (hρi n).mul_prod (hσi n)
    have := norm_integral_le_of_norm_le
      (f := fun p : ℂ × ℂ => ρ n p.1 * σ n p.2 * killedHeat openSquare s.toNNReal p.1 p.2)
      (hi.mul_const (timeBound (d / 2) s)) (ae_of_all _ fun p => ?_)
    · rwa [integral_mul_const, integral_prod_mul (μ := (volume : Measure ℂ))
        (ν := (volume : Measure ℂ)) (ρ n) (σ n), hρ1, hσ1, one_mul, one_mul] at this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hρ0 n _) (hσ0 n _)),
      abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
    by_cases h1 : ρ n p.1 = 0
    · simp [h1]
    by_cases h2 : σ n p.2 = 0
    · simp [h2]
    exact mul_le_mul_of_nonneg_left (killedHeat_le_timeBound (by positivity) hs (hsep n p h1 h2))
      (mul_nonneg (hρ0 n _) (hσ0 n _))
  have hAm : ∀ n, AEStronglyMeasurable (A n) (volume.restrict (Ioi 0)) := by
    intro n
    have hf : StronglyMeasurable fun r : (ℝ × ℂ) × ℂ =>
        ρ n r.1.2 * killedHeat openSquare r.1.1.toNNReal r.1.2 r.2 * σ n r.2 :=
      ((((bx n).continuous_normed.measurable.comp (measurable_snd.comp measurable_fst)).mul
        measurable_killedHeat_param).mul
        ((by' n).continuous_normed.measurable.comp measurable_snd)).stronglyMeasurable
    have hg := hf.integral_prod_right (f := fun q : ℝ × ℂ => fun y' : ℂ =>
      ρ n q.2 * killedHeat openSquare q.1.toNNReal q.2 y' * σ n y') (ν := volume)
    exact (hg.integral_prod_right (f := fun s : ℝ => fun x' : ℂ =>
      ∫ y', ρ n x' * killedHeat openSquare s.toNNReal x' y' * σ n y') (ν := volume)).aestronglyMeasurable
  have hDCT := tendsto_integral_of_dominated_convergence (timeBound (d / 2)) hAm
    (integrableOn_timeBound _) (fun n => (ae_restrict_mem measurableSet_Ioi).mono
      fun s hs => hAb n s hs) ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => hAlim s hs)
  have hL := hDCT.const_mul Real.pi
  have heq : ∀ n, Real.pi * ∫ s in Ioi 0, A n s =
      ∫ p, ρ n p.1 * σ n p.2 * greenH (sqM p.1) (sqM p.2) ∂(volume.prod volume) :=
    fun n => heat_eq_green (φ n) (ψ n)
  simp_rw [heq] at hL
  exact tendsto_nhds_unique hL hRt

end GMCIdent2
end LQGMetric
