/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSqLim at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KHSQ3, target `killedHeat_sqOpen`)

Letting the dyadic mesh `t/2ⁿ → 0` in the discrete optional stopping identity
`integral_stayUpTo_sqMode`: the correction term vanishes because at the first grid exit the
path is within one mesh step of the boundary, where `φ_p` vanishes (`φ_p` is Lipschitz and
`0` on `∂Q`; uniform continuity of the path on `[0, t]`), and the staying events decrease to
`stayGrid` = "in `Q` at all dyadic times `≤ t`". Result (`KilledHeatSq.integral_stayGrid_sqMode`):

  `E[φ_p(z + B_t); z + B_d ∈ Q for all dyadic d ≤ t] = e^{−λ_p t/2} φ_p(z)`   (`z ∈ Q`).

This is optional stopping for the space-time martingale `e^{λ_p s/2} φ_p(z + B_s)` at the exit
time of the square (Karatzas–Shreve §4.3; Feller II §X.5). Own elementary assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeatSq

open KilledHeat HeatSq Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- In `Q` at every dyadic time `≤ t`. -/
def stayGrid (Q : Set ℂ) (B : ℝ≥0 → Ω → ℂ) (z : ℂ) (t : ℝ≥0) : Set Ω :=
  ⋂ n : ℕ, stayUpTo Q B z t n (2 ^ n + 1)

lemma gridT_succ_two_mul (t : ℝ≥0) (n j : ℕ) : gridT t (n + 1) (2 * j) = gridT t n j := by
  unfold gridT
  push_cast
  rw [pow_succ]
  field_simp

lemma stayUpTo_antitone (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) :
    Antitone fun n : ℕ ↦ stayUpTo Q B z t n (2 ^ n + 1) := by
  refine antitone_nat_of_succ_le fun n ω hω j hj ↦ ?_
  rw [← gridT_succ_two_mul]
  exact hω (2 * j) (by rw [pow_succ]; omega)

lemma sinMode_bound {a L : ℝ} (hL : 0 < L) (k : ℕ) {u v : ℝ} (hv : a < v ∧ v < a + L)
    (hu : ¬(a < u ∧ u < a + L)) : |sinMode a L k u| ≤ π * k / L * |u - v| := by
  have hc : 0 ≤ π * k / L := by positivity
  rcases not_and_or.mp hu with hu | hu
  · push Not at hu
    have h := abs_sin_sub_sin_le (π * k * (u - a) / L) 0
    rw [sin_zero, sub_zero, sub_zero] at h
    unfold sinMode
    refine h.trans ?_
    rw [show π * k * (u - a) / L = π * k / L * (u - a) by ring, abs_mul, abs_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith
  · push Not at hu
    have h := abs_sin_sub_sin_le (π * k * (u - a) / L) (k * π)
    rw [sin_nat_mul_pi, sub_zero] at h
    unfold sinMode
    refine h.trans ?_
    rw [show π * k * (u - a) / L - k * π = π * k / L * (u - (a + L)) by field_simp; ring,
      abs_mul, abs_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
    linarith

/-- `φ_p` is small just outside the square: `|φ_p(y')| ≤ c ‖y' − y‖` for `y ∈ Q`, `y' ∉ Q`. -/
lemma sqMode_bound {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) {y y' : ℂ} (hy : y ∈ sqOpen a L)
    (hy' : y' ∉ sqOpen a L) :
    |sqMode a L p y'| ≤ (π * p.1 / L + π * p.2 / L) * ‖y' - y‖ := by
  have h1 : |y'.re - y.re| ≤ ‖y' - y‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : |y'.im - y.im| ≤ ‖y' - y‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have c1 : 0 ≤ π * p.1 / L := by positivity
  have c2 : 0 ≤ π * p.2 / L := by positivity
  have hn : 0 ≤ ‖y' - y‖ := norm_nonneg _
  unfold sqMode
  rw [abs_mul]
  have s1 := abs_sinMode_le a L p.1 y'.re
  have s2 := abs_sinMode_le a L p.2 y'.im
  have hy1 : a < y.re ∧ y.re < a + L := ⟨hy.1, hy.2.1⟩
  have hy2 : a < y.im ∧ y.im < a + L := ⟨hy.2.2.1, hy.2.2.2⟩
  by_cases hre : a < y'.re ∧ y'.re < a + L
  · have him : ¬(a < y'.im ∧ y'.im < a + L) := fun h ↦ hy' ⟨hre.1, hre.2, h.1, h.2⟩
    have b := sinMode_bound hL p.2 hy2 him
    calc |sinMode a L p.1 y'.re| * |sinMode a L p.2 y'.im| ≤ 1 * (π * p.2 / L * ‖y' - y‖) :=
          mul_le_mul s1 (b.trans (by gcongr)) (abs_nonneg _) zero_le_one
      _ ≤ _ := by nlinarith
  · have b := sinMode_bound hL p.1 hy1 hre
    calc |sinMode a L p.1 y'.re| * |sinMode a L p.2 y'.im| ≤ (π * p.1 / L * ‖y' - y‖) * 1 :=
          mul_le_mul (b.trans (by gcongr)) s2 (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith

lemma sqDecay_le_one (L : ℝ) {h : ℝ} (hh : 0 ≤ h) (p : ℕ × ℕ) : sqDecay L h p ≤ 1 := by
  unfold sqDecay modeDecay
  rw [← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ π ^ 2 / (2 * L ^ 2) := by positivity
  have h1 : 0 ≤ π ^ 2 / (2 * L ^ 2) * h * (p.1 : ℝ) ^ 2 := by positivity
  have h2 : 0 ≤ π ^ 2 / (2 * L ^ 2) * h * (p.2 : ℝ) ^ 2 := by positivity
  linarith

lemma sum_indicator_exitAt_le (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n M : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.range M, (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω ≤ 1 := by
  have h := indicator_stayUpTo_eq (B := B) Q z t n M ω
  have h0 : 0 ≤ (stayUpTo Q B z t n M).indicator (1 : Ω → ℝ) ω :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  linarith

lemma aemeasurable_indicator_exitAt (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (z : ℂ) (t : ℝ≥0) (n m : ℕ) :
    AEMeasurable (fun ω ↦ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω) P := by
  have e : (fun ω ↦ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω) =
      (exitSet Q z m).indicator 1 ∘ pastVec B (fun j ↦ gridT t n (min j m)) :=
    funext fun ω ↦ (indicator_exitSet_pastVec Q z t n m ω).symm
  rw [e]
  exact (measurable_one.indicator (measurableSet_exitSet hQ z m)).comp_aemeasurable
    (aemeasurable_pastVec hB _)

/-- The correction term of the optional stopping identity, pointwise. -/
def corr (a L : ℝ) (p : ℕ × ℕ) (Q : Set ℂ) (B : ℝ≥0 → Ω → ℂ) (z : ℂ) (t : ℝ≥0) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range (2 ^ n + 1), sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p *
    ((exitAt Q B z t n m).indicator 1 ω * sqMode a L p (z + B (gridT t n m) ω))

lemma abs_corr_le {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) {z : ℂ} (hz : z ∈ sqOpen a L)
    {t : ℝ≥0} {n : ℕ} {ω : Ω} (h0 : B 0 ω = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hstep : ∀ m, 1 ≤ m → m ≤ 2 ^ n →
      ‖B (gridT t n m) ω - B (gridT t n (m - 1)) ω‖ ≤ ε) :
    |corr a L p (sqOpen a L) B z t n ω| ≤ (π * p.1 / L + π * p.2 / L) * ε := by
  set c := π * p.1 / L + π * p.2 / L with hc
  have hc0 : 0 ≤ c := by positivity
  unfold corr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ Finset.range (2 ^ n + 1),
      |sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p *
        ((exitAt (sqOpen a L) B z t n m).indicator 1 ω * sqMode a L p (z + B (gridT t n m) ω))|
        ≤ (exitAt (sqOpen a L) B z t n m).indicator (1 : Ω → ℝ) ω * (c * ε) := by
    intro m hm
    have hm' : m ≤ 2 ^ n := by simp at hm; omega
    have hd0 : 0 ≤ sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p := by
      unfold sqDecay; exact (mul_pos (modeDecay_pos _ _ _) (modeDecay_pos _ _ _)).le
    have hd1 := sqDecay_le_one L (NNReal.coe_nonneg (t - gridT t n m)) p
    by_cases hω : ω ∈ exitAt (sqOpen a L) B z t n m
    · rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul, one_mul, abs_mul, abs_of_nonneg hd0]
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · exfalso; apply hω.2; simpa [gridT, h0] using hz
        · exact h
      have hprev : z + B (gridT t n (m - 1)) ω ∈ sqOpen a L := hω.1 (m - 1) (by omega)
      have hb := sqMode_bound hL p hprev hω.2
      rw [show z + B (gridT t n m) ω - (z + B (gridT t n (m - 1)) ω) =
        B (gridT t n m) ω - B (gridT t n (m - 1)) ω by ring] at hb
      calc sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p * |sqMode a L p (z + B (gridT t n m) ω)|
          ≤ 1 * (c * ε) := mul_le_mul hd1 (hb.trans (by gcongr; exact hstep m hm1 hm'))
            (abs_nonneg _) zero_le_one
        _ = c * ε := one_mul _
    · rw [Set.indicator_of_notMem hω]
      simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  calc (∑ m ∈ Finset.range (2 ^ n + 1), (exitAt (sqOpen a L) B z t n m).indicator (1 : Ω → ℝ) ω)
        * (c * ε) ≤ 1 * (c * ε) :=
        mul_le_mul_of_nonneg_right (sum_indicator_exitAt_le _ z t n _ ω) (by positivity)
    _ = c * ε := one_mul _

lemma abs_corr_le_one (a L : ℝ) (p : ℕ × ℕ) (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    |corr a L p Q B z t n ω| ≤ 1 := by
  unfold corr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun m _ ↦ ?_).trans (sum_indicator_exitAt_le (B := B) Q z t n _ ω)
  have hd0 : 0 ≤ sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p := by
    unfold sqDecay; exact (mul_pos (modeDecay_pos _ _ _) (modeDecay_pos _ _ _)).le
  have hd1 := sqDecay_le_one L (NNReal.coe_nonneg (t - gridT t n m)) p
  have hi0 : 0 ≤ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  rw [abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hi0]
  calc sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p * ((exitAt Q B z t n m).indicator 1 ω *
        |sqMode a L p (z + B (gridT t n m) ω)|)
      ≤ 1 * ((exitAt Q B z t n m).indicator 1 ω * 1) :=
        mul_le_mul hd1 (mul_le_mul_of_nonneg_left (abs_sqMode_le _ _ _ _) hi0)
          (by positivity) zero_le_one
    _ = _ := by ring

lemma gridT_dist {t : ℝ≥0} {n m : ℕ} (hm : 1 ≤ m) :
    dist (gridT t n m) (gridT t n (m - 1)) = (t : ℝ) / 2 ^ n := by
  rw [NNReal.dist_eq]
  unfold gridT
  push_cast
  rw [NNReal.coe_sub (by exact_mod_cast hm)]
  push_cast
  rw [show (m : ℝ) * t / 2 ^ n - (m - 1) * t / 2 ^ n = t / 2 ^ n by ring]
  exact abs_of_nonneg (by positivity)

lemma tendsto_corr {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) {z : ℂ} (hz : z ∈ sqOpen a L)
    (t : ℝ≥0) {ω : Ω} (hc : Continuous fun s ↦ B s ω) (h0 : B 0 ω = 0) :
    Tendsto (fun n ↦ corr a L p (sqOpen a L) B z t n ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set c := π * p.1 / L + π * p.2 / L with hcdef
  have hc0 : 0 ≤ c := by positivity
  set ε' := ε / (2 * (c + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hu : UniformContinuousOn (fun s ↦ B s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hu ε' hε'0
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / δ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmesh : (t : ℝ) / 2 ^ n < δ := by
    have h2 : (N : ℝ) < 2 ^ n := by
      have := Nat.lt_two_pow_self (n := N)
      have h3 : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      calc (N : ℝ) < 2 ^ N := by exact_mod_cast this
        _ ≤ 2 ^ n := h3
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hstep : ∀ m, 1 ≤ m → m ≤ 2 ^ n →
      ‖B (gridT t n m) ω - B (gridT t n (m - 1)) ω‖ ≤ ε' := by
    intro m hm1 hm
    have := hδu (gridT t n m) ⟨zero_le, gridT_le hm⟩ (gridT t n (m - 1))
      ⟨zero_le, gridT_le (by omega)⟩ (by rw [gridT_dist hm1]; exact hmesh)
    rw [← dist_eq_norm]
    exact this.le
  have hb := abs_corr_le hL p hz h0 hε'0.le hstep
  rw [Real.dist_eq, sub_zero]
  calc |corr a L p (sqOpen a L) B z t n ω| ≤ c * ε' := hb
    _ = ε * (c / (2 * (c + 1))) := by rw [hε']; field_simp
    _ < ε * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hε
        rw [div_lt_one (by positivity)]
        linarith
    _ = ε := mul_one ε

/-- **Optional stopping at the exit from the square** (dyadic form):
`E[φ_p(z + B_t); z + B_d ∈ Q at all dyadic d ≤ t] = e^{−λ_p t/2} φ_p(z)` for `z ∈ Q`. -/
theorem integral_stayGrid_sqMode (hB : IsPlanarBM B P) {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ)
    {z : ℂ} (hz : z ∈ sqOpen a L) (t : ℝ≥0) :
    ∫ ω, (stayGrid (sqOpen a L) B z t).indicator 1 ω * sqMode a L p (z + B t ω) ∂P =
      sqDecay L t p * sqMode a L p z := by
  have := hB.gauss.isProbabilityMeasure
  have hQ := measurableSet_sqOpen a L
  have hφm : AEMeasurable (fun ω ↦ sqMode a L p (z + B t ω)) P :=
    (continuous_sqMode a L p).measurable.comp_aemeasurable
      (aemeasurable_const.add (aemeasurable_B hB t))
  have hstaym : ∀ n, AEMeasurable (fun ω ↦
      (stayUpTo (sqOpen a L) B z t n (2 ^ n + 1)).indicator (1 : Ω → ℝ) ω) P := by
    intro n
    have e : (fun ω ↦ (stayUpTo (sqOpen a L) B z t n (2 ^ n + 1)).indicator (1 : Ω → ℝ) ω) =
        fun ω ↦ 1 - ∑ m ∈ Finset.range (2 ^ n + 1),
          (exitAt (sqOpen a L) B z t n m).indicator 1 ω :=
      funext fun ω ↦ indicator_stayUpTo_eq _ z t n _ ω
    rw [e]
    exact aemeasurable_const.sub (Finset.aemeasurable_fun_sum _ fun m _ ↦
      aemeasurable_indicator_exitAt hB hQ z t n m)
  have hlim1 : Tendsto (fun n ↦ ∫ ω, (stayUpTo (sqOpen a L) B z t n (2 ^ n + 1)).indicator 1 ω *
      sqMode a L p (z + B t ω) ∂P) atTop
      (𝓝 (∫ ω, (stayGrid (sqOpen a L) B z t).indicator 1 ω * sqMode a L p (z + B t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
      (fun n ↦ ((hstaym n).mul hφm).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (abs_indicator_one_le _ _) (abs_nonneg _) (abs_sqMode_le _ _ _ _)
    · by_cases hω : ω ∈ stayGrid (sqOpen a L) B z t
      · have hn : ∀ n, ω ∈ stayUpTo (sqOpen a L) B z t n (2 ^ n + 1) :=
          fun n ↦ Set.mem_iInter.mp hω n
        simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hn _)]
        exact tendsto_const_nhds
      · obtain ⟨n0, hn0⟩ : ∃ n0, ω ∉ stayUpTo (sqOpen a L) B z t n0 (2 ^ n0 + 1) := by
          by_contra h
          push Not at h
          exact hω (Set.mem_iInter.mpr h)
        rw [Set.indicator_of_notMem hω, zero_mul]
        refine tendsto_atTop_of_eventually_const (i₀ := n0) fun n hn ↦ ?_
        rw [Set.indicator_of_notMem (fun h ↦ hn0 (stayUpTo_antitone _ z t hn h)), zero_mul]
  have hlim2 : Tendsto (fun n ↦ ∫ ω, corr a L p (sqOpen a L) B z t n ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω ↦ corr a L p (sqOpen a L) B z t n ω) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)
      (fun n ↦ ?_) (integrable_const _)
      (fun n ↦ ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_corr_le_one _ _ _ _ _ _ _ _)
      (by filter_upwards [hB.cont, ae_zero hB] with ω hc h0 using tendsto_corr hL p hz t hc h0)
    · simpa using h
    · unfold corr
      exact (Finset.aemeasurable_fun_sum _ fun m _ ↦ aemeasurable_const.mul
        ((aemeasurable_indicator_exitAt hB hQ z t n m).mul
          ((continuous_sqMode a L p).measurable.comp_aemeasurable
            (aemeasurable_const.add (aemeasurable_B hB _))))).aestronglyMeasurable
  have hO : ∀ n, ∫ ω, (stayUpTo (sqOpen a L) B z t n (2 ^ n + 1)).indicator 1 ω *
      sqMode a L p (z + B t ω) ∂P =
      sqDecay L t p * sqMode a L p z - ∫ ω, corr a L p (sqOpen a L) B z t n ω ∂P := by
    intro n
    rw [integral_stayUpTo_sqMode hB hQ a L p z t n le_rfl]
    congr 1
    unfold corr
    rw [integral_finsetSum _ fun m _ ↦ (integrable_exitAt_mul hB hQ a L p z t _ n m).const_mul _]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [integral_const_mul]
  simp only [hO] at hlim1
  have hlim3 : Tendsto (fun n ↦ sqDecay L t p * sqMode a L p z -
      ∫ ω, corr a L p (sqOpen a L) B z t n ω ∂P) atTop (𝓝 (sqDecay L t p * sqMode a L p z - 0)) :=
    tendsto_const_nhds.sub hlim2
  rw [sub_zero] at hlim3
  exact tendsto_nhds_unique hlim1 hlim3

end KilledHeatSq
end LQGMetric
