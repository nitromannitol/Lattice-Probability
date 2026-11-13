/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.JumpPathOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import LatticeProb.Bonanno.ReflectedGMS.Forms.TraceOccupationRenewal
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Relate the existing jump-path functional to the discounted holding series.
The clock and path are reused from `ReflectedWalk.ContinuousTimeChain`. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.ContinuousTimeChain FullNetworkForm

theorem jumpClock_ne_top (T : ℕ → ℝ) (n : ℕ) : jumpClock T n ≠ ⊤ := by
  unfold jumpClock
  exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top

theorem jumpClock_toReal_succ (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) (n : ℕ) :
    (jumpClock T (n + 1)).toReal = (jumpClock T n).toReal + T n := by
  unfold jumpClock
  rw [Finset.sum_range_succ, ENNReal.toReal_add
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (hT n)]

theorem finiteTraceDiscountPrefix_eq_exp_jumpClock (alpha : ℝ)
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) (n : ℕ) :
    finiteTraceDiscountPrefix alpha T n =
      ENNReal.ofReal (Real.exp (-alpha * (jumpClock T n).toReal)) := by
  induction n with
  | zero => simp [finiteTraceDiscountPrefix, jumpClock]
  | succ n ih =>
    rw [finiteTraceDiscountPrefix, Finset.prod_range_succ]
    change finiteTraceDiscountPrefix alpha T n * finiteTraceHoldingDiscount alpha (T n) = _
    rw [ih, jumpClock_toReal_succ T hT, mul_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rfl

/-- The exponential occupation of one holding interval is exactly its
prefix discount times its holding reward. -/
theorem lintegral_exp_neg_mul_Ico {alpha a d : ℝ} (ha : 0 < alpha) (hd : 0 ≤ d) :
    (∫⁻ t : ℝ in Ico a (a + d), ENNReal.ofReal (Real.exp (-alpha * t))) =
      ENNReal.ofReal (Real.exp (-alpha * a)) * ENNReal.ofReal (1 / alpha) *
        (1 - ENNReal.ofReal (Real.exp (-alpha * d))) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-alpha * t)) := by fun_prop
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-alpha * t)) (Ico a (a + d)) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
  have hreal : (∫ t : ℝ in Ico a (a + d), Real.exp (-alpha * t)) =
      Real.exp (-alpha * a) * (1 / alpha) * (1 - Real.exp (-alpha * d)) := by
    rw [integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_add_of_nonneg_right hd),
      intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr ha.ne'),
      integral_exp]
    simp only [smul_eq_mul, mul_add, Real.exp_add]
    field_simp
    ring
  rw [hreal, ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (one_div_pos.mpr ha).le),
    ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_sub 1 (Real.exp_nonneg _),
    ENNReal.ofReal_one]


private def realJumpInterval (T : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  Ico (jumpClock T n).toReal (jumpClock T (n + 1)).toReal

private theorem inJump_iff_realJumpInterval (T : ℕ → ℝ) (n : ℕ) (t : ℝ≥0) :
    InJump T n (t : ℝ≥0∞) ↔ (t : ℝ) ∈ realJumpInterval T n := by
  unfold InJump realJumpInterval
  rw [← ENNReal.toReal_le_toReal (jumpClock_ne_top T n) ENNReal.coe_ne_top,
    ← ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (jumpClock_ne_top T (n + 1))]
  simp

/-- The literal occupation of the existing jump path equals the discounted
holding series, including self returns. No nonexplosion assumption is needed:
after a finite accumulation time the jump path is `none`. -/
theorem discountedVertexOccupation_jumpPath_eq_series
    {V : Type*} [MeasurableSpace V] [DecidableEq V]
    (p : (ℕ → V) × (ℕ → ℝ)) {alpha : ℝ} (ha : 0 < alpha)
    (hT : ∀ n, 0 ≤ p.2 n) (y : V) :
    discountedVertexOccupation (fun t p => jumpPath p t) alpha y p =
      finiteTraceOccupationSeries alpha (fun v => if v = y then 1 else 0) p := by
  classical
  let J : ℕ → Set ℝ := fun n => if p.1 n = y then realJumpInterval p.2 n else ∅
  have hJ : ∀ n, MeasurableSet (J n) := by
    intro n
    dsimp [J, realJumpInterval]
    split_ifs <;> measurability
  have hmem {n : ℕ} {s : ℝ} (hs : s ∈ realJumpInterval p.2 n) :
      0 ≤ s ∧ InJump p.2 n (Real.toNNReal s : ℝ≥0∞) := by
    have hn : 0 ≤ s := ENNReal.toReal_nonneg.trans hs.1
    exact ⟨hn, (inJump_iff_realJumpInterval p.2 n (Real.toNNReal s)).mpr
      (by simpa only [Real.coe_toNNReal s hn] using hs)⟩
  have hd : Pairwise (fun n m => Disjoint (J n) (J m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro s hn hm
    have hn' : s ∈ realJumpInterval p.2 n := by
      by_cases hy : p.1 n = y
      · simpa [J, hy] using hn
      · simp [J, hy] at hn
    have hm' : s ∈ realJumpInterval p.2 m := by
      by_cases hy : p.1 m = y
      · simpa [J, hy] using hm
      · simp [J, hy] at hm
    exact hnm (inJump_unique (hmem hn').2 (hmem hm').2)
  have hsupp : Ici (0 : ℝ) ∩ {s : ℝ | jumpPath p (Real.toNNReal s) = some y} =
      ⋃ n, J n := by
    ext s
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨n, hn, hy⟩ := (jumpPath_eq_some_iff p (Real.toNNReal s) y).mp hp
      apply mem_iUnion.mpr
      refine ⟨n, ?_⟩
      simp only [J, hy, ite_true]
      simpa only [Real.coe_toNNReal s hs] using
        (inJump_iff_realJumpInterval p.2 n (Real.toNNReal s)).mp hn
    · intro hs
      obtain ⟨n, hn⟩ := mem_iUnion.mp hs
      by_cases hy : p.1 n = y
      · have hn : s ∈ realJumpInterval p.2 n := by simpa [J, hy] using hn
        exact ⟨(hmem hn).1, (jumpPath_eq_some_iff p (Real.toNNReal s) y).mpr
          ⟨n, (hmem hn).2, hy⟩⟩
      · simp [J, hy] at hn
  unfold discountedVertexOccupation
  rw [restrict_Ioi_eq_restrict_Ici,
    ← lintegral_indicator measurableSet_Ici]
  have hind :
      (Ici (0 : ℝ)).indicator
        ({s : ℝ | jumpPath p (Real.toNNReal s) = some y}.indicator
          (fun s => ENNReal.ofReal (Real.exp (-alpha * s)))) =
      (⋃ n, J n).indicator (fun s => ENNReal.ofReal (Real.exp (-alpha * s))) := by
    rw [← hsupp]
    ext s
    by_cases h0 : s ∈ Ici (0 : ℝ) <;>
      by_cases hy : jumpPath p (Real.toNNReal s) = some y <;> simp [h0, hy]
  rw [hind, lintegral_indicator (MeasurableSet.iUnion hJ), lintegral_iUnion hJ hd]
  unfold finiteTraceOccupationSeries
  apply tsum_congr
  intro n
  by_cases hy : p.1 n = y
  · simp only [J, hy, ite_true, realJumpInterval]
    rw [jumpClock_toReal_succ p.2 hT, lintegral_exp_neg_mul_Ico ha (hT n)]
    simp only [finiteTraceOccupationTerm, hy, ite_true, ENNReal.ofReal_one, mul_one,
      finiteTraceHoldingReward, finiteTraceHoldingDiscount,
      finiteTraceDiscountPrefix_eq_exp_jumpClock alpha p.2 hT]
    exact mul_assoc _ _ _
  · simp [J, hy, finiteTraceOccupationTerm]

end ReflectedGMS
