/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B2

/-!
# DZZ crude moments: the geometric-tail second-moment bound (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-very-crude-prime), (eq-very-crude), l. 849–857:
`E (log D'/log δ⁻¹)² = O(1)`, `E (log D/log δ⁻¹)² = O(1)`. DZZ derive both from an exponential
tail of a scale index ("the tail of the distribution of `log S_δ / log δ` decays at least
exponentially", l. 849–851). This file abstracts the tail-sum computation of
`lintegral_sq_log_tilde_le` (P2-DZZ53b, S5L53B2) into a generic lemma:

* `lintegral_sq_le_of_geom`: if `f ≤ a₀ + c m` off a bad set `T m` and `P(T m) ≤ C (r²)^m`,
  then `∫⁻ f² ≤ 4 (a₀² + c² C (1-r)^{-2})` (own elementary tail-sum argument, as in S5L53B2);
* `memLp_two_of_lintegral_sq`: the Bochner form (`MemLp _ 2`, `∫ X² ≤ B`) of such a bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **geometric-tail second-moment bound** (the computation of `lintegral_sq_log_tilde_le`). -/
theorem lintegral_sq_le_of_geom {P : Measure Ω} [IsProbabilityMeasure P] (f : Ω → ℝ≥0∞)
    (T : ℕ → Set Ω) (hTm : ∀ m, MeasurableSet (T m)) {a₀ c C r : ℝ} (ha₀ : 0 ≤ a₀)
    (hc : 0 < c) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hPq : ∀ m : ℕ, P (T m) ≤ ENNReal.ofReal (C * (r ^ 2) ^ m))
    (hpt : ∀ ω (m : ℕ), ω ∉ T m → f ω ≤ ENNReal.ofReal (a₀ + c * m)) :
    ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal (4 * (a₀ ^ 2 + c ^ 2 * (C * ((1 - r)⁻¹) ^ 2))) := by
  set G2 : ℝ≥0∞ := ENNReal.ofReal C * ((1 - ENNReal.ofReal r)⁻¹ * (1 - ENNReal.ofReal r)⁻¹)
    with hG2
  have hG2e : G2 = ENNReal.ofReal (C * ((1 - r)⁻¹) ^ 2) := by
    have h1 : 1 - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ hr0]
    rw [hG2, h1, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by
      have : 0 < 1 - r := by linarith
      positivity), ← ENNReal.ofReal_mul hC, sq]
  -- pointwise bound
  have hpt' : ∀ ω, f ω ≤ ENNReal.ofReal a₀ + ENNReal.ofReal c *
      ∑' m : ℕ, (T m).indicator 1 ω := by
    intro ω
    by_cases h : ∃ m, ω ∉ T m
    · classical
      set m := Nat.find h
      have hm : ω ∉ T m := Nat.find_spec h
      have hlt : ∀ i < m, ω ∈ T i := fun i hi => by
        have := Nat.find_min h hi; push Not at this; exact this
      have hsum : (m : ℝ≥0∞) ≤ ∑' i : ℕ, (T i).indicator 1 ω := by
        calc (m : ℝ≥0∞) = ∑ i ∈ Finset.range m, (T i).indicator 1 ω := by
              rw [Finset.sum_congr rfl fun i hi => by
                rw [indicator_of_mem (hlt i (Finset.mem_range.1 hi))]]
              simp
          _ ≤ _ := ENNReal.sum_le_tsum _
      calc f ω ≤ ENNReal.ofReal (a₀ + c * m) := hpt ω m hm
        _ = ENNReal.ofReal a₀ + ENNReal.ofReal c * (m : ℝ≥0∞) := by
            rw [ENNReal.ofReal_add ha₀ (by positivity), ENNReal.ofReal_mul hc.le,
              ENNReal.ofReal_natCast]
        _ ≤ _ := by gcongr
    · push Not at h
      have htop : ∑' m : ℕ, (T m).indicator (1 : Ω → ℝ≥0∞) ω = ⊤ := by
        simp only [indicator_of_mem (h _), Pi.one_apply]
        exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
      have hne : ENNReal.ofReal c ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc
      rw [htop, ENNReal.mul_top hne]
      simp
  have hpair : ∀ m m' : ℕ, P (T m ∩ T m') ≤
      ENNReal.ofReal C * ENNReal.ofReal r ^ m * ENNReal.ofReal r ^ m' := fun m m' => by
    rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_pow hr0,
      ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
    have key : ∀ n n' : ℕ, n ≤ n' → (r ^ 2) ^ n' ≤ r ^ n * r ^ n' := fun n n' hn => by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
    rcases le_total m m' with h | h
    · refine (measure_mono inter_subset_right).trans ((hPq m').trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (key m m' h) hC
    · refine (measure_mono inter_subset_left).trans ((hPq m).trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [mul_assoc, mul_comm (r ^ m)]
      exact mul_le_mul_of_nonneg_left (key m' m h) hC
  set N : Ω → ℝ≥0∞ := fun ω => ∑' m : ℕ, (T m).indicator 1 ω with hN
  have hN2 : ∫⁻ ω, N ω ^ 2 ∂P ≤ G2 := by
    have e : ∀ ω, N ω ^ 2 = ∑' m', ∑' m, (T m ∩ T m').indicator 1 ω := by
      intro ω
      rw [sq]
      simp only [hN]
      rw [← ENNReal.tsum_mul_left]
      congr 1; funext m'
      rw [← ENNReal.tsum_mul_right]
      congr 1; funext m
      rw [inter_indicator_one, Pi.mul_apply]
    simp_rw [e]
    rw [lintegral_tsum fun m' => (Measurable.ennreal_tsum fun m =>
      measurable_one.indicator ((hTm _).inter (hTm _))).aemeasurable]
    calc ∑' m', ∫⁻ ω, ∑' m, (T m ∩ T m').indicator 1 ω ∂P
        = ∑' m', ∑' m, P (T m ∩ T m') := by
          congr 1; funext m'
          rw [lintegral_tsum fun m => (measurable_one.indicator
            ((hTm _).inter (hTm _))).aemeasurable]
          simp only [lintegral_indicator_one ((hTm _).inter (hTm _))]
      _ ≤ ∑' m', ∑' m, ENNReal.ofReal C * ENNReal.ofReal r ^ m * ENNReal.ofReal r ^ m' :=
          ENNReal.tsum_le_tsum fun m' => ENNReal.tsum_le_tsum fun m => hpair m m'
      _ = G2 := by
          simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hG2]
          ring
  calc ∫⁻ ω, f ω ^ 2 ∂P ≤ ∫⁻ ω, 4 * (ENNReal.ofReal a₀ ^ 2 +
        ENNReal.ofReal c ^ 2 * N ω ^ 2) ∂P :=
        lintegral_mono fun ω => ((pow_le_pow_left₀ bot_le (hpt' ω) 2).trans
          (ennreal_add_sq_le_four _ _)).trans_eq (by rw [mul_pow])
    _ = 4 * (ENNReal.ofReal a₀ ^ 2 + ENNReal.ofReal c ^ 2 * ∫⁻ ω, N ω ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    _ ≤ 4 * (ENNReal.ofReal a₀ ^ 2 + ENNReal.ofReal c ^ 2 * G2) := by gcongr
    _ = _ := by
        rw [hG2e, ← ENNReal.ofReal_pow ha₀, ← ENNReal.ofReal_pow hc.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by have : 0 < 1 - r := by linarith
                positivity), ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]

/-- the Bochner form of a `∫⁻` second-moment bound for a nonnegative a.e.-measurable `X` -/
theorem memLp_two_of_lintegral_sq {P : Measure Ω} {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXm : AEMeasurable X P) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂P ≤ ENNReal.ofReal B) :
    MemLp X 2 P ∧ ∫ ω, X ω ^ 2 ∂P ≤ B := by
  have e : ∀ ω, ENNReal.ofReal (X ω) ^ 2 = ENNReal.ofReal (X ω ^ 2) := fun ω =>
    (ENNReal.ofReal_pow (hX0 ω) 2).symm
  simp_rw [e] at h
  have hsqm : AEStronglyMeasurable (fun ω => X ω ^ 2) P := (hXm.pow_const 2).aestronglyMeasurable
  have hint : Integrable (fun ω => X ω ^ 2) P := by
    refine ⟨hsqm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg (X ω))]
    exact h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg (X ω)) hsqm]
  exact ENNReal.toReal_le_of_le_ofReal hB h

end DZZ
end LQGMetric
