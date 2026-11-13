/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianFiniteExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Almost-sure exit of Brownian paths from bounded sets

Only a single coordinate and its actual Gaussian marginal laws are needed.
At the square times `(n + 1)^2`, the chance of lying in any fixed bounded
interval tends to zero. This rules out remaining in a bounded domain forever.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace BouRabeeGwynne

private lemma standardGaussian_measure_shrinking_interval_tendsto_zero
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ ↦ gaussianReal 0 1 {x : ℝ | |x| ≤ R / (n + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let S : ℕ → Set ℝ := fun n ↦ {x | |x| ≤ R / (n + 1)}
  have hmeas (n : ℕ) : MeasurableSet (S n) :=
    (isClosed_le continuous_abs continuous_const).measurableSet
  have hanti : Antitone S := by
    intro n m hnm x hx
    exact hx.trans (div_le_div_of_nonneg_left hR (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hinter : (⋂ n, S n) = {0} := by
    ext x
    simp only [mem_iInter, S, mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxzero
      have hxpos : 0 < |x| := abs_pos.mpr hxzero
      obtain ⟨n, hn⟩ := exists_nat_gt (R / |x|)
      have hlarge : R < (n : ℝ) * |x| := (div_lt_iff₀ hxpos).mp hn
      have hsmall : |x| * ((n : ℝ) + 1) ≤ R :=
        (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp (hx n)
      nlinarith
    · rintro rfl n
      simpa only [abs_zero] using div_nonneg hR (by positivity : 0 ≤ (n : ℝ) + 1)
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hlim := tendsto_measure_iInter_atTop
    (fun n ↦ (hmeas n).nullMeasurableSet (μ := gaussianReal 0 1)) hanti
    ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, measure_singleton, Function.comp_def, S] using hlim

/-- The actual Gaussian marginals of variance `(n+1)^2` leave every fixed
bounded interval with probability tending to one. -/
theorem gaussian_square_time_measure_bounded_tendsto_zero {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ ↦ gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2)
      {x : ℝ | |x| ≤ R}) atTop (𝓝 (0 : ℝ≥0∞)) := by
  have heq (n : ℕ) : gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ R} =
      gaussianReal 0 1 {x : ℝ | |x| ≤ R / (n + 1)} := by
    have hc : 0 < (n : ℝ) + 1 := by positivity
    have hmap : (gaussianReal 0 1).map (fun x : ℝ ↦ ((n : ℝ) + 1) * x) =
        gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) := by
      rw [gaussianReal_map_const_mul, mul_zero, mul_one]
      congr 1
    rw [← hmap, Measure.map_apply (by fun_prop)
      (isClosed_le continuous_abs continuous_const).measurableSet]
    congr 1
    ext x
    simp only [mem_preimage, mem_setOf_eq, abs_mul, abs_of_pos hc, le_div_iff₀ hc]
    rw [mul_comm]
  simp_rw [heq]
  exact standardGaussian_measure_shrinking_interval_tendsto_zero hR

/-- A pre-Brownian process is almost surely not bounded at all square times.
This uses Gaussian marginals and no independence or stopping theorem. -/
theorem preBrownian_ae_not_bounded_square_times {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ¬ ∀ n : ℕ, |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R := by
  have hbound (n : ℕ) :
      P {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} ≤
        gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ R} := by
    calc
      _ ≤ P {ω | |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R} :=
        measure_mono (show {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} ⊆
          {ω | |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R} from fun ω hω ↦ hω n)
      _ = _ := (hB.hasLaw_eval _).measure_eq
        (isClosed_le continuous_abs continuous_const).measurableSet
  have hzero : P {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} = 0 :=
    le_antisymm (ge_of_tendsto' (gaussian_square_time_measure_bounded_tendsto_zero hR)
      hbound) bot_le
  simpa only [ae_iff, not_not] using hzero

/-- Every standard Brownian law in positive dimension exits a bounded set
almost surely, from every translated starting point. -/
theorem standardBrownianLaw_ae_finiteExit {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (z : Euc d) :
    ∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞ := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  let i : Fin d := ⟨0, hd⟩
  have hnot := preBrownian_ae_not_bounded_square_times
    (hμ.2.1 i).toIsPreBrownianReal (R := R + ‖z‖) (by positivity)
  filter_upwards [hnot] with ω hω
  intro hnever
  apply hω
  intro n
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  have hin : z + ω t ∈ U := by
    by_contra hout
    have hle : continuousExitTime U z ω ≤ (t : ℝ≥0∞) :=
      iInf_le_of_le ⟨t, hout⟩ le_rfl
    rw [hnever] at hle
    exact ENNReal.coe_ne_top (top_le_iff.mp hle)
  calc
    |ω t i| = ‖ω t i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ω t‖ := PiLp.norm_apply_le (ω t) i
    _ ≤ ‖z + ω t‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z + ω t) z
    _ ≤ R + ‖z‖ := add_le_add (hR _ hin) le_rfl

/-- One Gaussian coordinate gives a uniform tail bound over all starts in a
set whose norm is bounded by `R`. The event uses the actual first exit time. -/
theorem standardBrownianLaw_measure_lateExit_le {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} {R : ℝ} (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    {z : Euc d} (hz : z ∈ U) (n : ℕ) :
    μ {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < continuousExitTime U z ω} ≤
      gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ 2 * R} := by
  let i : Fin d := ⟨0, hd⟩
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  calc
    _ ≤ μ {ω | |ω t i| ≤ 2 * R} := by
      apply measure_mono
      intro ω hω
      have hin : z + ω t ∈ U := by
        by_contra hout
        have hle : continuousExitTime U z ω ≤ (t : ℝ≥0∞) :=
          iInf_le_of_le ⟨t, hout⟩ le_rfl
        exact (not_le_of_gt hω) hle
      calc
        |ω t i| = ‖ω t i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ω t‖ := PiLp.norm_apply_le (ω t) i
        _ ≤ ‖z + ω t‖ + ‖z‖ := by
          simpa only [add_sub_cancel_left] using norm_sub_le (z + ω t) z
        _ ≤ R + R := add_le_add (hR _ hin) (hR _ hz)
        _ = 2 * R := (two_mul R).symm
    _ = _ := ((hμ.2.1 i).toIsPreBrownianReal.hasLaw_eval t).measure_eq
      (isClosed_le continuous_abs continuous_const).measurableSet

/-- Bounded-domain Brownian exit tails vanish uniformly over starting points.
This is time truncation; a skeleton-count estimate remains a separate step. -/
theorem standardBrownianLaw_uniform_exitTail {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ U,
      μ {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < continuousExitTime U z ω} ≤ ε := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  have hlim := gaussian_square_time_measure_bounded_tendsto_zero
    (show 0 ≤ 2 * R by positivity)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  exact (standardBrownianLaw_measure_lateExit_le hd hμ hR hz n).trans hn.le

end BouRabeeGwynne
