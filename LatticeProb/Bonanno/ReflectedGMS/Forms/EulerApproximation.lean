/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.EulerApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpectralSemigroup
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Dyadic Euler approximation of the full-form spectral multiplier

The rational resolvent multiplier iterated over `2^n` equal steps converges
uniformly on the full spectral interval `[0,1]` at each positive time. Dini's
theorem upgrades the existing scalar exponential limit, including the spectral
endpoint zero. Existing CFC continuity then gives convergence in operator norm.

Identifying each rational step with a Markov resolvent is a separate obligation.
-/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.SemigroupMultiplier

/-- The scalar multiplier of one implicit Euler resolvent step. -/
noncomputable def eulerStep (h x : ℝ) : ℝ := x / (x + h * (1 - x))

theorem eulerStep_denominator_pos {h x : ℝ} (hh : 0 < h) (hx : x ∈ Set.Icc 0 1) :
    0 < x + h * (1 - x) := by
  have hp : 0 ≤ h * (1 - x) := mul_nonneg hh.le (sub_nonneg.mpr hx.2)
  by_cases hx0 : x = 0
  · simpa [hx0] using hh
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hp

theorem eulerStep_mem_Icc {h x : ℝ} (hh : 0 < h) (hx : x ∈ Set.Icc 0 1) :
    eulerStep h x ∈ Set.Icc 0 1 := by
  have hd := eulerStep_denominator_pos hh hx
  refine ⟨div_nonneg hx.1 hd.le, ?_⟩
  apply (div_le_one hd).2
  exact le_add_of_nonneg_right (mul_nonneg hh.le (sub_nonneg.mpr hx.2))

theorem continuousOn_eulerStep {h : ℝ} (hh : 0 < h) :
    ContinuousOn (eulerStep h) (Set.Icc 0 1) := by
  unfold eulerStep
  exact continuousOn_id.div
    (continuousOn_id.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
    (fun _ hx => (eulerStep_denominator_pos hh hx).ne')

/-- Doubling the number of steps decreases the scalar Euler approximation. -/
theorem eulerStep_half_sq_le {h x : ℝ} (hh : 0 < h) (hx : x ∈ Set.Icc 0 1) :
    eulerStep (h / 2) x ^ 2 ≤ eulerStep h x := by
  have hd := eulerStep_denominator_pos hh hx
  have hdhalf := eulerStep_denominator_pos (half_pos hh) hx
  unfold eulerStep
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos hdhalf 2) hd).2
  nlinarith [mul_nonneg hx.1 (sq_nonneg (h * (1 - x)))]

theorem eulerStep_eq_inv (h : ℝ) {x : ℝ} (hx : x ≠ 0) :
    eulerStep h x = (1 + h * (1 / x - 1))⁻¹ := by
  have heq : 1 + h * (1 / x - 1) = (x + h * (1 - x)) / x := by
    field_simp [hx]
    <;> ring
  rw [eulerStep, heq, inv_div]

/-- The Euler product with a dyadic number of equal time steps. -/
noncomputable def dyadicEuler (t : ℝ≥0) (n : ℕ) (x : ℝ) : ℝ :=
  eulerStep ((t : ℝ) / (2 : ℝ) ^ n) x ^ (2 ^ n : ℕ)

theorem continuousOn_dyadicEuler {t : ℝ≥0} (ht : 0 < t) (n : ℕ) :
    ContinuousOn (dyadicEuler t n) (Set.Icc 0 1) :=
  (continuousOn_eulerStep (div_pos (show 0 < (t : ℝ) from ht) (by positivity))).pow _

theorem antitone_dyadicEuler {t : ℝ≥0} (ht : 0 < t) {x : ℝ}
    (hx : x ∈ Set.Icc 0 1) : Antitone (fun n => dyadicEuler t n x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hh : 0 < (t : ℝ) / (2 : ℝ) ^ n := div_pos ht (by positivity)
  have hhalf : (t : ℝ) / (2 : ℝ) ^ (n + 1) = ((t : ℝ) / (2 : ℝ) ^ n) / 2 := by
    rw [pow_succ, div_mul_eq_div_div]
  change eulerStep ((t : ℝ) / (2 : ℝ) ^ (n + 1)) x ^ (2 ^ (n + 1) : ℕ) ≤
    eulerStep ((t : ℝ) / (2 : ℝ) ^ n) x ^ (2 ^ n : ℕ)
  rw [hhalf, pow_succ (2 : ℕ) n, Nat.mul_comm, pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) (eulerStep_half_sq_le hh hx) _

theorem dyadicEuler_tendsto {t : ℝ≥0} (ht : 0 < t) {x : ℝ}
    (hx : x ∈ Set.Icc 0 1) :
    Tendsto (fun n => dyadicEuler t n x) atTop (𝓝 (k t x)) := by
  by_cases hx0 : x = 0
  · subst x
    have hk : k t 0 = 0 := by simp [k, ht.ne', expNegInvGlue.zero]
    simpa [dyadicEuler, eulerStep, hk] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    let a : ℝ := (t : ℝ) * (1 / x - 1)
    have heq (n : ℕ) : dyadicEuler t n x =
        ((1 + a / ((2 ^ n : ℕ) : ℝ)) ^ (2 ^ n : ℕ))⁻¹ := by
      have ha : ((t : ℝ) / (2 : ℝ) ^ n) * (1 / x - 1) =
          a / ((2 ^ n : ℕ) : ℝ) := by
        push_cast
        dsimp [a]
        ring
      rw [dyadicEuler, eulerStep_eq_inv _ hx0, ha, inv_pow]
    have hlim := ((Real.tendsto_one_add_div_pow_exp a).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))).inv₀
        (Real.exp_ne_zero a)
    have htarget : (Real.exp a)⁻¹ = k t x := by
      rw [← Real.exp_neg, k_eq_exp ht hxpos]
      congr 1
      dsimp [a]
      ring
    simpa only [Function.comp_def, ← heq, htarget] using hlim

/-- Uniform convergence includes zero in the spectrum at every positive time. -/
theorem dyadicEuler_tendstoUniformlyOn {t : ℝ≥0} (ht : 0 < t) :
    TendstoUniformlyOn (dyadicEuler t) (k t) atTop (Set.Icc 0 1) :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (continuousOn_dyadicEuler ht) (fun _ hx => antitone_dyadicEuler ht hx)
    (continuous_k t).continuousOn (fun _ hx => dyadicEuler_tendsto ht hx)

end ReflectedGMS.SemigroupMultiplier

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Each CFC approximant is the actual operator power of its rational step. -/
theorem dyadicEuler_cfc_eq_pow (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ≥0} (ht : 0 < t) (n : ℕ) :
    cfc (dyadicEuler t n) R =
      cfc (eulerStep ((t : ℝ) / (2 : ℝ) ^ n)) R ^ (2 ^ n : ℕ) := by
  exact cfc_pow _ _ R
    ((continuousOn_eulerStep (div_pos ht (by positivity))).mono hspec) hR

/-- The dyadic rational Euler products converge in operator norm to the
previously constructed spectral semigroup. -/
theorem dyadicEuler_cfc_tendsto (R : H →L[ℂ] H)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n => cfc (dyadicEuler t n) R) atTop (𝓝 (spectralSemigroup R t)) :=
  tendsto_cfc_fun ((dyadicEuler_tendstoUniformlyOn ht).mono hspec)
    (Filter.Eventually.of_forall fun n => (continuousOn_dyadicEuler ht n).mono hspec)

/-- The operator powers that will inherit the resolvent's Markov property
converge to the exact spectral semigroup at each positive time. -/
theorem dyadicEuler_pow_tendsto (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n => cfc (eulerStep ((t : ℝ) / (2 : ℝ) ^ n)) R ^ (2 ^ n : ℕ))
      atTop (𝓝 (spectralSemigroup R t)) := by
  simpa only [dyadicEuler_cfc_eq_pow R hR hspec ht] using
    dyadicEuler_cfc_tendsto R hspec ht

end ReflectedGMS.FullNetworkForm
