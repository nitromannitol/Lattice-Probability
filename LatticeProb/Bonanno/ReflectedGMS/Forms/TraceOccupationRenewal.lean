/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TraceOccupationRenewal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ChainHoldingShift

/-!
# Renewal for the discounted occupation of the finite induced chain

The random variable in this file is built directly from the embedded-chain
law and its conditional exponential holding kernel.  Self returns are kept:
every trial contributes its own holding interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.FullNetworkForm

open ReflectedWalk

variable {S : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S]

/-- Discount accumulated before the `n`th holding interval. -/
noncomputable def finiteTraceDiscountPrefix (alpha : ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∏ j ∈ Finset.range n, finiteTraceHoldingDiscount alpha (t j)

/-- The `n`th discounted holding reward along an embedded path. -/
noncomputable def finiteTraceOccupationTerm
    (alpha : ℝ) (F : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  finiteTraceDiscountPrefix alpha p.2 n * ENNReal.ofReal (F (p.1 n)) *
    finiteTraceHoldingReward alpha (p.2 n)

/-- Total nonnegative discounted holding reward of the embedded chain. -/
noncomputable def finiteTraceOccupationSeries
    (alpha : ℝ) (F : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  ∑' n : ℕ, finiteTraceOccupationTerm alpha F p n

theorem measurable_finiteTraceDiscountPrefix (alpha : ℝ) (n : ℕ) :
    Measurable fun t : ℕ → ℝ => finiteTraceDiscountPrefix alpha t n := by
  unfold finiteTraceDiscountPrefix
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_finiteTraceHoldingDiscount alpha).comp (measurable_pi_apply i)

theorem measurable_finiteTraceOccupationTerm (alpha : ℝ) (F : S → ℝ) (n : ℕ) :
    Measurable fun p : (ℕ → S) × (ℕ → ℝ) =>
      finiteTraceOccupationTerm alpha F p n := by
  unfold finiteTraceOccupationTerm
  exact ((measurable_finiteTraceDiscountPrefix alpha n).comp measurable_snd).mul
    (((measurable_of_countable F).comp
      ((measurable_pi_apply n).comp measurable_fst)).ennreal_ofReal) |>.mul
      ((measurable_finiteTraceHoldingReward alpha).comp
        ((measurable_pi_apply n).comp measurable_snd))

theorem measurable_finiteTraceOccupationSeries (alpha : ℝ) (F : S → ℝ) :
    Measurable fun p : (ℕ → S) × (ℕ → ℝ) =>
      finiteTraceOccupationSeries alpha F p := by
  exact Measurable.ennreal_tsum fun n => measurable_finiteTraceOccupationTerm alpha F n

theorem finiteTraceOccupationTerm_zero
    (alpha : ℝ) (F : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) :
    finiteTraceOccupationTerm alpha F p 0 =
      ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0) := by
  simp [finiteTraceOccupationTerm, finiteTraceDiscountPrefix]

theorem finiteTraceOccupationTerm_succ
    (alpha : ℝ) (F : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) (n : ℕ) :
    finiteTraceOccupationTerm alpha F p (n + 1) =
      finiteTraceHoldingDiscount alpha (p.2 0) *
        finiteTraceOccupationTerm alpha F
          (MarkovChain.walkShift 1 p.1, MarkovChain.walkShift 1 p.2) n := by
  unfold finiteTraceOccupationTerm finiteTraceDiscountPrefix
  rw [show (∏ j ∈ Finset.range (n + 1), finiteTraceHoldingDiscount alpha (p.2 j)) =
      finiteTraceHoldingDiscount alpha (p.2 0) *
        ∏ j ∈ Finset.range n,
          finiteTraceHoldingDiscount alpha ((MarkovChain.walkShift 1 p.2) j) by
    rw [Finset.prod_range_succ']
    simp only [MarkovChain.walkShift]
    ac_rfl]
  simp only [MarkovChain.walkShift]
  ac_rfl

theorem finiteTraceOccupationSeries_shift
    (alpha : ℝ) (F : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) :
    finiteTraceOccupationSeries alpha F p =
      ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0) +
        finiteTraceHoldingDiscount alpha (p.2 0) *
          finiteTraceOccupationSeries alpha F
            (MarkovChain.walkShift 1 p.1, MarkovChain.walkShift 1 p.2) := by
  calc
    finiteTraceOccupationSeries alpha F p =
        finiteTraceOccupationTerm alpha F p 0 +
          ∑' n : ℕ, finiteTraceOccupationTerm alpha F p (n + 1) := by
      unfold finiteTraceOccupationSeries
      exact tsum_eq_zero_add' ENNReal.summable
    _ = ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0) +
          ∑' n : ℕ, finiteTraceHoldingDiscount alpha (p.2 0) *
            finiteTraceOccupationTerm alpha F
              (MarkovChain.walkShift 1 p.1, MarkovChain.walkShift 1 p.2) n := by
      rw [finiteTraceOccupationTerm_zero]
      congr 1
      apply tsum_congr
      intro n
      exact finiteTraceOccupationTerm_succ alpha F p n
    _ = _ := by
      rw [ENNReal.tsum_mul_left]
      rfl

/-- Expected total discounted occupation reward under the actual joint
embedded-chain/holding law. -/
noncomputable def finiteTraceExpectedOccupation
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (alpha : ℝ)
    (F : S → ℝ) (x : S) : ℝ≥0∞ :=
  ∫⁻ p, finiteTraceOccupationSeries alpha F p
    ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w)

/-- The expected series obeys the exact one-step renewal equation. -/
theorem finiteTraceExpectedOccupation_renewal
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (hw : ∀ z, 0 < w z)
    (F : S → ℝ) (x : S) {alpha : ℝ} (halpha : 0 < alpha) :
    finiteTraceExpectedOccupation κ w alpha F x =
      ENNReal.ofReal (F x) * ENNReal.ofReal (1 / (w x + alpha)) +
        ENNReal.ofReal (w x / (w x + alpha)) *
          ∫⁻ y, finiteTraceExpectedOccupation κ w alpha F y ∂κ x := by
  let μ := MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w
  have hfirst : Measurable fun p : (ℕ → S) × (ℕ → ℝ) =>
      ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0) := by
    simpa only [finiteTraceOccupationTerm_zero] using
      measurable_finiteTraceOccupationTerm alpha F 0
  have htail : Measurable fun p : (ℕ → S) × (ℕ → ℝ) =>
      finiteTraceOccupationSeries alpha F
        (MarkovChain.walkShift 1 p.1, MarkovChain.walkShift 1 p.2) :=
    (measurable_finiteTraceOccupationSeries alpha F).comp
      (((MarkovChain.measurable_walkShift 1).comp measurable_fst).prodMk
        ((MarkovChain.measurable_walkShift 1).comp measurable_snd))
  unfold finiteTraceExpectedOccupation
  rw [lintegral_congr (fun p => finiteTraceOccupationSeries_shift alpha F p),
    lintegral_add_left hfirst]
  rw [lintegral_chainLaw_compProd_firstReward κ w hw F x halpha]
  congr 1
  rw [lintegral_firstHolding_mul_jointWalkShift κ w hw x
    (measurable_finiteTraceHoldingDiscount alpha)
    (measurable_finiteTraceOccupationSeries alpha F)]
  rw [show (∫⁻ t, finiteTraceHoldingDiscount alpha t ∂expMeasure (w x)) =
      ENNReal.ofReal (w x / (w x + alpha)) by
    simpa [finiteTraceHoldingDiscount] using
      ReflectedGMS.DiscountedTraceStep.lintegral_expMeasure_discount
        (hw x) halpha.le]

end ReflectedGMS.FullNetworkForm
