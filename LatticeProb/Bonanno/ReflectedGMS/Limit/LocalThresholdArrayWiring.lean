/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalThresholdArrayWiring at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedThresholdArrayInputs
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledBracketLLNBridge

/-!
# The bracket law of large numbers enters the *local* threshold lane

`Limit/BracketLLNThresholdWiring.thresholdArrayInputs_of_pointwise` replaces the uniform `ucp`
field of the **global** `LocalizedArrayProducer.ThresholdArrayInputs` by the fixed-time bracket law
of large numbers, and `Limit/RescaledBracketLLNBridge.thresholdArrayInputs_of_rescaledBracketLLN`
feeds that fixed-time form from the CLT's `RescaledBracketLLN`.  Both exist only for the global
structure, whose martingale fields are *true* martingales.

The walk's bracket (`Process/MartingaleIngredients.HasOrdinaryEdgeBracket`) gives only *local*
martingales, and the entry point for that form is the **local** structure
`Limit/LocalizedThresholdArrayInputs.LocalThresholdArrayInputs`, whose `ucp` field is still the
uniform one.  This module is the missing adapter:

* `localThresholdArrayInputs_of_pointwise` — `LocalThresholdArrayInputs` with `ucp` replaced by
  the fixed-time convergence in probability at every `t ≤ T`;
* `localThresholdArrayInputs_of_rescaledBracketLLN` — the same at the rescaled bracket
  `εₙ² A(·/εₙ²)`, fed by `ApproximateBracketCLT.RescaledBracketLLN P A C`, the very hypothesis
  the CLT lane consumes;
* `nonempty_localizedMartingaleArray_of_local_rescaledBracketLLN` — the composition with
  `LocalizedThresholdArray.nonempty_localizedMartingaleArray_of_localThresholdInputs`.

The lift is `BracketLLNUniform.tendsto_measure_exists_gt_of_tendsto_pointwise`, which needs exactly
the monotonicity the structure already asks for; nothing new is assumed.

**This is an implication.**  Nothing here certifies the bracket law of large numbers, the local
martingale fields, or any consumer of `harray`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.LocalThresholdArrayWiring

open ReflectedGMS.LocalizedArrayProducer
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.LocalizedThresholdArray
open ReflectedGMS.BracketLLNUniform
open ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.ApproximateBracketCLT

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **The local threshold-lane inputs with the bracket law of large numbers at its fixed-time
form.**  Every hypothesis except the last is verbatim a field of
`LocalizedThresholdArray.LocalThresholdArrayInputs`; the last, `lln`, replaces `ucp`. -/
theorem localThresholdArrayInputs_of_pointwise
    {P : Measure Ω} {F : ℕ → Filtration ℝ≥0 m} {M V : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v K : ℝ}
    (v_nonneg : 0 ≤ v)
    (threshold_gt : v * (T : ℝ) < K)
    (localMartingale : ∀ n,
      MartingaleIngredients.IsLocallySquareIntegrableMartingale P (F n) (M n))
    (localCompensated : ∀ n, MartingaleIngredients.IsLocalMartingale P (F n)
      (fun t ω => M n t ω * M n t ω - V n t ω))
    (null : ∀ n (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[(F n) t] A)
    (cadlag : ∀ n, ∀ᵐ ω ∂P, IsCadlag (fun t => M n t ω))
    (start_martingale : ∀ n, ∀ᵐ ω ∂P, M n 0 ω = 0)
    (start_bracket : ∀ n, ∀ᵐ ω ∂P, V n 0 ω = 0)
    (adapted_bracket : ∀ n, Adapted (F n) (V n))
    (continuous_bracket : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => V n t ω))
    (monotone_bracket : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => V n t ω))
    (nonneg_bracket : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ V n t ω)
    (lln : ∀ t : ℝ≥0, t ≤ T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | δ < |V n t ω - v * (t : ℝ)|}) atTop (𝓝 0)) :
    LocalThresholdArrayInputs P F M V T v K where
  v_nonneg := v_nonneg
  threshold_gt := threshold_gt
  localMartingale := localMartingale
  localCompensated := localCompensated
  null := null
  cadlag := cadlag
  start_martingale := start_martingale
  start_bracket := start_bracket
  adapted_bracket := adapted_bracket
  continuous_bracket := continuous_bracket
  monotone_bracket := monotone_bracket
  nonneg_bracket := nonneg_bracket
  ucp := fun _ε hε =>
    tendsto_measure_exists_gt_of_tendsto_pointwise v_nonneg monotone_bracket lln hε

/-- **The local threshold-lane inputs at the rescaled bracket, fed by the CLT's bracket
hypothesis.**  The bracket rows are `rescaledBracket A ε n = εₙ² A(·/εₙ²)`, and the `ucp` field
is supplied by `RescaledBracketLLN P A C` — the `hLLN` input of
`ApproximateBracketCLTRescaled.rescaledIncrementCharFunLimit_of_bracket_data`.  So one bracket
law of large numbers feeds the CLT lane and the *local* tightness lane at once. -/
theorem localThresholdArrayInputs_of_rescaledBracketLLN
    {P : Measure Ω} {F : ℕ → Filtration ℝ≥0 m} {M : ℕ → ℝ≥0 → Ω → ℝ}
    {A : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C K : ℝ}
    (v_nonneg : 0 ≤ C)
    (threshold_gt : C * (T : ℝ) < K)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)))
    (localMartingale : ∀ n,
      MartingaleIngredients.IsLocallySquareIntegrableMartingale P (F n) (M n))
    (localCompensated : ∀ n, MartingaleIngredients.IsLocalMartingale P (F n)
      (fun t ω => M n t ω * M n t ω - rescaledBracket A ε n t ω))
    (null : ∀ n (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[(F n) t] S)
    (cadlag : ∀ n, ∀ᵐ ω ∂P, IsCadlag (fun t => M n t ω))
    (start_martingale : ∀ n, ∀ᵐ ω ∂P, M n 0 ω = 0)
    (start_bracket : ∀ n, ∀ᵐ ω ∂P, rescaledBracket A ε n 0 ω = 0)
    (adapted_bracket : ∀ n, Adapted (F n) (rescaledBracket A ε n))
    (continuous_bracket : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => rescaledBracket A ε n t ω))
    (monotone_bracket : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => rescaledBracket A ε n t ω))
    (nonneg_bracket : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ rescaledBracket A ε n t ω)
    (hLLN : RescaledBracketLLN P A C) :
    LocalThresholdArrayInputs P F M (rescaledBracket A ε) T C K :=
  localThresholdArrayInputs_of_pointwise v_nonneg threshold_gt localMartingale localCompensated
    null cadlag start_martingale start_bracket adapted_bracket continuous_bracket
    monotone_bracket nonneg_bracket (lln_of_rescaledBracketLLN hLLN hε T)

end ReflectedGMS.LocalThresholdArrayWiring
