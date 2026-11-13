/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ApproximateBracketCLTRescaled at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ApproximateBracketCLT
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledFddCharFunReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.UCPBracketLocalization
import LatticeProb.Bonanno.ReflectedGMS.Limit.ThresholdStoppedMartingaleMoments
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNUniformProbability

/-!
# `RescaledIncrementCharFunLimit` from the approximate-bracket CLT

`RescaledFddCharFunReduction.RescaledIncrementCharFunLimit P 𝔽 M target` is the `hinc` atom of
the FCLT lane: along every `ε k → 0⁺`, for every direction `η` and `s ≤ t`, the conditional
characteristic function of the rescaled increment `⟪η, εₖ M(t/εₖ²) - εₖ M(s/εₖ²)⟫` given the
rescaled past converges in `L¹` to `exp (-(ηᵀΣη)(t - s)/2)`.  This file feeds it from the
abstract theorem `ApproximateBracketCLT.tendsto_integral_norm_condExp_cexp_sub_of_exists_localized`.

* `rescaledIncrementCharFunLimit_of_localizedBracketArrays` — the bridge: `hinc` follows from
  the existence, for each scale sequence, direction and time pair, of a
  `LocalizedBracketArray` of the rescaled filtrations agreeing with the rescaled projections
  outside events of vanishing probability.
* `rescaledIncrementCharFunLimit_of_projectionSquareMartingale'` — **non-vacuity**: the
  exact-bracket witness `BrownianFdd.ProjectionSquareMartingale` satisfies the bridge's
  hypothesis (unstopped, `K = (ηᵀΣη)(t - s)`), giving a second, independent proof of
  `RescaledFddCharFunReduction.rescaledIncrementCharFunLimit_of_projectionSquareMartingale`
  through the random-bracket machinery.
* `rescaledIncrementCharFunLimit_of_bracket_data` — **`hinc` at the walk, with the bracket
  LLN as a named hypothesis**: for a plane-valued process whose projections are
  square-integrable martingales with continuous monotone random brackets `A η`, on a
  filtration containing the null events, `hinc` follows from
  - `RescaledBracketLLN` (the bracket LLN in probability, locally uniformly in time: the
    rescaled bracket `εₖ² A η(r/εₖ²)` converges to `(ηᵀΣη) r` uniformly on `[0, T]` in
    probability), and
  - `StoppedRescaledLindeberg` (the Lindeberg sums of the rescaled projections stopped at
    the first time the rescaled bracket reaches a level `K` vanish in the double limit).

  The localisation is the threshold stopping of `UCPBracketLocalization`; the stopped
  martingale and compensated-square inputs come from `ThresholdStoppedMartingaleMoments`.

Neither named hypothesis is proved here.  The bracket LLN is the regeneration statement of
its own packet (`ActualArrayBracketLimit.phi_bracket_limit_of_canonicalBracket` gives its
almost-sure locally uniform form conditional on `hLLN`); the Lindeberg condition is the
small-jumps statement of the `hmod` lane.  The true-martingale form of the bracket data is
the localised form produced by `CommonSquareLocalizer.exists_common_square_localizer`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace ReflectedGMS.ApproximateBracketCLT

open ReflectedGMS.MartingaleLimit ReflectedGMS.MultiTimeCharFun ReflectedGMS.RescaledFddCharFun
open ReflectedGMS.StatementIngredients ReflectedGMS.GaussianLimitIdentification
open ReflectedGMS.BrownianFdd

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The bridge -/

/-- **`hinc` from localized bracket arrays of the rescaled projections.** -/
theorem rescaledIncrementCharFunLimit_of_localizedBracketArrays [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t)) (target : AnisotropicBrownianTarget)
    (hloc : ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
      ∀ (η : BouRabeeGwynne.Euc 2) (s t : ℝ≥0), s ≤ t →
        ∃ (N' A' : ℕ → ℝ≥0 → Ω → ℝ) (K : ℝ), 0 ≤ K
          ∧ LocalizedBracketArray P (fun k => rescaleFiltration 𝔽 (ε k)) N' A' s t
              (bilinForm target.covariance η η) K
          ∧ Tendsto (fun k => P.real {ω | ¬ (N' k t ω = rescaledProjection M (ε k) η t ω
              ∧ N' k s ω = rescaledProjection M (ε k) η s ω)}) atTop (𝓝 0)) :
    RescaledIncrementCharFunLimit P 𝔽 M target := by
  intro ε hε η s t hst
  have hNm : ∀ k (v : ℝ≥0), Measurable (rescaledProjection M (ε k) η v) := by
    intro k v
    have hX : Measurable (rescaleProcess M (ε k) v) := by
      show Measurable ((ε k : ℝ) • M ((ε k)⁻¹ ^ 2 * v))
      exact (((hadapt _).mono (𝔽.le _)).measurable).const_smul _
    exact measurable_const.inner hX
  have hmain : Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp
      (((1 : ℝ) * (rescaledProjection M (ε k) η t ω - rescaledProjection M (ε k) η s ω) : ℝ)
        * Complex.I) | rescaleFiltration 𝔽 (ε k) s]) ω
      - ((Real.exp (-((1 : ℝ) ^ 2 * (bilinForm target.covariance η η * ((t : ℝ) - (s : ℝ)))
        / 2)) : ℝ) : ℂ)‖ ∂P) atTop (𝓝 0) :=
    tendsto_integral_norm_condExp_cexp_sub_of_exists_localized
      (𝔽 := fun k => rescaleFiltration 𝔽 (ε k)) (N := fun k => rescaledProjection M (ε k) η)
      hNm hst (bilinForm_self_nonneg target η) (hloc ε hε η s t hst) 1
  have hphase : ∀ (k : ℕ) (ω : Ω), Complex.exp
      ((⟪η, rescaleProcess M (ε k) t ω - rescaleProcess M (ε k) s ω⟫_ℝ : ℂ) * Complex.I)
      = Complex.exp (((1 : ℝ) * (rescaledProjection M (ε k) η t ω
          - rescaledProjection M (ε k) η s ω) : ℝ) * Complex.I) := by
    intro k ω
    simp only [rescaledProjection, inner_sub_right, one_mul]
  have hfac : gaussFactor (bilinForm target.covariance) η s t
      = ((Real.exp (-((1 : ℝ) ^ 2 * (bilinForm target.covariance η η * ((t : ℝ) - (s : ℝ)))
          / 2)) : ℝ) : ℂ) := by
    simp only [gaussFactor, one_pow, one_mul]
  simp only [hphase, hfac]
  exact hmain

/-! ## The exact-bracket witness through the random-bracket machinery -/

/-! ## Stopped paths: continuity, monotonicity, nonnegativity -/

/-- The indicator-stopped process of a path that is continuous is continuous. -/
theorem continuous_indicator_stoppedProcess {B : ℝ≥0 → Ω → ℝ} (ω : Ω)
    (hB : Continuous fun r => B r ω) (τ : Ω → WithTop ℝ≥0) :
    Continuous fun r => stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (B r)) τ r ω := by
  have heq : (fun r => stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (B r)) τ r ω)
      = fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω := by
    funext r
    rw [stoppedProcess_indicator_comm]
  rw [heq]
  by_cases hωτ : ⊥ < τ ω
  · have hind : (fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω)
        = fun r => stoppedProcess B τ r ω := by
      funext r
      rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    by_cases hτtop : τ ω = ⊤
    · have heq' : (fun r => stoppedProcess B τ r ω) = fun r => B r ω := by
        funext r
        exact stoppedProcess_eq_of_le (by rw [hτtop]; exact le_top)
      rw [heq']
      exact hB
    · let c := (τ ω).untop hτtop
      have hτcoe : (c : WithTop ℝ≥0) = τ ω := WithTop.coe_untop (τ ω) hτtop
      have heq' : (fun r => stoppedProcess B τ r ω) = fun r => B (min r c) ω := by
        funext r
        rw [stoppedProcess, ← hτcoe, ← WithTop.coe_min]
        rfl
      rw [heq']
      exact hB.comp (continuous_id.min continuous_const)
  · have hind : (fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω)
        = fun _ => (0 : ℝ) := by
      funext r
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact continuous_const

/-- The indicator-stopped process of a monotone path is monotone. -/
theorem monotone_indicator_stoppedProcess {B : ℝ≥0 → Ω → ℝ} (ω : Ω)
    (hB : Monotone fun r => B r ω) (τ : Ω → WithTop ℝ≥0) :
    Monotone fun r => stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (B r)) τ r ω := by
  have heq : (fun r => stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (B r)) τ r ω)
      = fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω := by
    funext r
    rw [stoppedProcess_indicator_comm]
  rw [heq]
  by_cases hωτ : ⊥ < τ ω
  · have hind : (fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω)
        = fun r => stoppedProcess B τ r ω := by
      funext r
      rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    by_cases hτtop : τ ω = ⊤
    · have heq' : (fun r => stoppedProcess B τ r ω) = fun r => B r ω := by
        funext r
        exact stoppedProcess_eq_of_le (by rw [hτtop]; exact le_top)
      rw [heq']
      exact hB
    · let c := (τ ω).untop hτtop
      have hτcoe : (c : WithTop ℝ≥0) = τ ω := WithTop.coe_untop (τ ω) hτtop
      have heq' : (fun r => stoppedProcess B τ r ω) = fun r => B (min r c) ω := by
        funext r
        rw [stoppedProcess, ← hτcoe, ← WithTop.coe_min]
        rfl
      rw [heq']
      exact hB.comp fun a b hab => min_le_min hab le_rfl
  · have hind : (fun r => {ω | ⊥ < τ ω}.indicator (stoppedProcess B τ r) ω)
        = fun _ => (0 : ℝ) := by
      funext r
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact monotone_const

/-- The indicator-stopped process of a nonnegative path is nonnegative. -/
theorem indicator_stoppedProcess_nonneg {B : ℝ≥0 → Ω → ℝ} (ω : Ω)
    (hB : ∀ r, 0 ≤ B r ω) (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) :
    0 ≤ stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (B r)) τ r ω := by
  rw [stoppedProcess_indicator_comm]
  exact Set.indicator_nonneg (fun ω' _ => hB _) ω

/-! ## The named inputs at the walk -/

/-- **The bracket LLN in probability at each fixed rescaled time.**  Along every `ε k → 0⁺`
and at every time `t`, the rescaled bracket `εₖ² A(t/εₖ²)` converges to `C t` in probability.
This is the fixed-time shape of `BracketLLNThresholdWiring.thresholdArrayInputs_of_pointwise`'s
`lln` field (which `BracketLLNAlmostSureBridge.tendsto_measure_gt_of_ae_tendsto` produces from
the almost-sure form); the locally uniform form needed by the threshold localisation is
recovered inside `rescaledIncrementCharFunLimit_of_bracket_data` by
`BracketLLNUniform.tendsto_measure_exists_gt_of_tendsto_pointwise`, using monotonicity. -/
def RescaledBracketLLN (P : Measure Ω) (A : ℝ≥0 → Ω → ℝ) (C : ℝ) : Prop :=
  ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
    ∀ (t : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun k => P {ω | δ < |(ε k : ℝ) ^ 2 * A ((ε k)⁻¹ ^ 2 * t) ω - C * (t : ℝ)|})
        atTop (𝓝 0)

/-! ## `hinc` at the walk -/

/-! ## Satisfiability of the two named inputs at the exact-bracket witness -/

/-- The indicator-stopped process agrees with the process strictly before the stopping time. -/
theorem stoppedProcess_indicator_eq_of_lt {N : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    {r : ℝ≥0} {ω : Ω} (h : (r : WithTop ℝ≥0) < τ ω) :
    stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (N r)) τ r ω = N r ω := by
  rw [stoppedProcess_eq_of_le h.le,
    Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from lt_of_le_of_lt bot_le h)]

end ReflectedGMS.ApproximateBracketCLT
