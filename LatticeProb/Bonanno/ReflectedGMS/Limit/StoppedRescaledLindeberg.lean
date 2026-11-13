/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedRescaledLindeberg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RandomBracketLindeberg
import LatticeProb.Bonanno.ReflectedGMS.Limit.ApproximateBracketCLTRescaled

/-!
# `StoppedRescaledLindeberg` from small increments and uniform terminal square tails

`ApproximateBracketCLTRescaled.StoppedRescaledLindeberg P M A η C` (the Lindeberg sums of the
bracket-stopped rescaled projection `N' k` vanish, first `k → ∞` then `n → ∞`) is one of the two
named inputs of `rescaledIncrementCharFunLimit_of_bracket_data`.  This file reduces it, under that
theorem's own structural hypotheses, to two walk-level atoms:

* **(i)** `StoppedRescaledSmallIncrements` — small increments in probability:
  `∀ᶠ k, ∀ᶠ n, P(some increment of N' k along the uniform partition of [s,t] exceeds δ) ≤ γ`;
* **(iii)** `StoppedRescaledTerminalSquareTail` — uniform square tails of the TERMINAL increment:
  `∀ γ > 0, ∃ m, ∀ᶠ k, ∫ ((N' k t - N' k s)² - m)⁺ ≤ γ`.

The intermediate atom **(ii)** `StoppedRescaledQuadraticTail` (uniform tails of the realized
quadratic sums, uniformly in `n`) is proved from (iii) by the generic random-bracket theorem
`RandomBracketLindeberg.exists_uniform_realizedQuadraticSum_tail`
(`stoppedRescaledQuadraticTail_of_terminalSquareTail`), and
`lindebergSum ≤ ∫ (Q_n - λ)⁺ + λ P(big increment)` gives `(i) ∧ (ii) ⟹ StoppedRescaledLindeberg`
(`stoppedRescaledLindeberg_of_smallIncrements_of_quadraticTail`).

## ⚠ (ii) is NOT a generic consequence of a bounded bracket

The predecessor handoff described (ii) as "a theorem about any martingale whose bracket increment
over `[s, t]` is bounded by `K`".  That is false: compensated Poisson martingales
`θ_k (Π_k r - r/θ_k²)` with `θ_k → ∞` have the deterministic bracket `r`, satisfy (i), and violate
both (ii) and the Lindeberg condition (see `RandomBracketLindeberg`).  The honest generic theorem
needs (iii), which is exactly the missing uniform integrability.  (iii) is not an extra
strengthening: given the rest of the setting it is implied by the CLT conclusion itself
(convergence in law + convergence of the second moments `E[A' t - A' s]`), and the tree already
has its producer shape, `ActualArrayLocalizerBounds.uniform_tail_sq_increment_of_threshold_localizers`
(uniform jump bound + bounded bracket).  (i) is also necessary:
`stoppedRescaledSmallIncrements_of_stoppedRescaledLindeberg`.

## Main results

* `stoppedRescaledProjection_bracket_data` — the plumbing of
  `rescaledIncrementCharFunLimit_of_bracket_data` at one scale: the bracket-stopped rescaled
  projection is a square-integrable martingale, its compensated square with the stopped bracket
  is a martingale, and the stopped bracket is monotone with values in `[0, K]`.
* `stoppedRescaledLindeberg_of_smallIncrements_of_quadraticTail` — `(i) ∧ (ii) ⟹ Lindeberg`.
* `stoppedRescaledQuadraticTail_of_terminalSquareTail` — `(iii) ⟹ (ii)`.
* `stoppedRescaledLindeberg_of_smallIncrements_of_terminalSquareTail` — `(i) ∧ (iii) ⟹ Lindeberg`.
* `stoppedRescaledSmallIncrements_of_stoppedRescaledLindeberg` — `Lindeberg ⟹ (i)`; with the checked
  witness `stoppedRescaledLindeberg_of_projectionSquareMartingale` this gives (i) at the
  exact-bracket witness (`stoppedRescaledSmallIncrements_of_projectionSquareMartingale`).
* `rescaledIncrementCharFunLimit_of_bracket_data_of_smallIncrements` — `hinc` at the walk with the
  Lindeberg input replaced by (i) and (iii).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace ReflectedGMS.ApproximateBracketCLT

open ReflectedGMS.MartingaleLimit ReflectedGMS.RescaledFddCharFun
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.BrownianFdd
open ReflectedGMS.StatementIngredients

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The bracket-stopped rescaled objects -/

/-- The rescaled bracket path `r ↦ e² A(r/e²)`. -/
noncomputable def rescaledBracketPath (A : ℝ≥0 → Ω → ℝ) (e : ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ :=
  (e : ℝ) ^ 2 * A (e⁻¹ ^ 2 * r) ω

/-- The rescaled projection `⟪η, e M(·/e²)⟫` stopped (with the project's `{τ > 0}` indicator)
at the first time the rescaled bracket reaches `K`.  This is verbatim the process inside
`StoppedRescaledLindeberg` (`stoppedRescaledLindeberg_iff`). -/
noncomputable def stoppedRescaledProjection (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (A : ℝ≥0 → Ω → ℝ) (η : BouRabeeGwynne.Euc 2) (e : ℝ≥0) (K : ℝ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (fun r => {ω | ⊥ < hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0 ω}.indicator
      (rescaledProjection M e η r))
    (hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0)

/-- The rescaled bracket stopped at the first time it reaches `K`. -/
noncomputable def stoppedRescaledBracket (A : ℝ≥0 → Ω → ℝ) (e : ℝ≥0) (K : ℝ) :
    ℝ≥0 → Ω → ℝ :=
  stoppedProcess (fun r => {ω | ⊥ < hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0 ω}.indicator
      (rescaledBracketPath A e r))
    (hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0)

/-! ## The named atoms -/

/-! ## The plumbing at one scale -/

/-- **The bracket-stopped rescaled projection at one scale.**  Under the structural hypotheses
of `rescaledIncrementCharFunLimit_of_bracket_data` (for one direction `η`), the stopped
rescaled projection is a square-integrable martingale for the rescaled filtration, its
compensated square with the stopped rescaled bracket is a martingale, and the stopped bracket
is monotone with values in `[0, K]`. -/
theorem stoppedRescaledProjection_bracket_data [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (η : BouRabeeGwynne.Euc 2)
    (A : ℝ≥0 → Ω → ℝ)
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hmart : Martingale (fun u ω => ⟪η, M u ω⟫_ℝ) 𝔽 P)
    (hsq : Martingale (fun u ω => ⟪η, M u ω⟫_ℝ ^ 2 - A u ω) 𝔽 P)
    (h2 : ∀ u : ℝ≥0, MemLp (fun ω => ⟪η, M u ω⟫_ℝ) 2 P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun u : ℝ≥0 => ⟪η, M u ω⟫_ℝ)
    (hAc : ∀ᵐ ω ∂P, Continuous fun u : ℝ≥0 => A u ω)
    (hAm : ∀ᵐ ω ∂P, Monotone fun u : ℝ≥0 => A u ω)
    (hA0 : ∀ᵐ ω ∂P, ∀ u, 0 ≤ A u ω) (e : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) :
    Martingale (stoppedRescaledProjection M A η e K) (rescaleFiltration 𝔽 e) P
      ∧ (∀ r, MemLp (stoppedRescaledProjection M A η e K r) 2 P)
      ∧ Martingale (fun r ω => stoppedRescaledProjection M A η e K r ω
            * stoppedRescaledProjection M A η e K r ω - stoppedRescaledBracket A e K r ω)
          (rescaleFiltration 𝔽 e) P
      ∧ (∀ᵐ ω ∂P, Monotone fun r => stoppedRescaledBracket A e K r ω)
      ∧ (∀ᵐ ω ∂P, ∀ r, 0 ≤ stoppedRescaledBracket A e K r ω
          ∧ stoppedRescaledBracket A e K r ω ≤ K) := by
  classical
  have hnull' : ∀ (r : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[rescaleFiltration 𝔽 e r] S :=
    fun r S hS => hnull _ S hS
  -- martingale properties of the rescaled projection
  have hNmart : Martingale (rescaledProjection M e η) (rescaleFiltration 𝔽 e) P := by
    have h1 : Martingale (fun u ω => ⟪η, M (e⁻¹ ^ 2 * u) ω⟫_ℝ) (rescaleFiltration 𝔽 e) P :=
      ⟨fun u => hmart.stronglyAdapted (e⁻¹ ^ 2 * u),
       fun i j hij => hmart.condExp_ae_eq (mul_le_mul_of_nonneg_left hij zero_le)⟩
    have heq : rescaledProjection M e η = (e : ℝ) • (fun u ω => ⟪η, M (e⁻¹ ^ 2 * u) ω⟫_ℝ) := by
      funext u ω
      rw [rescaledProjection_eq]
      rfl
    rw [heq]
    exact h1.smul _
  have hNsq : Martingale (fun r ω => rescaledProjection M e η r ω * rescaledProjection M e η r ω
      - rescaledBracketPath A e r ω) (rescaleFiltration 𝔽 e) P := by
    have h1 : Martingale (fun u ω => ⟪η, M (e⁻¹ ^ 2 * u) ω⟫_ℝ ^ 2 - A (e⁻¹ ^ 2 * u) ω)
        (rescaleFiltration 𝔽 e) P :=
      ⟨fun u => hsq.stronglyAdapted (e⁻¹ ^ 2 * u),
       fun i j hij => hsq.condExp_ae_eq (mul_le_mul_of_nonneg_left hij zero_le)⟩
    have heq : (fun r ω => rescaledProjection M e η r ω * rescaledProjection M e η r ω
        - rescaledBracketPath A e r ω)
        = ((e : ℝ) ^ 2) • (fun u ω => ⟪η, M (e⁻¹ ^ 2 * u) ω⟫_ℝ ^ 2 - A (e⁻¹ ^ 2 * u) ω) := by
      funext u ω
      simp only [rescaledBracketPath, Pi.smul_apply, smul_eq_mul, rescaledProjection_eq]
      ring
    rw [heq]
    exact h1.smul _
  have hN2 : ∀ r, MemLp (rescaledProjection M e η r) 2 P := fun r =>
    MemLp.ae_eq (Eventually.of_forall fun ω => (rescaledProjection_eq M e η r ω).symm)
      ((h2 (e⁻¹ ^ 2 * r)).const_mul (e : ℝ))
  -- adaptedness and path regularity of the rescaled bracket
  have hAad : ∀ u : ℝ≥0, Measurable[𝔽 u] (A u) := by
    intro u
    have h1 : StronglyMeasurable[𝔽 u] (fun ω => ⟪η, M u ω⟫_ℝ ^ 2 - A u ω) :=
      hsq.stronglyMeasurable u
    have h2' : StronglyMeasurable[𝔽 u] (fun ω => ⟪η, M u ω⟫_ℝ ^ 2) :=
      (hmart.stronglyMeasurable u).pow 2
    have heq : A u = fun ω => ⟪η, M u ω⟫_ℝ ^ 2 - (⟪η, M u ω⟫_ℝ ^ 2 - A u ω) := by
      funext ω
      ring
    rw [heq]
    exact (h2'.sub h1).measurable
  have hBad : Adapted (rescaleFiltration 𝔽 e) (rescaledBracketPath A e) := by
    intro r
    exact ((hAad _).stronglyMeasurable.const_mul ((e : ℝ) ^ 2)).measurable
  have hBc : ∀ᵐ ω ∂P, Continuous fun r => rescaledBracketPath A e r ω := by
    filter_upwards [hAc] with ω hω
    exact continuous_const.mul (hω.comp (continuous_const.mul continuous_id))
  have hBm : ∀ᵐ ω ∂P, Monotone fun r => rescaledBracketPath A e r ω := by
    filter_upwards [hAm] with ω hω
    intro a b hab
    exact mul_le_mul_of_nonneg_left (hω (mul_le_mul_of_nonneg_left hab zero_le)) (sq_nonneg _)
  have hB0 : ∀ᵐ ω ∂P, ∀ r, 0 ≤ rescaledBracketPath A e r ω := by
    filter_upwards [hA0] with ω hω
    intro r
    exact mul_nonneg (sq_nonneg _) (hω _)
  have hNrc : ∀ᵐ ω ∂P, IsRightContinuous fun r => rescaledProjection M e η r ω := by
    filter_upwards [hrc] with ω hω
    have hcomp : IsRightContinuous fun r : ℝ≥0 => ⟪η, M (e⁻¹ ^ 2 * r) ω⟫_ℝ := by
      rcases eq_or_ne (e⁻¹ ^ 2) 0 with h0 | h0
      · have heq : (fun r : ℝ≥0 => ⟪η, M (e⁻¹ ^ 2 * r) ω⟫_ℝ) = fun _ => ⟪η, M 0 ω⟫_ℝ := by
          funext r
          rw [h0, zero_mul]
        rw [heq]
        exact IsRightContinuous.const
      · intro r
        have hpos : 0 < e⁻¹ ^ 2 := pos_iff_ne_zero.2 h0
        refine (hω (e⁻¹ ^ 2 * r)).comp
          (f := fun r : ℝ≥0 => e⁻¹ ^ 2 * r) (s := Set.Ioi r)
          (continuous_const.mul continuous_id).continuousWithinAt ?_
        intro r' hr'
        exact mul_lt_mul_of_pos_left hr' hpos
    have heq : (fun r => rescaledProjection M e η r ω)
        = fun r => (e : ℝ) * ⟪η, M (e⁻¹ ^ 2 * r) ω⟫_ℝ :=
      funext fun r => rescaledProjection_eq M e η r ω
    rw [heq]
    exact IsRightContinuous.const.mul hcomp
  have hCrc : ∀ᵐ ω ∂P, IsRightContinuous fun r =>
      rescaledProjection M e η r ω * rescaledProjection M e η r ω - rescaledBracketPath A e r ω := by
    filter_upwards [hNrc, hBc] with ω h1 h2'
    exact (h1.mul h1).sub h2'.isRightContinuous
  -- the threshold stop
  have hτ : IsStoppingTime (rescaleFiltration 𝔽 e)
      (hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0) :=
    isStoppingTime_continuous_diagonal_bracket_hitting hBad hnull' hBc hBm K
  obtain ⟨hN'm, hN'2⟩ :=
    indicator_stoppedProcess_martingale_and_memLp_two hNmart hτ hnull' hNrc hN2
  have hN'sq := indicator_stopped_square_compensated_martingale hNsq hτ hnull' hCrc
  refine ⟨hN'm, hN'2, hN'sq, ?_, ?_⟩
  · filter_upwards [hBm] with ω hω
    exact monotone_indicator_stoppedProcess ω hω _
  · filter_upwards [hBc, hB0] with ω hc h0 r
    refine ⟨indicator_stoppedProcess_nonneg ω h0 _ r, ?_⟩
    by_cases hz : rescaledBracketPath A e 0 ω ≤ K
    · exact (le_abs_self _).trans
        (indicator_stopped_continuous_bracket_abs_le hc hz h0 hK _ le_rfl r)
    · have hτ0 : hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0 ω
          ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) :=
        hittingAfter_le_of_mem le_rfl
          (show rescaledBracketPath A e 0 ω ∈ Set.Ici K from (lt_of_not_ge hz).le)
      have hbot : ((0 : ℝ≥0) : WithTop ℝ≥0) = ⊥ := rfl
      have hnot : ω ∉ {ω | ⊥ < hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0 ω} := by
        intro hmem
        have hlt : (⊥ : WithTop ℝ≥0) < ⊥ := lt_of_lt_of_le hmem (hτ0.trans hbot.le)
        exact lt_irrefl _ hlt
      show stoppedProcess (fun r => {ω | ⊥ < hittingAfter (rescaledBracketPath A e)
          (Set.Ici K) 0 ω}.indicator (rescaledBracketPath A e r))
          (hittingAfter (rescaledBracketPath A e) (Set.Ici K) 0) r ω ≤ K
      rw [stoppedProcess_indicator_comm, Set.indicator_of_notMem hnot]
      exact hK

/-! ## The reductions -/

/-! ## `hinc` at the walk with the Lindeberg input reduced -/

end ReflectedGMS.ApproximateBracketCLT
