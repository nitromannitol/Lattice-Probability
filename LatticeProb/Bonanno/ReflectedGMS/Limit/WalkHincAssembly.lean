/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.WalkHincAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WalkLindeberg
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayCLTLocal
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketTimeAverage
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedArrayProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledFddCharFunReduction

/-!
# `hinc` at the actual walk through the LOCAL CLT lane

`RescaledFddCharFunReduction.rescaledFddCharFunLimits_of_increment_limits` (:207) takes
`hinc : RescaledIncrementCharFunLimit P 𝔽 M target`.  At the walk `M` is only a LOCAL martingale,
so the global consumer `ApproximateBracketCLT.rescaledIncrementCharFunLimit_of_bracket_data`
(true-martingale `hmart`) does not apply.  This module assembles the local route end to end,
through `ApproximateBracketCLT.rescaledIncrementCharFunLimit_of_localizedBracketArrays`.

* `rescaledIncrementCharFunLimit_of_local_bracket_data` — the abstract local theorem.  For each
  scale sequence, direction `η` and `s ≤ t`: the common square localizer `ρ` of `⟪η, M⟫`
  (`CommonSquareLocalizer.exists_common_square_localizer`), the diagonal index `j k` at the
  parabolic horizons `εₖ⁻² t` (`DiagonalLocalizer.exists_diagonal_localizer_index_rescaled`),
  the per-scale plumbing of the localized path `localizedPath M (ρ (j k))`
  (`StoppedRescaledLindeberg.stoppedRescaledProjection_bracket_data`), the bracket threshold
  (`UCPBracketLocalization.exists_threshold_bracket_localization_of_ucp`, fed by the bracket LLN
  and the diagonal exit), and the Lindeberg field
  (`WalkLindebergRows.lindeberg_of_rescaledStopRows`, rows = localize, rescale, then stop at the
  bracket threshold — the doubly-stopped rows).  CONDITIONAL on its binders: the local bracket
  data, the bracket LLN, and the three path properties of `M` (càdlàg, small jumps from bounded
  regions, rescaled compact containment).
* `rescaledIncrementCharFunLimit_walk` — **`hinc` at the actual walk**, on the completed sample
  space with the completed area filtration.  Beyond the consumer context (`hclock`, `hz`,
  `hsub`, `hdiam`, all held by the walk consumers), its hypotheses are exactly
  `hbr : CanonicalBracket …` (bracket lane) and the directional bracket LLN `hdir` (regeneration
  lane; verbatim the conclusion of
  `RescaledBracketLLNBridgeDisintegrated.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_disintegrated_target`
  at a fixed environment).

The localizer is taken in the ORIGINAL time and then rescaled, rather than rescaled first
(`ActualThresholdArrayCLTLocal.exists_rescaled_diagonal_localizer`/`tendsto_disagreement_of_two_stops`):
the rescaled-first form needs `∀ k, 0 < ε k`, which the consumer's `ε → 0⁺` does not supply
(finitely many `ε k` may vanish).  In original time every step holds at every scale, `ε k = 0`
included, and the only case split is the row transfer `isRescaledStopRow_of_localizedPath`.

New helper facts about the walk's bracket: `dirBracket_ordinaryEdgeBracket_monotone` (the
directional bracket is monotone, from the nonnegative directional density under `Geometry`) and
`dirBracket_ordinaryEdgeBracket_zero`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.WalkHincAssembly

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement MartingaleIngredients
open ReflectedWalk QuenchedFormulation ProcessFiltration
open ReflectedGMS.MartingaleLimit ReflectedGMS.ApproximateBracketCLT
open ReflectedGMS.RescaledFddCharFun ReflectedGMS.GaussianLimitIdentification
open ReflectedGMS.WalkLindeberg ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.InvarianceAssembly ReflectedGMS.DirectionalNondegeneracy

/-! ## Localized paths -/

section Localized

variable {Ω : Type*}

/-- A path localized at a random time `ρ` with the project's exact `{ρ > 0}` indicator — the
shape of every stopped process of `CommonSquareLocalizer.exists_common_square_localizer`. -/
noncomputable def localizedPath {E : Type*} [Zero E] (N : ℝ≥0 → Ω → E)
    (ρ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → E :=
  stoppedProcess (fun u => {ω | ⊥ < ρ ω}.indicator (N u)) ρ

/-- Projections commute with localization. -/
theorem inner_localizedPath (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (ρ : Ω → WithTop ℝ≥0)
    (η : BouRabeeGwynne.Euc 2) (u : ℝ≥0) (ω : Ω) :
    ⟪η, localizedPath M ρ u ω⟫_ℝ = localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) ρ u ω := by
  show ⟪η, {ω | ⊥ < ρ ω}.indicator (M (min (u : WithTop ℝ≥0) (ρ ω)).untopA) ω⟫_ℝ =
    {ω | ⊥ < ρ ω}.indicator (fun ω => ⟪η, M (min (u : WithTop ℝ≥0) (ρ ω)).untopA ω⟫_ℝ) ω
  by_cases h : ω ∈ {ω | ⊥ < ρ ω}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, inner_zero_right]

/-- A localized path agrees with the path strictly before the localizing time. -/
theorem localizedPath_eq_of_lt {E : Type*} [Zero E] (N : ℝ≥0 → Ω → E) (ρ : Ω → WithTop ℝ≥0)
    {u : ℝ≥0} {ω : Ω} (h : (u : WithTop ℝ≥0) < ρ ω) : localizedPath N ρ u ω = N u ω := by
  show stoppedProcess (fun u => {ω | ⊥ < ρ ω}.indicator (N u)) ρ u ω = N u ω
  rw [stoppedProcess_eq_of_le h.le,
    Set.indicator_of_mem (show ω ∈ {ω | ⊥ < ρ ω} from lt_of_le_of_lt bot_le h)]

/-- **A rescaled stopped row of the localized path is a rescaled stopped row of the path.**
Localizing at `ρ` in the original time is, after the diffusive rescaling by `e ≠ 0`, the time map
`r ↦ e² (e⁻² r ∧ ρ)` (still `1`-Lipschitz and below the identity) and the `{ρ > 0}` factor goes
into the constant.  At `e = 0` both sides vanish. -/
theorem isRescaledStopRow_of_localizedPath {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} {η : BouRabeeGwynne.Euc 2} {e : ℝ≥0}
    {ρ : Ω → WithTop ℝ≥0} {N : ℝ≥0 → Ω → ℝ}
    (h : IsRescaledStopRow P (localizedPath M ρ) η e N) : IsRescaledStopRow P M η e N := by
  filter_upwards [h] with ω ⟨a, ha, g, hg, hgL, hN⟩
  classical
  rcases eq_or_ne e 0 with he | he
  · refine ⟨a, ha, g, hg, hgL, fun r => ?_⟩
    rw [hN r, he]
    simp
  · have hc : e⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero he)
    have hcpos : (0 : ℝ) < ((e⁻¹ ^ 2 : ℝ≥0) : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.2 hc
    refine ⟨{ω | ⊥ < ρ ω}.indicator (fun _ => a) ω, ?_,
      fun r => (e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r), fun r => ?_, fun r r' => ?_,
      fun r => ?_⟩
    · by_cases hω : ω ∈ {ω | ⊥ < ρ ω}
      · rw [Set.indicator_of_mem hω]
        exact ha
      · rw [Set.indicator_of_notMem hω]
        simp
    · show (e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r) ≤ r
      calc (e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r)
          ≤ (e⁻¹ ^ 2)⁻¹ * (e⁻¹ ^ 2 * g r) :=
            mul_le_mul_of_nonneg_left (stopTime_le _ _) zero_le
        _ = g r := inv_mul_cancel_left₀ hc (g r)
        _ ≤ r := hg r
    · show dist ((e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r))
          ((e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r')) ≤ dist r r'
      have h1 := dist_stopTime_le (ρ ω) (e⁻¹ ^ 2 * g r) (e⁻¹ ^ 2 * g r')
      have h2 := hgL r r'
      simp only [NNReal.dist_eq] at h1 h2 ⊢
      rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_sub, abs_mul,
        abs_of_nonneg hcpos.le] at h1
      rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_sub, abs_mul, NNReal.coe_inv,
        abs_of_nonneg (inv_nonneg.2 hcpos.le)]
      calc ((e⁻¹ ^ 2 : ℝ≥0) : ℝ)⁻¹ *
            |((stopTime (ρ ω) (e⁻¹ ^ 2 * g r) : ℝ≥0) : ℝ) -
              ((stopTime (ρ ω) (e⁻¹ ^ 2 * g r') : ℝ≥0) : ℝ)|
          ≤ ((e⁻¹ ^ 2 : ℝ≥0) : ℝ)⁻¹ *
            (((e⁻¹ ^ 2 : ℝ≥0) : ℝ) * |((g r : ℝ≥0) : ℝ) - ((g r' : ℝ≥0) : ℝ)|) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hcpos.le)
        _ = |((g r : ℝ≥0) : ℝ) - ((g r' : ℝ≥0) : ℝ)| := inv_mul_cancel_left₀ hcpos.ne' _
        _ ≤ |(r : ℝ) - (r' : ℝ)| := h2
    · show N r ω = {ω | ⊥ < ρ ω}.indicator (fun _ => a) ω * ((e : ℝ) *
          ⟪η, M (e⁻¹ ^ 2 * ((e⁻¹ ^ 2)⁻¹ * stopTime (ρ ω) (e⁻¹ ^ 2 * g r))) ω⟫_ℝ)
      rw [mul_inv_cancel_left₀ hc, hN r]
      show a * ((e : ℝ) * ⟪η, {ω | ⊥ < ρ ω}.indicator
          (M (stopTime (ρ ω) (e⁻¹ ^ 2 * g r))) ω⟫_ℝ) = _
      by_cases hω : ω ∈ {ω | ⊥ < ρ ω}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, inner_zero_right]
        ring

/-- The same, with the localized path named by an equation. -/
theorem isRescaledStopRow_of_eq_localizedPath {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {M M' : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} {η : BouRabeeGwynne.Euc 2} {e : ℝ≥0}
    {ρ : Ω → WithTop ℝ≥0} {N : ℝ≥0 → Ω → ℝ} (hM' : M' = localizedPath M ρ)
    (h : IsRescaledStopRow P M' η e N) : IsRescaledStopRow P M η e N := by
  subst hM'
  exact isRescaledStopRow_of_localizedPath h

end Localized

/-! ## The directional bracket of the walk is monotone -/

section DirectionalBracket

/-- The directional bracket is the time integral of the directional density. -/
theorem dirBracket_ordinaryEdgeBracket_eq_integral {Ω V : Type*} (cells : IndexedCells V)
    (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) (ω : Ω) (η : EuclideanSpace ℝ (Fin 2))
    (t : ℝ≥0)
    (hint : ∀ i j : Fin 2, IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X s.toNNReal ω) i j) volume 0 (t : ℝ)) :
    dirBracket (ordinaryEdgeBracket cells Φ X) η t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), BracketTimeAverage.dirForm
        (stateBracketDensity cells Φ (X s.toNNReal ω)) (fun k => η k) := by
  have h := BracketTimeAverage.dirForm_ordinaryEdgeBracket cells Φ X ω (fun k => η k)
    t.coe_nonneg hint
  rw [Real.toNNReal_coe] at h
  exact h

/-- The directional bracket vanishes at time zero. -/
theorem dirBracket_ordinaryEdgeBracket_zero {Ω V : Type*} (cells : IndexedCells V)
    (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) (ω : Ω) (η : EuclideanSpace ℝ (Fin 2)) :
    dirBracket (ordinaryEdgeBracket cells Φ X) η 0 ω = 0 := by
  simp [dirBracket, ordinaryEdgeBracket]

/-- **The directional bracket of the walk is monotone** along every path on which the bracket
densities are locally interval integrable (the second clause of `HasOrdinaryEdgeBracket`): the
directional density `ηᵀ Γ η` is nonnegative at every state under `Geometry`
(`BracketTimeAverage.dirForm_stateBracketDensity_nonneg`). -/
theorem dirBracket_ordinaryEdgeBracket_monotone {Ω V : Type*} [Countable V]
    (cells : IndexedCells V) (hcells : Geometry cells) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) (η : EuclideanSpace ℝ (Fin 2))
    (hint : ∀ (i j : Fin 2) (t : ℝ≥0), IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X s.toNNReal ω) i j) volume 0 (t : ℝ)) :
    Monotone fun t => dirBracket (ordinaryEdgeBracket cells Φ X) η t ω := by
  have hI : ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ =>
      BracketTimeAverage.dirForm (stateBracketDensity cells Φ (X s.toNNReal ω)) (fun k => η k))
      volume 0 (t : ℝ) := by
    intro t
    have h : IntervalIntegrable (∑ p : Fin 2 × Fin 2, fun s : ℝ =>
        η p.1 * stateBracketDensity cells Φ (X s.toNNReal ω) p.1 p.2 * η p.2) volume 0 (t : ℝ) :=
      IntervalIntegrable.sum _ fun p _ => ((hint p.1 p.2 t).const_mul (η p.1)).mul_const (η p.2)
    convert h using 1
    funext s
    rw [BracketTimeAverage.dirForm_eq_prodSum, Finset.sum_apply]
  intro a b hab
  show dirBracket (ordinaryEdgeBracket cells Φ X) η a ω ≤
    dirBracket (ordinaryEdgeBracket cells Φ X) η b ω
  rw [dirBracket_ordinaryEdgeBracket_eq_integral cells Φ X ω η b (fun i j => hint i j b),
    dirBracket_ordinaryEdgeBracket_eq_integral cells Φ X ω η a (fun i j => hint i j a)]
  have hsub := intervalIntegral.integral_interval_sub_left (hI b) (hI a)
  have hnn : 0 ≤ ∫ s in (a : ℝ)..(b : ℝ),
      BracketTimeAverage.dirForm (stateBracketDensity cells Φ (X s.toNNReal ω))
        (fun k => η k) :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hab)
      fun u _ => BracketTimeAverage.dirForm_stateBracketDensity_nonneg cells hcells Φ _ _
  linarith

end DirectionalBracket

/-! ## The abstract local theorem -/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`hinc` from LOCAL bracket data, the bracket LLN and the path properties of `M`.**

CONDITIONAL on: every projection `⟪η, M⟫` is a locally square-integrable martingale (`hloc`)
whose compensated square with `A η` is a local martingale (`hsq`); `A η` has continuous,
monotone, nonnegative paths; the rescaled brackets satisfy the LLN with slope `ηᵀΣη`; `M` is
càdlàg with small jumps from bounded regions and rescaled compact containment; the filtration
contains the null events.  No true-martingale hypothesis. -/
theorem rescaledIncrementCharFunLimit_of_local_bracket_data [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (target : AnisotropicBrownianTarget)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (A : BouRabeeGwynne.Euc 2 → ℝ≥0 → Ω → ℝ)
    (hloc : ∀ η, MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽
      (fun u ω => ⟪η, M u ω⟫_ℝ))
    (hsq : ∀ η, MartingaleIngredients.IsLocalMartingale P 𝔽
      (fun u ω => ⟪η, M u ω⟫_ℝ ^ 2 - A η u ω))
    (hAc : ∀ η, ∀ᵐ ω ∂P, Continuous fun u : ℝ≥0 => A η u ω)
    (hAm : ∀ η, ∀ᵐ ω ∂P, Monotone fun u : ℝ≥0 => A η u ω)
    (hA0 : ∀ η, ∀ᵐ ω ∂P, ∀ u, 0 ≤ A η u ω)
    (hLLN : ∀ η, RescaledBracketLLN P (A η) (bilinForm target.covariance η η))
    (hcad : ∀ᵐ ω ∂P, IsCadlag fun r => M r ω)
    (hjump : SmallJumpsFromBoundedRegion P M) (hcont : RescaledCompactContainment P M) :
    RescaledIncrementCharFunLimit P 𝔽 M target := by
  classical
  refine rescaledIncrementCharFunLimit_of_localizedBracketArrays 𝔽 M hadapt target ?_
  intro ε hε η s t hst
  set C : ℝ := bilinForm target.covariance η η with hCdef
  have hC0 : 0 ≤ C := bilinForm_self_nonneg target η
  have hrc : ∀ᵐ ω ∂P, IsRightContinuous fun u : ℝ≥0 => ⟪η, M u ω⟫_ℝ :=
    hcad.mono fun ω h =>
      (h.continuous_comp (continuous_const.inner continuous_id)).isRightContinuous
  -- the common square localizer, in the original time
  have hsq' : MartingaleIngredients.IsLocalMartingale P 𝔽
      (fun u ω => ⟪η, M u ω⟫_ℝ * ⟪η, M u ω⟫_ℝ - A η u ω) := by
    have heq : (fun u ω => ⟪η, M u ω⟫_ℝ * ⟪η, M u ω⟫_ℝ - A η u ω) =
        fun u ω => ⟪η, M u ω⟫_ℝ ^ 2 - A η u ω := by
      funext u ω
      ring
    rw [heq]
    exact hsq η
  obtain ⟨ρ, hρ, hρdata⟩ := exists_common_square_localizer
    (M := fun u ω => ⟪η, M u ω⟫_ℝ) (B := A η) (hloc η) hsq' hnull hrc
    ((hAc η).mono fun ω h => h.isRightContinuous)
  -- the diagonal localizer index at the parabolic horizons
  obtain ⟨j, -, hjexit⟩ := exists_diagonal_localizer_index_rescaled hρ ε t
  -- the localized paths
  obtain ⟨Mk, hMk⟩ : ∃ Mk : ℕ → ℝ≥0 → Ω → BouRabeeGwynne.Euc 2,
      Mk = fun k => localizedPath M (ρ (j k)) := ⟨_, rfl⟩
  obtain ⟨Ak, hAk⟩ : ∃ Ak : ℕ → ℝ≥0 → Ω → ℝ,
      Ak = fun k => localizedPath (A η) (ρ (j k)) := ⟨_, rfl⟩
  have hinner : ∀ k (u : ℝ≥0) (ω : Ω), ⟪η, Mk k u ω⟫_ℝ =
      localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) u ω := by
    intro k u ω
    rw [hMk]
    exact inner_localizedPath M (ρ (j k)) η u ω
  have hagreeM : ∀ k (ω : Ω) (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ (j k) ω → Mk k u ω = M u ω := by
    intro k ω u hu
    rw [hMk]
    exact localizedPath_eq_of_lt M (ρ (j k)) hu
  have hagreeA : ∀ k (ω : Ω) (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ (j k) ω →
      Ak k u ω = A η u ω := by
    intro k ω u hu
    rw [hAk]
    exact localizedPath_eq_of_lt (A η) (ρ (j k)) hu
  -- the localized projections are true square-integrable martingales
  have hdataρ : ∀ k,
      Martingale (fun u ω => ⟪η, Mk k u ω⟫_ℝ) 𝔽 P ∧
      (∀ u, MemLp (fun ω => ⟪η, Mk k u ω⟫_ℝ) 2 P) ∧
      Martingale (fun u ω => ⟪η, Mk k u ω⟫_ℝ ^ 2 - Ak k u ω) 𝔽 P := by
    intro k
    have hd := hρdata (j k)
    dsimp only at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have hfun : (fun u ω => ⟪η, Mk k u ω⟫_ℝ) =
        localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) :=
      funext fun u => funext fun ω => hinner k u ω
    refine ⟨?_, fun u => ?_, ?_⟩
    · rw [hfun]
      exact h1
    · have hu : (fun ω => ⟪η, Mk k u ω⟫_ℝ) =
          localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) u :=
        funext fun ω => hinner k u ω
      rw [hu]
      exact h2 u
    · have heq : (fun u ω => ⟪η, Mk k u ω⟫_ℝ ^ 2 - Ak k u ω) = fun u ω =>
          localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) u ω *
            localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) u ω -
          localizedPath (A η) (ρ (j k)) u ω := by
        funext u ω
        rw [hinner k u ω, hAk, sq]
      rw [heq]
      exact h3
  have hrck : ∀ k, ∀ᵐ ω ∂P, IsRightContinuous fun u : ℝ≥0 => ⟪η, Mk k u ω⟫_ℝ := by
    intro k
    filter_upwards [hrc] with ω hω
    have heq : (fun u : ℝ≥0 => ⟪η, Mk k u ω⟫_ℝ) =
        fun u => localizedPath (fun u ω => ⟪η, M u ω⟫_ℝ) (ρ (j k)) u ω :=
      funext fun u => hinner k u ω
    rw [heq]
    exact LocalizedArrayProducer.isRightContinuous_indicator_stoppedProcess
      (N := fun u ω => ⟪η, M u ω⟫_ℝ) ω hω (ρ (j k))
  have hAck : ∀ k, ∀ᵐ ω ∂P, Continuous fun u : ℝ≥0 => Ak k u ω := by
    intro k
    filter_upwards [hAc η] with ω hω
    rw [hAk]
    exact continuous_indicator_stoppedProcess ω hω (ρ (j k))
  have hAmk : ∀ k, ∀ᵐ ω ∂P, Monotone fun u : ℝ≥0 => Ak k u ω := by
    intro k
    filter_upwards [hAm η] with ω hω
    rw [hAk]
    exact monotone_indicator_stoppedProcess ω hω (ρ (j k))
  have hA0k : ∀ k, ∀ᵐ ω ∂P, ∀ u, 0 ≤ Ak k u ω := by
    intro k
    filter_upwards [hA0 η] with ω hω u
    rw [hAk]
    exact indicator_stoppedProcess_nonneg ω hω (ρ (j k)) u
  -- the level and the per-scale plumbing
  set K : ℝ := C * (t : ℝ) + 1 with hKdef
  have hKT : C * (t : ℝ) < K := by
    simp only [hKdef]
    linarith
  have hK0 : 0 ≤ K := by
    have := mul_nonneg hC0 t.coe_nonneg
    simp only [hKdef]
    linarith
  have hdata := fun k => stoppedRescaledProjection_bracket_data 𝔽 (Mk k) η (Ak k) hnull
    (hdataρ k).1 (hdataρ k).2.2 (hdataρ k).2.1 (hrck k) (hAck k) (hAmk k) (hA0k k) (ε k) hK0
  have hrc' := fun k => ae_rightContinuous_stoppedRescaledProjection (P := P) (Mk k) (Ak k) η
    (ε k) K (hrck k) (hAck k)
  -- the rescaled localized brackets
  have hAkad : ∀ k (u : ℝ≥0), Measurable[𝔽 u] (Ak k u) := by
    intro k u
    have h1 : StronglyMeasurable[𝔽 u] (fun ω => ⟪η, Mk k u ω⟫_ℝ ^ 2 - Ak k u ω) :=
      (hdataρ k).2.2.stronglyMeasurable u
    have h2' : StronglyMeasurable[𝔽 u] (fun ω => ⟪η, Mk k u ω⟫_ℝ ^ 2) :=
      ((hdataρ k).1.stronglyMeasurable u).pow 2
    have heq : Ak k u = fun ω => ⟪η, Mk k u ω⟫_ℝ ^ 2 - (⟪η, Mk k u ω⟫_ℝ ^ 2 - Ak k u ω) := by
      funext ω
      ring
    rw [heq]
    exact (h2'.sub h1).measurable
  have hBad : ∀ k, Adapted (rescaleFiltration 𝔽 (ε k)) (rescaledBracketPath (Ak k) (ε k)) := by
    intro k r
    exact ((hAkad k _).stronglyMeasurable.const_mul ((ε k : ℝ) ^ 2)).measurable
  have hBc : ∀ k, ∀ᵐ ω ∂P, Continuous fun r => rescaledBracketPath (Ak k) (ε k) r ω := by
    intro k
    filter_upwards [hAck k] with ω hω
    exact continuous_const.mul (hω.comp (continuous_const.mul continuous_id))
  have hBm : ∀ k, ∀ᵐ ω ∂P, Monotone fun r => rescaledBracketPath (Ak k) (ε k) r ω := by
    intro k
    filter_upwards [hAmk k] with ω hω
    intro a b hab
    exact mul_le_mul_of_nonneg_left (hω (mul_le_mul_of_nonneg_left hab zero_le)) (sq_nonneg _)
  have hB0 : ∀ k, ∀ᵐ ω ∂P, ∀ r, 0 ≤ rescaledBracketPath (Ak k) (ε k) r ω := by
    intro k
    filter_upwards [hA0k k] with ω hω r
    exact mul_nonneg (sq_nonneg _) (hω _)
  -- the bracket LLN of the localized brackets: union bound with the diagonal exit
  have hpt : ∀ r : ℝ≥0, r ≤ t → ∀ δ : ℝ, 0 < δ → Tendsto (fun k =>
      P {ω | δ < |rescaledBracketPath (Ak k) (ε k) r ω - C * (r : ℝ)|}) atTop (𝓝 0) := by
    intro r hr δ hδ
    have hsum := (hLLN η ε hε r δ hδ).add hjexit
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun k => ?_)
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    rw [Set.mem_union]
    by_cases hρω : ρ (j k) ω ≤ (((ε k)⁻¹ ^ 2 * t : ℝ≥0) : WithTop ℝ≥0)
    · exact Or.inr hρω
    · refine Or.inl ?_
      have hlt : (((ε k)⁻¹ ^ 2 * r : ℝ≥0) : WithTop ℝ≥0) < ρ (j k) ω :=
        lt_of_le_of_lt (WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left hr zero_le))
          (not_le.1 hρω)
      have hω' : δ < |rescaledBracketPath (Ak k) (ε k) r ω - C * (r : ℝ)| := hω
      rw [rescaledBracketPath, hagreeA k ω _ hlt] at hω'
      exact hω'
  have hucp : ∀ δ : ℝ, 0 < δ → Tendsto (fun k => P {ω | ∃ r ∈ Set.Icc (0 : ℝ≥0) t,
      δ < |rescaledBracketPath (Ak k) (ε k) r ω - C * (r : ℝ)|}) atTop (𝓝 0) :=
    fun δ hδ => BracketLLNUniform.tendsto_measure_exists_gt_of_tendsto_pointwise hC0 hBm hpt hδ
  -- the bracket threshold
  obtain ⟨τ, hτdef, -, hexit, -, R, hRint, hRerr, hRlim⟩ :=
    exists_threshold_bracket_localization_of_ucp (P := P)
      (F := fun k => rescaleFiltration 𝔽 (ε k))
      (B := fun k => rescaledBracketPath (Ak k) (ε k)) t hC0 hKT hBad
      (fun k r S hS => hnull _ S hS) hBc hBm hB0 hucp
  have hτeq : τ = fun k => hittingAfter (rescaledBracketPath (Ak k) (ε k)) (Set.Ici K) 0 :=
    funext hτdef
  subst hτeq
  have hRerr' : ∀ k, ∀ᵐ ω ∂P, ∀ r ≤ t,
      |stoppedRescaledBracket (Ak k) (ε k) K r ω - C * (r : ℝ)| ≤ R k ω := hRerr
  have hexit' : Tendsto (fun k => P {ω |
      hittingAfter (rescaledBracketPath (Ak k) (ε k)) (Set.Ici K) 0 ω ≤ (t : WithTop ℝ≥0)})
      atTop (𝓝 0) := hexit
  -- the rows: localize (original time), rescale, stop at the bracket threshold
  have hrow : ∀ k, IsRescaledStopRow P M η (ε k)
      (stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K) := fun k =>
    isRescaledStopRow_of_eq_localizedPath (congrFun hMk k)
      (isRescaledStopRow_stoppedRescaledProjection P (Mk k) (Ak k) η (ε k) K)
  refine ⟨fun k => stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K,
    fun k => stoppedRescaledBracket (Ak k) (ε k) K, K, hK0, ?_, ?_⟩
  · show LocalizedBracketArray P (fun k => rescaleFiltration 𝔽 (ε k))
      (fun k => stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K)
      (fun k => stoppedRescaledBracket (Ak k) (ε k) K) s t C K
    refine LocalizedBracketArray.of_square_martingale hst (fun k => (hdata k).1) (fun k => ?_)
      (fun k => (hdata k).2.1) (fun k => ?_) (fun k => ?_) (fun k => ?_) ?_ ?_
    · have heq : (fun v ω => stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K v ω ^ 2 -
            stoppedRescaledBracket (Ak k) (ε k) K v ω) = fun v ω =>
            stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K v ω *
              stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K v ω -
            stoppedRescaledBracket (Ak k) (ε k) K v ω := by
        funext v ω
        ring
      rw [heq]
      exact (hdata k).2.2.1
    · filter_upwards [hBc k] with ω hω
      exact (continuous_indicator_stoppedProcess ω hω _).continuousOn
    · filter_upwards [(hdata k).2.2.2.1] with ω hω
      exact hω.monotoneOn _
    · filter_upwards [(hdata k).2.2.2.2] with ω hω
      linarith [(hω t).2, (hω s).1]
    · exact lindeberg_of_rescaledStopRows 𝔽 η hadapt hnull hcad hjump hcont hε hrow
        (fun k => (hdata k).1) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.1)
        (fun k => (hrc' k).1) (fun k => (hrc' k).2) (fun k => (hdata k).2.2.2.1) hK0
        (fun k => (hdata k).2.2.2.2) hst
    · -- the bracket limit in probability, from the integrable envelope
      rw [tendstoInMeasure_iff_measureReal_norm]
      intro ϱ hϱ
      have hR0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ R k ω := by
        intro k
        filter_upwards [hRerr' k] with ω hω
        exact (abs_nonneg _).trans (hω t le_rfl)
      have hsub : ∀ k, ∀ᵐ ω ∂P, ϱ ≤ ‖stoppedRescaledBracket (Ak k) (ε k) K t ω -
          stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))‖ →
          ϱ ≤ 2 * R k ω := by
        intro k
        filter_upwards [hRerr' k] with ω hω hϱω
        have h1 := hω t le_rfl
        have h2' := hω s hst
        rw [Real.norm_eq_abs] at hϱω
        have h3 : |stoppedRescaledBracket (Ak k) (ε k) K t ω -
            stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))|
            ≤ |stoppedRescaledBracket (Ak k) (ε k) K t ω - C * (t : ℝ)| +
              |stoppedRescaledBracket (Ak k) (ε k) K s ω - C * (s : ℝ)| := by
          rw [show stoppedRescaledBracket (Ak k) (ε k) K t ω -
              stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))
            = (stoppedRescaledBracket (Ak k) (ε k) K t ω - C * (t : ℝ)) -
              (stoppedRescaledBracket (Ak k) (ε k) K s ω - C * (s : ℝ)) by ring]
          exact abs_sub _ _
        linarith
      have hmarkov : ∀ k, P.real {ω | ϱ ≤ ‖stoppedRescaledBracket (Ak k) (ε k) K t ω -
          stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))‖}
          ≤ (2 / ϱ) * ∫ ω, R k ω ∂P := by
        intro k
        have hle : P.real {ω | ϱ ≤ ‖stoppedRescaledBracket (Ak k) (ε k) K t ω -
            stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))‖}
            ≤ P.real {ω | ϱ ≤ 2 * R k ω} := by
          simp only [measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hsub k))
        have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => 2 * R k ω)
          ((hR0 k).mono fun ω hω => by simpa using hω) ((hRint k).const_mul 2) ϱ
        rw [integral_const_mul] at hmk
        calc P.real {ω | ϱ ≤ ‖stoppedRescaledBracket (Ak k) (ε k) K t ω -
              stoppedRescaledBracket (Ak k) (ε k) K s ω - C * ((t : ℝ) - (s : ℝ))‖}
            ≤ P.real {ω | ϱ ≤ 2 * R k ω} := hle
          _ ≤ (2 / ϱ) * ∫ ω, R k ω ∂P := by
              rw [div_mul_eq_mul_div, le_div_iff₀ hϱ]
              linarith
      refine squeeze_zero (fun k => measureReal_nonneg) hmarkov ?_
      simpa using hRlim.const_mul (2 / ϱ)
  · -- the disagreement: union of the threshold exit and the diagonal exit
    have hsubset : ∀ k, {ω | ¬ (stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K t ω =
          rescaledProjection M (ε k) η t ω ∧
        stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K s ω =
          rescaledProjection M (ε k) η s ω)} ⊆
        {ω | hittingAfter (rescaledBracketPath (Ak k) (ε k)) (Set.Ici K) 0 ω ≤
          (t : WithTop ℝ≥0)} ∪
        {ω | ρ (j k) ω ≤ (((ε k)⁻¹ ^ 2 * t : ℝ≥0) : WithTop ℝ≥0)} := by
      intro k ω hω
      by_contra hno
      rw [Set.mem_union, not_or] at hno
      have hτlt : (t : WithTop ℝ≥0) <
          hittingAfter (rescaledBracketPath (Ak k) (ε k)) (Set.Ici K) 0 ω := not_le.1 hno.1
      have hρlt : (((ε k)⁻¹ ^ 2 * t : ℝ≥0) : WithTop ℝ≥0) < ρ (j k) ω := not_le.1 hno.2
      apply hω
      have key : ∀ r : ℝ≥0, r ≤ t → stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K r ω =
          rescaledProjection M (ε k) η r ω := by
        intro r hr
        have hrτ : (r : WithTop ℝ≥0) <
            hittingAfter (rescaledBracketPath (Ak k) (ε k)) (Set.Ici K) 0 ω :=
          lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) hτlt
        have hrρ : (((ε k)⁻¹ ^ 2 * r : ℝ≥0) : WithTop ℝ≥0) < ρ (j k) ω :=
          lt_of_le_of_lt (WithTop.coe_le_coe.2 (mul_le_mul_of_nonneg_left hr zero_le)) hρlt
        rw [stoppedRescaledProjection, stoppedProcess_indicator_eq_of_lt hrτ,
          rescaledProjection_eq, rescaledProjection_eq, hagreeM k ω _ hrρ]
      exact ⟨key t le_rfl, key s hst⟩
    have hsum := hexit'.add hjexit
    rw [add_zero] at hsum
    have hENN : Tendsto (fun k => P {ω | ¬ (stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K
          t ω = rescaledProjection M (ε k) η t ω ∧
        stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K s ω =
          rescaledProjection M (ε k) η s ω)}) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
        fun k => (measure_mono (hsubset k)).trans (measure_union_le _ _)
    show Tendsto (fun k => P.real {ω | ¬ (stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K
          t ω = rescaledProjection M (ε k) η t ω ∧
        stoppedRescaledProjection (Mk k) (Ak k) η (ε k) K s ω =
          rescaledProjection M (ε k) η s ω)}) atTop (𝓝 0)
    simp only [measureReal_def]
    exact (ENNReal.tendsto_toReal_zero_iff (fun k => measure_ne_top P _)).mpr hENN

end Generic

/-! ## `hinc` at the actual walk -/

/-- **`hinc` at the actual walk, through the local CLT lane.**  On the completed sample space
with the completed area filtration (where `CanonicalBracket` lives), the rescaled increments of
the walk's harmonic-coordinate path `M` satisfy `RescaledIncrementCharFunLimit`.

Hypotheses beyond the consumer context (`hclock`, `hz`, `hsub`, `hdiam`): exactly
* `hbr : CanonicalBracket …` — the bracket lane (the invariance assembly's `hbracket`);
* `hdir` — the directional bracket LLN on `areaSampleLaw`, the regeneration lane's output shape.

Everything else is read off `hbr` (adaptedness, null events, local martingale projections,
continuity of the bracket) or proved here (monotonicity and nonnegativity of the directional
bracket), and the three path properties of `M` come from `WalkLindeberg.walkLindebergInputs_completion`. -/
theorem rescaledIncrementCharFunLimit_walk (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (target : AnisotropicBrownianTarget)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (bilinForm target.covariance η η)) :
    RescaledIncrementCharFunLimit
      (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
        (areaSampleLaw (decode e) D hG start))
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M target := by
  have : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
    BracketClausesScalarReduction.isProbabilityMeasure_areaSampleLaw e D hG start
  have : IsProbabilityMeasure (areaSampleLaw (decode e) D hG start).completion :=
    ⟨(Measure.completion_apply _ Set.univ).trans measure_univ⟩
  have hLLNdiag : ∀ k : Fin 2, RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
      (ordinaryEdgeBracket (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) k k)
      (bilinForm target.covariance (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)) := by
    intro k
    have h := hdir (EuclideanSpace.single k 1)
    rwa [ActualThresholdArray.dirBracket_single] at h
  obtain ⟨hcad, hjump, hcont⟩ := walkLindebergInputs_completion e D hG z Φ start Xexp Xexact M
    hclock hbr _ hLLNdiag hz hsub hdiam
  have hBc : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, ∀ i j : Fin 2,
      Continuous fun u => ordinaryEdgeBracket (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D) i j u ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => (hbr.2.2 i j).2.1.mono fun _ h => h.2.1
  have hAc : ∀ η : EuclideanSpace ℝ (Fin 2),
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, Continuous fun u =>
        dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η u ω := fun η =>
    hBc.mono fun ω h => by
      show Continuous fun u => ∑ i : Fin 2, ∑ j : Fin 2, η i * ordinaryEdgeBracket (decode e)
        (Φ.at e) (exponentialAreaPath (decode e) D) i j u ω * η j
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (h i j)).mul continuous_const
  have hAm : ∀ η : EuclideanSpace ℝ (Fin 2),
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, Monotone fun u =>
        dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η u ω := fun η =>
    hbr.2.1.mono fun ω h => dirBracket_ordinaryEdgeBracket_monotone (decode e)
      (decode_geometry e) (Φ.at e) (exponentialAreaPath (decode e) D) ω η h.2
  have hA0 : ∀ η : EuclideanSpace ℝ (Fin 2),
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, ∀ u,
        0 ≤ dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η u ω := fun η =>
    (hAm η).mono fun ω h u =>
      (dirBracket_ordinaryEdgeBracket_zero (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D) ω η).symm.trans_le (h zero_le)
  exact rescaledIncrementCharFunLimit_of_local_bracket_data
    (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M target hbr.1.1
    (BracketClausesScalarReduction.measurableSet_areaFiltration_of_null e D hG start)
    (fun η => dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
      (exponentialAreaPath (decode e) D)) η)
    (fun η => (ActualThresholdArray.canonicalBracket_projection_data e D hG Φ start M hbr η).1)
    (fun η => (ActualThresholdArray.canonicalBracket_projection_data e D hG Φ start M hbr η).2)
    hAc hAm hA0 (fun η => ActualThresholdArray.rescaledBracketLLN_completion (hdir η))
    hcad hjump hcont

/-! ## Shape check against the `hinc` consumer

`rescaledIncrementCharFunLimit_walk` fills the `hinc` slot of
`RescaledFddCharFunReduction.rescaledFddCharFunLimits_of_increment_limits` on the completed sample
space, with the walk's own filtration and adaptedness (`hbr.1.1`): this `example` elaborates. -/

example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (z Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hz : IsCellRepresentative z)
    (hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e))
    (hdiam : SubmacroscopicDiameters (decode e))
    (target : AnisotropicBrownianTarget)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (hdir : ∀ η : EuclideanSpace ℝ (Fin 2),
      RescaledBracketLLN (areaSampleLaw (decode e) D hG start)
        (dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D)) η)
        (bilinForm target.covariance η η))
    [IsProbabilityMeasure (areaSampleLaw (decode e) D hG start).completion]
    (Iw : NullMeasurableSpace (Existence.Sample (Vertex e.val))
      (areaSampleLaw (decode e) D hG start) → BouRabeeGwynne.BrownianPath 2)
    (hI : Measurable Iw) (p : Plane)
    (h0 : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion, M 0 ω = p)
    (hinterp : RescaledInterpolationErrorVanishes
      (areaSampleLaw (decode e) D hG start).completion Iw M) :
    GaussianWeakLimit.RescaledFddCharFunLimits
      ((areaSampleLaw (decode e) D hG start).completion.toProbabilityMeasure.map Iw) target :=
  rescaledFddCharFunLimits_of_increment_limits Iw hI
    (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M hbr.1.1 p h0 target
    (rescaledIncrementCharFunLimit_walk e D hG z Φ start Xexp Xexact M hclock hz hsub hdiam
      target hbr hdir)
    hinterp

end ReflectedGMS.WalkHincAssembly
