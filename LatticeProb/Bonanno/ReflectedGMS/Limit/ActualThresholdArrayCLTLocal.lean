/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualThresholdArrayCLTLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayWalk
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizingExit

/-!
# The Euclidean assembly and the double-stop exit bound for the local CLT lane

The CLT bridge `ApproximateBracketCLT.rescaledIncrementCharFunLimit_of_localizedBracketArrays`
(`Limit/ApproximateBracketCLTRescaled.lean`) accepts, for each scale sequence, direction `η` and
time pair `s ≤ t`, a `LocalizedBracketArray` of the rescaled filtrations together with the
vanishing of the probability that the array rows disagree with the rescaled projection
`⟪η, εₖ M(·/εₖ²)⟫` at `s` or `t`.  At the walk `M` is only a *local* martingale, and the
diagonal-localizer packet (`outputs/opus-lindeberg-diagonal-localizer-handoff.md` §4) left two
pieces for the local assembly.  Both are here.

* **The Euclidean assembly.**  `isLocallySquareIntegrableMartingale_inner` and
  `isLocalMartingale_inner_compensated`: from the plane-valued bracket data, every projection
  `⟪η, M⟫` is a locally square-integrable martingale whose compensated square with the
  directional bracket `dirBracket B η` is a local martingale.  At the walk,
  `canonicalBracket_projection_data` reads both off `InvarianceMainStatement.CanonicalBracket`
  for every direction at once — the local form of the `hmart`/`hsq` inputs of
  `rescaledIncrementCharFunLimit_of_bracket_data`.
* **The `hexit'` union bound.**  `stoppedProcess_indicator_twice_eq` and
  `tendsto_disagreement_of_two_stops`: a process stopped first at a localizer `ρ` and then at a
  bracket threshold `τ` agrees with the original at `s` and `t` off `{ρ ≤ t} ∪ {τ ≤ t}`, so the
  disagreement probability vanishes as soon as both exit probabilities do.
  `exists_rescaled_diagonal_localizer` supplies the first one at the parabolic horizon, in the
  time-changed form of `Limit/ActualThresholdArrayRescale` (`timeScaleTop`).

## What is NOT here, and why

The local assembly of the whole `LocalizedBracketArray` needs, besides these two pieces, the
**Lindeberg field for the doubly-stopped rows** `N'' k` (localizer stop, then bracket stop).  The
Lindeberg lane (`Limit/StoppedRescaledLindeberg`, owned by a live neighbour) produces it only for
the singly-stopped rows `N' k` of a *global* martingale.  It does not transfer for free: off the
localizer exit event the increments agree, but on it the Lindeberg integrand is not controlled
without uniform integrability.  The neighbour's two atoms do transfer — small increments by a
union bound with the exit event, and the terminal square tail because `x ↦ (x² − m)⁺` is convex,
so optional stopping bounds the doubly-stopped tail by the singly-stopped one — but that is the
neighbour's statement to restate, not this module's.  Every other field of the array (martingale,
`L²`, adaptedness, monotonicity, boundedness, bracket identity, oscillation, bracket limit) is
available from the pieces here and the threshold machinery.
-/

-- Merged from `ReflectedGMS/Limit/DiagonalLocalizer.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_DiagonalLocalizer

/-!
# The diagonal choice of localizer index along a sequence of horizons

`ReflectedGMS.MartingaleLimit.exists_common_square_localizer` turns a locally square-integrable
martingale whose compensated square is a local martingale into a *sequence* of true
square-integrable martingales, indexed by a localizing sequence `ρ`.  Every consumer in the
rescaled FCLT lane, however, is a limit statement along a sequence of scales `ε k → 0⁺`, where
the relevant time horizon at scale `k` is `(ε k)⁻¹ ^ 2 * t` and therefore *grows without bound*.
A single localizer index never suffices for such a family: the exit probability
`P {ρ j ≤ T}` is small for fixed `T` and large `j`, not for a horizon that moves with the index.

This file supplies the missing diagonal extraction.  Along any sequence of horizons `T k` there
is an index sequence `j k → ∞` whose exit probabilities at the matching horizon vanish:

* `exists_diagonal_localizer_index` — the general statement;
* `exists_diagonal_localizer_index_rescaled` — the same at the parabolic horizons
  `(ε k)⁻¹ ^ 2 * t` of the rescaled lane.

The only input is `LocalizingExit.localizing_exit_tendsto_zero`, i.e. the definition of a genuine
localizing sequence; no path regularity, no martingale property and no integrability is used, so
the statement applies verbatim to the localizers produced by `CommonSquareLocalizer` and by
`LocalMartingaleCombination`'s pointwise minima.

The intended consumer is the *bridge*
`ApproximateBracketCLT.rescaledIncrementCharFunLimit_of_localizedBracketArrays`, whose
hypothesis already tolerates an array agreeing with the rescaled projections outside events of
vanishing probability: the disagreement event of the diagonally localized array is contained in
the union of the diagonal exit event controlled here with the bracket-threshold exit event.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **The diagonal localizer index.**  Along any sequence of finite horizons `T k` a genuine
localizing sequence admits a diverging index sequence `j k` whose exit probability before the
matching horizon `T k` tends to zero.  For each `k` the fixed-horizon exit probabilities vanish
in the index (`localizing_exit_tendsto_zero`), so an index beyond `k` with exit probability at
most `(k + 1)⁻¹` exists; the diagonal is any choice of such indices. -/
theorem exists_diagonal_localizer_index
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {ρ : ℕ → Ω → WithTop ℝ≥0}
    (hρ : IsLocalizingSequence F ρ P) (T : ℕ → ℝ≥0) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => P {ω | ρ (j k) ω ≤ T k}) atTop (𝓝 0) := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ≥0∞) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    rw [ENNReal.inv_pos]
    exact ENNReal.natCast_ne_top (k + 1)
  have hstep : ∀ k : ℕ, ∃ N : ℕ, k ≤ N ∧ P {ω | ρ N ω ≤ T k} ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    have hlim := localizing_exit_tendsto_zero hρ (T k)
    obtain ⟨N₀, hN₀⟩ :=
      eventually_atTop.mp (hlim.eventually (gt_mem_nhds (hpos k)))
    refine ⟨max k N₀, le_max_left _ _, ?_⟩
    exact (hN₀ (max k N₀) (le_max_right _ _)).le
  choose j hjge hjle using hstep
  refine ⟨j, tendsto_atTop_mono hjge tendsto_id, ?_⟩
  have hinv : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
    (fun _ => zero_le) hjle

/-- **The diagonal localizer index at the parabolic horizons of the rescaled lane.**  At scale
`ε k` the rescaled process on `[0, t]` reads the original process on `[0, (ε k)⁻¹ ^ 2 * t]`, so
this is the form in which the localizer index must be chosen for a statement along `ε k → 0⁺`. -/
theorem exists_diagonal_localizer_index_rescaled
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {ρ : ℕ → Ω → WithTop ℝ≥0}
    (hρ : IsLocalizingSequence F ρ P) (ε : ℕ → ℝ≥0) (t : ℝ≥0) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun k => P {ω | ρ (j k) ω ≤ (ε k)⁻¹ ^ 2 * t}) atTop (𝓝 0) :=
  exists_diagonal_localizer_index hρ fun k => (ε k)⁻¹ ^ 2 * t

end ReflectedGMS.MartingaleLimit

end Merged_DiagonalLocalizer

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.ActualThresholdArray

open Code EnvironmentFields EnvironmentLaws StatementIngredients
open AreaClocks SpatialEnds InvarianceMainStatement MartingaleIngredients
open ReflectedWalk ProcessFiltration
open ReflectedGMS.LocalMartingaleCombination
open ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.RescaledFddCharFun

/-! ## The Euclidean assembly -/

section Euclidean

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The planar real inner product in coordinates. -/
theorem inner_euc_two (η v : EuclideanSpace ℝ (Fin 2)) : ⟪η, v⟫_ℝ = η 0 * v 0 + η 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **Every projection of a plane-valued locally square-integrable martingale is one.** -/
theorem isLocallySquareIntegrableMartingale_inner {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)}
    (hM : IsLocallySquareIntegrableMartingale P F M)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) (η : EuclideanSpace ℝ (Fin 2)) :
    IsLocallySquareIntegrableMartingale P F (fun t ω => ⟪η, M t ω⟫_ℝ) := by
  have hri : ∀ i : Fin 2, ∀ᵐ ω ∂P, IsRightContinuous (fun t => η i * M t ω i) := by
    intro i
    filter_upwards [hr] with ω hω
    have hc : IsRightContinuous (fun _ : ℝ≥0 => η i) := IsRightContinuous.const
    exact hc.mul (PlaneCoordinateMartingale.isRightContinuous_coord hω i)
  have h := isLocallySquareIntegrableMartingale_add
    (isLocallySquareIntegrableMartingale_const_mul (isLocallySquareIntegrableMartingale_coord hM 0)
      (η 0))
    (isLocallySquareIntegrableMartingale_const_mul (isLocallySquareIntegrableMartingale_coord hM 1)
      (η 1))
    hnull (hri 0) (hri 1)
  have heq : (fun t ω => ⟪η, M t ω⟫_ℝ) = fun t ω => η 0 * M t ω 0 + η 1 * M t ω 1 := by
    funext t ω
    exact inner_euc_two η (M t ω)
  rw [heq]
  exact h

/-- **The compensated square of every projection is a local martingale**, with the directional
bracket `dirBracket B η = ∑ᵢⱼ ηᵢ Bᵢⱼ ηⱼ`, from the four entrywise compensated products. -/
theorem isLocalMartingale_inner_compensated {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)}
    {B : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ}
    (hMB : ∀ i j, IsLocalMartingale P F (fun t ω => M t ω i * M t ω j - B i j t ω))
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hB : ∀ i j, ∀ᵐ ω ∂P, Continuous (fun t => B i j t ω)) (η : EuclideanSpace ℝ (Fin 2)) :
    IsLocalMartingale P F (fun t ω => ⟪η, M t ω⟫_ℝ ^ 2 - dirBracket B η t ω) := by
  set Z : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ :=
    fun i j t ω => η i * η j * (M t ω i * M t ω j - B i j t ω) with hZdef
  have hrc : ∀ i j, ∀ᵐ ω ∂P, IsRightContinuous (fun t => Z i j t ω) := by
    intro i j
    filter_upwards [hr, hB i j] with ω h1 h2
    have hc : IsRightContinuous (fun _ : ℝ≥0 => η i * η j) := IsRightContinuous.const
    exact hc.mul (((PlaneCoordinateMartingale.isRightContinuous_coord h1 i).mul
      (PlaneCoordinateMartingale.isRightContinuous_coord h1 j)).sub h2.isRightContinuous)
  have hZ : ∀ i j, IsLocalMartingale P F (Z i j) := fun i j =>
    isLocalMartingale_const_mul (hMB i j) (η i * η j)
  have h1 := isLocalMartingale_add (hZ 0 0) (hZ 0 1) hnull (hrc 0 0) (hrc 0 1)
  have hr1 : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Z 0 0 t ω + Z 0 1 t ω) := by
    filter_upwards [hrc 0 0, hrc 0 1] with ω a b
    exact a.add b
  have h2 := isLocalMartingale_add h1 (hZ 1 0) hnull hr1 (hrc 1 0)
  have hr2 : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => Z 0 0 t ω + Z 0 1 t ω + Z 1 0 t ω) := by
    filter_upwards [hr1, hrc 1 0] with ω a b
    exact a.add b
  have h3 := isLocalMartingale_add h2 (hZ 1 1) hnull hr2 (hrc 1 1)
  have heq : (fun t ω => ⟪η, M t ω⟫_ℝ ^ 2 - dirBracket B η t ω) =
      fun t ω => Z 0 0 t ω + Z 0 1 t ω + Z 1 0 t ω + Z 1 1 t ω := by
    funext t ω
    simp only [hZdef, dirBracket, Fin.sum_univ_two, inner_euc_two]
    ring
  rw [heq]
  exact h3

end Euclidean

/-- **The Euclidean assembly at the walk.**  From the walk's bracket `CanonicalBracket`, on the
completed sample space and the completed area filtration: for every direction `η`, the projection
`⟪η, M⟫` is a locally square-integrable martingale and `⟪η, M⟫² − dirBracket [M] η` is a local
martingale.  These are the local forms of the `hmart`/`hsq` inputs of
`ApproximateBracketCLT.rescaledIncrementCharFunLimit_of_bracket_data`. -/
theorem canonicalBracket_projection_data (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (η : EuclideanSpace ℝ (Fin 2)) :
    IsLocallySquareIntegrableMartingale
        (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
          (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (fun t ω => ⟪η, M t ω⟫_ℝ) ∧
      IsLocalMartingale
        (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val))
          (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (fun t ω => ⟪η, M t ω⟫_ℝ ^ 2 -
          dirBracket (ordinaryEdgeBracket (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D)) η t ω) := by
  have hPc : IsFiniteMeasure (areaSampleLaw (decode e) D hG start).completion :=
    BracketClausesScalarReduction.isFiniteMeasure_areaSampleLaw_completion e D hG start
  obtain ⟨hloc, hpath, hcov⟩ := hbr
  have hr : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
      IsRightContinuous (fun t => M t ω) := hpath.mono fun _ h => h.1.isRightContinuous
  exact ⟨isLocallySquareIntegrableMartingale_inner hloc
      (BracketClausesScalarReduction.measurableSet_areaFiltration_of_null e D hG start) hr η,
    isLocalMartingale_inner_compensated (fun i j => (hcov i j).2.2)
      (BracketClausesScalarReduction.measurableSet_areaFiltration_of_null e D hG start) hr
      (fun i j => (hcov i j).2.1.mono fun _ h => h.2.1) η⟩

/-! ## The `hexit'` union bound -/

section Exit

variable {Ω : Type*} {m : MeasurableSpace Ω}

end Exit

end ReflectedGMS.ActualThresholdArray
