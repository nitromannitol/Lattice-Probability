/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CanonicalOccupationDischarge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaTransitionReversibility
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.LogCutoffSpatialBoundedness
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialCutoffFromLocalMass
import LatticeProb.Bonanno.ReflectedGMS.HarmonicMainStatement

/-!
# Discharge of `CanonicalOccupationLocallyFinite`

`Limit/LocalizedBracketOccupation.CanonicalOccupationLocallyFinite` asks that,
almost surely under the canonical area-clock law started at any vertex, the
integrated ordinary-edge rate

  `∫₀ᵗ Γ(u)(X_r) dr`,  `Γ(u)(x) = (cellArea x)⁻¹ ∑_y c(x,y) (u y − u x)²`,

be finite at every horizon, for the six coordinate functions built from the
harmonic coordinate `Φ`.  Bracket clauses 2, 3 and 4 are already derived from
this one atom.  This file proves it.

## The argument (manuscript `p:lem:localharm`, "the localization also proves
## finiteness of the displayed integrals on compact time intervals")

It is a **quenched, spatially localized expectation bound**, not a path-regularity
statement and not a rooted-energy statement.

1. *Detailed balance of the area-clock walk.*  For the walk with rate
   `π(x) / cellArea x` the cell area is a reversing measure at every fixed time,
   `a_z · P_z(X_r = x) = a_x · P_x(X_r = z)`, with **no** summability of the
   areas (`Forms/AreaTransitionReversibility.reflected_transition_detailedBalance_of_positive_speed`).
   Hence `P_z(X_r = x) ≤ a_x / a_z`.
2. *The area cancels.*  Multiplying, `a_x · Γ(u)(x) = ∑_y c(x,y) (u y − u x)²`
   is the ordered energy row at `x`, with no area weight left.
3. *Localize to a ball.*  Restricting the integrand to the cells meeting
   `closedBall 0 R`, Tonelli and 1–2 bound the `P_z`-expectation of the
   localized occupation up to time `t` by `(t / a_z) · 2 𝓔_Q(u)`, where
   `𝓔_Q(u)` is the Dirichlet energy of `u` on the rectangle patch
   `Q = [−2R, 2R]²`, which contains those cells and all their neighbours.
   This is **finite by the `FullSpatialHarmonicity` clause (H5c) of
   `IsHarmonicCoordinate`** — the per-rectangle `vectorEnergy … < ∞` — not by
   total energy (false at `decode e`) and not by `FiniteSpecificEnergy` (H4,
   which controls only the root cell in `ν`-expectation and would need a
   fixed-time annealed stationarity that the dilation-covariant
   `MassTransport` does not supply).
4. *Remove the localization.*  The quenched spatial bound `r:eq:localbounded`
   (`Recurrence/LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime`)
   gives, a.s. and for every horizon `n`, a radius `R` with the whole visited
   path inside the cells meeting `closedBall 0 R`; on that event the localized
   and the full occupations coincide on `[0, n]`.  Countably many `(n, R)` are
   handled by `ae_all_iff`, and `Forms/PolarizedJumpOccupation.stationaryJumpOccupation_lt_top_all_of_nat`
   lifts integer horizons to every `t : ℝ≥0`.

Neither `Summable (cellArea …)` nor `HasFiniteEnergy` on the whole graph appears
anywhere; no non-explosion of the path is used or implied (the path may visit
the end inside a bounded region — the argument only needs the visited cells to
meet a bounded ball, which is what `r:eq:localbounded` says).

## Status

`ae_canonicalOccupationLocallyFinite` is a **discharge**: its hypotheses are
`MassTransport ν`, `FiniteEnergyMoment ν` and `IsHarmonicCoordinate ν Φ` — the
very inputs `hmt`, `hFE`, `hΦ` already carried by
`InvarianceAssemblyFourInputs.reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged` —
plus the per-environment walk data `EnvironmentWalkData e D hG`, which is the
`hdata` clause discharged there by `AreaClockAdmissibleDischarge.ae_environmentWalkData`.
Nothing here consumes a bracket, martingale or limit atom, so there is no cycle;
and the hypotheses are the ones the shifted-square tiling witness satisfies, so
the theorem is not vacuous.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal

namespace ReflectedGMS.CanonicalOccupationDischarge

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm StatementIngredients

universe u

/-! ## Part 1: the spatially localized ordinary-edge occupation -/

section General

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The ordinary-edge rate restricted to the vertex states in `S`; zero at the
collapsed end state and at vertices outside `S`. -/
noncomputable def localizedStateRate (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ)
    (S : Set V) : Option V → ℝ≥0∞ :=
  (some '' S).indicator (stateVertexCarreDuChamp G m u)

theorem localizedStateRate_none (G : ConductanceGraph V) (m u : V → ℝ) (S : Set V) :
    localizedStateRate G m u S none = 0 := by
  unfold localizedStateRate
  apply Set.indicator_of_notMem
  simp

theorem localizedStateRate_some_of_mem (G : ConductanceGraph V) (m u : V → ℝ)
    (S : Set V) {x : V} (hx : x ∈ S) :
    localizedStateRate G m u S (some x) =
      ENNReal.ofReal (vertexCarreDuChamp G m u x) := by
  unfold localizedStateRate
  rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]
  rfl

theorem localizedStateRate_some_of_notMem (G : ConductanceGraph V) (m u : V → ℝ)
    (S : Set V) {x : V} (hx : x ∉ S) :
    localizedStateRate G m u S (some x) = 0 := by
  unfold localizedStateRate
  apply Set.indicator_of_notMem
  rintro ⟨y, hy, hxy⟩
  exact hx (Option.some_inj.mp hxy ▸ hy)

/-- The localized rate evaluated on the canonical jointly measurable dyadic
version of the raw path. -/
noncomputable def localizedDyadicRate (PF : ProcessFamily V) (G : ConductanceGraph V)
    (m : V → ℝ) (u : V → ℝ) (S : Set V) (ω : PF.Ω) (r : ℝ) : ℝ≥0∞ :=
  localizedStateRate G m u S (dyadicLimit PF.X (Real.toNNReal r) ω)

theorem measurable_uncurry_localizedDyadicRate (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (S : Set V) :
    Measurable (Function.uncurry (localizedDyadicRate PF G m u S)) := by
  exact (measurable_of_countable (localizedStateRate G m u S)).comp
    (measurable_swap_toNNReal (measurable_uncurry_dyadicLimit PF.measurable_X))

/-- The integrated localized ordinary-edge rate up to a deterministic time. -/
noncomputable def localizedJumpOccupation (PF : ProcessFamily V) (G : ConductanceGraph V)
    (m : V → ℝ) (u : V → ℝ) (S : Set V) (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Icc 0 (t : ℝ), localizedDyadicRate PF G m u S ω r

theorem measurable_localizedJumpOccupation (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (S : Set V) (t : ℝ≥0) :
    Measurable (localizedJumpOccupation PF G m u S t) := by
  let F : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator (localizedDyadicRate PF G m u S ω) r
  have hF : Measurable (Function.uncurry F) := by
    dsimp only [F]
    exact (measurable_uncurry_localizedDyadicRate PF G m u S).indicator
      (measurable_snd measurableSet_Icc)
  change Measurable (fun ω ↦ ∫⁻ r : ℝ in Icc 0 (t : ℝ),
    localizedDyadicRate PF G m u S ω r)
  simpa only [F, lintegral_indicator measurableSet_Icc] using
    hF.lintegral_prod_right

/-! ## Part 2: the area cancels against the speed weight -/

/-- Row summability of the ordered energy row from finite degree alone. -/
theorem summable_gradSq_row_of_finite_neighborSet (G : ConductanceGraph V)
    (u : V → ℝ) {x : V} (hx : (G.toSimpleGraph.neighborSet x).Finite) :
    Summable (fun y : V ↦ G.gradSq u (x, y)) := by
  classical
  refine summable_of_ne_finset_zero (s := hx.toFinset) fun y hy ↦ ?_
  have hnadj : ¬ G.toSimpleGraph.Adj x y := fun hadj ↦
    hy (hx.mem_toFinset.mpr ((SimpleGraph.mem_neighborSet _ _ _).mpr hadj))
  have h1 : ¬ (0 < G.c x y) := fun hpos ↦ hnadj (G.toSimpleGraph_adj.mpr hpos)
  have h0 : G.c x y = 0 := le_antisymm (not_lt.mp h1) (G.c_nonneg x y)
  simp [ConductanceGraph.gradSq, h0]

/-- **The speed cancels.**  `m x · Γ(u)(x)` is the ordered energy row at `x`,
with no speed left; in `ℝ≥0∞` and with finite degree it is the `tsum` of the
`ofReal` row terms. -/
theorem ofReal_speed_mul_vertexCarreDuChamp_eq (G : ConductanceGraph V) (m u : V → ℝ)
    {x : V} (hmx : 0 < m x) (hdeg : (G.toSimpleGraph.neighborSet x).Finite) :
    ENNReal.ofReal (m x * vertexCarreDuChamp G m u x) =
      ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y)) := by
  have hrow : m x * vertexCarreDuChamp G m u x = ∑' y : V, G.gradSq u (x, y) := by
    rw [vertexCarreDuChamp, ← tsum_mul_left]
    apply tsum_congr
    intro y
    simp only [ConductanceGraph.gradSq]
    field_simp [hmx.ne']
  rw [hrow]
  exact ENNReal.ofReal_tsum_of_nonneg (fun y ↦ G.gradSq_nonneg u (x, y))
    (summable_gradSq_row_of_finite_neighborSet G u hdeg)

/-! ## Part 3: the fixed-time expectation bound from detailed balance -/

/-- **Expectation of the localized rate at one time, from detailed balance.**
For the reflected walk with rate `π / m` and any pointwise positive speed `m`
(no summability), the `P_z`-expectation of the localized rate at time `r` is at
most `(m z)⁻¹` times the sum over `x ∈ S` of the ordered energy rows. -/
theorem lintegral_localizedStateRate_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hdeg : ∀ x, (G.toSimpleGraph.neighborSet x).Finite)
    (u : V → ℝ) (S : Set V) (z : V) (r : ℝ≥0) :
    (∫⁻ ω, localizedStateRate G m u S (PF.X r ω) ∂PF.P z) ≤
      ENNReal.ofReal (m z)⁻¹ *
        ∑' x : V, S.indicator
          (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x := by
  have hfm : Measurable (localizedStateRate G m u S) := measurable_of_countable _
  have hterm : ∀ x : V,
      localizedStateRate G m u S (some x) * (PF.P z) {ω | PF.X r ω = some x} ≤
        ENNReal.ofReal (m z)⁻¹ *
          S.indicator (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [localizedStateRate_some_of_mem G m u S hx,
        Set.indicator_of_mem hx (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y)))]
      have hdb := AreaReversibility.reflected_transition_detailedBalance_of_positive_speed
        h hG hm r z x
      have hle1 : (PF.P x {ω | PF.X r ω = some z}).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one
          (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      have hPle : (PF.P z {ω | PF.X r ω = some x}).toReal ≤ m x / m z := by
        rw [le_div_iff₀ (hm z), mul_comm, hdb]
        exact mul_le_of_le_one_right (hm x).le hle1
      have hP : PF.P z {ω | PF.X r ω = some x} ≤ ENNReal.ofReal (m x / m z) :=
        calc PF.P z {ω | PF.X r ω = some x}
            = ENNReal.ofReal ((PF.P z {ω | PF.X r ω = some x}).toReal) :=
              (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (m x / m z) := ENNReal.ofReal_le_ofReal hPle
      have hΓ : 0 ≤ vertexCarreDuChamp G m u x := vertexCarreDuChamp_nonneg G m hm u x
      have hinv : (0 : ℝ) ≤ (m z)⁻¹ := inv_nonneg.2 (hm z).le
      calc ENNReal.ofReal (vertexCarreDuChamp G m u x) * PF.P z {ω | PF.X r ω = some x}
          ≤ ENNReal.ofReal (vertexCarreDuChamp G m u x) * ENNReal.ofReal (m x / m z) := by
            gcongr
        _ = ENNReal.ofReal (m z)⁻¹ *
              ENNReal.ofReal (m x * vertexCarreDuChamp G m u x) := by
            rw [← ENNReal.ofReal_mul hΓ, ← ENNReal.ofReal_mul hinv]
            congr 1
            ring
        _ = ENNReal.ofReal (m z)⁻¹ * ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y)) := by
            rw [ofReal_speed_mul_vertexCarreDuChamp_eq G m u (hm x) (hdeg x)]
    · rw [localizedStateRate_some_of_notMem G m u S hx, zero_mul]
      exact zero_le
  calc (∫⁻ ω, localizedStateRate G m u S (PF.X r ω) ∂PF.P z)
      = ∫⁻ q, localizedStateRate G m u S q ∂((PF.P z).map (PF.X r)) :=
        (lintegral_map hfm (PF.measurable_X r)).symm
    _ = ∑' q : Option V, localizedStateRate G m u S q * ((PF.P z).map (PF.X r)) {q} :=
        lintegral_countable' _
    _ = ∑' x : V, localizedStateRate G m u S (some x) *
          ((PF.P z).map (PF.X r)) {some x} := by
        refine ((Option.some_injective V).tsum_eq
          (f := fun q : Option V ↦
            localizedStateRate G m u S q * ((PF.P z).map (PF.X r)) {q}) ?_).symm
        intro q hq
        have hq' : localizedStateRate G m u S q * ((PF.P z).map (PF.X r)) {q} ≠ 0 := hq
        rcases q with _ | x
        · exact absurd (by rw [localizedStateRate_none, zero_mul]) hq'
        · exact ⟨x, rfl⟩
    _ = ∑' x : V, localizedStateRate G m u S (some x) *
          (PF.P z) {ω | PF.X r ω = some x} := by
        apply tsum_congr
        intro x
        rw [Measure.map_apply (PF.measurable_X r) (measurableSet_singleton _)]
        rfl
    _ ≤ ∑' x : V, ENNReal.ofReal (m z)⁻¹ *
          S.indicator (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (m z)⁻¹ *
          ∑' x : V, S.indicator
            (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x :=
        ENNReal.tsum_mul_left

/-! ## Part 4: the rows over `S` are bounded by a patch energy -/

/-- If every neighbour of a vertex of `S` lies in `P ⊇ S`, the energy rows over
`S` are bounded by the ordered energy of `u` on `P`. -/
theorem tsum_indicator_row_le_tsum_patch (G : ConductanceGraph V) (u : V → ℝ)
    {S P : Set V} (hSP : S ⊆ P)
    (hnbr : ∀ x ∈ S, ∀ y : V, G.c x y ≠ 0 → y ∈ P) :
    (∑' x : V, S.indicator
        (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x) ≤
      ∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)) := by
  have hrow : ∀ x ∈ S, (∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) =
      ∑' y : P, ENNReal.ofReal (G.gradSq u (x, y.1)) := by
    intro x hx
    refine Eq.trans ?_ (tsum_subtype P (fun y ↦ ENNReal.ofReal (G.gradSq u (x, y)))).symm
    apply tsum_congr
    intro y
    by_cases hy : y ∈ P
    · rw [Set.indicator_of_mem hy (fun y ↦ ENNReal.ofReal (G.gradSq u (x, y)))]
    · rw [Set.indicator_of_notMem hy (fun y ↦ ENNReal.ofReal (G.gradSq u (x, y)))]
      have hc : G.c x y = 0 := by
        by_contra hc
        exact hy (hnbr x hx y hc)
      simp [ConductanceGraph.gradSq, hc]
  calc (∑' x : V, S.indicator
          (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x)
      ≤ ∑' x : V, P.indicator
          (fun x ↦ ∑' y : P, ENNReal.ofReal (G.gradSq u (x, y.1))) x := by
        apply ENNReal.tsum_le_tsum
        intro x
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx
              (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))),
            Set.indicator_of_mem (hSP hx)
              (fun x ↦ ∑' y : P, ENNReal.ofReal (G.gradSq u (x, y.1))),
            hrow x hx]
        · rw [Set.indicator_of_notMem hx
              (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y)))]
          exact zero_le
    _ = ∑' x : P, ∑' y : P, ENNReal.ofReal (G.gradSq u (x.1, y.1)) :=
        (tsum_subtype P (fun x ↦ ∑' y : P, ENNReal.ofReal (G.gradSq u (x, y.1)))).symm
    _ = ∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)) :=
        (ENNReal.tsum_prod' (f := fun p : P × P ↦
          ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)))).symm

/-- The ordered energy of `u` on the patch `P` is finite exactly when the
restricted graph energy of `u ∘ val` is finite. -/
theorem tsum_ofReal_gradSq_patch_ne_top (G : ConductanceGraph V) (u : V → ℝ)
    (P : Set V) (hfe : (restrictGraph G P).HasFiniteEnergy (fun v ↦ u v.1)) :
    (∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1))) ≠ ∞ :=
  (tsum_ofReal_gradSq_ne_top_iff (restrictGraph G P) (fun v ↦ u v.1)).2 hfe

/-! ## Part 5: the localized occupation has finite expectation, hence is a.s. finite -/

/-- **Finite expectation of the localized occupation.**  Tonelli, the
fixed-time bound of Part 3 and the patch bound of Part 4. -/
theorem lintegral_localizedJumpOccupation_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hdeg : ∀ x, (G.toSimpleGraph.neighborSet x).Finite)
    (u : V → ℝ) {S P : Set V} (hSP : S ⊆ P)
    (hnbr : ∀ x ∈ S, ∀ y : V, G.c x y ≠ 0 → y ∈ P)
    (hfe : (restrictGraph G P).HasFiniteEnergy (fun v ↦ u v.1))
    (z : V) (t : ℝ≥0) :
    (∫⁻ ω, localizedJumpOccupation PF G m u S t ω ∂PF.P z) < ∞ := by
  have hCtop : ENNReal.ofReal (m z)⁻¹ *
      (∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tsum_ofReal_gradSq_patch_ne_top G u P hfe)
  have hver : ∀ r : ℝ, (∫⁻ ω, localizedDyadicRate PF G m u S ω r ∂PF.P z) ≤
      ENNReal.ofReal (m z)⁻¹ *
        ∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)) := by
    intro r
    have hae : ∀ᵐ ω ∂PF.P z,
        dyadicLimit PF.X (Real.toNNReal r) ω = PF.X (Real.toNNReal r) ω := by
      filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
      exact hω (Real.toNNReal r)
    calc (∫⁻ ω, localizedDyadicRate PF G m u S ω r ∂PF.P z)
        = ∫⁻ ω, localizedStateRate G m u S (PF.X (Real.toNNReal r) ω) ∂PF.P z := by
          apply lintegral_congr_ae
          filter_upwards [hae] with ω hω
          simp only [localizedDyadicRate, hω]
      _ ≤ ENNReal.ofReal (m z)⁻¹ *
            ∑' x : V, S.indicator
              (fun x ↦ ∑' y : V, ENNReal.ofReal (G.gradSq u (x, y))) x :=
          lintegral_localizedStateRate_le h hG hm hdeg u S z (Real.toNNReal r)
      _ ≤ ENNReal.ofReal (m z)⁻¹ *
            ∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)) := by
          gcongr
          exact tsum_indicator_row_le_tsum_patch G u hSP hnbr
  let F : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator (localizedDyadicRate PF G m u S ω) r
  have hF : Measurable (Function.uncurry F) := by
    dsimp only [F]
    exact (measurable_uncurry_localizedDyadicRate PF G m u S).indicator
      (measurable_snd measurableSet_Icc)
  calc (∫⁻ ω, localizedJumpOccupation PF G m u S t ω ∂PF.P z)
      = ∫⁻ ω, ∫⁻ r, F ω r ∂volume ∂PF.P z := by
        apply lintegral_congr
        intro ω
        simp only [localizedJumpOccupation, F, lintegral_indicator measurableSet_Icc]
    _ = ∫⁻ r, ∫⁻ ω, F ω r ∂PF.P z ∂volume := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ ≤ ∫⁻ _ : ℝ in Icc 0 (t : ℝ), ENNReal.ofReal (m z)⁻¹ *
          ∑' p : P × P, ENNReal.ofReal (G.gradSq u (p.1.1, p.2.1)) := by
        rw [← lintegral_indicator measurableSet_Icc]
        apply lintegral_mono
        intro r
        by_cases hr : r ∈ Icc (0 : ℝ) (t : ℝ)
        · simp only [F, Set.indicator_of_mem hr]
          exact hver r
        · simp [F, Set.indicator_of_notMem hr]
    _ < ∞ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top)

/-- Almost-sure finiteness of the localized occupation at one horizon. -/
theorem ae_localizedJumpOccupation_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hdeg : ∀ x, (G.toSimpleGraph.neighborSet x).Finite)
    (u : V → ℝ) {S P : Set V} (hSP : S ⊆ P)
    (hnbr : ∀ x ∈ S, ∀ y : V, G.c x y ≠ 0 → y ∈ P)
    (hfe : (restrictGraph G P).HasFiniteEnergy (fun v ↦ u v.1))
    (z : V) (t : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, localizedJumpOccupation PF G m u S t ω < ∞ :=
  ae_lt_top (measurable_localizedJumpOccupation PF G m u S t)
    (lintegral_localizedJumpOccupation_lt_top h hG hm hdeg u hSP hnbr hfe z t).ne

/-! ## Part 6: geometry — the ball cells and their neighbours sit in a square patch -/

/-- The axis-parallel square `[-R, R]²`. -/
def squareRect (R : ℝ) (hR : 0 < R) : Rectangle :=
  ⟨fun _ ↦ -R, fun _ ↦ R, fun _ ↦ neg_lt_self hR⟩

theorem closedBall_subset_squareRect (R : ℝ) (hR : 0 < R) :
    Metric.closedBall (0 : Plane) R ⊆ (squareRect R hR).carrier := by
  intro y hy i
  have hyn : ‖y‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hj : |y i| ≤ R := le_trans (SpatialCutoff.abs_coord_le_norm y i) hyn
  exact ⟨(abs_le.1 hj).1, (abs_le.1 hj).2⟩

/-- A cell meeting `closedBall 0 R` is a patch vertex of the square `[-2R, 2R]²`. -/
theorem mem_patchVertices_squareRect_of_hits (F : IndexedCells V) {R : ℝ} (hR : 0 < R)
    {x : V} (hx : Hits F (Metric.closedBall (0 : Plane) R) x) :
    x ∈ patchVertices F (squareRect (2 * R) (by linarith)) := by
  obtain ⟨q, hqx, hqB⟩ := hx
  refine ⟨q, hqx, closedBall_subset_squareRect (2 * R) (by linarith) ?_⟩
  exact Metric.closedBall_subset_closedBall (by linarith) hqB

/-- **Neighbour enclosure.**  If cells meeting `closedBall 0 R` have diameter at
most `R / 100`, every graph neighbour of such a cell is a patch vertex of the
square `[-2R, 2R]²` (adjacent cells meet, Geometry clause eight). -/
theorem mem_patchVertices_squareRect_of_adj (F : IndexedCells V) (hF : Geometry F)
    {R : ℝ} (hR : 0 < R)
    (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {x y : V} (hx : Hits F (Metric.closedBall (0 : Plane) R) x)
    (hc : F.graph.c x y ≠ 0) :
    y ∈ patchVertices F (squareRect (2 * R) (by linarith)) := by
  have hadj : F.graph.toSimpleGraph.Adj x y :=
    lt_of_le_of_ne (F.graph.c_nonneg x y) (Ne.symm hc)
  obtain ⟨p, hpx, hpy⟩ := hF.2.2.2.2.2.2.2 hadj
  obtain ⟨q, hqx, hqB⟩ := hx
  have hpq : dist p q ≤ Metric.diam (F.cell x : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell x).isCompact.isBounded hpx hqx
  have hq : ‖q‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hqB
  have hdiam := hD x ⟨q, hqx, hqB⟩
  have hp : ‖p‖ ≤ 2 * R := by
    have h1 : ‖p‖ ≤ dist p q + ‖q‖ := by
      simpa only [dist_zero_right] using dist_triangle p q 0
    linarith
  refine ⟨p, hpy, closedBall_subset_squareRect (2 * R) (by linarith) ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hp

/-! ## Part 7: the general theorem — occupation finiteness from patch energy -/

/-- **Local finiteness of the ordinary-edge occupation of the area-clock walk
from patch energy and spatial boundedness.**

For the reflected walk with the area rate `π / cellArea` (any exhaustion, any
construction satisfying `IsReflectedWalk`), a coordinate `u` whose restriction
to every rectangle patch has finite energy, and the logarithmic-cutoff data of
`r:prop:log` at the start `o` (which yield `r:eq:localbounded`), the integrated
ordinary-edge rate is almost surely finite at every horizon.

No summability of the cell areas, no total energy and no non-explosion of the
path is assumed. -/
theorem stationaryJumpOccupation_ae_lt_top_all_of_patch_energy
    (F : IndexedCells V) (hF : Geometry F)
    {hmin : F.graph.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk F.graph (fun v ↦ F.graph.pi v / cellArea F v) hmin PF)
    (hw : ∀ v, 0 < F.graph.pi v / cellArea F v)
    (u : V → ℝ)
    (hloc : ∀ Q : Rectangle,
      (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy (fun v ↦ u v.1))
    (z : V → Plane) (hz : CellRepresentatives F z) (o : V)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖z o‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    ∀ᵐ ω ∂PF.P o, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF F.graph (cellArea F) u t ω < ∞ := by
  have hG : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  have hdeg : ∀ x, (F.graph.toSimpleGraph.neighborSet x).Finite := hF.2.2.2.2.2.2.1
  have hm : ∀ v, 0 < cellArea F v := cellArea_pos F hF
  -- localized finiteness at every natural radius `R ≥ r₀` and natural horizon `n`
  have hfin : ∀ R : ℕ, ∀ n : ℕ, ∀ᵐ ω ∂PF.P o, r₀ ≤ (R : ℝ) →
      localizedJumpOccupation PF F.graph (cellArea F) u
        {v : V | Hits F (Metric.closedBall (0 : Plane) (R : ℝ)) v} (n : ℝ≥0) ω < ∞ := by
    intro R n
    by_cases hR : r₀ ≤ (R : ℝ)
    · have hRpos : (0 : ℝ) < R := lt_of_lt_of_le hr₀ hR
      have h2R : (0 : ℝ) < 2 * R := by linarith
      filter_upwards [ae_localizedJumpOccupation_lt_top h hG hm hdeg u
        (S := {v : V | Hits F (Metric.closedBall (0 : Plane) (R : ℝ)) v})
        (P := patchVertices F (squareRect (2 * R) h2R))
        (fun x hx ↦ mem_patchVertices_squareRect_of_hits F hRpos hx)
        (fun x hx y hc ↦ mem_patchVertices_squareRect_of_adj F hF hRpos (hD R hR) hx hc)
        (hloc _) o n] with ω hω
      exact fun _ ↦ hω
    · exact ae_of_all _ (fun ω hR' ↦ absurd hR' hR)
  have hfin' : ∀ᵐ ω ∂PF.P o, ∀ R : ℕ, ∀ n : ℕ, r₀ ≤ (R : ℝ) →
      localizedJumpOccupation PF F.graph (cellArea F) u
        {v : V | Hits F (Metric.closedBall (0 : Plane) (R : ℝ)) v} (n : ℝ≥0) ω < ∞ :=
    ae_all_iff.2 fun R ↦ ae_all_iff.2 (hfin R)
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    F hF z hz PF h hw o hr₀ hC ho hD hW
  have hreg := ae_rightRegularAt (h o).2.2.1 (h o).2.2.2.1
  filter_upwards [hfin', hbdd, hreg] with ω hω hM hreg
  apply stationaryJumpOccupation_lt_top_all_of_nat
  intro n
  obtain ⟨M, hMn⟩ := hM n
  obtain ⟨R, hRr₀, hMR⟩ : ∃ R : ℕ, r₀ ≤ (R : ℝ) ∧ M ≤ (R : ℝ) := by
    refine ⟨max ⌈M⌉₊ ⌈r₀⌉₊, ?_, ?_⟩
    · calc r₀ ≤ (⌈r₀⌉₊ : ℝ) := Nat.le_ceil r₀
        _ ≤ ((max ⌈M⌉₊ ⌈r₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    · calc M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
        _ ≤ ((max ⌈M⌉₊ ⌈r₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have heq : stationaryJumpOccupation PF F.graph (cellArea F) u (n : ℝ≥0) ω =
      localizedJumpOccupation PF F.graph (cellArea F) u
        {v : V | Hits F (Metric.closedBall (0 : Plane) (R : ℝ)) v} (n : ℝ≥0) ω := by
    unfold stationaryJumpOccupation localizedJumpOccupation
    apply setLIntegral_congr_fun measurableSet_Icc
    intro r hr
    simp only [dyadicVertexCarreDuChamp, localizedDyadicRate,
      dyadicLimit_eq_of_rightRegular hreg]
    cases hX : PF.X (Real.toNNReal r) ω with
    | none => simp [localizedStateRate_none, stateVertexCarreDuChamp]
    | some v =>
      have htn : Real.toNNReal r ≤ (n : ℝ≥0) := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact_mod_cast hr.2
      have hv : v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) (R : ℝ)) v} := by
        refine ⟨z v, hz v, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (hMn _ htn v hX).trans hMR
      rw [localizedStateRate_some_of_mem F.graph (cellArea F) u _ hv]
      rfl
  rw [heq]
  exact hω R n hRr₀

end General

/-! ## Part 8: the canonical data -/

section Canonical

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement AreaClocks QuenchedFormulation LocalizedBracketOccupation

/-- Each coordinate of `Φ` has finite energy on every rectangle patch, from the
`FullSpatialHarmonicity` clause. -/
theorem hasFiniteEnergy_patch_coord (e : Env) (Φ : CellField)
    (hpatch : ∀ Q : Rectangle,
      vectorEnergy (restrictGraph (decode e).graph (patchVertices (decode e) Q))
        (fun v ↦ Φ.at e v.1) < ∞)
    (i : Fin 2) (Q : Rectangle) :
    (restrictGraph (decode e).graph (patchVertices (decode e) Q)).HasFiniteEnergy
      (fun v ↦ Φ.at e v.1 i) := by
  rw [← energyENN_ne_top_iff]
  refine ne_top_of_le_ne_top (hpatch Q).ne ?_
  unfold vectorEnergy
  exact Finset.single_le_sum
    (f := fun j : Fin 2 ↦ energyENN (restrictGraph (decode e).graph (patchVertices (decode e) Q))
      (fun v ↦ Φ.at e v.1 j))
    (fun _ _ ↦ zero_le) (Finset.mem_univ i)

/-- **`CanonicalOccupationLocallyFinite` holds for almost every environment, at
every exhaustion, connectivity witness, walk datum and start.**

DISCHARGE, not reduction: the hypotheses are exactly the `hmt`, `hFE`, `hΦ`
inputs of the four-input invariance assembly, and the walk data
`EnvironmentWalkData e D hG` is its already discharged `hdata` clause. -/
theorem ae_canonicalOccupationLocallyFinite (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ start : Vertex e.val,
          CanonicalOccupationLocallyFinite e D hG Φ start := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax,
    hΦ.2.2.2.2.1] with e hlog hΦe
  intro hnt D hG hdat start
  letI := hnt
  obtain ⟨hmin, hrate, hwalk, -⟩ := hdat
  have hpatch : ∀ Q : Rectangle,
      vectorEnergy (restrictGraph (decode e).graph (patchVertices (decode e) Q))
        (fun v ↦ Φ.at e v.1) < ∞ := fun Q ↦ (hΦe.2.2.1.1 Q).1
  let z : Vertex e.val → Plane := fun v ↦ ((decode e).cell v).nonempty.some
  have hz : CellRepresentatives (decode e) z := fun v ↦ ((decode e).cell v).nonempty.some_mem
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog z start
  have key : ∀ u : Vertex e.val → ℝ,
      (∀ Q : Rectangle,
        (restrictGraph (decode e).graph (patchVertices (decode e) Q)).HasFiniteEnergy
          (fun v ↦ u v.1)) →
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
        stationaryJumpOccupation (Existence.processFamily D hG (areaRate (decode e)))
          (decode e).graph (cellArea (decode e)) u t ω < ∞ :=
    fun u hu ↦ stationaryJumpOccupation_ae_lt_top_all_of_patch_energy (decode e)
      (decode_geometry e) hwalk hrate u hu z hz start hr₀ hC ho hD hW
  refine ⟨fun i ↦ key _ (hasFiniteEnergy_patch_coord e Φ hpatch i), fun i j ↦ key _ ?_⟩
  intro Q
  exact (hasFiniteEnergy_patch_coord e Φ hpatch i Q).add
    (hasFiniteEnergy_patch_coord e Φ hpatch j Q)

end Canonical

end ReflectedGMS.CanonicalOccupationDischarge
