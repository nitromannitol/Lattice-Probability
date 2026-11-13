/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedRectangleOrthogonalityProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.RectangleInSelectedBlock
import LatticeProb.Bonanno.ReflectedGMS.Corrector.EventuallySelectedEngulfing
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CoveredOrigin

/-!
# `hharm` from `hpatch` alone

This module discharges the input `hharm` of
`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs`, i.e.
`HarmonicCoordinateAssembly.MarkedHarmonicity ν ms`, from the assembly's **own** patch
convergence input `hpatch` together with the mass transport and (FE) moment that the
assembly already carries.  No new environmental hypothesis is introduced.

The chain is:

* `Corrector/EventuallySelectedEngulfing.eventually_exists_selected_engulfing` — almost
  surely a fixed bounded rectangle lies in the *interior* of a `κ`-selected square once the
  parameter is large (this is where the uniform dyadic grid law is used, and it is the step
  the manuscript states as "eventually the rectangle lies inside a selected block").  Since
  the covering clause of `Geometry` was weakened to `μH[1] (uncoveredSet F) = 0`, that step
  now also needs the origin to lie in a cell, which is not automatic and is *not* a new
  hypothesis of this producer: it is discharged here, almost surely, by
  `ae_zero_notMem_uncoveredSet` — the manuscript's Lemma 2.4 — from the mass transport the
  producer already carries;
* `Corrector/RectangleInSelectedBlock.finiteEnergy_and_orthogonality_of_selected_engulfing` —
  on such a rectangle the block interpolant has finite patch energy and is orthogonal to the
  whole finite-energy zero-spatial-boundary class, by the first variation of the blockwise
  minimality;
* `rectangle_orthogonality_of_eventually` below — the identity passes to the patch-energy
  limit.  Only *eventual* finite patch energy of the approximants is needed: the sequence is
  shifted before the checked
  `LimitingPotentialFreeOrthogonality.dirichletForm_eq_zero_of_tendsto_energy` is applied.
* the remaining two conjuncts of `MarkedHarmonicity` are the checked
  `MarkedRectangleHarmonicity.fullRectangleMinimizer_of_orthogonality` and
  `MarkedRectangleHarmonicity.tsum_smul_sub_eq_zero_of_orthogonality`.

## Relation to `MarkedApproximantRectangleOrthogonality`

`MarkedRectangleHarmonicity.MarkedApproximantRectangleOrthogonality` asks for finite patch
energy of `φ_{m_j}` on every rectangle at **every** stage `j`, together with eventual
orthogonality.  Its orthogonality clause is proved here
(`approximantRectangleOrthogonality_clause`), but the finiteness clause at the *early*
stages is **not** available from the engulfing: when the rectangle is not yet inside a single
selected square, the patch of the rectangle meets uncountably many selected squares in
general and no block-local minimality controls the energy across their common boundaries.
This module therefore routes around that clause: the shift in
`rectangle_orthogonality_of_eventually` makes the early stages irrelevant, and
`markedHarmonicity_of_patchConvergence` proves the *conclusion*
`MarkedHarmonicity ν ms` that `MarkedApproximantRectangleOrthogonality` was introduced to
deliver.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS

namespace MarkedRectangleOrthogonalityProducer

open StatementIngredients DyadicApproximation

/-! ### The limit transfer on a single rectangle -/

section Transfer

variable {V : Type*}

/-- **Free orthogonality on one rectangle, transferred to the patch-energy limit.**  The
approximants are required to have finite patch energy at *every* stage; the eventual version
is `rectangle_orthogonality_of_eventually`. -/
theorem rectangle_orthogonality_of_tendsto (F : IndexedCells V) (Q : Rectangle)
    {φ : ℕ → V → Plane} {Φ : V → Plane}
    (hφE : ∀ j : ℕ, vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V)) < ∞)
    (hconv : Tendsto (fun j => vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V) - Φ (v : V))) atTop (𝓝 0))
    (horth : ∀ᶠ j in atTop, ∀ u : patchVertices F Q → Plane,
      FullZeroBoundaryVariation F Q u →
      vectorPairing (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => φ j (v : V)) u = 0) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => Φ (v : V)) < ∞ ∧
      ∀ u : patchVertices F Q → Plane, FullZeroBoundaryVariation F Q u →
        vectorPairing (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => Φ (v : V)) u = 0 := by
  have hDcoord : ∀ i : Fin 2, Tendsto (fun j => energyENN
      (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => (φ j (v : V) - Φ (v : V) : Plane) i)) atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le) fun j => ?_
    exact MarkedRectangleHarmonicity.energyENN_coord_le_vectorEnergy
      (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V) - Φ (v : V)) i
  have hEfin : ∀ᶠ j in atTop, vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V) - Φ (v : V)) < ∞ :=
    Tendsto.eventually_lt_const (by simp) hconv
  obtain ⟨j₀, hj₀⟩ := hEfin.exists
  have hψc : ∀ (j : ℕ) (i : Fin 2),
      (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun v : patchVertices F Q => φ j (v : V) i) := fun j i =>
    hasFiniteEnergy_coord _ (hφE j) i
  have hΨc : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
      (fun v : patchVertices F Q => Φ (v : V) i) := by
    intro i
    have hd : (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun v : patchVertices F Q => (φ j₀ (v : V) - Φ (v : V) : Plane) i) :=
      hasFiniteEnergy_coord _ hj₀ i
    have hrw : (fun v : patchVertices F Q => Φ (v : V) i)
        = (fun v : patchVertices F Q => φ j₀ (v : V) i)
          - fun v : patchVertices F Q => (φ j₀ (v : V) - Φ (v : V) : Plane) i := by
      funext v
      simp only [Pi.sub_apply, PiLp.sub_apply]
      ring
    rw [hrw]
    exact (hψc j₀ i).sub hd
  have hΔ : ∀ (i : Fin 2) (j : ℕ),
      (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        ((fun v : patchVertices F Q => Φ (v : V) i)
          - fun v : patchVertices F Q => φ j (v : V) i) := fun i j => (hΨc i).sub (hψc j i)
  have hE : ∀ i : Fin 2, Tendsto (fun j =>
      (restrictGraph F.graph (patchVertices F Q)).Energy
        ((fun v : patchVertices F Q => Φ (v : V) i)
          - fun v : patchVertices F Q => φ j (v : V) i)) atTop (𝓝 0) := by
    intro i
    have hrw : ∀ j : ℕ, (restrictGraph F.graph (patchVertices F Q)).Energy
        ((fun v : patchVertices F Q => Φ (v : V) i)
          - fun v : patchVertices F Q => φ j (v : V) i)
        = (energyENN (restrictGraph F.graph (patchVertices F Q))
            (fun v : patchVertices F Q => (φ j (v : V) - Φ (v : V) : Plane) i)).toReal := by
      intro j
      rw [← energyENN_toReal_eq_Energy _ (hΔ i j),
        MarkedRectangleHarmonicity.energyENN_coord_sub_comm
          (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => Φ (v : V))
          (fun v : patchVertices F Q => φ j (v : V)) i]
    simp only [hrw]
    have hcomp := (ENNReal.tendsto_toReal (by simp)).comp (hDcoord i)
    simpa [Function.comp_def] using hcomp
  refine ⟨vectorEnergy_lt_top_of_coord _ hΨc, fun u hu => ?_⟩
  have hcoord : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).dirichletForm
      (fun v : patchVertices F Q => Φ (v : V) i)
      (fun v : patchVertices F Q => u v i) = 0 := by
    intro i
    refine LimitingPotentialFreeOrthogonality.dirichletForm_eq_zero_of_tendsto_energy
      (restrictGraph F.graph (patchVertices F Q))
      (ψ := fun j => fun v : patchVertices F Q => φ j (v : V) i)
      (Ψ := fun v : patchVertices F Q => Φ (v : V) i)
      (v := fun v : patchVertices F Q => u v i)
      (fun j => hψc j i) (fun j => hΔ i j) (hasFiniteEnergy_coord _ hu.1 i) (hE i) ?_
    filter_upwards [horth] with j hj
    have hvar : FullZeroBoundaryVariation F Q
        (fun z : patchVertices F Q => (EuclideanSpace.single i (u z i) : Plane)) :=
      MarkedRectangleHarmonicity.fullZeroBoundaryVariation_single F Q
        (fun z : patchVertices F Q => u z i) i
        (hasFiniteEnergy_coord _ hu.1 i)
        (fun z hz => by show u z i = 0; rw [hu.2 z hz]; simp)
    have hzero := hj _ hvar
    rwa [MarkedRectangleHarmonicity.vectorPairing_single
      (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V))
      (fun z : patchVertices F Q => u z i) i] at hzero
  have hdef : vectorPairing (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => Φ (v : V)) u
      = ∑ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).dirichletForm
        (fun v : patchVertices F Q => Φ (v : V) i)
        (fun v : patchVertices F Q => u v i) := rfl
  rw [hdef, Finset.sum_congr rfl fun i _ => hcoord i]
  simp

/-- **The eventual version.**  Only eventual finite patch energy of the approximants is
assumed: the sequence is shifted past the exceptional stages, which changes neither the
patch-energy limit nor the eventual orthogonality. -/
theorem rectangle_orthogonality_of_eventually (F : IndexedCells V) (Q : Rectangle)
    {φ : ℕ → V → Plane} {Φ : V → Plane}
    (hφE : ∀ᶠ j in atTop, vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V)) < ∞)
    (hconv : Tendsto (fun j => vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => φ j (v : V) - Φ (v : V))) atTop (𝓝 0))
    (horth : ∀ᶠ j in atTop, ∀ u : patchVertices F Q → Plane,
      FullZeroBoundaryVariation F Q u →
      vectorPairing (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => φ j (v : V)) u = 0) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => Φ (v : V)) < ∞ ∧
      ∀ u : patchVertices F Q → Plane, FullZeroBoundaryVariation F Q u →
        vectorPairing (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => Φ (v : V)) u = 0 := by
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.1 hφE
  refine rectangle_orthogonality_of_tendsto F Q (φ := fun j => φ (j + j₀)) (Φ := Φ)
    (fun j => hj₀ (j + j₀) (Nat.le_add_left j₀ j)) ?_ ?_
  · simpa [Function.comp_def] using hconv.comp (tendsto_add_atTop_nat j₀)
  · obtain ⟨j₁, hj₁⟩ := Filter.eventually_atTop.1 horth
    exact Filter.eventually_atTop.2
      ⟨j₁, fun j hj => hj₁ (j + j₀) (le_trans hj (Nat.le_add_right j j₀))⟩

end Transfer

/-! ### The marked producer -/

section Marked

open Code EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly

/-- The marked form of `ae_zero_notMem_uncoveredSet` (`Spatial/CoveredOrigin.lean`), the
manuscript's Lemma 2.4: almost every marked environment has its origin in a cell. -/
theorem ae_zero_notMem_uncoveredSet_marked (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, (0 : Plane) ∉ uncoveredSet (decode ω.1) :=
  ae_marked_of_ae_env ν (ae_zero_notMem_uncoveredSet ν hν)

/-- Almost every marked environment has an eventually centred grid. -/
theorem ae_eventuallyCentred_grid (ν : Measure Env) [SFinite ν] :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      EventuallySelectedEngulfing.EventuallyCentred ω.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := gridLaw)).tendsto_ae.eventually
    (EventuallySelectedEngulfing.ae_eventuallyCentred uniformGridLaw_gridLaw)

/-- **The orthogonality clause of `MarkedApproximantRectangleOrthogonality`.**  Almost surely
every bounded rectangle is eventually free-orthogonal for the concrete block interpolants
along any strictly increasing stage sequence. -/
theorem approximantRectangleOrthogonality_clause (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ Q : Rectangle,
      ∀ᶠ j in atTop,
        vectorEnergy (restrictGraph (decode ω.1).graph (patchVertices (decode ω.1) Q))
            (fun v : patchVertices (decode ω.1) Q =>
              phi (decode ω.1) ω.2 (ms j) (v : Vertex ω.1.val)) < ∞ ∧
          ∀ u : patchVertices (decode ω.1) Q → Plane,
            FullZeroBoundaryVariation (decode ω.1) Q u →
            vectorPairing (restrictGraph (decode ω.1).graph (patchVertices (decode ω.1) Q))
              (fun v : patchVertices (decode ω.1) Q =>
                phi (decode ω.1) ω.2 (ms j) (v : Vertex ω.1.val)) u = 0 := by
  have hMax : SpatialMaximalBound ν := spatialMaximalBound_of_massTransport ν hν hFE
  filter_upwards [ae_marked_geometry ν hν hFE.ne hMax,
    ae_blockInterpolation_clause ν hν hFE.ne hMax, ae_eventuallyCentred_grid ν,
    ae_zero_notMem_uncoveredSet_marked ν hν]
    with ω hgeom hblock hcent hcov
  intro Q
  have heng := EventuallySelectedEngulfing.eventually_exists_selected_engulfing
    (decode ω.1) (decode_geometry ω.1) hcov ω.2 hgeom.2.1 hcent Q
  have hms' : ∀ᶠ j in atTop, ∃ s : SquareIndex,
      Selected (decode ω.1) ω.2 ((ms j : ℕ) : ℝ) s ∧
        Q.carrier ⊆ interior (square ω.2 s).carrier := hms.tendsto_atTop.eventually heng
  filter_upwards [hms', eventually_gt_atTop 0] with j hj hj0
  obtain ⟨s, hs, hQ⟩ := hj
  have hmne : ms j ≠ 0 := by
    have : j ≤ ms j := hms.le_apply
    omega
  exact RectangleInSelectedBlock.finiteEnergy_and_orthogonality_of_selected_engulfing
    (decode_geometry ω.1) ω.2 hmne (hblock.2 (ms j)).1 hs hQ

/-- **`hharm` from `hpatch`.**  The three conjuncts of
`HarmonicCoordinateAssembly.MarkedHarmonicity` — free orthogonality on every bounded
rectangle, full-energy Dirichlet minimality with uniqueness, and pointwise vector
harmonicity — hold almost surely for the marked limit, given only the assembly's own patch
convergence input and the mass transport and (FE) moment it already carries. -/
theorem markedHarmonicity_of_patchConvergence (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hpatch : MarkedPatchConvergence ν ms) :
    MarkedHarmonicity ν ms := by
  filter_upwards [hpatch, approximantRectangleOrthogonality_clause ν hν hFE ms hms]
    with ω hp ho
  have hF : Geometry (decode ω.1) := decode_geometry ω.1
  have h1 : FullRectangleOrthogonality (decode ω.1) (markedPotential ms ω) := by
    intro Q
    refine rectangle_orthogonality_of_eventually (decode ω.1) Q
      (φ := fun j v => phi (decode ω.1) ω.2 (ms j) v)
      (Φ := markedPotential ms ω) ?_
      (hp Q.carrier (BlockInterpolantExistence.isBounded_carrier Q)) ?_
    · filter_upwards [ho Q] with j hj
      exact hj.1
    · filter_upwards [ho Q] with j hj
      exact hj.2
  exact ⟨h1, MarkedRectangleHarmonicity.fullRectangleMinimizer_of_orthogonality hF h1,
    fun v => MarkedRectangleHarmonicity.tsum_smul_sub_eq_zero_of_orthogonality hF h1 v⟩

end Marked

end MarkedRectangleOrthogonalityProducer

end ReflectedGMS
