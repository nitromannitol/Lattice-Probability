/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolantSelectionCandidate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionSolvability

/-!
# The measurable block-interpolant candidate, and `hmeas`

`Corrector/BlockInterpolantSelectionSolvability.lean` reduces the measurability input `hmeas`
of the harmonic-coordinate assembly to exactly one proposition,
`HasMeasurableBlockInterpolantCandidate`: a measurable field which, on the good event and at
a positive stage, is a block interpolant whenever one exists.  This module produces that
field, so `hmeas` closes.

The construction is the manuscript's own (`s:lem:minimizer`, `s:lem:measurablemin` and the
measurability appendix `s:app:measurable`), carried out on the fixed `ℕ`-indexing:

* **The reference datum is gated, not the graph.**  The manuscript's Dirichlet lemma assumes
  the boundary datum has finite energy; for the centroid trace that is the manuscript's
  `W`-bound, which holds only almost surely.  `gatedDatum` replaces the centroid datum by `0`
  off the per-square solvability event — measurable exactly because
  `BlockInterpolantSelectionSolvability.measurableSet_squareSolvableEvent` is proved — and
  `solvable_gatedDatum` then holds at **every** marked environment, the witness being the
  solvability witness on the event and `0` off it.
* **A measurable full-energy minimizer from solvability alone.**
  `exists_measurable_anchored_energy_minimizer_of_solvable` is
  `Corrector/MeasurableInfinitePatchMinimizer.exists_measurable_anchored_energy_minimizer`
  with the hypothesis `HasFiniteEnergy (u ω)` replaced by "some finite-energy field carries
  the trace of `u ω` on `A ω`".  This is a genuine weakening and it is what the block problem
  needs: the trace class of `u ω` and of the witness coincide, so every level statement
  transports verbatim.
* **The plane-valued patch field.**  `patchField` assembles the two coordinate minimizers,
  and `centroidTraceMinimizer_patchField` shows that on the solvability event its restriction
  to the patch is the manuscript's `CentroidTraceMinimizer` — finite vector energy, the
  centroid trace, and minimality against *every* plane-valued competitor.  Minimality
  transports by extending a competitor off the patch with `Function.extend` and the centroid
  datum, which is admissible precisely because the anchor set on the fixed index type
  contains the complement of the patch.
* **A measurable gluing.**  `BlockInterpolantExistence.glue` chooses a selected square through
  `Classical.choose`, which is not measurable.  `candidate` chooses the **first** square in a
  fixed enumeration of `SquareIndex`, so its fibres are countable Boolean combinations of the
  selection and patch-label events; `candidate_eq_glue` identifies it with `glue`, through
  `BlockInterpolantExistence.glue_eq_of_mem_patch`, which says the glued value does not depend
  on which selected square is used.

`isBlockInterpolation_candidate` then gives the specification at every marked environment all
of whose selected squares are solvable — in particular whenever a block interpolant exists at
all, by `BlockInterpolantGateReduction.patchSolvable_of_exists_isBlockInterpolation` — and
`measurable_gatedApproximant` is the conclusion:

  `∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n`,

**the input `hmeas` itself, with no hypotheses.**  `harmonicCoordinateConclusions_of_nine_inputs`
restates the assembly's reduction without it.

Note that nothing here is almost-sure: the candidate is a block interpolant at *every* marked
environment whose selected squares are solvable, and the measurability is exact, which is what
the assembly needs — `hmeas` is consumed as data by `HarmonicCoordinateAssembly.harmonicCellField`,
not only through the `AEMeasurable` clauses of the conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace ReflectedGMS.BlockInterpolantSelectionCandidate

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open EnvironmentLaws HarmonicLawIngredients
open HarmonicCoordinateAssembly GatedApproximantMeasurability
open BlockInterpolantSelectionGate BlockInterpolantGateReduction
open PatchSolvableEventMeasurability PatchLabelMeasurability
open VaryingVertexIndexing MeasurableInfinitePatchMinimizer
open AnchoredFiniteExhaustion FiniteDirichletEnergyLimit
open BlockInterpolantSelectionSolvability

/-! ### A measurable anchored minimizer from solvability of the trace problem -/

theorem hasFiniteEnergy_zero {V : Type*} (G : ReflectedWalk.ConductanceGraph V) :
    G.HasFiniteEnergy (fun _ => (0 : ℝ)) := by
  have hz : G.gradSq (fun _ => (0 : ℝ)) = fun _ : V × V => (0 : ℝ) := by
    funext p
    simp [ReflectedWalk.ConductanceGraph.gradSq]
  show Summable (G.gradSq (fun _ => (0 : ℝ)))
  rw [hz]
  exact summable_zero

/-- **The measurable full-energy anchored minimizer, from solvability of the trace problem.**

This is `Corrector/MeasurableInfinitePatchMinimizer.exists_measurable_anchored_energy_minimizer`
with `HasFiniteEnergy (u ω)` weakened to: at every `ω` *some* finite-energy field carries the
trace of `u ω` on `A ω`.  The proof is the same, with the reference field of the limit step
replaced by that witness — legitimate because the two fields have the same trace on `A ω`, so
they define the same competition class at every level and in the limit. -/
theorem exists_measurable_anchored_energy_minimizer_of_solvable
    {Ω : Type*} [MeasurableSpace Ω] {V : Type*} [Countable V]
    {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y)
    {A : Ω → Set V} (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω})
    (hanchor : ∀ ω : Ω, BoundaryAnchored (G ω) (A ω))
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x)
    (hsolv : ∀ ω : Ω, ∃ h : V → ℝ, (G ω).HasFiniteEnergy h ∧ ∀ a ∈ A ω, h a = u ω a) :
    ∃ f : Ω → V → ℝ, (∀ x : V, Measurable fun ω => f ω x) ∧
      ∀ ω : Ω,
        (G ω).HasFiniteEnergy (f ω) ∧
        (∀ a ∈ A ω, f ω a = u ω a) ∧
        (∀ w : V → ℝ, (G ω).HasFiniteEnergy w → (∀ a ∈ A ω, w a = u ω a) →
          (G ω).Energy (f ω) ≤ (G ω).Energy w) := by
  classical
  have hex : ∀ (ω : Ω) (x : V), ∃ l : List V, IsAnchorChain (G ω) (A ω) x l :=
    fun ω x => exists_isAnchorChain (G ω) (hanchor ω) x
  have hstep : ∀ n : ℕ, ∃ F : Ω → V → ℝ, (∀ x : V, Measurable fun ω => F ω x) ∧
      ∀ ω : Ω,
        (∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → F ω a = u ω a) ∧
        (∀ w : V → ℝ, (∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → w a = u ω a) →
          restrictedEnergy (G ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V) (F ω)
            ≤ restrictedEnergy (G ω)
                ((patchLevel (G ω) (A ω) n : Finset V) : Set V) w) := by
    intro n
    obtain ⟨F, -, hFeval, hF⟩ :=
      MeasurableBlockMinimizer.exists_measurable_varying_block_minimizer_anchorSet
        (G := G) hG (S := fun ω => patchLevel (G ω) (A ω) n)
        (fun t => measurableSet_patchLevel_eq hG hA hex n t)
        (A := A) hA (fun ω => boundaryAnchored_patchLevel (G ω) (fun x => hex ω x) n) hu
    exact ⟨F, hFeval, fun ω => ⟨(hF ω).1, (hF ω).2.2.1⟩⟩
  choose F hFmeas hF using hstep
  have hlim : ∀ ω : Ω, ∃ g : V → ℝ,
      (∀ x : V, Tendsto (fun n => F n ω x) atTop (𝓝 (g x))) ∧
      (G ω).HasFiniteEnergy g ∧ (∀ a ∈ A ω, g a = u ω a) ∧
      ∀ w : V → ℝ, (G ω).HasFiniteEnergy w → (∀ a ∈ A ω, w a = u ω a) →
        (G ω).Energy g ≤ (G ω).Energy w := by
    intro ω
    obtain ⟨h, hhE, hhtr⟩ := hsolv ω
    have htrace' : ∀ n : ℕ, ∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → F n ω a = h a := by
      intro n a ha haL
      rw [(hF n ω).1 a ha haL, hhtr a ha]
    have hmin' : ∀ n : ℕ, ∀ w : V → ℝ,
        (∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → w a = h a) →
        restrictedEnergy (G ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V) (F n ω)
          ≤ restrictedEnergy (G ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V) w := by
      intro n w hw
      refine (hF n ω).2 w fun a ha haL => ?_
      rw [hw a ha haL, ← hhtr a ha]
    obtain ⟨g, hgconv, hgE, hgtr, hgmin⟩ :=
      FiniteMinimizerPointwiseConvergence.exists_tendsto_pointwise_anchored_minimizer
        (G ω) (A := A ω) (u := h) (L := fun n => patchLevel (G ω) (A ω) n)
        (F := fun n => F n ω) (hanchor ω) hhE (patchLevel_mono (G ω))
        (fun x => exists_mem_patchLevel (G ω) (fun y => hex ω y) x) htrace' hmin'
    refine ⟨g, hgconv, hgE, ?_, ?_⟩
    · intro a ha
      rw [hgtr a ha, hhtr a ha]
    · intro w hwE hwtr
      refine hgmin w hwE fun a ha => ?_
      rw [hwtr a ha, ← hhtr a ha]
  choose g hgconv hgE hgtrace hgmin using hlim
  have hgmeas : ∀ x : V, Measurable fun ω => g ω x := by
    intro x
    refine measurable_of_tendsto_metrizable (f := fun n ω => F n ω x)
      (fun n => hFmeas n x) ?_
    exact tendsto_pi_nhds.2 fun ω => hgconv ω x
  exact ⟨g, hgmeas, fun ω => ⟨hgE ω, hgtrace ω, hgmin ω⟩⟩

/-! ### The gated centroid datum -/

/-- The centroid boundary datum of a square, switched off where the per-square Dirichlet
problem is not solvable.  Measurable because the solvability event is. -/
noncomputable def gatedDatum (s : SquareIndex) (i : Fin 2) (ω : MarkedEnvironment) (n : ℕ) :
    ℝ :=
  if ω ∈ SquareSolvableEvent s then centroidDatum i ω n else 0

theorem measurable_gatedDatum (s : SquareIndex) (i : Fin 2) (n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedDatum s i ω n :=
  Measurable.ite (measurableSet_squareSolvableEvent s) (measurable_centroidDatum i n)
    measurable_const

theorem gatedDatum_of_mem {s : SquareIndex} {i : Fin 2} {ω : MarkedEnvironment}
    (hω : ω ∈ SquareSolvableEvent s) (n : ℕ) :
    gatedDatum s i ω n = centroidDatum i ω n := if_pos hω

/-- **The gated trace problem is solvable at every marked environment.**  On the solvability
event the witness is the one the event provides; off it the datum is `0` and the zero field
is a witness. -/
theorem solvable_gatedDatum (s : SquareIndex) (i : Fin 2) (ω : MarkedEnvironment) :
    ∃ h : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy h ∧
      ∀ a ∈ anchorLabels s ω, h a = gatedDatum s i ω a := by
  by_cases hω : ω ∈ SquareSolvableEvent s
  · have hmem : ω ∈ NatSolvableEvent s i := by
      have h := hω
      rw [squareSolvableEvent_eq_iInter s] at h
      exact Set.mem_iInter.1 h i
    obtain ⟨h, hhE, hhtr⟩ := hmem
    refine ⟨h, hhE, fun a ha => ?_⟩
    rw [hhtr a ha, gatedDatum_of_mem hω]
  · refine ⟨fun _ => 0, hasFiniteEnergy_zero _, fun a _ => ?_⟩
    show (0 : ℝ) = gatedDatum s i ω a
    rw [gatedDatum, if_neg hω]

/-! ### The coordinate minimizers of every square -/

theorem exists_measurable_patchMinimizers :
    ∃ Θ : SquareIndex → Fin 2 → MarkedEnvironment → ℕ → ℝ,
      (∀ (s : SquareIndex) (i : Fin 2) (n : ℕ),
        Measurable fun ω : MarkedEnvironment => Θ s i ω n) ∧
      ∀ (s : SquareIndex) (i : Fin 2) (ω : MarkedEnvironment),
        (patchGraph s ω).HasFiniteEnergy (Θ s i ω) ∧
        (∀ a ∈ anchorLabels s ω, Θ s i ω a = gatedDatum s i ω a) ∧
        (∀ w : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy w →
          (∀ a ∈ anchorLabels s ω, w a = gatedDatum s i ω a) →
          (patchGraph s ω).Energy (Θ s i ω) ≤ (patchGraph s ω).Energy w) := by
  have hstep : ∀ (s : SquareIndex) (i : Fin 2), ∃ Θ : MarkedEnvironment → ℕ → ℝ,
      (∀ n : ℕ, Measurable fun ω : MarkedEnvironment => Θ ω n) ∧
      ∀ ω : MarkedEnvironment,
        (patchGraph s ω).HasFiniteEnergy (Θ ω) ∧
        (∀ a ∈ anchorLabels s ω, Θ ω a = gatedDatum s i ω a) ∧
        (∀ w : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy w →
          (∀ a ∈ anchorLabels s ω, w a = gatedDatum s i ω a) →
          (patchGraph s ω).Energy (Θ ω) ≤ (patchGraph s ω).Energy w) := by
    intro s i
    exact exists_measurable_anchored_energy_minimizer_of_solvable
      (G := fun ω : MarkedEnvironment => patchGraph s ω)
      (fun x y => measurable_patchGraph_c s x y)
      (A := fun ω : MarkedEnvironment => anchorLabels s ω)
      (fun x => measurableSet_mem_anchorLabels s x)
      (fun ω => boundaryAnchored_patchGraph s ω)
      (u := fun ω : MarkedEnvironment => fun n : ℕ => gatedDatum s i ω n)
      (fun n => measurable_gatedDatum s i n)
      (fun ω => solvable_gatedDatum s i ω)
  choose Θ hΘmeas hΘ using hstep
  exact ⟨Θ, fun s i n => hΘmeas s i n, fun s i ω => hΘ s i ω⟩

/-! ### The plane-valued patch field -/

variable (Θ : SquareIndex → Fin 2 → MarkedEnvironment → ℕ → ℝ)

/-- The plane-valued minimizer of one square, assembled from its two coordinates. -/
noncomputable def patchField (s : SquareIndex) (ω : MarkedEnvironment) (n : ℕ) : Plane :=
  (WithLp.toLp 2 (fun i : Fin 2 => Θ s i ω n) : Plane)

theorem measurable_patchField
    (hΘmeas : ∀ (s : SquareIndex) (i : Fin 2) (n : ℕ),
      Measurable fun ω : MarkedEnvironment => Θ s i ω n)
    (s : SquareIndex) (n : ℕ) :
    Measurable fun ω : MarkedEnvironment => patchField Θ s ω n := by
  have h : Measurable fun ω : MarkedEnvironment => (fun i : Fin 2 => Θ s i ω n) :=
    Measurable.of_eval fun i => hΘmeas s i n
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp h

/-- **On the solvability event the patch field is the manuscript's centroid-trace
minimizer.** -/
theorem centroidTraceMinimizer_patchField
    (hΘ : ∀ (s : SquareIndex) (i : Fin 2) (ω : MarkedEnvironment),
      (patchGraph s ω).HasFiniteEnergy (Θ s i ω) ∧
      (∀ a ∈ anchorLabels s ω, Θ s i ω a = gatedDatum s i ω a) ∧
      (∀ w : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy w →
        (∀ a ∈ anchorLabels s ω, w a = gatedDatum s i ω a) →
        (patchGraph s ω).Energy (Θ s i ω) ≤ (patchGraph s ω).Energy w))
    (s : SquareIndex) (ω : MarkedEnvironment) (hω : ω ∈ SquareSolvableEvent s) :
    CentroidTraceMinimizer (decode ω.1) (square ω.2 s)
      (fun v : Vertex ω.1.val => patchField Θ s ω v.val) := by
  have hi := isFullEmbedding_patchGraph s ω
  have hcoordfin : ∀ i : Fin 2,
      (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1) (square ω.2 s))).HasFiniteEnergy
        (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
          patchField Θ s ω v.1.val i) :=
    fun i => (hi.hasFiniteEnergy_comp_iff (Θ s i ω)).2 (hΘ s i ω).1
  refine ⟨vectorEnergy_lt_top_of_coord _ hcoordfin, ?_, ?_⟩
  · intro v hv
    have hmem : (v.1.val : ℕ) ∈ anchorLabels s ω :=
      Or.inl ((mem_boundaryLabels_iff s ω v.1).1 hv)
    refine PiLp.ext fun i => ?_
    show Θ s i ω (v.1.val : ℕ) = cellCentroid (decode ω.1) v.1 i
    rw [(hΘ s i ω).2.1 _ hmem, gatedDatum_of_mem hω]
    exact congrArg (fun z : Plane => z i) (slotCentroid_eq_cellCentroid ω.1 v.1)
  · intro w hwtr
    show vectorEnergy (restrictGraph (decode ω.1).graph
          (patchVertices (decode ω.1) (square ω.2 s)))
            (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
              patchField Θ s ω (v.1.val : ℕ))
        ≤ vectorEnergy (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))) w
    by_cases hinf : vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1) (square ω.2 s))) w = ∞
    · rw [hinf]
      exact le_top
    · have hlt : vectorEnergy (restrictGraph (decode ω.1).graph
          (patchVertices (decode ω.1) (square ω.2 s))) w < ∞ :=
        lt_top_iff_ne_top.2 hinf
      have hwc : ∀ i : Fin 2,
          (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))).HasFiniteEnergy
            (fun v : patchVertices (decode ω.1) (square ω.2 s) => w v i) :=
        fun i => hasFiniteEnergy_coord _ hlt i
      -- extend each coordinate competitor off the patch by the centroid datum
      set W : Fin 2 → ℕ → ℝ := fun i =>
        Function.extend (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ))
          (fun v : patchVertices (decode ω.1) (square ω.2 s) => w v i)
          (fun n : ℕ => centroidDatum i ω n) with hWdef
      have hWres : ∀ i : Fin 2,
          (fun v : patchVertices (decode ω.1) (square ω.2 s) => W i (v.1.val : ℕ))
            = fun v : patchVertices (decode ω.1) (square ω.2 s) => w v i := fun i =>
        funext fun v => hi.injective.extend_apply _ _ v
      have hWfin : ∀ i : Fin 2, (patchGraph s ω).HasFiniteEnergy (W i) := by
        intro i
        refine (hi.hasFiniteEnergy_comp_iff (W i)).1 ?_
        show (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))).HasFiniteEnergy
          (fun v : patchVertices (decode ω.1) (square ω.2 s) => W i (v.1.val : ℕ))
        rw [hWres i]
        exact hwc i
      have hWtr : ∀ i : Fin 2, ∀ a ∈ anchorLabels s ω, W i a = gatedDatum s i ω a := by
        intro i a ha
        rw [gatedDatum_of_mem hω]
        by_cases haP : a ∈ patchLabels s ω
        · have hsome : (ω.1.val.1 a).isSome := isSome_of_mem_patchLabels haP
          have hvS : (⟨a, hsome⟩ : Vertex ω.1.val)
              ∈ patchVertices (decode ω.1) (square ω.2 s) :=
            (mem_patchLabels_iff s ω ⟨a, hsome⟩).2 haP
          have hbL : a ∈ boundaryLabels s ω := by
            rcases ha with hb | hnp
            · exact hb
            · exact absurd haP hnp
          have hbv : (⟨a, hsome⟩ : Vertex ω.1.val)
              ∈ boundaryVertices (decode ω.1) (square ω.2 s) :=
            (mem_boundaryLabels_iff s ω ⟨a, hsome⟩).2 hbL
          have hval : W i a
              = w (⟨⟨a, hsome⟩, hvS⟩ : patchVertices (decode ω.1) (square ω.2 s)) i :=
            hi.injective.extend_apply _ _
              (⟨⟨a, hsome⟩, hvS⟩ : patchVertices (decode ω.1) (square ω.2 s))
          rw [hval, hwtr ⟨⟨a, hsome⟩, hvS⟩ hbv]
          exact (congrArg (fun z : Plane => z i)
            (slotCentroid_eq_cellCentroid ω.1 ⟨a, hsome⟩)).symm
        · show W i a = centroidDatum i ω a
          rw [hWdef]
          refine Function.extend_apply' _ (fun n : ℕ => centroidDatum i ω n) a ?_
          rintro ⟨v, hv⟩
          exact haP (hv ▸ (mem_patchLabels_iff s ω v.1).1 v.2)
      have hEcoord : ∀ i : Fin 2,
          (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))).Energy
              (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
                patchField Θ s ω v.1.val i)
            ≤ (restrictGraph (decode ω.1).graph
                (patchVertices (decode ω.1) (square ω.2 s))).Energy
              (fun v : patchVertices (decode ω.1) (square ω.2 s) => w v i) := by
        intro i
        have h1 : (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))).Energy
              (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
                patchField Θ s ω v.1.val i)
            = (patchGraph s ω).Energy (Θ s i ω) := hi.Energy_comp (Θ s i ω)
        have h2 : (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))).Energy
              (fun v : patchVertices (decode ω.1) (square ω.2 s) => W i (v.1.val : ℕ))
            = (patchGraph s ω).Energy (W i) := hi.Energy_comp (W i)
        rw [h1, ← hWres i, h2]
        exact (hΘ s i ω).2.2 (W i) (hWfin i) (hWtr i)
      have hLsum : vectorEnergy (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s)))
              (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
                patchField Θ s ω (v.1.val : ℕ))
          = ENNReal.ofReal (∑ i : Fin 2,
              (restrictGraph (decode ω.1).graph
                (patchVertices (decode ω.1) (square ω.2 s))).Energy
                  (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
                    patchField Θ s ω (v.1.val : ℕ) i)) :=
        vectorEnergy_eq_ofReal_sum _ hcoordfin
      have hRsum : vectorEnergy (restrictGraph (decode ω.1).graph
            (patchVertices (decode ω.1) (square ω.2 s))) w
          = ENNReal.ofReal (∑ i : Fin 2,
              (restrictGraph (decode ω.1).graph
                (patchVertices (decode ω.1) (square ω.2 s))).Energy
                  (fun v : patchVertices (decode ω.1) (square ω.2 s) => w v i)) :=
        vectorEnergy_eq_ofReal_sum _ hwc
      rw [hLsum, hRsum]
      exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun i _ => hEcoord i)

/-! ### The measurable gluing -/

instance nonempty_squareIndex : Nonempty SquareIndex := ⟨(0, fun _ => 0)⟩

/-- A fixed enumeration of the countably many dyadic square indices. -/
noncomputable def sqEnum : ℕ → SquareIndex := (exists_surjective_nat SquareIndex).choose

theorem sqEnum_surjective : Function.Surjective sqEnum :=
  (exists_surjective_nat SquareIndex).choose_spec

/-- The event that the `j`-th square of the enumeration is selected at stage `m` and owns the
label `n`. -/
def ownedEvent (m j n : ℕ) : Set MarkedEnvironment :=
  SelectedEvent m (sqEnum j) ∩ patchLabelEvent (sqEnum j) n

theorem measurableSet_ownedEvent (m j n : ℕ) : MeasurableSet (ownedEvent m j n) :=
  (measurableSet_selectedEvent m (sqEnum j)).inter (measurableSet_patchLabelEvent (sqEnum j) n)

/-- **The measurably glued block-interpolant candidate.**  At a label owned by some selected
square, the patch field of the *first* such square in the fixed enumeration; elsewhere the
centroid. -/
noncomputable def candidate (m : ℕ) (ω : MarkedEnvironment) (n : ℕ) : Plane :=
  if h : ∃ j : ℕ, ω ∈ ownedEvent m j n then patchField Θ (sqEnum (Nat.find h)) ω n
  else slotCentroid ω.1 n

/-- The fibre of the enumeration index chosen at a label. -/
def findEvent (m j n : ℕ) : Set MarkedEnvironment :=
  ownedEvent m j n ∩ ⋂ k : ℕ, ⋂ _ : k < j, (ownedEvent m k n)ᶜ

theorem measurableSet_findEvent (m j n : ℕ) : MeasurableSet (findEvent m j n) :=
  (measurableSet_ownedEvent m j n).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (measurableSet_ownedEvent m k n).compl)

theorem measurable_candidate
    (hΘmeas : ∀ (s : SquareIndex) (i : Fin 2) (n : ℕ),
      Measurable fun ω : MarkedEnvironment => Θ s i ω n) (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => candidate Θ m ω n := by
  intro B hB
  have hEq : (fun ω : MarkedEnvironment => candidate Θ m ω n) ⁻¹' B
      = (⋃ j : ℕ, (findEvent m j n ∩
            ((fun ω : MarkedEnvironment => patchField Θ (sqEnum j) ω n) ⁻¹' B)))
        ∪ ((⋃ j : ℕ, ownedEvent m j n)ᶜ ∩
            ((fun ω : MarkedEnvironment => slotCentroid ω.1 n) ⁻¹' B)) := by
    refine Set.ext fun ω => ?_
    by_cases h : ∃ j : ℕ, ω ∈ ownedEvent m j n
    · have hval : candidate Θ m ω n = patchField Θ (sqEnum (Nat.find h)) ω n := by
        rw [candidate, dif_pos h]
      constructor
      · intro hmem
        refine Or.inl (Set.mem_iUnion.2 ⟨Nat.find h, ⟨Nat.find_spec h, ?_⟩, ?_⟩)
        · exact Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun hk => Nat.find_min h hk
        · show patchField Θ (sqEnum (Nat.find h)) ω n ∈ B
          rw [← hval]
          exact hmem
      · intro hmem
        rcases hmem with hmem | hmem
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
          have hfind : Nat.find h = j := by
            refine Nat.find_eq_iff h |>.2 ⟨hj.1.1, fun k hk => ?_⟩
            exact Set.mem_iInter.1 (Set.mem_iInter.1 hj.1.2 k) hk
          show candidate Θ m ω n ∈ B
          rw [hval, hfind]
          exact hj.2
        · exact absurd (Set.mem_iUnion.2 h) hmem.1
    · have hval : candidate Θ m ω n = slotCentroid ω.1 n := by
        rw [candidate, dif_neg h]
      constructor
      · intro hmem
        refine Or.inr ⟨fun hc => h (Set.mem_iUnion.1 hc), ?_⟩
        show slotCentroid ω.1 n ∈ B
        rw [← hval]
        exact hmem
      · intro hmem
        rcases hmem with hmem | hmem
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
          exact absurd ⟨j, hj.1.1⟩ h
        · show candidate Θ m ω n ∈ B
          rw [hval]
          exact hmem.2
  rw [hEq]
  refine MeasurableSet.union (MeasurableSet.iUnion fun j => ?_) ?_
  · exact (measurableSet_findEvent m j n).inter
      (measurable_patchField Θ hΘmeas (sqEnum j) n hB)
  · exact ((MeasurableSet.iUnion fun j => measurableSet_ownedEvent m j n).compl).inter
      (((measurable_slotCentroid n).comp measurable_fst) hB)

/-! ### The candidate is the glued interpolant -/

theorem candidate_eq_glue (m : ℕ) (ω : MarkedEnvironment)
    (hg : ∀ t : SquareIndex, Selected (decode ω.1) ω.2 (m : ℝ) t →
      CentroidTraceMinimizer (decode ω.1) (square ω.2 t)
        (fun v : Vertex ω.1.val => patchField Θ t ω v.val)) :
    (fun v : Vertex ω.1.val => candidate Θ m ω v.val)
      = BlockInterpolantExistence.glue (decode ω.1) ω.2 (m : ℝ)
          (fun t : SquareIndex => fun v : Vertex ω.1.val => patchField Θ t ω v.val) := by
  funext v
  by_cases h : ∃ j : ℕ, ω ∈ ownedEvent m j v.val
  · have hval : candidate Θ m ω v.val
        = patchField Θ (sqEnum (Nat.find h)) ω v.val := by
      rw [candidate, dif_pos h]
    have hspec := Nat.find_spec h
    have hs : Selected (decode ω.1) ω.2 (m : ℝ) (sqEnum (Nat.find h)) := hspec.1
    have hv : v ∈ patchVertices (decode ω.1) (square ω.2 (sqEnum (Nat.find h))) :=
      (mem_patchLabels_iff (sqEnum (Nat.find h)) ω v).2 hspec.2
    rw [hval, BlockInterpolantExistence.glue_eq_of_mem_patch (decode ω.1)
      (decode_geometry ω.1).1 ω.2 (m : ℝ) hg hs hv]
  · have hval : candidate Θ m ω v.val = slotCentroid ω.1 v.val := by
      rw [candidate, dif_neg h]
    have hnone : ¬ ∃ t : SquareIndex, Selected (decode ω.1) ω.2 (m : ℝ) t ∧
        v ∈ patchVertices (decode ω.1) (square ω.2 t) := by
      rintro ⟨t, ht, hvt⟩
      obtain ⟨j, rfl⟩ := sqEnum_surjective t
      exact h ⟨j, ht, (mem_patchLabels_iff (sqEnum j) ω v).1 hvt⟩
    rw [hval, BlockInterpolantExistence.glue_of_not_exists (decode ω.1) ω.2 (m : ℝ) _ hnone]
    exact slotCentroid_eq_cellCentroid ω.1 v

/-- **The candidate satisfies the block-interpolation specification** at every marked
environment all of whose selected squares are solvable. -/
theorem isBlockInterpolation_candidate
    (hΘ : ∀ (s : SquareIndex) (i : Fin 2) (ω : MarkedEnvironment),
      (patchGraph s ω).HasFiniteEnergy (Θ s i ω) ∧
      (∀ a ∈ anchorLabels s ω, Θ s i ω a = gatedDatum s i ω a) ∧
      (∀ w : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy w →
        (∀ a ∈ anchorLabels s ω, w a = gatedDatum s i ω a) →
        (patchGraph s ω).Energy (Θ s i ω) ≤ (patchGraph s ω).Energy w))
    {m : ℕ} (hm : m ≠ 0) (ω : MarkedEnvironment)
    (hsolv : ∀ t : SquareIndex, Selected (decode ω.1) ω.2 (m : ℝ) t →
      ω ∈ SquareSolvableEvent t) :
    IsBlockInterpolation (decode ω.1) ω.2 m
      fun v : Vertex ω.1.val => candidate Θ m ω v.val := by
  have hg : ∀ t : SquareIndex, Selected (decode ω.1) ω.2 (m : ℝ) t →
      CentroidTraceMinimizer (decode ω.1) (square ω.2 t)
        (fun v : Vertex ω.1.val => patchField Θ t ω v.val) := fun t ht =>
    centroidTraceMinimizer_patchField Θ hΘ t ω (hsolv t ht)
  rw [candidate_eq_glue Θ m ω hg, IsBlockInterpolation, if_neg hm]
  exact ⟨fun v hv => BlockInterpolantExistence.glue_eq_centroid_of_mem_skeleton
      (decode ω.1) (decode_geometry ω.1).1 ω.2 (m : ℝ) hg hv,
    fun t ht => BlockInterpolantExistence.centroidTraceMinimizer_glue
      (decode ω.1) (decode_geometry ω.1).1 ω.2 (m : ℝ) hg ht⟩

/-- Where a block interpolant exists, every selected square is solvable. -/
theorem squareSolvable_of_exists_isBlockInterpolation {m : ℕ} (hm : m ≠ 0)
    (ω : MarkedEnvironment)
    (hex : ∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f)
    (t : SquareIndex) (ht : Selected (decode ω.1) ω.2 (m : ℝ) t) :
    ω ∈ SquareSolvableEvent t :=
  patchSolvable_of_exists_isBlockInterpolation (decode ω.1) ω.2 hm hex t ht

/-! ### `hmeas` -/

/-- **A measurable block-interpolant candidate exists.**  This is the residual named by
`BlockInterpolantSelectionSolvability.HasMeasurableBlockInterpolantCandidate`. -/
theorem hasMeasurableBlockInterpolantCandidate :
    HasMeasurableBlockInterpolantCandidate := by
  obtain ⟨Θ, hΘmeas, hΘ⟩ := exists_measurable_patchMinimizers
  refine ⟨fun m => candidate Θ m, fun m n => measurable_candidate Θ hΘmeas m n, ?_⟩
  intro m hm ω _ hex
  exact isBlockInterpolation_candidate Θ hΘ hm ω
    (squareSolvable_of_exists_isBlockInterpolation hm ω hex)

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly, with no
hypotheses.** -/
theorem measurable_gatedApproximant (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n :=
  hmeas_of_measurableBlockInterpolantCandidate hasMeasurableBlockInterpolantCandidate m n

end ReflectedGMS.BlockInterpolantSelectionCandidate
