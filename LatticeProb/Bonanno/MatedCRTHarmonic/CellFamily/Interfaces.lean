/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.Interfaces at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ScaledGridControl
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite

/-!
# Intermediate random-cell and [18] interfaces for the scaled-grid estimate

These propositions describe inputs for the SLE/LQG and probabilistic arguments.
`Lemma27CellDiam` states the cell-diameter conclusion of [18] Lemma 2.7;
`Lemma38AnnulusHit` states the annulus-hitting conclusion of [18] Lemma 3.8.
`RandomCellFamily` is the mesh-indexed random cellular embedding interface.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u v

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

/-- A random family of mesh-`2⁻ᵏ` cellular embeddings of the structure graphs. -/
structure RandomCellFamily where
  Ω : Type*
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  E : ℕ → Ω → Type*
  G : ∀ k ω, LFMultigraph ℤ (E k ω)
  H : ∀ k ω, CellularEmbedding (G k ω) (0 : ℤ)

instance randomCellFamilyMeasurableSpace (F : RandomCellFamily) : MeasurableSpace F.Ω := F.mΩ

instance randomCellFamilyProbability (F : RandomCellFamily) : IsProbabilityMeasure F.P := F.prob

/-- Almost-sure connectedness of every mesh graph. This follows for the mated-CRT graph from
its definition and `matedCRT_graph_connected`; the cell-model construction
transports it through the identification of the cell graph with the mated-CRT graph. -/
def GraphConnected (F : RandomCellFamily) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, (F.G k ω).adj.Connected

/-- Almost-sure Route M separation for each random cell configuration, in the form actually used by the scaled-grid estimate:
when cells meeting the twice-radius closed disk are small relative to `r`, walks following the template disconnect.
The producer is `RouteM.templateSeparation_matedCRT` (TFΨ/TFD/TFJ/TFR), given `PeanosphereG0` and the stated
small-cell hypothesis. The polar loop is `polarTemplate_loop_affine`. -/
def TemplateSeparation (F : RandomCellFamily) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, ∀ z r, 0 < r →
    (∀ x, ((F.H k ω).cell x ∩ closedBall z (2 * r)).Nonempty →
      diam ((F.H k ω).cell x) ≤ r / 1000) →
    (F.H k ω).TemplateSeparation z r

/-- The mesh `ε_k = 2⁻ᵏ` used for the random maps. -/
def mesh (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

/-- **Adjacency-only** identification of the family graph with the mated-CRT graph on the same outcome. Its producer
is the cell-model graph identification, transported from unit mesh by the edge equivalence in
`MesoModel.TransferScaling`. The adjacency relation forgets loops and multiplicities, so this determines neither walk laws nor degrees nor looplessness;
it suffices only for `GraphConnected`, (CAL) and `TemplateSeparation`. Every walk- or degree-dependent use needs the
multigraph identity `MatedCRTMultigraphIdentification`, which implies this one
(`MatedCRTMultigraphIdentification.graphIdentification`). -/
def MatedCRTGraphIdentification (F : RandomCellFamily) (bm : F.Ω → MatedCRT.Path2) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, ∃ h : MatedCRT.IsLocallyFinite (mesh k) (bm ω),
    ∀ x y, (F.G k ω).adj.Adj x y ↔
      (MatedCRT.graph (mesh k) (bm ω) h).adj.Adj x y

/-- Identification of the family graph with the mated-CRT **multigraph** on the same outcome: almost surely, the
mesh-`2⁻ᵏ` edge type is `MatedCRT.Edge (mesh k) (bm ω)` and the family multigraph *is* `MatedCRT.graph (mesh k) (bm ω)`
(same edges, same ends, same multiplicities).
Unlike the adjacency identification it determines the walk
laws ([18] Lemma 3.8, the itinerary, `ScaledGridControl`, the joint-scaling event identity), `deg` (`uDens` in
Proposition 2.10) and looplessness (`MatedCRTMultigraphIdentification.loopless`). The cell-model instance
defines its mesh graphs as the mated-CRT multigraphs of [18] (1.1),
so that the identity holds by construction; the unit-to-mesh transport of the multigraph is
`MesoModel.graphCast_eq_unitRescalePath`. -/
def MatedCRTMultigraphIdentification (F : RandomCellFamily) (bm : F.Ω → MatedCRT.Path2) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, ∃ (hE : F.E k ω = MatedCRT.Edge (mesh k) (bm ω))
    (hlf : MatedCRT.IsLocallyFinite (mesh k) (bm ω)),
    cast (congrArg (LFMultigraph ℤ) hE) (F.G k ω) = MatedCRT.graph (mesh k) (bm ω) hlf

/-- Adjacency is transported along a `cast` identity of multigraphs over equal edge types. -/
theorem lfMultigraph_adj_iff_of_cast {V : Type u} {E E' : Type v} (hE : E = E')
    (G : LFMultigraph V E) (G' : LFMultigraph V E')
    (h : cast (congrArg (LFMultigraph V) hE) G = G') (x y : V) :
    G.adj.Adj x y ↔ G'.adj.Adj x y := by
  subst hE
  subst h
  exact Iff.rfl

/-- Absence of loops is transported along a `cast` identity of multigraphs over equal edge types. -/
theorem lfMultigraph_src_ne_tgt_of_cast {V : Type u} {E E' : Type v} (hE : E = E')
    (G : LFMultigraph V E) (G' : LFMultigraph V E')
    (h : cast (congrArg (LFMultigraph V) hE) G = G')
    (hloop : ∀ e : E', G'.src e ≠ G'.tgt e) : ∀ e : E, G.src e ≠ G.tgt e := by
  subst hE
  subst h
  exact hloop

/-- The mated-CRT multigraph has no loops: every edge `e` of `MatedCRT.graph` has `src e < tgt e`
(frozen `MatedCRT.IsEdge`). -/
theorem matedCRT_graph_src_ne_tgt (ε : ℝ) (path : MatedCRT.Path2)
    (h : MatedCRT.IsLocallyFinite ε path) (e : MatedCRT.Edge ε path) :
    (MatedCRT.graph ε path h).src e ≠ (MatedCRT.graph ε path h).tgt e :=
  ne_of_lt e.2.1

namespace MatedCRTMultigraphIdentification

variable {F : RandomCellFamily} {bm : F.Ω → MatedCRT.Path2}

/-- The adjacency consequence of the multigraph identification. -/
theorem adj_iff (h : MatedCRTMultigraphIdentification F bm) (k : ℕ) :
    ∀ᵐ ω ∂F.P, ∃ hlf : MatedCRT.IsLocallyFinite (mesh k) (bm ω),
      ∀ x y, (F.G k ω).adj.Adj x y ↔ (MatedCRT.graph (mesh k) (bm ω) hlf).adj.Adj x y := by
  filter_upwards [h k] with ω hω
  obtain ⟨hE, hlf, hG⟩ := hω
  exact ⟨hlf, lfMultigraph_adj_iff_of_cast hE (F.G k ω) _ hG⟩

/-- The multigraph identification implies the adjacency-only one. -/
theorem graphIdentification (h : MatedCRTMultigraphIdentification F bm) :
    MatedCRTGraphIdentification F bm :=
  fun k => h.adj_iff k

/-- Almost surely the family multigraphs have no loops; this supplies `GraphLoopless F`. -/
theorem loopless (h : MatedCRTMultigraphIdentification F bm) (k : ℕ) :
    ∀ᵐ ω ∂F.P, ∀ e : F.E k ω, (F.G k ω).src e ≠ (F.G k ω).tgt e := by
  filter_upwards [h k] with ω hω
  obtain ⟨hE, hlf, hG⟩ := hω
  exact lfMultigraph_src_ne_tgt_of_cast hE (F.G k ω) _ hG
    (matedCRT_graph_src_ne_tgt (mesh k) (bm ω) hlf)

end MatedCRTMultigraphIdentification

/-- The Route M inputs for the mesh-indexed mated-CRT cells: the Peanosphere bundle and G0 (`SideStrict`), together
with identification of each family graph and cell map with the mated-CRT graph and its SLE/LQG cells. The
Peanosphere/G0 input is produced by the mating-of-trees layer; the cell identification is the cell-model
coupling. -/
def PeanosphereG0 (F : RandomCellFamily) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, ∃ (path : MatedCRT.Path2) (η : ℝ → ℂ)
    (h : MatedCRT.IsLocallyFinite (mesh k) path)
    (H' : CellularEmbedding (MatedCRT.graph (mesh k) path h) 0),
      RouteM.Peanosphere path η ∧ RouteM.SideStrict (mesh k) path ∧
      (∀ x y, (F.G k ω).adj.Adj x y ↔ (MatedCRT.graph (mesh k) path h).adj.Adj x y) ∧
      (∀ x, (F.H k ω).cell x = H'.cell x) ∧
      ∀ x, H'.cell x = η '' Set.Icc (mesh k * ((x : ℝ) - 1)) (mesh k * x)

/-- The first, cell-diameter event in the scaled-grid estimate. -/
def DiameterGood (F : RandomCellFamily) (k : ℕ) (q ρ : ℝ) : Set F.Ω :=
  {ω | ∀ x, ((F.H k ω).cell x ∩ closedBall (0 : ℂ) ρ).Nonempty →
    diam ((F.H k ω).cell x) ≤ mesh k ^ q}

/-- Center of an integer grid triple at mesh `ε^χ`. -/
def gridCenter (ε χ : ℝ) (t : ℤ × ℤ × ℤ) : ℂ :=
  ((ε ^ χ : ℝ) : ℂ) * ((t.1 : ℂ) + (t.2.1 : ℂ) * Complex.I)

/-- Radius coordinate of an integer grid triple at mesh `ε^χ`. -/
def gridRadius (ε χ : ℝ) (t : ℤ × ℤ × ℤ) : ℝ := ε ^ χ * t.2.2

/-- A walk hits the inner sphere before the outer sphere. -/
def HitsBefore (J : ℤ → Set ℂ) (z : ℂ) (s r : ℝ) (X : ℕ → ℤ) : Prop :=
  Markov.hitTime (verticesMeeting J (sphere z (s * r))) X <
    Markov.hitTime (verticesMeeting J (sphere z r)) X

/-- Interface conclusion of [18] Lemma 2.7: with polynomially high probability, every cell meeting the fixed
Euclidean disk has diameter at most `ε_k^q`. This follows from
`GMSLemma27.lemma27CellDiam_of_cellModel`. The corrected argument
consumes the bad-event form `Lemma27CellDiamBad` instead (produced by `CellScaling.lemma27CellDiamBad_of_cellModel`). -/
def Lemma27CellDiam (F : RandomCellFamily) (q ρ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ k,
    F.P {ω | ∀ x, ((F.H k ω).cell x ∩ closedBall (0 : ℂ) ρ).Nonempty →
      diam ((F.H k ω).cell x) ≤ mesh k ^ q} ≥ 1 - ENNReal.ofReal (C * mesh k ^ α)

/-- Interface conclusion of corrected [18] Lemma 3.8: with polynomially high probability, uniformly over disk
centres and radii in the stated range, every start within four inner radii hits the inner sphere before the outer
sphere with the displayed lower probability. The event below is an uncountable intersection over `s`, not known to be
measurable; the probability statements about it are therefore stated as outer-measure bounds on its complement
(`Lemma38AnnulusHitBad`). `Lemma38AnnulusHit` (good-event form, identical to the one-scale argument's
`Lemma38AnnulusHitFixed`) is not used by the bad-event argument. -/
def Lemma38EnvironmentGood (F : RandomCellFamily) (k : ℕ) (z : ℂ) (r β₈ A₈ : ℝ) : Set F.Ω :=
  {ω | ∀ s ∈ Set.Icc (mesh k ^ β₈) (1 / 10),
    ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s * r)),
      ENNReal.ofReal (1 - A₈ / Real.sqrt (Real.log s⁻¹)) ≤
        (F.G k ω).walkLaw x {ω' | HitsBefore (F.H k ω).cell z s r
          ((F.G k ω).vertexPath ω')}}

def Lemma38AnnulusHit (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ α₈ : ℝ, 0 < α₈ ∧ ∃ β₈ : ℝ, 0 < β₈ ∧ ∃ A₈ C₈ : ℝ,
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ β₈ ≤ r → r ≤ ρ → ball z r ⊆ ball (0 : ℂ) ρ →
      F.P {ω | ∀ s ∈ Set.Icc (mesh k ^ β₈) (1 / 10),
        ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s * r)),
          ENNReal.ofReal (1 - A₈ / Real.sqrt (Real.log s⁻¹)) ≤
            (F.G k ω).walkLaw x {ω' | HitsBefore (F.H k ω).cell z s r
              ((F.G k ω).vertexPath ω')}} ≥ 1 - ENNReal.ofReal (C₈ * mesh k ^ α₈)

/-- The pathwise conclusion of the corrected scaled-grid estimate itinerary: a finite walk prefix whose cell intervals
follow a similarity-rotated polar template and whose cells remain in a narrow annulus. The separation producer is
`TemplateSeparation`; its Route M proof uses `polarTemplate_loop_affine`.
The itinerary event is built by the waypoint construction. -/
def PolarTemplateItinerary {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) (z : ℂ) (r : ℝ) (X : ℕ → ℤ) : Prop :=
  ∃ n : ℕ, ∃ ϑ : ℝ, ∃ α β : ℕ → ℝ,
    RouteM.IsTemplateWalk H z r ϑ n X α β ∧
      (∀ j ≤ n, H.cell (X j) ⊆ annulus z (4 * r / 5) (6 * r / 5)) ∧
      (∀ j, G.adj.Adj (X j) (X (j + 1)))

/-- The environment event that every start on the target circle has a route itinerary of the explicit probability
`2^{−⌈11600/s₀⌉}`. The estimate combines [18] Lemma 3.8 with the finite waypoint construction. -/
def PolarItineraryGood (F : RandomCellFamily) (k : ℕ) (z : ℂ) (r s₀ : ℝ) : Set F.Ω :=
  {ω | ∀ x ∈ verticesMeeting (F.H k ω).cell (sphere z r),
    ENNReal.ofReal ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))) ≤
      (F.G k ω).walkLaw x {ξ | PolarTemplateItinerary (F.H k ω) z r ((F.G k ω).vertexPath ξ)}}

/-- The finite family of events used for one mesh: one cell-diameter event and one itinerary event per admissible
grid annulus. -/
def GridEnvironmentGood (F : RandomCellFamily) (k : ℕ) (q χ ρ s₀ : ℝ)
    (S : ℕ → Finset (ℤ × ℤ × ℤ)) : Set F.Ω :=
  {ω | ω ∈ DiameterGood F k q ρ ∧
    ∀ t ∈ S k, ω ∈ PolarItineraryGood F k
      (gridCenter (mesh k) χ t) (gridRadius (mesh k) χ t) s₀}

/-- The uniform environment estimate for the itinerary event supplies a positive-probability finite
template itinerary. The finite waypoint argument uses [18] Lemma 3.8. The bad-event proof uses
`ItineraryEstimateBad`, produced by `itineraryEstimateBad_of_lemma38Bad_fixed2`. -/
def ItineraryEstimate (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ s₀ αᵢ βᵢ Cᵢ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < αᵢ ∧ 0 < βᵢ ∧
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ βᵢ ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      F.P (PolarItineraryGood F k z r s₀) ≥
        1 - ENNReal.ofReal (Cᵢ * mesh k ^ αᵢ)

/-- Exact integer-triple description of the finite annular grid. -/
def FiniteGridSpecification (χ β ρ : ℝ) (S : ℕ → Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∀ k, ∀ m n ℓ, (m, n, ℓ) ∈ S k ↔
      (((mesh k ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∈ ball (0 : ℂ) ρ ∧
      mesh k ^ β ≤ mesh k ^ χ * ℓ ∧ mesh k ^ χ * ℓ ≤ ρ ∧
      ball (((mesh k ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I))
        (2 * (mesh k ^ χ * ℓ)) ⊆ ball (0 : ℂ) ρ

/-- The finite-grid cardinal estimate used in the union bound: the number of integer triples is at
most `C_grid ε^{-3χ}`. It follows by counting center and radius coordinates. -/
def FiniteGridCard (χ β ρ C_grid : ℝ) : Prop :=
  ∃ S : ℕ → Finset (ℤ × ℤ × ℤ), FiniteGridSpecification χ β ρ S ∧
    ∀ k, (S k).card ≤ C_grid * mesh k ^ (-3 * χ)

/-- The elementary lattice-count input for all admissible finite grids counts center and radius
coordinates separately and obtains `O(mesh⁻³χ)`. -/
def FiniteGridCount (ρ : ℝ) : Prop :=
  ∀ χ β, 0 < χ → 0 < β → β < χ →
    ∃ C_grid, 0 ≤ C_grid ∧ FiniteGridCard χ β ρ C_grid

end MatedCRTHarmonic.CellFamily
