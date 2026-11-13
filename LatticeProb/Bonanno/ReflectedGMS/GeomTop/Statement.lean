/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.Statement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingDef
import LatticeProb.Bonanno.ReflectedGMS.GeneralMainStatements
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Theorems 1.2 and 1.3 of the geometric-topology revision — statements

Manuscript: *An invariance principle for reflected random walk on cell configurations with spatial
singularities*, "Geometric-topology revision", 24 September 2026 (`work/geomtop/manuscript.pdf`,
text in `work/geomtop/manuscript-text.txt`).  Definition 1.1 and (LCS): lines 55–82; the
environment topology and laws: lines 83–101 and Section 2 (lines 277–552; Definition 2.1 at
323–332, the finite-restriction distance (2.1) at 298–311); (1.4)/(1.5), (FE): 125–145;
Theorem 1.2: 163–194; ergodicity: 199–200; Theorem 1.3: 216–251.

The theorem texts are those of the earlier general-cell revision (formalized in
`GeneralMainStatements`); what changes is **where the random environment lives**:

* the environment space is `C_sing`, the **unmarked** configurations — sets of whole cells with
  adjacency and conductances — satisfying the geometric clauses (i)–(iii) of Definition 1.1
  (`SingSpace`); (LCS) is *not* part of the space;
* it carries the **geometric topology** `τ_sing`: the metric topology of `d_sing` (2.2), built from
  the whole-cell homeomorphism-matching distance `δ` (2.1) of finite restrictions of the
  configuration to finite unions of rational test disks, capped at `N` cells;
* every environment law is a probability on `B_sing = B(τ_sing)`; mass transport (1.4) tests
  `B_sing ⊗ B(ℂ²)`-measurable kernels on `C_sing`, and ergodicity concerns `B_sing`-measurable
  invariant events;
* "the geometric conditions and (LCS) are required on one measurable probability-one set".

Rational cell labels are only auxiliary Borel coordinates (the manuscript's Proposition 2.7): the
conclusions, which are the conclusions already formalized for labelled environments
(`HarmonicCoordinateConclusions`, `ReflectedInvarianceConclusions`, `EndSpatialImageConclusions`),
are asserted for the law `ν` of those coordinates, i.e. `ν.map Subtype.val = μ.map code`, which
determines `ν`.  The conclusions also assert that the coordinate map is `B_sing`-measurable and that
almost every environment's coordinates are valid in the earlier sense (so the reused almost-sure
clauses genuinely hold for almost every environment).

The normalized covariance rule (1.10) is asserted "where `H_u` is uniquely defined", with `H_u` the
unique cell containing `u` when it is unique (line 122) — including a point of a cell's boundary
lying in no other cell.  The reused clause `NormalizedCovariant` asserts it only off every cell
boundary, and unlike the general-cell revision this manuscript does not read covariance of
potentials modulo an additive constant.  The conclusions therefore add `UniqueCellCovariant`,
which is (1.10) at every uniquely defined `H_u`, in every environment.

Encoding choices: a finite restriction is a `GMS.CellConfig` with finitely many cells and the
symbol `†` is `none`; the enumeration of nonempty finite tuples of rational points is
`Denumerable.ofNat`; mass-transport kernels are `[0,∞)`-valued, which is equivalent to the
`[0,∞]`-valued reading (`GeomTop.massTransport_ennreal_geom`).  "Countably infinite" in Definition 1.1 is not imposed separately: it follows from
(i)–(ii) (disjoint interiors each contain a rational point; finitely many compact cells cannot cover
the complement of an `H¹`-null set).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.GeomTop

open GMS

/-- **Definition 1.1(ii)**: a singular-set witness for an unmarked configuration. -/
structure SingularWitness (H : CellConfig) where
  sing : Set Plane
  isClosed_sing : IsClosed sing
  hausdorff_sing : μH[1] sing = 0
  cover : singᶜ ⊆ ⋃ K ∈ H.cells, (K : Set Plane)
  locallyFinite : ∀ z ∉ sing, ∃ U ∈ 𝓝 z, (H.restrict U).Finite

/-- **Definition 1.1 (i)–(iii)** for an unmarked configuration (the class `C_sing`). -/
structure IsSingConfiguration (H : CellConfig) : Prop where
  isConnected : ∀ K ∈ H.cells, IsConnected (K : Set Plane)
  interior_nonempty : ∀ K ∈ H.cells, (interior (K : Set Plane)).Nonempty
  volume_inter : ∀ K ∈ H.cells, ∀ K' ∈ H.cells, K ≠ K' → volume ((K : Set Plane) ∩ K') = 0
  witness : Nonempty (SingularWitness H)
  c_nonneg : ∀ K K', 0 ≤ H.c K K'
  c_symm : ∀ K K', H.c K K' = H.c K' K
  adj_mem : ∀ K K', H.Adj K K' → K ∈ H.cells ∧ K' ∈ H.cells
  adj_ne : ∀ K K', H.Adj K K' → K ≠ K'
  adj_inter : ∀ K K', H.Adj K K' → ((K : Set Plane) ∩ K').Nonempty

/-- **(LCS)** relative to `S`: `H(L)` is connected for every horizontal or vertical compact segment
`L` disjoint from `S` (preconnected; nonempty by coverage). -/
def LineConnectedOff (H : CellConfig) (S : Set Plane) : Prop :=
  (∀ a b y : ℝ, Disjoint (horizontal a b y) S → (H.inducedGraph (horizontal a b y)).Preconnected) ∧
    ∀ x a b : ℝ, Disjoint (vertical x a b) S → (H.inducedGraph (vertical x a b)).Preconnected

namespace CellConfigOps

variable (H : CellConfig)

/-- The finite restriction `H(A)`: the whole cells meeting `A`, with induced adjacency and
conductances. -/
noncomputable def restrictConfig (A : Set Plane) : CellConfig where
  cells := H.restrict A
  c K K' := open Classical in if K ∈ H.restrict A ∧ K' ∈ H.restrict A then H.c K K' else 0

/-- `P_N(H,U)`: the restriction `H(U)` if it has at most `N` cells, and `†` (`none`) otherwise. -/
noncomputable def capped (N : ℕ) (U : Set Plane) : Option CellConfig :=
  open Classical in if (H.restrict U).encard ≤ N then some (restrictConfig H U) else none

end CellConfigOps

/-- A plane homeomorphism mapping the cells of `F` bijectively onto those of `F'` (as whole compact
sets), preserving adjacency in both directions. -/
def MatchesWhole (F F' : CellConfig) (f : Plane ≃ₜ Plane) : Prop :=
  (∀ K ∈ F.cells, CellConfig.mapCell f K ∈ F'.cells) ∧
    (∀ K ∈ F'.cells, CellConfig.mapCell f.symm K ∈ F.cells) ∧
    (∀ K ∈ F.cells, ∀ K' ∈ F.cells,
      (F.Adj K K' ↔ F'.Adj (CellConfig.mapCell f K) (CellConfig.mapCell f K')))

/-- `sup_z |f(z) − z| + max_{{H,K} ∈ E(F)} |c_F(H,K) − c_{F'}(f(H), f(K))|` (the maximum over an
empty edge set is `0`). -/
noncomputable def wholeDistortion (F F' : CellConfig) (f : Plane ≃ₜ Plane) : ℝ≥0∞ :=
  (⨆ z : Plane, edist (f z) z) +
    ⨆ (K ∈ F.cells) (K' ∈ F.cells) (_ : F.Adj K K'),
      ENNReal.ofReal |F.c K K' - F'.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')|

/-- **The distance (2.1) of finite restrictions**, with the extra symbol `†` = `none`:
`δ(F,F') = 1 ∧ inf_f {…}` (an infimum over an empty set is `+∞`), `δ(†,F) = 1`, `δ(†,†) = 0`. -/
noncomputable def restrictionDist : Option CellConfig → Option CellConfig → ℝ≥0∞
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some F, some F' => min 1 (⨅ (f : Plane ≃ₜ Plane) (_ : MatchesWhole F F' f), wholeDistortion F F' f)

/-- Nonempty finite tuples of points of `ℚ²`. -/
abbrev RatTuple := {l : List (ℚ × ℚ) // l ≠ []}

instance : Infinite RatTuple :=
  Infinite.of_injective (fun n : ℕ => (⟨[((n : ℚ), 0)], List.cons_ne_nil _ _⟩ : RatTuple))
    (fun m n h => by simpa using congrArg (fun l : RatTuple => (l.1.head l.2).1) h)

noncomputable instance : Denumerable RatTuple := Denumerable.ofEncodableOfInfinite RatTuple

/-- The fixed enumeration `q(1), q(2), …` of nonempty finite rational tuples (index shifted to `ℕ`). -/
noncomputable def ratTuple (j : ℕ) : RatTuple := Denumerable.ofNat RatTuple j

/-- The point of the plane with rational coordinates `p`. -/
noncomputable def ratPoint (p : ℚ × ℚ) : Plane := WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

/-- The test window `U_{q,r} = ⋃_i B_r(q_i)`. -/
def window (q : RatTuple) (r : ℝ) : Set Plane := ⋃ p ∈ q.1, Metric.ball (ratPoint p) r

/-- **The geometric environment metric (2.2)**:
`d_sing(H,H') = Σ_{j,N ≥ 1} 2^{-j-N} ∫₀^∞ e^{-r} δ(P_N(H, U_{q(j),r}), P_N(H', U_{q(j),r})) dr`. -/
noncomputable def dSing (H H' : CellConfig) : ℝ≥0∞ :=
  ∑' (j : ℕ) (N : ℕ), (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r)) *
      restrictionDist (CellConfigOps.capped H (N + 1) (window (ratTuple j) r))
        (CellConfigOps.capped H' (N + 1) (window (ratTuple j) r))

/-- **The environment space `C_sing`**: unmarked configurations satisfying (i)–(iii). -/
abbrev SingSpace : Type := {H : CellConfig // IsSingConfiguration H}

/-- **The geometric topology `τ_sing`**, the metric topology of `d_sing` (generated by its balls). -/
instance : TopologicalSpace SingSpace :=
  TopologicalSpace.generateFrom
    {S | ∃ (H : SingSpace) (ε : ℝ≥0∞), 0 < ε ∧ S = {H' | dSing H.1 H'.1 < ε}}

/-- `B_sing = B(τ_sing)`. -/
instance : MeasurableSpace SingSpace := borel SingSpace

instance : BorelSpace SingSpace := ⟨rfl⟩

/-- `H'` is `C(H − u)`. -/
def IsSimilar (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) : Prop :=
  H'.1 = H.1.similarity s u hs

/-- **(1.4)/(1.5) mass transport modulo scaling** on `C_sing`: for every nonnegative
`B_sing ⊗ B(ℂ²)`-measurable `T` with `T(C(H−u), C(w−u), C(z−u)) = C⁻² T(H,w,z)`,
`E ∫ T(H,0,z) dz = E ∫ T(H,z,0) dz`. -/
def MassTransport (μ : Measure SingSpace) : Prop :=
  ∀ T : SingSpace × Plane × Plane → ℝ≥0, Measurable T →
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      ∀ w z : Plane,
        T (H', positiveSimilarity s u w, positiveSimilarity s u z) = (s ^ 2)⁻¹ * T (H, w, z)) →
    (∫⁻ H, ∫⁻ z : Plane, (T (H, 0, z) : ℝ≥0∞) ∂volume ∂μ) =
      ∫⁻ H, ∫⁻ z : Plane, (T (H, z, 0) : ℝ≥0∞) ∂volume ∂μ

/-- **Ergodicity modulo scaling**: every `B_sing`-measurable event invariant under translations and
positive dilations has probability `0` or `1`. -/
def EnvironmentErgodic (μ : Measure SingSpace) : Prop :=
  ∀ A : Set SingSpace, MeasurableSet A →
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (H ∈ A ↔ H' ∈ A)) →
    μ A = 0 ∨ μ A = 1

/-- The boundary mask: cell frontiers together with the uncovered set. -/
def boundaryMask (H : CellConfig) : Set Plane :=
  (⋃ K ∈ H.cells, frontier (K : Set Plane)) ∪ (⋃ K ∈ H.cells, (K : Set Plane))ᶜ

/-- The (FE) integrand `d_H²/a_H · (π(H) + π*(H))` with extended nonnegative sums. -/
noncomputable def feDensity (H : CellConfig) (K : Cell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2) / ENNReal.ofReal (CellConfig.area K) *
    ((∑' K' : H.cells, ENNReal.ofReal (H.c K K')) + ∑' K' : H.cells, ENNReal.ofReal (H.c K K')⁻¹)

/-- The (FE) integrand at the cell containing the origin; zero at uncovered or boundary roots. -/
noncomputable def rootedFEDensity (H : CellConfig) : ℝ≥0∞ :=
  open Classical in
  if h : (0 : Plane) ∉ boundaryMask H ∧ ∃ K ∈ H.cells, (0 : Plane) ∈ (K : Set Plane) then
    feDensity H h.2.choose else 0

/-- **(FE)**: `E[d²_{H₀}/a_{H₀} (π(H₀) + π*(H₀))] < ∞`. -/
def FiniteEnergyMoment (μ : Measure SingSpace) : Prop := (∫⁻ H, rootedFEDensity H.1 ∂μ) < ∞

/-- "The geometric conditions and (LCS) are required on one measurable probability-one set", with
one witness serving (ii) and (LCS). -/
def LCSOnMeasurableSet (μ : Measure SingSpace) : Prop :=
  ∃ A : Set SingSpace, MeasurableSet A ∧ μ A = 1 ∧
    ∀ H ∈ A, ∃ w : SingularWitness H.1, LineConnectedOff H.1 w.sing

/-- The auxiliary rational-label coordinates of an environment (manuscript Proposition 2.7). -/
noncomputable def coords (H : SingSpace) : Code.RawCode := H.1.code

open Code EnvironmentLaws EnvironmentFields HarmonicLawIngredients HarmonicMainStatement
open InvarianceMainStatement StatementIngredients

/-- **(1.10) wherever `H_u` is uniquely defined**: if `u` lies in the cell `r` and in no other cell
of `e`, and `e'` is `C(e − u)` with matching relabelling, then
`Φ_{e'}(relabel v) = C (Φ_e(v) − Φ_e(r))` for every cell `v`.  (With `C = 1`, `u = 0` this includes
the normalization `Φ(H₀) = 0` wherever `H₀` is uniquely defined.) -/
def UniqueCellCovariant (Φ : CellField) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → ∀ r : Vertex e.val,
      u ∈ ((decode e).cell r : Set Plane) →
      (∀ w : Vertex e.val, u ∈ ((decode e).cell w : Set Plane) → w = r) →
      ∀ v, Φ.at e' (relabel v) = s • (Φ.at e v - Φ.at e r)

/-- The harmonic-coordinate conclusions (a)–(d) of Theorem 1.2, with (1.10) at every uniquely
defined `H_u`. -/
def GeomHarmonicCoordinateConclusions (ν : Measure Env) : Prop :=
  ∃ Φ : CellField, IsHarmonicCoordinate ν Φ ∧ UniqueCellCovariant Φ

/-- The conclusions (a)–(e) of Theorem 1.3 (the body of `ReflectedInvarianceConclusions`), for a
harmonic coordinate that also satisfies (1.10) at every uniquely defined `H_u`. -/
def GeomReflectedInvarianceConclusions (ν : Measure Env) : Prop :=
  ∃ (Φ : CellField) (target : AnisotropicBrownianTarget),
    (IsHarmonicCoordinate ν Φ ∧ UniqueCellCovariant Φ) ∧
    IntegrableBracket ν Φ ∧
    target.covariance = meanCovariance ν Φ ∧
    (∃ z : CellField, IsCellRepresentative z ∧ RepresentativeCovariant z) ∧
    ∀ᵐ e : Env ∂ν, EnvironmentProcessConclusions e Φ target

/-- **Theorem 1.2** (harmonic coordinates) of the geometric-topology revision.  For a law on
`(C_sing, B_sing)` satisfying (LCS) on a measurable probability-one set, (1.4) and (FE), the
harmonic-coordinate conclusions (a)–(d) hold for the law `ν` of the environment's auxiliary
labelled coordinates.

This declaration states a proposition; it does not assert that it has been proved. -/
def GeomHarmonicCoordinateMainTheorem : Prop :=
  ∀ (μ : Measure SingSpace) [IsProbabilityMeasure μ],
    LCSOnMeasurableSet μ → MassTransport μ → FiniteEnergyMoment μ →
      Measurable coords ∧ (∀ᵐ H ∂μ, Valid (coords H)) ∧
      ∃ (ν : Measure Env) (_ : IsProbabilityMeasure ν),
        ν.map Subtype.val = μ.map coords ∧ GeomHarmonicCoordinateConclusions ν

/-- **Theorem 1.3** (reflected invariance principle) of the geometric-topology revision: under the
hypotheses of Theorem 1.2 and ergodicity modulo scaling, clauses (a)–(e) hold for the law of the
labelled coordinates; almost every environment's coordinates satisfy Definition 1.1 and (LCS); and
every graph end of every environment satisfying Definition 1.1 and (LCS) with a locally finite graph
has a unique spatial image in `Ssing ∪ {∞}` (Proposition 3.6).

This declaration states a proposition; it does not assert that it has been proved. -/
def GeomReflectedInvarianceMainTheorem : Prop :=
  ∀ (μ : Measure SingSpace) [IsProbabilityMeasure μ],
    LCSOnMeasurableSet μ → MassTransport μ → FiniteEnergyMoment μ → EnvironmentErgodic μ →
      Measurable coords ∧ (∀ᵐ H ∂μ, Valid (coords H)) ∧ (∀ᵐ H ∂μ, ValidGeneral (coords H)) ∧
      ∃ (ν : Measure Env) (_ : IsProbabilityMeasure ν),
        ν.map Subtype.val = μ.map coords ∧ GeomReflectedInvarianceConclusions ν ∧
          ∀ e : Env, ValidGeneral e.val → GeneralMainStatements.EndSpatialImageConclusions (decode e)

/-- The strengthened conclusions imply the reused ones. -/
theorem GeomHarmonicCoordinateConclusions.toHarmonicCoordinateConclusions {ν : Measure Env}
    (h : GeomHarmonicCoordinateConclusions ν) : HarmonicCoordinateConclusions ν :=
  let ⟨Φ, hΦ, _⟩ := h; ⟨Φ, hΦ⟩

/-- The strengthened conclusions imply the reused ones. -/
theorem GeomReflectedInvarianceConclusions.toReflectedInvarianceConclusions {ν : Measure Env}
    (h : GeomReflectedInvarianceConclusions ν) : ReflectedInvarianceConclusions ν :=
  let ⟨Φ, target, ⟨hΦ, _⟩, hrest⟩ := h; ⟨Φ, target, hΦ, hrest⟩

end ReflectedGMS.GeomTop
