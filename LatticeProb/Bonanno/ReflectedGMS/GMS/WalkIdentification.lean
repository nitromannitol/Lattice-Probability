/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.WalkIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkJumpChainLaw
import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw
import LatticeProb.Bonanno.ReflectedGMS.GMS.InterpolatedConvergence
import LatticeProb.Bonanno.ReflectedGMS.Geometry.EndSpatialImageGeneral
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGMSSpecialization
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly

/-!
# The reflected walk of a GMS environment is GMS's simple random walk

Fix an environment `e` whose decoded configuration satisfies the hypotheses of GMS Theorem 1.16
(`GMSGeometry`, so the singular set is empty), together with the proved per-environment
conclusions of the reflected invariance principle at one start (`FixedStartConclusions`), and a
bijection `σ` between the labelled cells and GMS's cells matching cells and conductances.  Then:

1. **no end-valued times** (`ae_exactAreaPath_ne_none`): by Proposition 2.6 with the empty
   singular witness every graph end is at spatial infinity (`atSpatialInfinity_of_gmsGeometry`),
   and the exact-holding path avoids spatial infinity;
2. **the jump chain** `exactJumpChain` of the exact-holding path (its values at the successive exit
   times) is, after transport by `σ`, a simple random walk: `isSRWLaw_map_exactJumpChain`;
3. **the pathwise identity** `ae_exactAreaPath_eq_walk`: the exact-holding path *is* GMS's walk
   `CellConfig.walk` of the transported chain, at every real time (holding times `Area/π`, no
   explosion);
4. **uniqueness** (`eq_map_exactJumpChain_of_isSRWLaw`): every law with `IsSRWLaw (σ start)` is the
   law of the transported jump chain;
5. **recurrence** `recurrent_of_fixedStartConclusions`;
6. **a discrete harmonic coordinate sublinear to the centroids**
   `exists_discreteHarmonic_sublinearToCentroid`.

For the convergence half: `ae_interpolatedWalk_eq_scaledBrownianPath` (GMS's rescaled interpolated
walk of the transported chain is `scaledBrownianPath ε⁻¹` of one unscaled interpolation
`interpolation`), `ae_interpolation_segment` (that interpolation is the affine interpolation
through `p (σ v)` over every holding interval of the exact-holding path), and
`integral_interpolatedWalk_eq` (the integral of any measurable functional of GMS's interpolated
walk under any `IsSRWLaw` law equals the corresponding `areaSampleLaw` integral).

## How the jump chain law is obtained

No new strong-Markov computation is made: the law is the uniqueness proof's Step 1
(`ReflectedWalk.Theorem16.measure_embeddedCyl`) for the exponential area-clock walk, which is a
reflected walk (`IsReflectedWalk`); the exponential and the exact path have the same jump chain
because the exact path is a homeomorphic time change of the exponential one (a conclusion of
`FixedStartConclusions`).  Non-explosion comes from local spatial boundedness of the regular spatial
extension through the in-cell representative `InvarianceAssembly.lexMinField` together with
spatial local finiteness of the cells.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.GMS.WalkIdentification

open Code EnvironmentFields StatementIngredients AreaClocks SpatialEnds InvarianceMainStatement
  HarmonicMainStatement ReflectedWalk WalkStepPath InterpolatedConvergence

/-! ## Every graph end is at spatial infinity -/

/-- With the empty singular witness of a GMS configuration, Proposition 2.6 puts every graph end at
spatial infinity. -/
theorem atSpatialInfinity_of_gmsGeometry {e : Env}
    (hgeo : GMSGeometry (decode e).toCellConfiguration) (en : GraphEnd (decode e)) :
    AtSpatialInfinity (decode e) en := by
  obtain ⟨-, himg, hiff, -⟩ :=
    GeneralMainStatements.endSpatialImageConclusions_of_geometry (decode_geometry e)
      hgeo.singularSet en
  refine hiff.1 ?_
  rcases himg with h | ⟨z, hz, -⟩
  · exact h
  · rw [GMSGeometry.sing_singularSet] at hz
    exact absurd hz (Set.notMem_empty z)

theorem areaHoldingLength_pos {e : Env} (hpos : ∀ v, 0 < areaRate (decode e) v)
    (v : Vertex e.val) : 0 < areaHoldingLength (decode e) v := by
  have h := hpos v
  unfold areaRate at h
  unfold areaHoldingLength
  rw [← inv_div]
  exact inv_pos.2 h

/-- The jump chain of the exact-holding area-clock path: its values at the successive exit
times. -/
noncomputable def exactJumpChain (e : Env) (D : (decode e).graph.Exhaustion)
    (start : Vertex e.val) : Existence.Sample (Vertex e.val) → ℕ → Vertex e.val :=
  jumpChainOf (exactAreaPath (decode e) D) start

/-- The unscaled linear interpolation of GMS's walk of the transported jump chain through the
points `p`. -/
noncomputable def interpolation (e : Env) (D : (decode e).graph.Exhaustion)
    (start : Vertex e.val) (H : CellConfig) (σ : Vertex e.val ≃ H.cells) (p : H.cells → Plane)
    (ω : Existence.Sample (Vertex e.val)) : BouRabeeGwynne.BrownianPath 2 :=
  H.interpolatedWalk p 1 (fun k => σ (exactJumpChain e D start ω k))

/-! ## The exact path is almost surely a step path -/

section Environment

variable {e : Env} [Nontrivial (Vertex e.val)] {D : (decode e).graph.Exhaustion}
  {hG : (decode e).graph.toSimpleGraph.Connected} {hmin : (decode e).graph.EnergyMinimizer}
  {Φ : CellField} {target : AnisotropicBrownianTarget} {start : Vertex e.val}

/-- **Almost surely the exact-holding path and the exponential path are step paths with the same
jump chain**, the exact holding at `v` is `Area/π`, the chain moves along edges and starts at
`start`. -/
theorem ae_isStepPath (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∃ (J : ℕ → Vertex e.val) (s s' : ℕ → ℝ≥0),
      IsStepPath (fun t => exactAreaPath (decode e) D t ω) J s ∧
      IsStepPath (fun t => exponentialAreaPath (decode e) D t ω) J s' ∧
      (∀ k, (s (k + 1) : ℝ) - s k = areaHoldingLength (decode e) (J k)) ∧
      (∀ k, (decode e).graph.toSimpleGraph.Adj (J k) (J (k + 1))) ∧ J 0 = start := by
  obtain ⟨Xexp, Xexact, M, hae, -, -, -, hrep⟩ := hfix
  obtain ⟨Zexp, Zexact, Iexp, Iexact, hrae, -⟩ :=
    hrep InvarianceAssembly.lexMinField InvarianceAssembly.isCellRepresentative_lexMinField
  have hstart : ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start,
      exponentialAreaPath (decode e) D 0 ω = some start := (hwalk start).1
  filter_upwards [hae, hrae, hstart] with ω hω hrω h0
  obtain ⟨-, hcolExact, -, -, -, hav, -, htc, hlen, -⟩ := hω
  obtain ⟨-, hRSE, -, hICI⟩ := hrω
  have hvert : ∀ t, ∃ v, Xexact t ω = Sum.inl v := by
    intro t
    rcases hX : Xexact t ω with v | en
    · exact ⟨v, rfl⟩
    · exact absurd (atSpatialInfinity_of_gmsGeometry hgeo en) (hav t en hX)
  have hfin := finite_visited_of_spatialExtension hRSE.1 hRSE.2.2.1
    (fun v => InvarianceAssembly.isCellRepresentative_lexMinField e v) hgeo.locallyFinite
  obtain ⟨J, s, hs, hhold, hadj⟩ := exists_isStepPath_of_holdingIntervals
    (g := fun t => Xexact t ω) hvert hICI.2.1 hlen (areaHoldingLength_pos hpos) hfin
  have hs' : IsStepPath (fun t => exactAreaPath (decode e) D t ω) J s := by
    have hfun : (fun t => exactAreaPath (decode e) D t ω) = fun t => collapse (Xexact t ω) :=
      funext fun t => (hcolExact t).symm
    rw [hfun]
    exact hs
  obtain ⟨h, hmono, h00, hht⟩ := htc
  have hs'' : IsStepPath (fun t => exponentialAreaPath (decode e) D t ω) J (fun k => h (s k)) :=
    hs'.comp_symm h hmono h00 hht
  refine ⟨J, s, fun k => h (s k), hs', hs'', hhold, hadj, ?_⟩
  have e1 : exactAreaPath (decode e) D 0 ω = some (J 0) := by
    have := hs'.apply_self 0
    rwa [hs'.zero] at this
  have e2 : exactAreaPath (decode e) D 0 ω = exponentialAreaPath (decode e) D 0 ω := by
    have := hht 0
    rw [h00] at this
    exact this
  exact Option.some_injective _ (e1.symm.trans (e2.trans h0))

/-- The same, stated for the jump chain `exactJumpChain` itself; the exponential path has the same
jump chain. -/
theorem ae_exactJumpChain (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∃ s s' : ℕ → ℝ≥0,
      IsStepPath (fun t => exactAreaPath (decode e) D t ω) (exactJumpChain e D start ω) s ∧
      IsStepPath (fun t => exponentialAreaPath (decode e) D t ω) (exactJumpChain e D start ω) s' ∧
      (∀ k, (s (k + 1) : ℝ) - s k =
        areaHoldingLength (decode e) (exactJumpChain e D start ω k)) ∧
      (∀ k, (decode e).graph.toSimpleGraph.Adj (exactJumpChain e D start ω k)
        (exactJumpChain e D start ω (k + 1))) ∧
      exactJumpChain e D start ω 0 = start ∧
      jumpChainOf (exponentialAreaPath (decode e) D) start ω = exactJumpChain e D start ω := by
  filter_upwards [ae_isStepPath hgeo hpos hwalk hfix] with ω hω
  obtain ⟨J, s, s', hs, hs', hhold, hadj, h0⟩ := hω
  have hJ : exactJumpChain e D start ω = J := jumpChainOf_of_isStepPath hs start
  have hJ' : jumpChainOf (exponentialAreaPath (decode e) D) start ω = J :=
    jumpChainOf_of_isStepPath hs' start
  rw [hJ, hJ']
  exact ⟨s, s', hs, hs', hhold, hadj, h0, rfl⟩

/-- **Target 1: no end-valued times.**  Almost surely the exact-holding path is at a vertex at every
time. -/
theorem ae_exactAreaPath_ne_none (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∀ t, exactAreaPath (decode e) D t ω ≠ none := by
  filter_upwards [ae_isStepPath hgeo hpos hwalk hfix] with ω hω
  obtain ⟨J, s, _, hs, -⟩ := hω
  intro t
  obtain ⟨k, hk⟩ := hs.exists_mem t
  rw [show exactAreaPath (decode e) D t ω = some (J k) from hs.eq_of_mem k t hk]
  exact Option.some_ne_none _

theorem ae_isStepPath_process (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    ∀ᵐ ω ∂(Existence.processFamily D hG (areaRate (decode e))).P start,
      ∃ (J : ℕ → Vertex e.val) (s : ℕ → ℝ≥0),
        IsStepPath (fun t => (Existence.processFamily D hG (areaRate (decode e))).X t ω) J s := by
  filter_upwards [ae_isStepPath hgeo hpos hwalk hfix] with ω hω
  obtain ⟨J, _, s', -, hs', -⟩ := hω
  exact ⟨J, s', hs'⟩

/-! ## The law of the jump chain -/

open Classical in
/-- **Target 2 (labelled form): the jump chain of the exact path is the simple random walk**, with
transitions `c(v,w)/π(v)` from `start`. -/
theorem measure_exactJumpChain_cyl (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) (g : ℕ → Vertex e.val) (n : ℕ) :
    areaSampleLaw (decode e) D hG start {ω | ∀ j ≤ n, exactJumpChain e D start ω j = g j} =
      (if g 0 = start then 1 else 0) *
        ∏ j ∈ Finset.range n, ENNReal.ofReal
          ((decode e).graph.c (g j) (g (j + 1)) / (decode e).graph.pi (g j)) := by
  have hset : {ω | ∀ j ≤ n, exactJumpChain e D start ω j = g j}
      =ᵐ[areaSampleLaw (decode e) D hG start]
      {ω | ∀ j ≤ n, jumpChainOf (Existence.processFamily D hG (areaRate (decode e))).X start
        ω j = g j} := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_exactJumpChain hgeo hpos hwalk hfix] with ω hω
    obtain ⟨_, _, -, -, -, -, -, hJ⟩ := hω
    show (∀ j ≤ n, exactJumpChain e D start ω j = g j) ↔
      (∀ j ≤ n, jumpChainOf (exponentialAreaPath (decode e) D) start ω j = g j)
    rw [hJ]
  rw [measure_congr hset]
  refine (measure_jumpChainOf_cyl hwalk hG start (ae_isStepPath_process hgeo hpos hwalk hfix)
    g n).trans ?_
  congr 1
  split_ifs <;> rfl

/-- The jump chain is an a.e.-measurable random sequence. -/
theorem aemeasurable_exactJumpChain (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    AEMeasurable (exactJumpChain e D start) (areaSampleLaw (decode e) D hG start) := by
  refine (aemeasurable_jumpChainOf hwalk start
    (ae_isStepPath_process hgeo hpos hwalk hfix)).congr ?_
  filter_upwards [ae_exactJumpChain hgeo hpos hwalk hfix] with ω hω
  obtain ⟨_, _, -, -, -, -, -, hJ⟩ := hω
  exact hJ

/-! ## Transport to GMS's unlabelled configuration -/

section GMS

variable {H : CellConfig} (σ : Vertex e.val ≃ H.cells)

omit [Nontrivial (Vertex e.val)] in
theorem pi_sigma (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) (v : Vertex e.val) :
    H.pi (σ v) = (decode e).graph.pi v := by
  unfold CellConfig.pi ReflectedWalk.ConductanceGraph.pi
  rw [← σ.tsum_eq]
  simp only [hc]

omit [Nontrivial (Vertex e.val)] in
theorem holding_sigma (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) (v : Vertex e.val) :
    H.holding (σ v) = areaHoldingLength (decode e) v := by
  rw [CellConfig.holding, CellConfig.area, pi_sigma σ hc v, hcell v]
  rfl

omit [Nontrivial (Vertex e.val)] in
theorem transition_sigma (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w)
    (v w : Vertex e.val) :
    H.transition (σ v) (σ w) = (decode e).graph.c v w / (decode e).graph.pi v := by
  rw [CellConfig.transition, hc, pi_sigma σ hc]

omit [Nontrivial (Vertex e.val)] in
theorem centroid_sigma (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (v : Vertex e.val) : CellConfig.centroid (σ v : Cell) = cellCentroid (decode e) v := by
  rw [CellConfig.centroid, hcell v]
  rfl

omit [Nontrivial (Vertex e.val)] in
theorem holding_pos_of_sigma (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w)
    (hpos : ∀ v, 0 < areaRate (decode e) v) (K : H.cells) : 0 < H.holding K := by
  rw [← σ.apply_symm_apply K, holding_sigma σ hcell hc]
  exact areaHoldingLength_pos hpos _

omit [Nontrivial (Vertex e.val)] in
include σ in
theorem countable_cells : Countable H.cells := σ.symm.injective.countable

/-- The transported jump chain is an a.e.-measurable random sequence of cells. -/
theorem aemeasurable_transportedChain (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start) :
    AEMeasurable (fun ω k => σ (exactJumpChain e D start ω k))
      (areaSampleLaw (decode e) D hG start) := by
  have hm : Measurable fun f : ℕ → Vertex e.val => fun k => σ (f k) :=
    Measurable.of_eval fun k => (measurable_of_countable σ).comp (measurable_pi_apply k)
  exact hm.comp_aemeasurable (aemeasurable_exactJumpChain hgeo hpos hwalk hfix)

/-- **Target 2: the transported jump chain of the exact path has GMS's simple-random-walk law**
from `σ start`. -/
theorem isSRWLaw_map_exactJumpChain (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) :
    H.IsSRWLaw (σ start) ((areaSampleLaw (decode e) D hG start).map
      (fun ω k => σ (exactJumpChain e D start ω k))) := by
  classical
  have hJσ := aemeasurable_transportedChain σ hgeo hpos hwalk hfix
  refine And.intro inferInstance (fun n x => ?_)
  have hmeas : MeasurableSet {ω' : ℕ → H.cells | ∀ i : Fin (n + 1), ω' i = x i} := by
    have hsetEq : {ω' : ℕ → H.cells | ∀ i : Fin (n + 1), ω' i = x i} =
        ⋂ i : Fin (n + 1), (fun ω' : ℕ → H.cells => ω' i) ⁻¹' {x i} := by
      ext ω'
      simp
    rw [hsetEq]
    exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)
  rw [Measure.map_apply_of_aemeasurable hJσ hmeas]
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Vertex e.val, ∀ j (h : j < n + 1), g j = σ.symm (x ⟨j, h⟩) :=
    ⟨fun j => if h : j < n + 1 then σ.symm (x ⟨j, h⟩) else start, fun j h => dif_pos h⟩
  have hpre : (fun ω k => σ (exactJumpChain e D start ω k)) ⁻¹'
      {ω' : ℕ → H.cells | ∀ i : Fin (n + 1), ω' i = x i} =
      {ω | ∀ j ≤ n, exactJumpChain e D start ω j = g j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro h j hj
      rw [hg j (Nat.lt_succ_of_le hj), ← h ⟨j, Nat.lt_succ_of_le hj⟩, Equiv.symm_apply_apply]
    · intro h i
      rw [h i (Nat.lt_succ_iff.1 i.2), hg i i.2, Equiv.apply_symm_apply]
  rw [hpre, measure_exactJumpChain_cyl hgeo hpos hwalk hfix g n]
  have h0 : g 0 = start ↔ x 0 = σ start := by
    rw [hg 0 (Nat.succ_pos n), Equiv.symm_apply_eq]
    simp [Fin.zero_eta]
  congr 1
  · by_cases hx : x 0 = σ start
    · rw [if_pos hx, if_pos (h0.2 hx)]
    · rw [if_neg hx, if_neg fun h => hx (h0.1 h)]
  · rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hg i (Nat.lt_succ_of_lt i.2), hg ((i : ℕ) + 1) (Nat.succ_lt_succ i.2), ← transition_sigma σ hc,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- **Target 4: uniqueness.**  Every law with `IsSRWLaw (σ start)` is the law of the transported
jump chain of the exact-holding path. -/
theorem eq_map_exactJumpChain_of_isSRWLaw (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w)
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw (σ start) Q) :
    Q = (areaSampleLaw (decode e) D hG start).map
      (fun ω k => σ (exactJumpChain e D start ω k)) := by
  have := countable_cells σ
  exact hQ.unique (isSRWLaw_map_exactJumpChain σ hgeo hpos hwalk hfix hc)

/-- Almost surely the jump times of GMS's walk of the transported chain are the jump times of the
exact path, and they are unbounded. -/
theorem ae_jumpTime_eq (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∃ s : ℕ → ℝ≥0,
      IsStepPath (fun t => exactAreaPath (decode e) D t ω) (exactJumpChain e D start ω) s ∧
      (∀ n, H.jumpTime (fun k => σ (exactJumpChain e D start ω k)) n = s n) ∧
      H.JumpTimesUnbounded (fun k => σ (exactJumpChain e D start ω k)) := by
  filter_upwards [ae_exactJumpChain hgeo hpos hwalk hfix] with ω hω
  obtain ⟨s, _, hs, -, hhold, -, -, -⟩ := hω
  have hT : ∀ n, H.jumpTime (fun k => σ (exactJumpChain e D start ω k)) n = s n := by
    intro n
    unfold CellConfig.jumpTime
    simp only [holding_sigma σ hcell hc, ← hhold]
    rw [Finset.sum_range_sub (fun k => (s k : ℝ)) n, hs.zero]
    simp
  refine ⟨s, hs, hT, fun N => ?_⟩
  obtain ⟨n, hn⟩ := hs.exists_lt (N : ℝ≥0)
  refine ⟨n, ?_⟩
  rw [hT n]
  exact_mod_cast hn

/-- **Target 3: the pathwise identity.**  Almost surely, at every time, the exact-holding path is
at the vertex `σ⁻¹` of GMS's walk of the transported jump chain. -/
theorem ae_exactAreaPath_eq_walk (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∀ t : ℝ≥0,
      exactAreaPath (decode e) D t ω =
        some (σ.symm (H.walk (fun k => σ (exactJumpChain e D start ω k)) t)) := by
  filter_upwards [ae_jumpTime_eq σ hgeo hpos hwalk hfix hcell hc] with ω hω
  obtain ⟨s, hs, hT, -⟩ := hω
  intro t
  obtain ⟨k, hk⟩ := hs.exists_mem t
  have hw : H.walk (fun k => σ (exactJumpChain e D start ω k)) t =
      σ (exactJumpChain e D start ω k) :=
    CellConfig.walk_eq_of_mem (holding_pos_of_sigma σ hcell hc hpos)
      (by rw [hT k]; exact_mod_cast hk.1) (by rw [hT (k + 1)]; exact_mod_cast hk.2)
  rw [hw, Equiv.symm_apply_apply]
  exact hs.eq_of_mem k t hk

/-! ## The interpolated walk -/

/-- **GMS's rescaled interpolated walk of the transported chain is `scaledBrownianPath ε⁻¹` of the
unscaled interpolation**, almost surely and for every `ε` (its placeholder branch is not
taken: no explosion). -/
theorem ae_interpolatedWalk_eq_scaledBrownianPath
    (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) (p : H.cells → Plane) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∀ ε : ℝ≥0,
      H.interpolatedWalk p ε (fun k => σ (exactJumpChain e D start ω k)) =
        BouRabeeGwynne.scaledBrownianPath ε⁻¹ (interpolation e D start H σ p ω) := by
  filter_upwards [ae_jumpTime_eq σ hgeo hpos hwalk hfix hcell hc] with ω hω
  obtain ⟨s, -, -, hunb⟩ := hω
  have hposK := holding_pos_of_sigma σ hcell hc hpos
  intro ε
  ext t : 1
  rw [WeakConvergenceTransfer.scaledBrownianPath_inv_apply_div]
  unfold interpolation
  rw [H.coe_interpolatedWalk hposK hunb ε, H.coe_interpolatedWalk hposK hunb 1]
  simp

/-- **The interpolation is affine over every holding interval of the exact path**, from `p (σ v)`
to `p (σ w)` (the `hY` input of `InterpolatedConvergence.convergesWeaklyInC_interpolated`, with the
point choice `p ∘ σ`). -/
theorem ae_interpolation_segment (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) (p : H.cells → Plane) :
    ∀ᵐ ω ∂areaSampleLaw (decode e) D hG start, ∀ v w a b,
      IsOptionHoldingInterval (decode e) (fun r => exactAreaPath (decode e) D r ω) v w a b →
        ∀ r ∈ Icc a b, interpolation e D start H σ p ω r =
          AffineMap.lineMap (p (σ v)) (p (σ w)) (((r : ℝ) - a) / ((b : ℝ) - a)) := by
  filter_upwards [ae_jumpTime_eq σ hgeo hpos hwalk hfix hcell hc] with ω hω
  obtain ⟨s, hs, hT, hunb⟩ := hω
  have hposK := holding_pos_of_sigma σ hcell hc hpos
  intro v w a b hI r hr
  -- the holding interval is `[s k, s (k+1))` for some `k`
  obtain ⟨k, hk⟩ := hs.exists_mem a
  have hfa : exactAreaPath (decode e) D a ω = some v := hI.2.1 a ⟨le_rfl, hI.1⟩
  have hv : exactJumpChain e D start ω k = v :=
    Option.some_injective _ ((hs.eq_of_mem k a hk).symm.trans hfa)
  have ha : a = s k := by
    by_contra hne
    have hlt : s k < a := lt_of_le_of_ne hk.1 (Ne.symm hne)
    rcases hI.2.2.2.2 with h0 | hleft
    · rw [h0] at hlt
      exact absurd hlt (by simp)
    · obtain ⟨q, hq, hqv⟩ := hleft (s k) hlt
      exact hqv ((hs.eq_of_mem k q ⟨hq.1.le, lt_trans hq.2 hk.2⟩).trans (by rw [hv]))
  have hb : b = s (k + 1) := by
    rcases lt_trichotomy b (s (k + 1)) with hlt | heq | hgt
    · exfalso
      have hfb : exactAreaPath (decode e) D b ω = some w := hI.2.2.1
      have h1 : exactAreaPath (decode e) D b ω = some v := by
        have hsb : s k ≤ b := by
          rw [← ha]
          exact hI.1.le
        have := hs.eq_of_mem k b ⟨hsb, hlt⟩
        rw [hv] at this
        exact this
      have hvw : v = w := Option.some_injective _ (h1.symm.trans hfb)
      exact (SimpleGraph.irrefl _) (hvw ▸ hI.2.2.2.1)
    · exact heq
    · exfalso
      have h1 : exactAreaPath (decode e) D (s (k + 1)) ω = some v :=
        hI.2.1 _ ⟨by rw [ha]; exact (hs.strictMono (Nat.lt_succ_self k)).le, hgt⟩
      have h2 := hs.apply_self (k + 1)
      have : exactJumpChain e D start ω (k + 1) = exactJumpChain e D start ω k := by
        rw [hv]
        exact Option.some_injective _ (h2.symm.trans h1)
      exact hs.succ_ne k this
  have hw : exactJumpChain e D start ω (k + 1) = w := by
    have hfb : exactAreaPath (decode e) D b ω = some w := hI.2.2.1
    rw [hb] at hfb
    exact Option.some_injective _ ((hs.apply_self (k + 1)).symm.trans hfb)
  subst ha hb hv hw
  unfold interpolation
  rw [H.coe_interpolatedWalk hposK hunb 1]
  simp only [NNReal.coe_one, one_pow, div_one, one_smul]
  have hr1 : H.jumpTime (fun k => σ (exactJumpChain e D start ω k)) k ≤ (r : ℝ) := by
    rw [hT k]
    exact_mod_cast hr.1
  have hr2 : (r : ℝ) ≤ H.jumpTime (fun k => σ (exactJumpChain e D start ω k)) (k + 1) := by
    rw [hT (k + 1)]
    exact_mod_cast hr.2
  rw [CellConfig.interpolatedPath_eq_lineMap (p := p) hposK hr1 hr2, hT k, hT (k + 1)]

/-- **The integral of any measurable functional of GMS's interpolated walk under any law with
`IsSRWLaw (σ start)` equals the corresponding integral under the reflected walk's sample law.** -/
theorem integral_interpolatedWalk_eq (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : FixedStartConclusions e D hG Φ target start)
    (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w)
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw (σ start) Q) (p : H.cells → Plane) (ε : ℝ≥0)
    {G : BouRabeeGwynne.BrownianPath 2 → ℝ} (hGm : Measurable G) :
    ∫ ω', G (H.interpolatedWalk p ε ω') ∂Q =
      ∫ ω, G (BouRabeeGwynne.scaledBrownianPath ε⁻¹ (interpolation e D start H σ p ω))
        ∂(areaSampleLaw (decode e) D hG start) := by
  have := countable_cells σ
  have hposK := holding_pos_of_sigma σ hcell hc hpos
  have hJσ := aemeasurable_transportedChain σ hgeo hpos hwalk hfix
  rw [eq_map_exactJumpChain_of_isSRWLaw σ hgeo hpos hwalk hfix hc hQ]
  have hunbMap : ∀ᵐ ω' ∂(areaSampleLaw (decode e) D hG start).map
      (fun ω k => σ (exactJumpChain e D start ω k)), H.JumpTimesUnbounded ω' := by
    rw [ae_map_iff hJσ (CellConfig.measurableSet_jumpTimesUnbounded (H := H))]
    filter_upwards [ae_jumpTime_eq σ hgeo hpos hwalk hfix hcell hc] with ω hω
    obtain ⟨_, -, -, hunb⟩ := hω
    exact hunb
  refine (integral_map hJσ ?_).trans (integral_congr_ae ?_)
  · exact (hGm.comp_aemeasurable
      (CellConfig.aemeasurable_interpolatedWalk hposK p ε hunbMap)).aestronglyMeasurable
  · filter_upwards [ae_interpolatedWalk_eq_scaledBrownianPath σ hgeo hpos hwalk hfix hcell hc p]
      with ω hω
    simp only [hω ε]

/-- **Target 5: recurrence of GMS's simple random walk.** -/
theorem recurrent_of_fixedStartConclusions (hgeo : GMSGeometry (decode e).toCellConfiguration)
    (hpos : ∀ v, 0 < areaRate (decode e) v)
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hfix : ∀ start, FixedStartConclusions e D hG Φ target start)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) : H.Recurrent := by
  intro K₀ Q hQ
  have hQ' : H.IsSRWLaw (σ (σ.symm K₀)) Q := by rwa [Equiv.apply_symm_apply]
  rw [eq_map_exactJumpChain_of_isSRWLaw σ hgeo hpos hwalk (hfix (σ.symm K₀)) hc hQ']
  have hmeas : MeasurableSet {ω' : ℕ → H.cells | {n | ω' n = K₀}.Infinite} := by
    have hsetEq : {ω' : ℕ → H.cells | {n | ω' n = K₀}.Infinite} =
        ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), (fun ω' : ℕ → H.cells => ω' n) ⁻¹' {K₀} := by
      ext ω'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_singleton_iff, exists_prop]
      rw [← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
    rw [hsetEq]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurable_pi_apply n (measurableSet_singleton K₀)
  rw [ae_map_iff (aemeasurable_transportedChain σ hgeo hpos hwalk (hfix (σ.symm K₀))) hmeas]
  obtain ⟨_, _, _, -, -, hret, -⟩ := hfix (σ.symm K₀)
  filter_upwards [ae_exactJumpChain hgeo hpos hwalk (hfix (σ.symm K₀)), hret] with ω hω hr
  obtain ⟨s, _, hs, -, -, -, -⟩ := hω
  refine Nat.frequently_atTop_iff_infinite.1 (Filter.frequently_atTop.2 fun N => ?_)
  obtain ⟨t, htN, ht⟩ := hr (σ.symm K₀) (s N)
  obtain ⟨k, hk⟩ := hs.exists_mem t
  refine ⟨k, ?_, ?_⟩
  · have hlt : s N < s (k + 1) := lt_of_le_of_lt htN hk.2
    exact Nat.lt_succ_iff.1 (hs.strictMono.lt_iff_lt.1 hlt)
  · have hJk : exactJumpChain e D (σ.symm K₀) ω k = σ.symm K₀ :=
      Option.some_injective _ ((hs.eq_of_mem k t hk).symm.trans ht)
    show σ (exactJumpChain e D (σ.symm K₀) ω k) = K₀
    rw [hJk, Equiv.apply_symm_apply]

end GMS

end Environment

/-! ## The harmonic coordinate -/

/-- **Target 6: a discrete harmonic coordinate sublinear to the centroids**, from the
per-environment clauses of `IsHarmonicCoordinate`. -/
theorem exists_discreteHarmonic_sublinearToCentroid {e : Env} {H : CellConfig}
    (σ : Vertex e.val ≃ H.cells) (hcell : ∀ v, ((σ v : H.cells) : Cell) = (decode e).cell v)
    (hc : ∀ v w, H.c (σ v) (σ w) = (decode e).graph.c v w) {Φ : CellField}
    (hdh : DiscreteHarmonicity Φ e) (hsub : SublinearCorrector Φ e) :
    ∃ φ : H.cells → Plane, H.DiscreteHarmonic φ ∧ H.SublinearToCentroid φ := by
  refine ⟨fun K => Φ.at e (σ.symm K), ?_, ?_⟩
  · intro K
    obtain ⟨v, rfl⟩ := σ.surjective K
    rw [← σ.tsum_eq]
    simp only [Equiv.symm_apply_apply, hc]
    exact hdh v
  · obtain ⟨hcen, -⟩ := hsub
    rw [CellConfig.SublinearToCentroid, ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact Filter.Eventually.of_forall fun _ => by rw [htop]; exact le_top
    have hη : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨R₀, hR₀, hR⟩ := hcen ε.toReal hη
    filter_upwards [Filter.eventually_ge_atTop R₀] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
    have hsup : (⨆ (K : H.cells) (_ : (K : Cell) ∈ H.restrict (Metric.ball 0 r)),
        (‖Φ.at e (σ.symm K) - CellConfig.centroid (K : Cell)‖₊ : ℝ≥0∞)) ≤
          ENNReal.ofReal (ε.toReal * r) := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨v, rfl⟩ := σ.surjective K
      have hhit : Hits (decode e) (Metric.closedBall 0 r) v := by
        obtain ⟨-, z, hz1, hz2⟩ := hK
        refine ⟨z, ?_, Metric.ball_subset_closedBall hz2⟩
        rw [← hcell v]
        exact hz1
      have hb := hR r hr v hhit
      rw [centroid_sigma σ hcell v, Equiv.symm_apply_apply, ← ENNReal.ofReal_coe_nnreal,
        coe_nnnorm]
      exact ENNReal.ofReal_le_ofReal hb
    calc _ ≤ ENNReal.ofReal r⁻¹ * ENNReal.ofReal (ε.toReal * r) := mul_le_mul' le_rfl hsup
      _ = ENNReal.ofReal (r⁻¹ * (ε.toReal * r)) :=
          (ENNReal.ofReal_mul (inv_nonneg.2 hr0.le)).symm
      _ = ε := by
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one, ENNReal.ofReal_toReal htop]

end ReflectedGMS.GMS.WalkIdentification

open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry ae_exactAreaPath_ne_none
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry isSRWLaw_map_exactJumpChain
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry ae_exactAreaPath_eq_walk
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry eq_map_exactJumpChain_of_isSRWLaw
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry recurrent_of_fixedStartConclusions
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry exists_discreteHarmonic_sublinearToCentroid
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry ae_interpolatedWalk_eq_scaledBrownianPath
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry ae_interpolation_segment
open ReflectedGMS.GMS.WalkIdentification in
assert_no_sorry integral_interpolatedWalk_eq

#print axioms ReflectedGMS.GMS.WalkIdentification.atSpatialInfinity_of_gmsGeometry
#print axioms ReflectedGMS.GMS.WalkIdentification.ae_exactAreaPath_ne_none
#print axioms ReflectedGMS.GMS.WalkIdentification.measure_exactJumpChain_cyl
#print axioms ReflectedGMS.GMS.WalkIdentification.isSRWLaw_map_exactJumpChain
#print axioms ReflectedGMS.GMS.WalkIdentification.ae_exactAreaPath_eq_walk
#print axioms ReflectedGMS.GMS.WalkIdentification.eq_map_exactJumpChain_of_isSRWLaw
#print axioms ReflectedGMS.GMS.WalkIdentification.recurrent_of_fixedStartConclusions
#print axioms ReflectedGMS.GMS.WalkIdentification.exists_discreteHarmonic_sublinearToCentroid
#print axioms ReflectedGMS.GMS.WalkIdentification.ae_interpolatedWalk_eq_scaledBrownianPath
#print axioms ReflectedGMS.GMS.WalkIdentification.ae_interpolation_segment
#print axioms ReflectedGMS.GMS.WalkIdentification.integral_interpolatedWalk_eq
