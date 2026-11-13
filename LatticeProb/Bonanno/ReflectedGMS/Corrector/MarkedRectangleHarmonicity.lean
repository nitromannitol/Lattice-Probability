/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedRectangleHarmonicity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import LatticeProb.Bonanno.ReflectedGMS.Geometry.BoundaryAnchoring
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexTest
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LimitingPotentialFreeOrthogonality

/-!
# `MarkedHarmonicity` from one approximant-level input (`s:prop:limit`(a), `s:eq:freeorth`)

`HarmonicCoordinateAssembly.MarkedHarmonicity ν ms` is the `hharm` input of
`harmonicCoordinateConclusions_of_named_inputs`.  It has **three** conjuncts, all about the
*limit* `Φ = markedPotential ms ω`:

1. `FullRectangleOrthogonality (decode ω.1) Φ` — finite patch energy on every bounded
   rectangle and orthogonality to the **full** finite-energy zero-spatial-boundary variation
   space of that rectangle;
2. `FullRectangleMinimizer (decode ω.1) Φ` — full-energy Dirichlet minimality for the
   prescribed trace, **with uniqueness**;
3. `∀ v, ∑' w, c(v,w) • (Φ w − Φ v) = 0` — vector-valued pointwise discrete harmonicity.

This module proves all three from
* `HarmonicCoordinateAssembly.MarkedPatchConvergence ν ms`, which is **already** an input of
  `harmonicCoordinateConclusions_of_named_inputs` (so it costs nothing), and
* one new named atomic input, `MarkedApproximantRectangleOrthogonality ν ms`, which is a
  statement about the *concrete block interpolants* `phi` and not about the limit: on each
  bounded rectangle the interpolants have finite patch energy, and *eventually along the
  subsequence* they are free-orthogonal on that rectangle.  Its intended producer is the
  blockwise minimality of `DyadicApproximation.CentroidTraceMinimizer` (checked, via
  `NestedEnergyProjections.vectorPairing_sub_eq_zero_of_centroidTraceMinimizer`) together
  with the geometric fact that a fixed rectangle eventually sits strictly inside a selected
  square; that geometric half is **not** proved here.

Nothing below certifies that input, and nothing below proves the harmonic-coordinate main
theorem.  `harmonicCoordinateConclusions_of_approximant_orthogonality` is a conditional
reduction exactly like `harmonicCoordinateConclusions_of_named_inputs`, with `hharm`
replaced by the approximant-level hypothesis.

## What is *not* assumed

Per the standing correction, pointwise harmonicity does **not** give variational minimality
on an infinite patch, so conjunct 2 is **not** deduced from conjunct 3.  Both are deduced
from conjunct 1, which is the genuine variational statement:

* conjunct 2 comes from the first-variation identity plus the **boundary anchoring** of the
  patch graph, which the checked `Geometry/BoundaryAnchoring` supplies from the cell geometry
  alone (`boundaryAnchored_restrictGraph_cells_hitting`); the uniqueness half is then the
  definiteness statement `eq_zero_of_zeroTrace_energy_zero` of `Analysis/AnchoredEnergy`;
* conjunct 3 comes from testing conjunct 1 against a **single-vertex** variation on a
  rectangle whose interior swallows the cell of the vertex, using the checked integration by
  parts `VertexTest.dirichletForm_indic_eq_neg_laplacian`.

Competitor classes are the full finite-energy spaces throughout: no finite-support closure,
no decay condition, and no finiteness of the patch is used anywhere.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS

namespace MarkedRectangleHarmonicity

open StatementIngredients

/-! ### Coordinate arithmetic in the plane -/

/-- A coordinate of a plane vector is bounded by its Euclidean norm. -/
theorem abs_coord_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖x i‖ ^ 2 ≤ ∑ j : Fin 2, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖x j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h1 : |x i| = Real.sqrt (‖x i‖ ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]
  rw [h1]
  exact Real.sqrt_le_sqrt hle

/-- Coordinatewise extensionality for plane vectors, in the coordinate form used below. -/
theorem plane_ext {x y : Plane} (h : ∀ i : Fin 2, x i = y i) : x = y :=
  UnmarkedCoordinateDescent.plane_ext h

/-- A finite sum of plane vectors is computed coordinatewise. -/
theorem sum_coord {V : Type*} (N : Finset V) (h : V → Plane) (i : Fin 2) :
    (∑ w ∈ N, h w) i = ∑ w ∈ N, h w i := by
  classical
  refine Finset.induction_on N ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp

/-! ### Elementary facts about the vector energy and the vector pairing -/

section VectorToolbox

variable {W : Type*} (H : ReflectedWalk.ConductanceGraph W)

/-- A single coordinate energy never exceeds the vector energy. -/
theorem energyENN_coord_le_vectorEnergy (f : W → Plane) (i : Fin 2) :
    energyENN H (fun v => f v i) ≤ vectorEnergy H f :=
  Finset.single_le_sum (f := fun j : Fin 2 => energyENN H (fun v => f v j))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- The coordinate energy of a difference is insensitive to the order of the difference. -/
theorem energyENN_coord_sub_comm (f g : W → Plane) (i : Fin 2) :
    energyENN H ((fun v => f v i) - fun v => g v i)
      = energyENN H (fun v => (g v - f v) i) := by
  unfold energyENN
  refine congrArg (fun t : ℝ≥0∞ => t / 2) (tsum_congr fun p => ?_)
  congr 1
  simp only [ReflectedWalk.ConductanceGraph.gradSq, Pi.sub_apply, PiLp.sub_apply]
  ring

/-- The Dirichlet form against the zero test function vanishes. -/
theorem dirichletForm_zero_right (f : W → ℝ) : H.dirichletForm f (fun _ => (0 : ℝ)) = 0 := by
  simp [ReflectedWalk.ConductanceGraph.dirichletForm,
    ReflectedWalk.ConductanceGraph.gradProd]

/-- Pairing a plane-valued field against a variation carried by a single coordinate. -/
theorem vectorPairing_single (f : W → Plane) (g : W → ℝ) (i : Fin 2) :
    vectorPairing H f (fun z => (EuclideanSpace.single i (g z) : Plane))
      = H.dirichletForm (fun z => f z i) g := by
  have key : ∀ j : Fin 2, H.dirichletForm (fun z => f z j)
      (fun z => (EuclideanSpace.single i (g z) : Plane) j)
      = if j = i then H.dirichletForm (fun z => f z i) g else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · have hz : (fun z => (EuclideanSpace.single i (g z) : Plane) j) = fun _ => (0 : ℝ) := by
        funext z
        simp [hj]
      rw [hz, dirichletForm_zero_right, if_neg hj]
  have hdef : vectorPairing H f (fun z => (EuclideanSpace.single i (g z) : Plane))
      = ∑ j : Fin 2, H.dirichletForm (fun z => f z j)
        (fun z => (EuclideanSpace.single i (g z) : Plane) j) := rfl
  rw [hdef, Finset.sum_congr rfl fun j _ => key j]
  simp

/-- **Pythagoras from orthogonality.**  If the pairing of `f` with `u` vanishes then the
vector energies add.  This is the converse direction to
`NestedEnergyProjections.vectorPairing_sub_eq_zero_of_min`. -/
theorem vectorEnergy_add_of_vectorPairing_eq_zero {f u : W → Plane}
    (hf : vectorEnergy H f < ∞) (hu : vectorEnergy H u < ∞)
    (h0 : vectorPairing H f u = 0) :
    vectorEnergy H (f + u) = vectorEnergy H f + vectorEnergy H u := by
  have hfc : ∀ i : Fin 2, H.HasFiniteEnergy fun v => f v i := fun i =>
    hasFiniteEnergy_coord H hf i
  have huc : ∀ i : Fin 2, H.HasFiniteEnergy fun v => u v i := fun i =>
    hasFiniteEnergy_coord H hu i
  have hsc : ∀ i : Fin 2, H.HasFiniteEnergy fun v => (f + u) v i := by
    intro i
    have hrw : (fun v => (f + u) v i) = (fun v => f v i) + fun v => u v i := by
      funext v
      simp only [Pi.add_apply, PiLp.add_apply]
    rw [hrw]
    exact (hfc i).add (huc i)
  have hline := NestedEnergyProjections.sum_energy_line H f u hfc huc 1
  have hsum : (∑ i : Fin 2, H.Energy fun v => (f + u) v i)
      = (∑ i : Fin 2, H.Energy fun v => f v i) + ∑ i : Fin 2, H.Energy fun v => u v i := by
    have hEq : (∑ i : Fin 2, H.Energy fun v => (f + u) v i)
        = ∑ i : Fin 2, H.Energy fun v => f v i + (1 : ℝ) * u v i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      funext v
      simp only [Pi.add_apply, PiLp.add_apply, one_mul]
    rw [hEq, hline, h0]
    ring
  rw [vectorEnergy_eq_ofReal_sum H hsc, vectorEnergy_eq_ofReal_sum H hfc,
    vectorEnergy_eq_ofReal_sum H huc, hsum,
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => H.Energy_nonneg _)
      (Finset.sum_nonneg fun i _ => H.Energy_nonneg _)]

end VectorToolbox

/-! ### Patch geometry: anchoring, neighbours, and an engulfing rectangle -/

section PatchGeometry

variable {V : Type*} [Countable V] (F : IndexedCells V)

/-- **The patch graph of a rectangle is anchored at its spatial boundary vertices.**  This is
`Geometry/BoundaryAnchoring` specialised to a rectangle carrier, which is bounded.  It is the
geometric input left open in the docstring of `Forms/VectorTraceMinimizer`. -/
theorem boundaryAnchored_patchVertices (hF : Geometry F) (Q : Rectangle) :
    BoundaryAnchored (restrictGraph F.graph (patchVertices F Q))
      {z : patchVertices F Q | (z : V) ∈ boundaryVertices F Q} :=
  boundaryAnchored_restrictGraph_cells_hitting F hF Q.carrier
    (BlockInterpolantExistence.isBounded_carrier Q)

/-- A neighbour of a patch vertex which does not meet the spatial boundary is again in the
patch. -/
theorem mem_patchVertices_of_adj (hF : Geometry F) {Q : Rectangle} {v w : V}
    (hv : v ∈ patchVertices F Q) (hvb : v ∉ boundaryVertices F Q)
    (hadj : F.graph.toSimpleGraph.Adj v w) : w ∈ patchVertices F Q := by
  by_contra hw
  exact hvb (hits_frontier_of_adj_of_hits_of_not_hits F hF hadj hv hw)

omit [Countable V] in
/-- **Every cell sits strictly inside some bounded rectangle.**  The cell is compact, so a
large enough axis-parallel square contains it in its interior; the vertex is then a patch
vertex which does not meet the spatial boundary. -/
theorem exists_rectangle_engulfing_cell (v : V) :
    ∃ Q : Rectangle, v ∈ patchVertices F Q ∧ v ∉ boundaryVertices F Q := by
  obtain ⟨r, hr⟩ := (F.cell v).isCompact.isBounded.subset_closedBall (0 : Plane)
  have hSpos : (0 : ℝ) < |r| + 1 := by positivity
  have hbox : ∀ z ∈ (F.cell v : Set Plane), ∀ i : Fin 2,
      -(|r| + 1) < z i ∧ z i < |r| + 1 := by
    intro z hz i
    have hnorm : ‖z‖ ≤ r := by
      have hball := hr hz
      rwa [mem_closedBall_zero_iff] at hball
    have hzi : |z i| ≤ ‖z‖ := abs_coord_le_norm z i
    have habs : |z i| < |r| + 1 := by
      have hra : r ≤ |r| := le_abs_self r
      linarith
    exact abs_lt.1 habs
  refine ⟨⟨fun _ => -(|r| + 1), fun _ => |r| + 1, fun _ => neg_lt_self hSpos⟩, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (F.cell v).nonempty
    refine ⟨z, hz, ?_⟩
    intro i
    exact ⟨(hbox z hz i).1.le, (hbox z hz i).2.le⟩
  · rintro ⟨z, hzc, hzf⟩
    set S : ℝ := |r| + 1 with hSdef
    set U : Set Plane := {y : Plane | ∀ i : Fin 2, -S < y i ∧ y i < S} with hUdef
    have hUopen : IsOpen U := by
      have h0 : Continuous fun y : Plane => y 0 := PiLp.continuous_apply 2 _ (0 : Fin 2)
      have h1 : Continuous fun y : Plane => y 1 := PiLp.continuous_apply 2 _ (1 : Fin 2)
      have hset : U = ((fun y : Plane => y 0) ⁻¹' Set.Ioo (-S) S)
          ∩ ((fun y : Plane => y 1) ⁻¹' Set.Ioo (-S) S) := by
        apply Set.eq_of_subset_of_subset
        · intro y hy
          exact ⟨⟨(hy 0).1, (hy 0).2⟩, (hy 1).1, (hy 1).2⟩
        · intro y hy
          show ∀ i : Fin 2, -S < y i ∧ y i < S
          rw [Fin.forall_fin_two]
          exact ⟨⟨hy.1.1, hy.1.2⟩, hy.2.1, hy.2.2⟩
      rw [hset]
      exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)
    have hUsub : U ⊆ ({z : Plane | ∀ i : Fin 2,
        (fun _ => -S) i ≤ z i ∧ z i ≤ (fun _ => S) i} : Set Plane) := by
      intro y hy i
      exact ⟨(hy i).1.le, (hy i).2.le⟩
    have hzU : z ∈ U := hbox z hzc
    exact hzf.2 (interior_maximal hUsub hUopen hzU)

end PatchGeometry

/-! ### Conjunct 2 and conjunct 3 from conjunct 1 -/

section FromOrthogonality

variable {V : Type*} [Countable V] {F : IndexedCells V}

omit [Countable V] in
/-- A single-coordinate variation supported by a scalar zero-trace function is an admissible
full-energy zero-spatial-boundary variation. -/
theorem fullZeroBoundaryVariation_single (F : IndexedCells V) (Q : Rectangle)
    (g : patchVertices F Q → ℝ) (i : Fin 2)
    (hg : (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy g)
    (hg0 : ∀ z : patchVertices F Q, (z : V) ∈ boundaryVertices F Q → g z = 0) :
    FullZeroBoundaryVariation F Q (fun z => (EuclideanSpace.single i (g z) : Plane)) := by
  constructor
  · refine vectorEnergy_lt_top_of_coord _ ?_
    intro j
    by_cases hj : j = i
    · subst hj
      have hrw : (fun z : patchVertices F Q =>
          (EuclideanSpace.single j (g z) : Plane) j) = g := by
        funext z
        simp
      rw [hrw]
      exact hg
    · have hrw : (fun z : patchVertices F Q =>
          (EuclideanSpace.single i (g z) : Plane) j) = fun _ => (0 : ℝ) := by
        funext z
        simp [hj]
      rw [hrw]
      exact (restrictGraph F.graph (patchVertices F Q)).hasFiniteEnergy_zero
  · intro z hz
    show (EuclideanSpace.single i (g z) : Plane) = 0
    rw [hg0 z hz]
    exact (PiLp.single_eq_zero_iff 2 i).mpr rfl

/-- **Conjunct 2 from conjunct 1.**  Free orthogonality against the *full* finite-energy
zero-spatial-boundary variation space makes the field an honest full-energy Dirichlet
minimizer for its own trace, and the boundary anchoring of the patch graph upgrades this to
uniqueness.  No finite-support closure and no finiteness of the patch is used. -/
theorem fullRectangleMinimizer_of_orthogonality (hF : Geometry F) {Φ : V → Plane}
    (horth : FullRectangleOrthogonality F Φ) : FullRectangleMinimizer F Φ := by
  intro Q
  obtain ⟨hΦE, hpair⟩ := horth Q
  refine ⟨hΦE, fun f htrace => ?_⟩
  by_cases hfE : vectorEnergy (restrictGraph F.graph (patchVertices F Q)) f = ∞
  · refine ⟨by rw [hfE]; exact le_top, fun heq => ?_⟩
    rw [hfE] at heq
    exact absurd heq.symm hΦE.ne
  · have hfEfin : vectorEnergy (restrictGraph F.graph (patchVertices F Q)) f < ∞ :=
      lt_top_iff_ne_top.2 hfE
    have hΦc : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun z : patchVertices F Q => Φ (z : V) i) := fun i => hasFiniteEnergy_coord _ hΦE i
    have hfc : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun z : patchVertices F Q => f z i) := fun i => hasFiniteEnergy_coord _ hfEfin i
    have hwc : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun z : patchVertices F Q => (f - fun z : patchVertices F Q => Φ (z : V)) z i) := by
      intro i
      have hrw : (fun z : patchVertices F Q =>
            (f - fun z : patchVertices F Q => Φ (z : V)) z i)
          = (fun z : patchVertices F Q => f z i)
            - fun z : patchVertices F Q => Φ (z : V) i := by
        funext z
        simp only [Pi.sub_apply, PiLp.sub_apply]
      rw [hrw]
      exact (hfc i).sub (hΦc i)
    have hwE : vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (f - fun z : patchVertices F Q => Φ (z : V)) < ∞ :=
      vectorEnergy_lt_top_of_coord _ hwc
    have hw0 : ∀ z : patchVertices F Q, (z : V) ∈ boundaryVertices F Q →
        (f - fun z : patchVertices F Q => Φ (z : V)) z = 0 := by
      intro z hz
      simp only [Pi.sub_apply, htrace z hz, sub_self]
    have h0 : vectorPairing (restrictGraph F.graph (patchVertices F Q))
        (fun z : patchVertices F Q => Φ (z : V))
        (f - fun z : patchVertices F Q => Φ (z : V)) = 0 :=
      hpair _ ⟨hwE, hw0⟩
    have hadd := vectorEnergy_add_of_vectorPairing_eq_zero
      (restrictGraph F.graph (patchVertices F Q)) hΦE hwE h0
    have hfw : (fun z : patchVertices F Q => Φ (z : V))
        + (f - fun z : patchVertices F Q => Φ (z : V)) = f := by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    rw [hfw] at hadd
    refine ⟨by rw [hadd]; exact le_self_add, fun heq => ?_⟩
    have hwzero : vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (f - fun z : patchVertices F Q => Φ (z : V)) = 0 := by
      by_contra hne
      have hlt := ENNReal.lt_add_right hΦE.ne hne
      rw [← hadd, heq] at hlt
      exact lt_irrefl _ hlt
    have hanch := boundaryAnchored_patchVertices F hF Q
    have hcoordzero : ∀ i : Fin 2,
        (fun z : patchVertices F Q => (f - fun z : patchVertices F Q => Φ (z : V)) z i) = 0 := by
      intro i
      refine eq_zero_of_zeroTrace_energy_zero _ hanch (hwc i) (fun a ha => ?_) ?_
      · rw [hw0 a ha]
        simp
      · have hle := energyENN_coord_le_vectorEnergy
          (restrictGraph F.graph (patchVertices F Q))
          (f - fun z : patchVertices F Q => Φ (z : V)) i
        rw [hwzero, le_zero_iff] at hle
        rw [← energyENN_toReal_eq_Energy _ (hwc i), hle]
        simp
    funext z
    refine UnmarkedCoordinateDescent.plane_ext fun i => ?_
    have hz := congrFun (hcoordzero i) z
    simp only [Pi.sub_apply, PiLp.sub_apply, Pi.zero_apply, sub_eq_zero] at hz
    exact hz

/-- **Conjunct 3 from conjunct 1.**  Testing the free-orthogonality identity against the
single-vertex variation on a rectangle whose interior swallows the cell of `v` gives the
vector-valued discrete harmonicity at `v`.  Only the cell geometry is used: the rectangle
exists because cells are compact, and all the neighbours of `v` lie in the patch because a
cell strictly inside the rectangle cannot be adjacent to a cell missing it. -/
theorem tsum_smul_sub_eq_zero_of_orthogonality (hF : Geometry F) {Φ : V → Plane}
    (horth : FullRectangleOrthogonality F Φ) (v : V) :
    ∑' w : V, F.graph.c v w • (Φ w - Φ v) = 0 := by
  classical
  obtain ⟨Q, hvQ, hvB⟩ := exists_rectangle_engulfing_cell F v
  obtain ⟨hΦE, hpair⟩ := horth Q
  have hΦc : ∀ i : Fin 2, (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
      (fun z : patchVertices F Q => Φ (z : V) i) := fun i => hasFiniteEnergy_coord _ hΦE i
  have hcoord : ∀ i : Fin 2, ∑' w : V, F.graph.c v w * (Φ w i - Φ v i) = 0 := by
    intro i
    have hind0 : ∀ z : patchVertices F Q, (z : V) ∈ boundaryVertices F Q →
        (restrictGraph F.graph (patchVertices F Q)).indic ⟨v, hvQ⟩ z = 0 := by
      intro z hz
      have hne : z ≠ ⟨v, hvQ⟩ := by
        rintro rfl
        exact hvB hz
      simp [ReflectedWalk.ConductanceGraph.indic, hne]
    have hvar := fullZeroBoundaryVariation_single F Q
      ((restrictGraph F.graph (patchVertices F Q)).indic ⟨v, hvQ⟩) i
      (VertexTest.indic_hasFiniteEnergy _ _) hind0
    have h0 := hpair _ hvar
    rw [vectorPairing_single (restrictGraph F.graph (patchVertices F Q))
        (fun z : patchVertices F Q => Φ (z : V)) _ i,
      VertexTest.dirichletForm_indic_eq_neg_laplacian _ _ (hΦc i)] at h0
    have h1 : ∑' z : patchVertices F Q,
        (restrictGraph F.graph (patchVertices F Q)).lapTerm
          (fun z : patchVertices F Q => Φ (z : V) i) ⟨v, hvQ⟩ z = 0 := neg_eq_zero.1 h0
    have hsupp : Function.support (fun w : V => F.graph.c v w * (Φ w i - Φ v i))
        ⊆ patchVertices F Q := by
      intro w hw
      have hc : F.graph.c v w ≠ 0 := by
        intro h
        exact hw (by simp [h])
      have hadj : F.graph.toSimpleGraph.Adj v w := by
        rw [ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
        exact lt_of_le_of_ne (F.graph.c_nonneg v w) (Ne.symm hc)
      exact mem_patchVertices_of_adj F hF hvQ hvB hadj
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    exact h1
  have hfin : (F.graph.toSimpleGraph.neighborSet v).Finite := hF.2.2.2.2.2.2.1 v
  have hout : ∀ w ∉ hfin.toFinset, F.graph.c v w • (Φ w - Φ v) = (0 : Plane) := by
    intro w hw
    have hc : F.graph.c v w = 0 := by
      by_contra hne
      refine hw (hfin.mem_toFinset.2 ?_)
      rw [SimpleGraph.mem_neighborSet, ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
      exact lt_of_le_of_ne (F.graph.c_nonneg v w) (Ne.symm hne)
    rw [hc, zero_smul]
  rw [tsum_eq_sum hout]
  refine plane_ext fun i => ?_
  have hout' : ∀ w ∉ hfin.toFinset, F.graph.c v w * (Φ w i - Φ v i) = 0 := by
    intro w hw
    have h := congrArg (fun x : Plane => x i) (hout w hw)
    simpa [PiLp.smul_apply, PiLp.sub_apply] using h
  have hterm : ∀ w ∈ hfin.toFinset,
      (F.graph.c v w • (Φ w - Φ v) : Plane) i = F.graph.c v w * (Φ w i - Φ v i) := by
    intro w _
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hsum : ∑ w ∈ hfin.toFinset, F.graph.c v w * (Φ w i - Φ v i) = 0 := by
    have hz := hcoord i
    rwa [tsum_eq_sum hout'] at hz
  rw [sum_coord, Finset.sum_congr rfl hterm, hsum]
  simp

end FromOrthogonality

/-! ### Conjunct 1 from patch-energy convergence and approximant orthogonality -/

section Transfer

variable {V : Type*}

end Transfer

/-! ### The marked-level input and the discharge of `MarkedHarmonicity` -/

section Marked

open Code EnvironmentFields EnvironmentLaws DyadicApproximation RootDensities
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly

end Marked

end MarkedRectangleHarmonicity

end ReflectedGMS
