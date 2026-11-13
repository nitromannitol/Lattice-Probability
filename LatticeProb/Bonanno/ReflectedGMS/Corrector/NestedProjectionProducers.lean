/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.NestedProjectionProducers at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedEnergyProjections
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActiveBlockEdges

/-!
# Producers for the nested energy projection `s:eq:pythmn`

`Corrector/NestedEnergyProjections.blockPythagoras_nested` proves the manuscript identity
`ℰ_{G_S}(φ_m) = ℰ_{G_S}(φ_n) + ℰ_{G_S}(φ_m - φ_n)` on a block `S ∈ 𝒮_n` of the `n`-partition
from two *explicit structural* hypotheses:

* `hmtr` — the **geometric pinning** `s:eq:pinnested`: `φ_m = b` on the spatial boundary of
  every `n`-block, which rests on `skel_n ⊆ skel_m` for `n ≥ m`; and
* `hmE` — finiteness of the energy of `φ_m` **on that single block**.

This module discharges the first of these from the actual dyadic geometry, and supplies the
signed edge-sum identity needed to feed the blockwise orthogonality into the mass-transport
redistribution.  The block-local energy finiteness `hmE` is *not* discharged here and stays
visible in every statement below; no finite energy of the whole infinite network is used or
assumed anywhere.

## The geometric half — `s:eq:pinnested`

* `mem_frontier_square_of_selected_of_le` — the exact coarsening statement at the level of a
  single point: if `S` is selected at parameter `m`, `T` is selected at parameter `n ≥ m`,
  and a point `z` of `∂T` lies in `S`, then `z ∈ ∂S`.  The proof is a level comparison along
  the ancestor chain, using only the checked `ActiveBlockEdges` geometry
  (`square_subset_ancestor`, `notMem_square_of_mem_interior_of_same_level`,
  `blockIndex_ancestor_monotone`): if `T` is strictly below `S` in level, the ancestor of `T`
  at `S`'s level has `κ` above `n ≥ m ≥ κ(S)`, so it is a *different* square of the same
  level and the lattice separates it from the interior of `S`; otherwise the ancestor of `S`
  at `T`'s level either differs from `T`, which the lattice again excludes, or equals `T`, in
  which case `S ⊆ T` and a point of `∂T` cannot be interior to `S`.
* `SelectionCoversOn` — the manuscript's §3.1 covering statement, *"the closures of the blocks
  cover every point belonging to a cell"*, the one structural input of the coarsening that is
  genuinely about the existence of the `κ`-stopping line and is not proved here.  The
  every-point form `SelectionCovers` is no longer available under the covering clause of
  `Geometry` and is kept only as the sharper hypothesis and for the no-regression bridges
  `SelectionCovers.on` and `SelectionCoversOn.toSelectionCovers`.
* `skeleton_subset_skeleton_of_le` — **`skel_n ⊆ skel_m` for `n ≥ m`**.
* `pinned_on_boundary_of_isBlockInterpolation` — the consumer form: `φ_m = b` on the spatial
  boundary of every `n`-selected square, for any `φ_m` satisfying the project's actual
  `DyadicApproximation.IsBlockInterpolation` (both the `m = 0` and the `m ≠ 0` clause).
* `blockPythagoras_nested_of_isBlockInterpolation` — `s:eq:pythmn` on an `n`-block with
  `hmtr` *removed*, stated directly for the actual nested block maps
  `IsBlockInterpolation F D m fm`, `IsBlockInterpolation F D n fn`.

## The signed-pairing half

`ActiveBlockEdges.vectorEnergy_eq_tsum_vectorGradSq` identifies the vector energy with half an
edge sum of the *nonnegative* coefficients `vectorGradSq`.  The redistribution of the
manuscript's *signed* coefficient `c(e) g(e)·g'(e)` needs the same identification for the
polarized coefficient:

* `vectorGradProd` — the plane-valued polarization of `vectorGradSq`, built from the existing
  `ReflectedWalk.ConductanceGraph.gradProd`;
* `ofReal_vectorGradProd_self` — `vectorGradProd G f f = vectorGradSq G f`, so the signed
  coefficient really polarizes the checked nonnegative one;
* `summable_vectorGradProd` — absolute summability from the two **block-local** energies,
  through the existing `ConductanceGraph.summable_gradProd` (pointwise Cauchy–Schwarz);
* `tsum_vectorGradProd_eq_two_mul_vectorPairing` — **`∑_e c(e) g(e)·g'(e) = 2 ⟪f, f'⟫_G`**;
* `tsum_vectorGradProd_sub_eq_zero_of_centroidTraceMinimizer` and
  `tsum_vectorGradProd_nested_eq_zero` — *"their sum on every block is zero by
  orthogonality"*, for the base competitor and for the actual nested pair `(φ_n, φ_m - φ_n)`.

What is still missing for the expected root densities is the packaging of the positive and
negative parts of that block sum as an `OwnedEdgeField` with measurable owner labels, and the
polarization of the expected root density itself; both are separately staffed.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.NestedProjectionProducers

open StatementIngredients DyadicApproximation DiameterBlockIndex ActiveBlockEdges

variable {V : Type*}

/-! ### Closed axis-parallel rectangles

The companion of the checked `ActiveBlockEdges.interior_carrier_subset`: the carrier is
closed, so a point of the frontier really lies in the rectangle. -/

/-- A closed axis-parallel rectangle is a closed set. -/
theorem isClosed_carrier (Q : Rectangle) : IsClosed Q.carrier := by
  have hcar : Q.carrier
      = (PiLp.homeomorph 2 fun _ : Fin 2 => ℝ) ⁻¹'
        (Set.univ.pi fun i => Set.Icc (Q.lower i) (Q.upper i)) := by
    ext z
    exact ⟨fun hz i _ => Set.mem_Icc.2 (hz i),
      fun hz i => Set.mem_Icc.1 (hz i (Set.mem_univ i))⟩
  rw [hcar]
  exact (isClosed_set_pi fun i _ => isClosed_Icc).preimage
    (PiLp.homeomorph 2 fun _ : Fin 2 => ℝ).continuous

theorem mem_carrier_of_mem_frontier (Q : Rectangle) {z : Plane}
    (hz : z ∈ frontier Q.carrier) : z ∈ Q.carrier :=
  (isClosed_carrier Q).closure_subset (frontier_subset_closure hz)

/-- A point of a set which is not interior to it lies on its frontier. -/
theorem mem_frontier_of_mem_of_notMem_interior {s : Set Plane} {z : Plane} (hzs : z ∈ s)
    (hz : z ∉ interior s) : z ∈ frontier s :=
  ⟨subset_closure hzs, hz⟩

/-! ### The partitions coarsen with the selection parameter

This is the geometric content of `s:eq:pinnested`. -/

/-- **Pointwise coarsening.**  Let `S` be selected at parameter `m` and `T` at parameter
`n ≥ m`.  Then every point of the spatial boundary of `T` which belongs to `S` belongs to the
spatial boundary of `S`.

Together with the fact that the selected squares cover the plane this is exactly
`skel_n ⊆ skel_m`: a cell meeting `∂T` meets `∂S` for the `m`-selected square containing the
meeting point. -/
theorem mem_frontier_square_of_selected_of_le (F : IndexedCells V) (D : Grid) {m n : ℝ}
    (hmn : m ≤ n) {s t : SquareIndex} (hs : Selected F D m s) (ht : Selected F D n t)
    {z : Plane} (hzs : z ∈ (square D s).carrier)
    (hzt : z ∈ frontier (square D t).carrier) :
    z ∈ frontier (square D s).carrier := by
  by_contra hcon
  have hint : z ∈ interior (square D s).carrier := by
    by_contra hni
    exact hcon (mem_frontier_of_mem_of_notMem_interior hzs hni)
  have hztc : z ∈ (square D t).carrier := mem_carrier_of_mem_frontier (square D t) hzt
  rcases le_or_gt s.1 t.1 with hle | hlt
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t.1 - s.1 := ⟨(t.1 - s.1).toNat, by omega⟩
    have hlev : (ancestor D s j).1 = t.1 := by
      rw [ancestor_fst, hj]
      ring
    by_cases heq : ancestor D s j = t
    · have hsub : (square D s).carrier ⊆ (square D t).carrier := by
        rw [← heq]
        exact square_subset_ancestor D s j
      exact hzt.2 (interior_mono hsub hint)
    · have hne2 : (ancestor D s j).2 ≠ t.2 := fun h2 => heq (Prod.ext hlev h2)
      exact notMem_square_of_mem_interior_of_same_level D hlev hne2
        (interior_mono (square_subset_ancestor D s j) hint) hztc
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = s.1 - t.1 := ⟨(s.1 - t.1).toNat, by omega⟩
    have hj1 : 0 < j := by omega
    have hlev : (ancestor D t j).1 = s.1 := by
      rw [ancestor_fst, hj]
      ring
    have hgt : ENNReal.ofReal m < blockIndex F D (ancestor D t j) := by
      have h1 : ENNReal.ofReal n < blockIndex F D (ancestor D t 1) := by
        rw [ancestor_one]
        exact ht.2.2
      have h2 : blockIndex F D (ancestor D t 1) ≤ blockIndex F D (ancestor D t j) :=
        blockIndex_ancestor_monotone F D t hj1
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmn) (lt_of_lt_of_le h1 h2)
    have hne2 : s.2 ≠ (ancestor D t j).2 := by
      intro h2
      have hseq : s = ancestor D t j := Prod.ext hlev.symm h2
      rw [hseq] at hs
      exact absurd hs.2.1 (not_le.2 hgt)
    exact notMem_square_of_mem_interior_of_same_level D hlev.symm hne2 hint
      (square_subset_ancestor D t j hztc)

/-- The *every point* form of the covering statement: every point of the plane lies in some
square selected at parameter `m`.  This is a statement about the existence of the
`κ`-stopping line — the same input as the hypotheses of
`DiameterBlockIndex.exists_selected_ancestor` — and is **not** proved here; it is strictly
weaker than, and says nothing about, the pinning conclusion below.

**It is no longer available under the covering clause of `Geometry`**, which only asks
`μH[1] (uncoveredSet F) = 0`.  The producers of the covering statement all go through a cell
containing the prescribed point — that is what bounds the block index of the squares around it
and forces one of them to be selected — and an uncovered point supplies no such cell; see
`Spatial/NonmacroscopicSelectedBlocks.exists_selected_mem`, whose covering side condition is
not removable.  `SelectionCoversOn` below is the manuscript's own statement and is what every
consumer actually uses; this definition is kept because at an environment with
`uncoveredSet F = ∅` the two agree (`SelectionCoversOn.toSelectionCovers`) and the old form
remains the sharper hypothesis to supply whenever it is available (`SelectionCovers.on`). -/
def SelectionCovers (F : IndexedCells V) (D : Grid) (m : ℝ) : Prop :=
  ∀ z : Plane, ∃ s : SquareIndex, Selected F D m s ∧ z ∈ (square D s).carrier

/-- **The manuscript's covering statement**, §3.1: the closures of the selected blocks *"cover
every point belonging to a cell, and hence Lebesgue-almost every point of the plane … No claim
is needed about an uncovered singular point."*

This is `SelectionCovers` with the conclusion asked only at the covered points.  It is not a
weakening in any place it is used: both consumers in the tree —
`skeleton_subset_skeleton_of_le` here and
`PairingOwnershipInstance.exists_selected_patch_of_adj` — apply it at a point that has just
been produced *inside a cell*, so the hypothesis `z ∉ uncoveredSet F` is discharged on the spot
by `notMem_uncoveredSet_of_mem_cell`.  Its domain is not empty either: the covered points are
dense (`ReflectedGMS.dense_compl_uncoveredSet`) and of full Lebesgue measure. -/
def SelectionCoversOn (F : IndexedCells V) (D : Grid) (m : ℝ) : Prop :=
  ∀ z : Plane, z ∉ uncoveredSet F →
    ∃ s : SquareIndex, Selected F D m s ∧ z ∈ (square D s).carrier

/-- A point of a cell is covered.  The trivial direction of `uncoveredSet`; the converse is
`ReflectedGMS.exists_mem_cell_of_notMem_uncoveredSet`. -/
theorem notMem_uncoveredSet_of_mem_cell {F : IndexedCells V} {v : V} {z : Plane}
    (hz : z ∈ (F.cell v : Set Plane)) : z ∉ uncoveredSet F := by
  intro hc
  exact hc (Set.mem_iUnion.2 ⟨v, hz⟩)

/-- **No regression**: the every-point form implies the manuscript's form. -/
theorem SelectionCovers.on {F : IndexedCells V} {D : Grid} {m : ℝ}
    (h : SelectionCovers F D m) : SelectionCoversOn F D m := fun z _ => h z

/-- **No regression, converse**: where nothing is uncovered — the earlier manuscript's
covering clause `⋃ v, cell v = univ` — the manuscript's form *is* the every-point form.  So
every conclusion drawn below from `SelectionCoversOn` is exactly as strong as the one drawn
from `SelectionCovers` before. -/
theorem SelectionCoversOn.toSelectionCovers {F : IndexedCells V} {D : Grid} {m : ℝ}
    (h : SelectionCoversOn F D m) (hemp : uncoveredSet F = ∅) : SelectionCovers F D m :=
  fun z => h z (by rw [hemp]; exact Set.notMem_empty z)

/-- The form in which the covering statement is consumed: at a point of a cell. -/
theorem SelectionCoversOn.of_mem_cell {F : IndexedCells V} {D : Grid} {m : ℝ}
    (h : SelectionCoversOn F D m) {v : V} {z : Plane} (hz : z ∈ (F.cell v : Set Plane)) :
    ∃ s : SquareIndex, Selected F D m s ∧ z ∈ (square D s).carrier :=
  h z (notMem_uncoveredSet_of_mem_cell hz)

/-- **`skel_n ⊆ skel_m` for `n ≥ m`** (`s:eq:pinnested`, first half).

The covering hypothesis is the manuscript's `SelectionCoversOn`, which suffices unchanged: the
point `z` at which it is applied is produced inside the cell of `v`. -/
theorem skeleton_subset_skeleton_of_le (F : IndexedCells V) (D : Grid) {m n : ℝ}
    (hmn : m ≤ n) (hcov : SelectionCoversOn F D m) :
    skeleton F D n ⊆ skeleton F D m := by
  rintro v ⟨t, ht, hv⟩
  obtain ⟨z, hzcell, hzfr⟩ :
      ((F.cell v : Set Plane) ∩ frontier (square D t).carrier).Nonempty := hv
  obtain ⟨s, hs, hzs⟩ := hcov.of_mem_cell hzcell
  exact ⟨s, hs, ⟨z, hzcell, mem_frontier_square_of_selected_of_le F D hmn hs ht hzs hzfr⟩⟩

/-! ### The pinning of `φ_m` on the boundary of an `n`-block -/

/-- On each of its selected blocks, an actual block interpolation is the centroid-trace
minimizer of that block. -/
theorem centroidTraceMinimizer_of_isBlockInterpolation (F : IndexedCells V) (D : Grid)
    {n : ℕ} (hn : n ≠ 0) {fn : V → Plane} (hfn : IsBlockInterpolation F D n fn)
    {t : SquareIndex} (ht : Selected F D (n : ℝ) t) :
    CentroidTraceMinimizer F (square D t) fn := by
  rw [IsBlockInterpolation, if_neg hn] at hfn
  exact hfn.2 t ht

/-! ### The signed edge coefficient and its block sum

`ActiveBlockEdges.vectorGradSq` is the nonnegative edge coefficient of the vector energy.  Its
polarization is the manuscript's signed coefficient `c(e) g(e)·g'(e)`. -/

section Signed

variable {W : Type*} (G : ReflectedWalk.ConductanceGraph W)

/-- The signed contribution of one ordered pair of vertices to the vector Dirichlet form:
the polarization of `ActiveBlockEdges.vectorGradSq`. -/
noncomputable def vectorGradProd (f g : W → Plane) (p : W × W) : ℝ :=
  ∑ i : Fin 2, G.gradProd (fun v => f v i) (fun v => g v i) p

theorem vectorGradProd_apply (f g : W → Plane) (p : W × W) :
    vectorGradProd G f g p
      = G.gradProd (fun v => f v 0) (fun v => g v 0) p
        + G.gradProd (fun v => f v 1) (fun v => g v 1) p := by
  simp [vectorGradProd, Fin.sum_univ_two]

/-- The signed coefficient really polarizes the checked nonnegative one. -/
theorem ofReal_vectorGradProd_self (f : W → Plane) (p : W × W) :
    ENNReal.ofReal (vectorGradProd G f f p) = vectorGradSq G f p := by
  have hself : ∀ i : Fin 2, G.gradProd (fun v => f v i) (fun v => f v i) p
      = G.gradSq (fun v => f v i) p := fun i => G.gradProd_self _ p
  rw [vectorGradProd]
  simp only [hself]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => G.gradSq_nonneg _ p]
  rfl

/-- **Absolute summability of the signed coefficient from the two block-local energies.**
This is the pointwise Cauchy–Schwarz bound of the existing
`ConductanceGraph.summable_gradProd`; only the energies of `f` and `g` *on this graph* are
used. -/
theorem summable_vectorGradProd {f g : W → Plane} (hf : vectorEnergy G f < ∞)
    (hg : vectorEnergy G g < ∞) : Summable (vectorGradProd G f g) := by
  have hf0 := hasFiniteEnergy_coord G hf 0
  have hf1 := hasFiniteEnergy_coord G hf 1
  have hg0 := hasFiniteEnergy_coord G hg 0
  have hg1 := hasFiniteEnergy_coord G hg 1
  have hsplit : vectorGradProd G f g = fun p : W × W =>
      G.gradProd (fun v => f v 0) (fun v => g v 0) p
        + G.gradProd (fun v => f v 1) (fun v => g v 1) p := by
    funext p
    exact vectorGradProd_apply G f g p
  rw [hsplit]
  exact (G.summable_gradProd hf0 hg0).add (G.summable_gradProd hf1 hg1)

/-- The scalar edge-sum identity: unconditional, since the Dirichlet form is by definition
half this sum. -/
theorem tsum_gradProd_eq (f g : W → ℝ) :
    (∑' p : W × W, G.gradProd f g p) = 2 * G.dirichletForm f g := by
  rw [ReflectedWalk.ConductanceGraph.dirichletForm]
  ring

/-- **The signed edge-sum identity** `∑_e c(e) g(e)·g'(e) = 2 ⟪f, f'⟫_G`, the signed analogue
of `ActiveBlockEdges.vectorEnergy_eq_tsum_vectorGradSq`.  Its hypotheses are exactly the two
energies **on this graph**, which on a block are the block-local energies. -/
theorem tsum_vectorGradProd_eq_two_mul_vectorPairing {f g : W → Plane}
    (hf : vectorEnergy G f < ∞) (hg : vectorEnergy G g < ∞) :
    (∑' p : W × W, vectorGradProd G f g p) = 2 * vectorPairing G f g := by
  have hf0 := hasFiniteEnergy_coord G hf 0
  have hf1 := hasFiniteEnergy_coord G hf 1
  have hg0 := hasFiniteEnergy_coord G hg 0
  have hg1 := hasFiniteEnergy_coord G hg 1
  have hsplit : vectorGradProd G f g = fun p : W × W =>
      G.gradProd (fun v => f v 0) (fun v => g v 0) p
        + G.gradProd (fun v => f v 1) (fun v => g v 1) p := by
    funext p
    exact vectorGradProd_apply G f g p
  rw [hsplit, (G.summable_gradProd hf0 hg0).tsum_add (G.summable_gradProd hf1 hg1),
    tsum_gradProd_eq, tsum_gradProd_eq]
  show _ = 2 * ∑ i : Fin 2, G.dirichletForm (fun v => f v i) (fun v => g v i)
  rw [Fin.sum_univ_two]
  ring

end Signed

/-! ### The block sum of the signed coefficient vanishes

*"Their sum on every block is zero by orthogonality."* -/

end ReflectedGMS.NestedProjectionProducers
