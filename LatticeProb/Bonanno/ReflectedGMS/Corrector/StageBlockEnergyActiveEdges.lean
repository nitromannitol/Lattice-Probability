/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageBlockEnergyActiveEdges at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageEnergyRedistributionField
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers

/-!
# The active-edge Pythagoras on a selected block, and the owned label sum

`Corrector/NestedEnergyProjections.blockPythagoras_centroid` is the Pythagorean identity
`ℰ_S(b) = ℰ_S(φ) + ℰ_S(b − φ)` for the **full** patch energy of a selected square `S`.  The
mass-transport redistribution, however, sees only the edges **owned** by `S` — its active edges
(`ActiveBlockEdges.ActiveEdge`) — and never the edges with both endpoints on the spatial boundary
of `S`.  This module proves the same identity for the active-edge energies:

* `activeEnergySum` / `inactiveEnergySum` split `2 ℰ_S(f)` into the active and the non-active
  ordered pairs of patch vertices (`activeEnergySum_add_inactiveEnergySum`);
* a non-active pair is either not an edge or has both endpoints on the skeleton
  (`vectorGradSq_eq_of_not_activeEdge`), so the non-active part is the same for any two fields
  agreeing on the skeleton (`inactiveEnergySum_congr`) and vanishes for a variation vanishing
  there (`inactiveEnergySum_eq_zero`);
* **`activeEnergySum_centroid_eq`**: for the centroid-trace minimizer `φ` of `S` pinned to the
  centroid on the skeleton, `A_S(b) = A_S(φ) + A_S(b − φ)`, obtained from the full Pythagoras by
  cancelling the common (finite) non-active part.  In particular the active energies of both the
  minimizer and the variation are dominated by the active energy of the centroid embedding.

The second half identifies the numerator of `OwnedEdgeField.ownerBlockDensity` — a sum over
ordered **label** pairs owned by the selected origin block — with `activeEnergySum` at that
block, for any owned edge field whose owner is the canonical `labelOwner` and whose weight on
owned edges is the energy coefficient (`tsum_indicator_ownedByOriginBlock_eq_activeEnergySum`,
`ownerBlockDensity_eq_activeEnergySum`).

Everything here is deterministic and block-local; no finite energy of the infinite network is
used.  **This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StageBlockEnergyActiveEdges

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open ActiveBlockEdges NestedProjectionProducers NestedEnergyProjections
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open OwnedFieldPairingTransport PairingOwnershipInstance

variable {V : Type*}

/-! ### The active and non-active energy sums of one selected block -/

section Deterministic

variable (F : IndexedCells V) (D : Grid) (m : ℝ) (S : SquareIndex)

/-- The active edges of `S`, as a set of ordered pairs of patch vertices. -/
def activePairs : Set (patchVertices F (square D S) × patchVertices F (square D S)) :=
  {q | ActiveEdge F D m S (q.1.1, q.2.1)}

/-- The energy carried by the active edges of `S` (ordered pairs, so twice the unoriented
active energy). -/
noncomputable def activeEnergySum (f : patchVertices F (square D S) → Plane) : ℝ≥0∞ :=
  ∑' q : patchVertices F (square D S) × patchVertices F (square D S),
    (activePairs F D m S).indicator
      (vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f) q

/-- The energy carried by the non-active ordered pairs of patch vertices of `S`. -/
noncomputable def inactiveEnergySum (f : patchVertices F (square D S) → Plane) : ℝ≥0∞ :=
  ∑' q : patchVertices F (square D S) × patchVertices F (square D S),
    (activePairs F D m S)ᶜ.indicator
      (vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f) q

/-- The active and the non-active sums reassemble twice the patch energy. -/
theorem activeEnergySum_add_inactiveEnergySum (f : patchVertices F (square D S) → Plane) :
    activeEnergySum F D m S f + inactiveEnergySum F D m S f
      = 2 * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S))) f := by
  unfold activeEnergySum inactiveEnergySum
  rw [← ENNReal.tsum_add]
  have h : ∀ q : patchVertices F (square D S) × patchVertices F (square D S),
      (activePairs F D m S).indicator
          (vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f) q
        + (activePairs F D m S)ᶜ.indicator
          (vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f) q
      = vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f q := by
    intro q
    have := congrFun (Set.indicator_self_add_compl (activePairs F D m S)
      (vectorGradSq (restrictGraph F.graph (patchVertices F (square D S))) f)) q
    simpa using this
  rw [tsum_congr h, vectorEnergy_eq_tsum_vectorGradSq]
  exact ((ENNReal.eq_div_iff (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ∞)).1 rfl).symm

/-- **A non-active pair sees only skeleton values.**  Either it is not an edge, in which case
its conductance vanishes, or both endpoints lie on the spatial boundary of `S`, which is part
of the skeleton. -/
theorem vectorGradSq_eq_of_not_activeEdge (hS : Selected F D m S) {f g : V → Plane}
    (hfg : ∀ v ∈ skeleton F D m, f v = g v)
    (q : patchVertices F (square D S) × patchVertices F (square D S))
    (hq : ¬ ActiveEdge F D m S (q.1.1, q.2.1)) :
    vectorGradSq (restrictGraph F.graph (patchVertices F (square D S)))
        (fun v : patchVertices F (square D S) => f v.1) q
      = vectorGradSq (restrictGraph F.graph (patchVertices F (square D S)))
        (fun v : patchVertices F (square D S) => g v.1) q := by
  by_cases hadj : F.graph.toSimpleGraph.Adj q.1.1 q.2.1
  · have hbd : q.1.1 ∈ boundaryVertices F (square D S) ∧
        q.2.1 ∈ boundaryVertices F (square D S) := by
      by_contra hb
      exact hq ⟨hS, hadj, q.1.2, q.2.2, hb⟩
    have h1 : f q.1.1 = g q.1.1 := hfg _ (mem_skeleton_of_mem_boundaryVertices F D m hS hbd.1)
    have h2 : f q.2.1 = g q.2.1 := hfg _ (mem_skeleton_of_mem_boundaryVertices F D m hS hbd.2)
    unfold vectorGradSq ReflectedWalk.ConductanceGraph.gradSq
    simp only [h1, h2]
  · have hc : F.graph.c q.1.1 q.2.1 = 0 := by
      rcases lt_or_eq_of_le (F.graph.c_nonneg q.1.1 q.2.1) with h | h
      · exact absurd (show F.graph.toSimpleGraph.Adj q.1.1 q.2.1 from h) hadj
      · exact h.symm
    have hc' : (restrictGraph F.graph (patchVertices F (square D S))).c q.1 q.2 = 0 := hc
    unfold vectorGradSq ReflectedWalk.ConductanceGraph.gradSq
    simp only [hc', zero_mul, ENNReal.ofReal_zero, Finset.sum_const_zero]

/-- The non-active sum is the same for any two fields agreeing on the skeleton. -/
theorem inactiveEnergySum_congr (hS : Selected F D m S) {f g : V → Plane}
    (hfg : ∀ v ∈ skeleton F D m, f v = g v) :
    inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => f v.1)
      = inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => g v.1) := by
  unfold inactiveEnergySum
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ (activePairs F D m S)ᶜ
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    exact vectorGradSq_eq_of_not_activeEdge F D m S hS hfg q hq
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

/-- A variation vanishing on the skeleton carries no non-active energy. -/
theorem inactiveEnergySum_eq_zero (hS : Selected F D m S) {u : V → Plane}
    (hu : ∀ v ∈ skeleton F D m, u v = 0) :
    inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => u v.1) = 0 := by
  rw [inactiveEnergySum_congr F D m S hS (g := fun _ => (0 : Plane)) hu]
  unfold inactiveEnergySum
  refine ENNReal.tsum_eq_zero.2 fun q => ?_
  refine Set.indicator_apply_eq_zero.2 fun _ => ?_
  exact vectorGradSq_eq_zero_of_apply_eq _ _ rfl

/-- **The active-edge Pythagoras.**  For the centroid-trace minimizer `φ` of `S`, pinned to the
centroid embedding `b` on the skeleton, the active energies satisfy
`A_S(b) = A_S(φ) + A_S(b − φ)`: the full Pythagoras of
`NestedEnergyProjections.blockPythagoras_centroid` with the common non-active part cancelled.
The only finiteness hypothesis is the block-local energy of the centroid embedding. -/
theorem activeEnergySum_centroid_eq (hS : Selected F D m S) {φ : V → Plane}
    (hmin : CentroidTraceMinimizer F (square D S) φ)
    (hbE : vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
      (fun v : patchVertices F (square D S) => cellCentroid F v.1) < ∞)
    (hpin : ∀ v ∈ skeleton F D m, φ v = cellCentroid F v) :
    activeEnergySum F D m S (fun v : patchVertices F (square D S) => cellCentroid F v.1)
      = activeEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
        + activeEnergySum F D m S
          (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1) := by
  have hpy : vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
        (fun v : patchVertices F (square D S) => cellCentroid F v.1)
      = vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
          (fun v : patchVertices F (square D S) => φ v.1)
        + vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
          (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1) := by
    have h := blockPythagoras_centroid F (square D S) hmin hbE
    have hfun : ((fun v : patchVertices F (square D S) => cellCentroid F v.1)
          - fun v : patchVertices F (square D S) => φ v.1)
        = fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1 := by
      funext v
      rfl
    rw [hfun] at h
    exact h
  have h1 := activeEnergySum_add_inactiveEnergySum F D m S
    (fun v : patchVertices F (square D S) => cellCentroid F v.1)
  have h2 := activeEnergySum_add_inactiveEnergySum F D m S
    (fun v : patchVertices F (square D S) => φ v.1)
  have h3 := activeEnergySum_add_inactiveEnergySum F D m S
    (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1)
  have hNu : inactiveEnergySum F D m S
      (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1) = 0 :=
    inactiveEnergySum_eq_zero F D m S hS (u := fun v => cellCentroid F v - φ v)
      (fun v hv => by rw [hpin v hv, sub_self])
  have hNb : inactiveEnergySum F D m S
        (fun v : patchVertices F (square D S) => cellCentroid F v.1)
      = inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1) :=
    inactiveEnergySum_congr F D m S hS (fun v hv => (hpin v hv).symm)
  have hNfin : inactiveEnergySum F D m S
      (fun v : patchVertices F (square D S) => φ v.1) ≠ ∞ := by
    have h2ne : (2 : ℝ≥0∞) * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
        (fun v : patchVertices F (square D S) => φ v.1) ≠ ∞ :=
      ENNReal.mul_ne_top (by simp) hmin.1.ne
    refine ne_top_of_le_ne_top h2ne ?_
    rw [← h2]
    exact le_add_self
  have key : activeEnergySum F D m S (fun v : patchVertices F (square D S) => cellCentroid F v.1)
        + inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
      = (activeEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
          + activeEnergySum F D m S
            (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1))
        + inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1) := by
    calc activeEnergySum F D m S (fun v : patchVertices F (square D S) => cellCentroid F v.1)
          + inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
        = activeEnergySum F D m S (fun v : patchVertices F (square D S) => cellCentroid F v.1)
          + inactiveEnergySum F D m S
            (fun v : patchVertices F (square D S) => cellCentroid F v.1) := by rw [hNb]
      _ = 2 * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
            (fun v : patchVertices F (square D S) => cellCentroid F v.1) := h1
      _ = 2 * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
              (fun v : patchVertices F (square D S) => φ v.1)
          + 2 * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
              (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1) := by
          rw [hpy, mul_add]
      _ = (activeEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
            + inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1))
          + (activeEnergySum F D m S
              (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1)
            + inactiveEnergySum F D m S
              (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1)) := by
          rw [h2, h3]
      _ = (activeEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1)
            + activeEnergySum F D m S
              (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1))
          + inactiveEnergySum F D m S (fun v : patchVertices F (square D S) => φ v.1) := by
          rw [hNu, add_zero]
          ring
  exact (ENNReal.add_left_inj hNfin).1 key

/-- The active energy of the variation `b − φ` is dominated by that of the centroid embedding. -/
theorem activeEnergySum_sub_le (hS : Selected F D m S) {φ : V → Plane}
    (hmin : CentroidTraceMinimizer F (square D S) φ)
    (hbE : vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
      (fun v : patchVertices F (square D S) => cellCentroid F v.1) < ∞)
    (hpin : ∀ v ∈ skeleton F D m, φ v = cellCentroid F v) :
    activeEnergySum F D m S
        (fun v : patchVertices F (square D S) => cellCentroid F v.1 - φ v.1)
      ≤ activeEnergySum F D m S (fun v : patchVertices F (square D S) => cellCentroid F v.1) := by
  rw [activeEnergySum_centroid_eq F D m S hS hmin hbE hpin]
  exact le_add_self

/-- **A variation vanishing on the skeleton has finite block energy as soon as its active
energy is finite**: its non-active energy is zero. -/
theorem vectorEnergy_lt_top_of_activeEnergySum_lt_top (hS : Selected F D m S) {u : V → Plane}
    (hu : ∀ v ∈ skeleton F D m, u v = 0)
    (hA : activeEnergySum F D m S (fun v : patchVertices F (square D S) => u v.1) < ∞) :
    vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
      (fun v : patchVertices F (square D S) => u v.1) < ∞ := by
  have h := activeEnergySum_add_inactiveEnergySum F D m S
    (fun v : patchVertices F (square D S) => u v.1)
  rw [inactiveEnergySum_eq_zero F D m S hS hu, add_zero] at h
  have h2 : 2 * vectorEnergy (restrictGraph F.graph (patchVertices F (square D S)))
      (fun v : patchVertices F (square D S) => u v.1) < ∞ := by
    rw [← h]
    exact hA
  exact lt_of_le_of_lt (le_mul_of_one_le_left zero_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)) h2

end Deterministic

/-! ### The owned label sum is the active energy sum at the selected origin block -/

section Owned

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

/-- The owner block of the origin is covered by the ordered pairs of its patch vertices, for
any owned edge field whose owner is the canonical `labelOwner`. -/
theorem ownedByOriginBlock_subset_range (Q : OwnedEdgeField R m)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), Q.owner ω q = labelOwner R m ω q) (ω : Ω) :
    Q.ownedByOriginBlock ω ⊆
      Set.range (labelPair (R.env ω)
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)))) := by
  rintro ⟨a, b⟩ hp
  have h : labelOwner R m ω (a, b)
      = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := by
    rw [← hO]
    exact hp
  by_cases ha : ((R.env ω).val.1 a).isSome
  · by_cases hb : ((R.env ω).val.1 b).isSome
    · rw [labelOwner_pair R m ω a b ha hb] at h
      have hact := activeEdge_of_activeOwner_eq_some (decode (R.env ω)) (R.grid ω) m h
      exact ⟨(⟨⟨a, ha⟩, hact.2.2.1⟩, ⟨⟨b, hb⟩, hact.2.2.2.1⟩), rfl⟩
    · rw [labelOwner_eq_none_of_snd R m ω a hb] at h
      exact absurd h (by simp)
  · rw [labelOwner_eq_none_of_fst R m ω ha b] at h
    exact absurd h (by simp)

/-- **The owned label sum is the active energy sum of the selected origin block**, for any
owned edge field with the canonical owner whose weight on owned edges is the energy
coefficient of `Ψ`. -/
theorem tsum_indicator_ownedByOriginBlock_eq_activeEnergySum (Q : OwnedEdgeField R m)
    (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), Q.owner ω q = labelOwner R m ω q)
    (hw : ∀ (ω : Ω) (p : ℕ × ℕ) (s : SquareIndex), Q.owner ω p = some s →
      Q.weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) (ω : Ω) :
    (∑' p : ℕ × ℕ, (Q.ownedByOriginBlock ω).indicator (Q.weight ω) p)
      = activeEnergySum (decode (R.env ω)) (R.grid ω) m
          (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)
          (fun v : patchVertices (decode (R.env ω))
            (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)) =>
              Ψ ω v.1) := by
  have hcell : ∀ v : Vertex (R.env ω).val, IsConnected ((decode (R.env ω)).cell v : Set Plane) :=
    (decode_geometry (R.env ω)).1
  have hsupp : Function.support ((Q.ownedByOriginBlock ω).indicator (Q.weight ω)) ⊆
      Set.range (labelPair (R.env ω)
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)))) :=
    Set.support_indicator_subset.trans (ownedByOriginBlock_subset_range Q hO ω)
  rw [← (injective_labelPair (R.env ω) _).tsum_eq hsupp]
  unfold activeEnergySum
  refine tsum_congr fun q => ?_
  by_cases hq : ActiveEdge (decode (R.env ω)) (R.grid ω) m
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) (q.1.1, q.2.1)
  · have hmem : labelPair (R.env ω) _ q ∈ Q.ownedByOriginBlock ω := by
      show Q.owner ω (q.1.1.1, q.2.1.1) = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)
      rw [hO, labelOwner_pair R m ω _ _ q.1.1.2 q.2.1.2]
      exact activeOwner_eq_some_of_activeEdge (decode (R.env ω)) hcell (R.grid ω) m hq
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show q ∈ activePairs (decode (R.env ω)) (R.grid ω) m
        (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) from hq),
      hw ω _ _ hmem, pairCoeff_labelPair R Ψ Ψ ω _ q, ofReal_vectorGradProd_self]
  · have hnot : labelPair (R.env ω) _ q ∉ Q.ownedByOriginBlock ω := by
      intro hmem
      have h : Q.owner ω (q.1.1.1, q.2.1.1)
          = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := hmem
      rw [hO, labelOwner_pair R m ω _ _ q.1.1.2 q.2.1.2] at h
      exact hq (activeEdge_of_activeOwner_eq_some (decode (R.env ω)) (R.grid ω) m h)
    rw [Set.indicator_of_notMem hnot,
      Set.indicator_of_notMem (show q ∉ activePairs (decode (R.env ω)) (R.grid ω) m
        (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) from hq)]

/-- **The owner-block density is the active energy sum over twice the block area.** -/
theorem ownerBlockDensity_eq_activeEnergySum (Q : OwnedEdgeField R m)
    (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), Q.owner ω q = labelOwner R m ω q)
    (hw : ∀ (ω : Ω) (p : ℕ × ℕ) (s : SquareIndex), Q.owner ω p = some s →
      Q.weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) (ω : Ω) :
    Q.ownerBlockDensity ω
      = activeEnergySum (decode (R.env ω)) (R.grid ω) m
          (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)
          (fun v : patchVertices (decode (R.env ω))
            (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)) =>
              Ψ ω v.1) / (2 * ENNReal.ofReal (R.blockSideAt m ω ^ 2)) := by
  unfold OwnedEdgeField.ownerBlockDensity
  rw [tsum_indicator_ownedByOriginBlock_eq_activeEnergySum Q Ψ hO hw ω]

/-- A finite owner-block density means a finite active energy at the origin block. -/
theorem activeEnergySum_lt_top_of_ownerBlockDensity_lt_top (Q : OwnedEdgeField R m)
    (Ψ : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), Q.owner ω q = labelOwner R m ω q)
    (hw : ∀ (ω : Ω) (p : ℕ × ℕ) (s : SquareIndex), Q.owner ω p = some s →
      Q.weight ω p = ENNReal.ofReal (pairCoeff (R.env ω) (Ψ ω) (Ψ ω) p)) (ω : Ω)
    (h : Q.ownerBlockDensity ω < ∞) :
    activeEnergySum (decode (R.env ω)) (R.grid ω) m
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)
      (fun v : patchVertices (decode (R.env ω))
        (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)) =>
          Ψ ω v.1) < ∞ := by
  rw [ownerBlockDensity_eq_activeEnergySum Q Ψ hO hw ω] at h
  have hd : 2 * ENNReal.ofReal (R.blockSideAt m ω ^ 2) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hd0 : 2 * ENNReal.ofReal (R.blockSideAt m ω ^ 2) ≠ 0 :=
    mul_ne_zero (by simp) (ENNReal.ofReal_pos.2 (pow_pos (R.blockSideAt_pos m ω) 2)).ne'
  have hmul := ENNReal.mul_lt_top h (lt_top_iff_ne_top.2 hd)
  rwa [ENNReal.div_mul_cancel hd0 hd] at hmul

end Owned

end ReflectedGMS.StageBlockEnergyActiveEdges
