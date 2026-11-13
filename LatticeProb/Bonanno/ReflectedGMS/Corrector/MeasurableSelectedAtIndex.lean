/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MeasurableSelectedAtIndex at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MeasurableSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActiveBlockEdges
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableBlockMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance

/-!
# The selection event of an *arbitrary* dyadic square is measurable

`Spatial/MeasurableSelectedBlocks.lean` proves that the block index `κ` and every selection
event are jointly measurable in the environment and the grid **along the origin chain**
(`measurableSet_originSelected`).  The restriction is not incidental: the ancestor indices of
the origin chain are the explicit levels `originIndex (k + j)`
(`MarkedBlockAveraging.ancestor_originIndex`), a formula free of the grid, whereas for a
general square index `s` the ancestor `ancestor D s j` depends on the grid through its parent
digits `D.digit`, and the two checked ingredients
`MeasurableSelectedBlocks.measurable_maxCellDiameter` and
`MeasurableSelectedBlocks.measurable_cellRatio` are available only at a **fixed** index.

This module removes that restriction, by the countable-partition technique that is project
policy for measurable choices (`Forms/MeasurableDirichletConstruction`,
`Corrector/MeasurableBlockMinimizer.measurable_select_of_countable`) and with no measurable
selection theorem.  The observation that makes it work is that `ancestor D s j` reads only
the **finitely many** digits `D.digit (s.1), …, D.digit (s.1 + j - 1)`, each valued in the
four-element type `Fin 2 → Fin 2`.  So for each `j` the parameter space splits into the
finitely many measurable events on which those digits are constant, and on each of them
`ancestor D s j` is a *constant* square index, where `measurable_cellRatio` applies verbatim.

* `ancestorOfWord` is the ancestor computed from an explicit digit sequence, and
  `ancestor_eq_ancestorOfWord` identifies it with `DyadicApproximation.ancestor`;
* `measurable_cellRatio_ancestor`, `measurable_ancestorRatio_index`,
  `measurable_inverseRatio_ancestor`, `measurable_blockIndex_index` and
  `measurable_blockIndex_parent` climb the chain of indices of
  `Geometry/DiameterBlockIndex`;
* `measurableSet_selected` is the conclusion: `{(e, D) | Selected (decode e) D m s}` is
  measurable for **every** real threshold `m` and **every** square index `s`.

`measurableSet_originSelected_of_index` recovers
`MeasurableSelectedBlocks.measurableSet_originSelected` as the special case
`s = originIndex k`, since `MarkedBlockAveraging.OriginSelected F D m k` is by definition
`Selected F D m (originIndex k)`; so the new statement is a strict generalisation of a result
the project already consumes, and in particular its selection events are not empty for
trivial reasons.  For a nonpositive threshold the event *is* empty, and the proof says so
explicitly rather than hiding it.

This is one of the measurability atoms needed to decide block-interpolant existence
measurably; it does **not** address the cell-versus-square incidence labels of a patch, nor
the per-square Dirichlet solvability, which are separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.MeasurableSelectedAtIndex

open StatementIngredients DyadicApproximation DiameterBlockIndex Code Spatial
open MeasurableSelectedBlocks UniformGridDilationInvariance ActiveBlockEdges
open MarkedBlockAveraging

/-! ### The ancestor chain as a function of finitely many digits -/

/-- One parent step against an explicitly supplied digit, so that the grid enters only
through `D.digit`. -/
def parentOfDigit (d : Fin 2 → Fin 2) (t : SquareIndex) : SquareIndex :=
  (t.1 + 1, fun i => (t.2 i + ((d i).val : ℤ)) / 2)

theorem parent_eq_parentOfDigit (D : Grid) (t : SquareIndex) :
    parent D t = parentOfDigit (D.digit t.1) t := rfl

/-- The `j`-th ancestor computed from an explicit digit sequence. -/
def ancestorOfWord (s : SquareIndex) (d : ℕ → Fin 2 → Fin 2) : ℕ → SquareIndex
  | 0 => s
  | j + 1 => parentOfDigit (d j) (ancestorOfWord s d j)

/-- The `j`-th ancestor uses only the first `j` digits above the level of `s`. -/
theorem ancestorOfWord_congr (s : SquareIndex) {d d' : ℕ → Fin 2 → Fin 2} :
    ∀ j : ℕ, (∀ t : ℕ, t < j → d t = d' t) →
      ancestorOfWord s d j = ancestorOfWord s d' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      have hj : ancestorOfWord s d j = ancestorOfWord s d' j :=
        ih fun t ht => h t (ht.trans (Nat.lt_succ_self j))
      show parentOfDigit (d j) (ancestorOfWord s d j)
        = parentOfDigit (d' j) (ancestorOfWord s d' j)
      rw [hj, h j (Nat.lt_succ_self j)]

/-- **The ancestor chain of a grid is the ancestor chain of its digit sequence.** -/
theorem ancestor_eq_ancestorOfWord (D : Grid) (s : SquareIndex) (j : ℕ) :
    ancestor D s j = ancestorOfWord s (fun t : ℕ => D.digit (s.1 + (t : ℤ))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hlev : (ancestor D s j).1 = s.1 + (j : ℤ) := ancestor_fst D s j
      rw [ancestor_succ', parent_eq_parentOfDigit, hlev, ih]
      rfl

/-! ### The finitely many digit words that a fixed ancestor depth can read -/

/-- The digits of the grid at the `j` levels starting from the level of `s`. -/
def digitWord (s : SquareIndex) (j : ℕ) (D : Grid) : Fin j → Fin 2 → Fin 2 :=
  fun t => D.digit (s.1 + (t.val : ℤ))

/-- A finite digit word read as a full digit sequence, with a junk value beyond its length. -/
def wordExtend {j : ℕ} (w : Fin j → Fin 2 → Fin 2) : ℕ → Fin 2 → Fin 2 :=
  fun t => if h : t < j then w ⟨t, h⟩ else fun _ => 0

/-- **The `j`-th ancestor is a function of the finite digit word alone.** -/
theorem ancestor_eq_of_digitWord (D : Grid) (s : SquareIndex) (j : ℕ) :
    ancestor D s j = ancestorOfWord s (wordExtend (digitWord s j D)) j := by
  rw [ancestor_eq_ancestorOfWord]
  refine ancestorOfWord_congr s j fun t ht => ?_
  simp only [wordExtend, digitWord, dif_pos ht]

/-- The digit word is a measurable function of the marked configuration, with finitely many
values, so its level sets partition the parameter space measurably. -/
theorem measurableSet_digitWord_eq (s : SquareIndex) (j : ℕ) (w : Fin j → Fin 2 → Fin 2) :
    MeasurableSet {p : Env × Grid | digitWord s j p.2 = w} := by
  have hEq : {p : Env × Grid | digitWord s j p.2 = w}
      = ⋂ t : Fin j, ⋂ i : Fin 2,
          (fun p : Env × Grid => p.2.digit (s.1 + (t.val : ℤ)) i) ⁻¹' {w t i} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter, mem_preimage, mem_singleton_iff, digitWord,
      funext_iff]
  rw [hEq]
  refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun i => ?_
  exact ((measurable_gridDigit (s.1 + (t.val : ℤ)) i).comp measurable_snd)
    (measurableSet_singleton (w t i))

/-! ### Measurability of the indices at an arbitrary square -/

/-- **The cell ratio of the `j`-th ancestor of an arbitrary square is jointly measurable.**
The parameter space is partitioned into the finitely many events on which the digit word is
constant; on each of them the ancestor is a fixed square index, where
`MeasurableSelectedBlocks.measurable_cellRatio` applies. -/
theorem measurable_cellRatio_ancestor (s : SquareIndex) (j : ℕ) :
    Measurable fun p : Env × Grid => cellRatio (decode p.1) p.2 (ancestor p.2 s j) := by
  have hEq : (fun p : Env × Grid => cellRatio (decode p.1) p.2 (ancestor p.2 s j))
      = fun p : Env × Grid =>
          (fun (w : Fin j → Fin 2 → Fin 2) (q : Env × Grid) =>
            cellRatio (decode q.1) q.2 (ancestorOfWord s (wordExtend w) j))
            (digitWord s j p.2) p := by
    funext p
    exact congrArg (cellRatio (decode p.1) p.2) (ancestor_eq_of_digitWord p.2 s j)
  rw [hEq]
  exact MeasurableBlockMinimizer.measurable_select_of_countable
    (measurableSet_digitWord_eq s j)
    fun w => measurable_cellRatio (ancestorOfWord s (wordExtend w) j)

/-- **The manuscript `a(S)` of an arbitrary square is jointly measurable.** -/
theorem measurable_ancestorRatio_index (s : SquareIndex) :
    Measurable fun p : Env × Grid => ancestorRatio (decode p.1) p.2 s := by
  have hEq : (fun p : Env × Grid => ancestorRatio (decode p.1) p.2 s)
      = fun p : Env × Grid => ⨆ j : ℕ, cellRatio (decode p.1) p.2 (ancestor p.2 s j) :=
    funext fun p => ancestorRatio_eq_iSup (decode p.1) p.2 s
  rw [hEq]
  exact Measurable.iSup fun j => measurable_cellRatio_ancestor s j

/-- The same for the `j`-th ancestor of an arbitrary square, again by the digit partition. -/
theorem measurable_ancestorRatio_ancestor (s : SquareIndex) (j : ℕ) :
    Measurable fun p : Env × Grid => ancestorRatio (decode p.1) p.2 (ancestor p.2 s j) := by
  have hEq : (fun p : Env × Grid => ancestorRatio (decode p.1) p.2 (ancestor p.2 s j))
      = fun p : Env × Grid =>
          (fun (w : Fin j → Fin 2 → Fin 2) (q : Env × Grid) =>
            ancestorRatio (decode q.1) q.2 (ancestorOfWord s (wordExtend w) j))
            (digitWord s j p.2) p := by
    funext p
    exact congrArg (ancestorRatio (decode p.1) p.2) (ancestor_eq_of_digitWord p.2 s j)
  rw [hEq]
  exact MeasurableBlockMinimizer.measurable_select_of_countable
    (measurableSet_digitWord_eq s j)
    fun w => measurable_ancestorRatio_index (ancestorOfWord s (wordExtend w) j)

/-- **The manuscript `b(S)` of the `j`-th ancestor of an arbitrary square.** -/
theorem measurable_inverseRatio_ancestor (s : SquareIndex) (j : ℕ) :
    Measurable fun p : Env × Grid => inverseRatio (decode p.1) p.2 (ancestor p.2 s j) :=
  (measurable_ancestorRatio_ancestor s j).inv

/-- **The manuscript block index `κ(S)` of an arbitrary square is jointly measurable.** -/
theorem measurable_blockIndex_index (s : SquareIndex) :
    Measurable fun p : Env × Grid => blockIndex (decode p.1) p.2 s := by
  have hEq : (fun p : Env × Grid => blockIndex (decode p.1) p.2 s)
      = fun p : Env × Grid => ∑' j : ℕ,
          ((4 : ℝ≥0∞) ^ j)⁻¹ * inverseRatio (decode p.1) p.2 (ancestor p.2 s j) := rfl
  rw [hEq]
  exact Measurable.ennreal_tsum fun j =>
    (measurable_inverseRatio_ancestor s j).const_mul _

/-- The block index of the parent, which is the second half of the selection condition. -/
theorem measurable_blockIndex_parent (s : SquareIndex) :
    Measurable fun p : Env × Grid => blockIndex (decode p.1) p.2 (parent p.2 s) := by
  have hEq : (fun p : Env × Grid => blockIndex (decode p.1) p.2 (parent p.2 s))
      = fun p : Env × Grid => ∑' j : ℕ,
          ((4 : ℝ≥0∞) ^ j)⁻¹ * inverseRatio (decode p.1) p.2 (ancestor p.2 s (j + 1)) := by
    funext p
    show ∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ *
        inverseRatio (decode p.1) p.2 (ancestor p.2 (parent p.2 s) j) = _
    exact tsum_congr fun j => by rw [← ancestor_succ]
  rw [hEq]
  exact Measurable.ennreal_tsum fun j =>
    (measurable_inverseRatio_ancestor s (j + 1)).const_mul _

/-! ### The selection event of an arbitrary square -/

/-- **Every selection event is measurable, at every threshold and every square index.**
For a nonpositive threshold the event is empty, which the proof records explicitly; for a
positive threshold it is the intersection of the two index comparisons, each of which is a
countable Boolean combination of the measurable diameter suprema of
`Spatial/MeasurableSelectedBlocks`. -/
theorem measurableSet_selected (m : ℝ) (s : SquareIndex) :
    MeasurableSet {p : Env × Grid | Selected (decode p.1) p.2 m s} := by
  by_cases hm : (0 : ℝ) < m
  · have hEq : {p : Env × Grid | Selected (decode p.1) p.2 m s}
        = {p : Env × Grid | blockIndex (decode p.1) p.2 s ≤ ENNReal.ofReal m} ∩
          {p : Env × Grid |
            ENNReal.ofReal m < blockIndex (decode p.1) p.2 (parent p.2 s)} := by
      ext p
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hm, h1, h2⟩
    rw [hEq]
    exact (measurableSet_le (measurable_blockIndex_index s) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_blockIndex_parent s))
  · have hEq : {p : Env × Grid | Selected (decode p.1) p.2 m s} = ∅ := by
      ext p
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨h, -, -⟩
      exact hm h
    rw [hEq]
    exact MeasurableSet.empty

/-- The selection event at a natural stage, the form used by the block-interpolation
specification `DyadicApproximation.IsBlockInterpolation`. -/
theorem measurableSet_selected_nat (m : ℕ) (s : SquareIndex) :
    MeasurableSet {p : Env × Grid | Selected (decode p.1) p.2 (m : ℝ) s} :=
  measurableSet_selected (m : ℝ) s

/-- **The origin-chain result is the special case `s = originIndex k`.**
`MarkedBlockAveraging.OriginSelected F D m k` is by definition `Selected F D m (originIndex
k)`, so `MeasurableSelectedBlocks.measurableSet_originSelected` is recovered; the general
statement above is therefore a strict generalisation of a result the project already
consumes, not a new event that might be empty. -/
theorem measurableSet_originSelected_of_index (m : ℝ) (k : ℤ) :
    MeasurableSet {p : Env × Grid | OriginSelected (decode p.1) p.2 m k} :=
  measurableSet_selected m (originIndex k)

end ReflectedGMS.MeasurableSelectedAtIndex
