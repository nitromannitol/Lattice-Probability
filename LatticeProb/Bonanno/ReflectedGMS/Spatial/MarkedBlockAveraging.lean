/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.MarkedBlockAveraging at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DiameterBlockIndex
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Marked conditional block averaging

This module carries out the measure-theoretic half of the manuscript lemma
"Conditional block averaging" (`s:lem:conditional`, Section "Spatial tools
without a joint ergodicity assertion") for the *actual* selected dyadic squares
of `ReflectedGMS.DyadicApproximation`.

The geometry is exact, not abstract:

* the dyadic square containing the origin at level `k` is always the index
  `originIndex k = (k, 0)`, because `Grid.origin_position` normalises the
  relative origin to its own square.  `parent_originIndex` and
  `ancestor_originIndex` identify the whole origin ancestor chain;
* `OriginSelected F D m k` is the manuscript's `S_m(0) = S` for the concrete
  `DyadicApproximation.Selected` threshold, and along the origin chain it is
  unique (`originSelected_unique`) and exists (`exists_originSelected`) by the
  checked selection results of `ReflectedGMS.DiameterBlockIndex`;
* `blockSet` is the half-open selected origin square, so the selected squares
  really partition the plane and the re-rooted block of an interior point is a
  translate of the original block.

On top of this geometry a marked configuration space is a measurable space
`Ω` with an environment observable, a further independent dyadic system
(`MarkedReRooting.grid`, the manuscript's `𝔻'`) and a measurable re-rooting
action `ω ↦ ω - z`.  The block average

`A_m U (ω) = ℓ(S_m(0))⁻² ∫_{S_m(0)} U (ω - z) dz`

is `MarkedReRooting.blockAverageLint` (nonnegative form) and
`MarkedReRooting.blockAverage` (Bochner form).

The results proved here are exactly the conditional-expectation half of the
lemma:

* `MarkedReRooting.blockSigma` is the sigma-field of measurable events whose
  indicator is unchanged by re-rooting at a point of the selected origin block,
  and `blockSigma_le` makes it a sub-sigma-field;
* `blockAverageLint_indicator` is the manuscript's step "inside the origin block
  `1_B` is unchanged", i.e. `A_m (1_B U) = 1_B A_m U`;
* `blockAverageLint_shift` is the invariance of `A_m` under every allowed
  re-rooting, hence `measurable_blockSigma_blockAverageLint`: `A_m` is
  `𝒢_m`-measurable;
* `setLIntegral_blockAverageLint` is the testing identity
  `E[1_B A_m U] = E[1_B U]` for invariant `B`;
* `blockAverage_ae_eq_condExp` concludes `A_m F = E[F | 𝒢_m]`.

The single probabilistic input is `MarkedReRooting.MarkedBlockTransport`: the
mark-averaged mass-transport identity `E[A_m U] = E[U]`, i.e. the manuscript's
marked transport `T(ω, 𝔻', w, z) = 1_{z ∈ S_m(w)} ℓ(S_m(w))⁻² U(ω - z)` read
through `EnvironmentLaws.MassTransport` after averaging over the independent
marks.  Its producer — the covariant kernel construction for the re-rooting
action together with the similarity invariance of the mark law — is *not*
proved here and is exposed as this explicit hypothesis, together with the
measurability data of the selected block (`BlockEquivariant`, the measurable
block graph and the measurable block side length).  No tail triviality and no
joint grid ergodicity is used anywhere.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.MarkedBlockAveraging

open StatementIngredients DyadicApproximation DiameterBlockIndex Code

variable {V : Type*}

/-! ### The origin ancestor chain -/

/-- Extensionality for square indices, which are pairs of a level and a lattice
position. -/
theorem squareIndex_ext {s t : SquareIndex} (h1 : s.1 = t.1) (h2 : ∀ i, s.2 i = t.2 i) :
    s = t :=
  Prod.ext h1 (funext h2)

/-- The dyadic square of level `k` containing the origin.  By
`Grid.origin_position` the relative origin of every level lies in its own
square, so this is the zero lattice position. -/
def originIndex (k : ℤ) : SquareIndex := (k, fun _ => (0 : ℤ))

@[simp] theorem originIndex_fst (k : ℤ) : (originIndex k).1 = k := rfl

@[simp] theorem originIndex_snd (k : ℤ) (i : Fin 2) : (originIndex k).2 i = 0 := rfl

/-- The parent of the origin square of level `k` is the origin square of level
`k + 1`: the binary digit is `0` or `1`, so integer division sends it to `0`. -/
theorem parent_originIndex (D : Grid) (k : ℤ) :
    parent D (originIndex k) = originIndex (k + 1) := by
  refine squareIndex_ext rfl fun i => ?_
  have h0 : (0 : ℤ) ≤ ((D.digit k i).val : ℤ) := Int.natCast_nonneg _
  have h2 : ((D.digit k i).val : ℤ) < 2 := by exact_mod_cast (D.digit k i).isLt
  have hpar : (parent D (originIndex k)).2 i
      = ((0 : ℤ) + ((D.digit k i).val : ℤ)) / 2 := rfl
  rw [hpar, originIndex_snd]
  omega

/-- The origin ancestor chain is the chain of origin squares. -/
theorem ancestor_originIndex (D : Grid) (k : ℤ) (j : ℕ) :
    ancestor D (originIndex k) j = originIndex (k + (j : ℤ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestor_succ' D (originIndex k) j, ih, parent_originIndex]
      congr 1
      push_cast
      ring

/-- The half-open dyadic square: these really partition the plane, so the
selected block of a point is unambiguous. -/
def halfOpenSquare (D : Grid) (s : SquareIndex) : Set Plane :=
  {z | ∀ i, (square D s).lower i ≤ z i ∧ z i < (square D s).upper i}

theorem halfOpenSquare_subset (D : Grid) (s : SquareIndex) :
    halfOpenSquare D s ⊆ (square D s).carrier := by
  intro z hz i
  exact ⟨(hz i).1, le_of_lt (hz i).2⟩

/-- The origin belongs to every origin square, by `Grid.origin_position`. -/
theorem zero_mem_halfOpenSquare_originIndex (D : Grid) (k : ℤ) :
    (0 : Plane) ∈ halfOpenSquare D (originIndex k) := by
  intro i
  have hpos := D.origin_position k i
  have hside : side D k = (2 : ℝ) ^ (D.phase + (k : ℝ)) := rfl
  have hlow : (square D (originIndex k)).lower i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) := rfl
  have hupp : (square D (originIndex k)).upper i
      = D.origin k i + side D k * ((0 : ℤ) : ℝ) + side D k := rfl
  have hzero : (0 : Plane) i = 0 := rfl
  rw [hlow, hupp, hzero]
  constructor
  · simpa using hpos.2
  · have h1 : -(side D k) < D.origin k i := by rw [hside]; exact hpos.1
    simp only [Int.cast_zero, mul_zero, add_zero]
    linarith

/-! ### The selected origin block -/

/-- The manuscript's `S_m(0)`: the origin square of level `k` is selected. -/
def OriginSelected (F : IndexedCells V) (D : Grid) (m : ℝ) (k : ℤ) : Prop :=
  Selected F D m (originIndex k)

/-- Strict increase of `κ` along the origin chain, from the checked
`DiameterBlockIndex.blockIndex_lt_blockIndex_parent_of_tendsto`.  The
hypotheses are the manuscript's finiteness of `κ` and `b(S^{(j)}) → ∞`. -/
theorem strictMono_blockIndex_originIndex (F : IndexedCells V) (D : Grid)
    (hfin : ∀ k : ℤ, blockIndex F D (originIndex k) ≠ ∞)
    (htop : ∀ k : ℤ, Filter.Tendsto
      (fun j : ℕ => inverseRatio F D (ancestor D (originIndex k) j))
      Filter.atTop (nhds ∞)) :
    StrictMono fun k : ℤ => blockIndex F D (originIndex k) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  have h := blockIndex_lt_blockIndex_parent_of_tendsto F D (originIndex k) (hfin k) (htop k)
  rwa [parent_originIndex] at h

/-- Along the origin chain at most one square is selected. -/
theorem originSelected_unique {F : IndexedCells V} {D : Grid} {m : ℝ}
    (hmono : StrictMono fun k : ℤ => blockIndex F D (originIndex k))
    {k l : ℤ} (hk : OriginSelected F D m k) (hl : OriginSelected F D m l) : k = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : ENNReal.ofReal m < blockIndex F D (originIndex (k + 1)) := by
      have h2 := hk.2.2
      rwa [parent_originIndex] at h2
    have h3 : blockIndex F D (originIndex (k + 1)) ≤ blockIndex F D (originIndex l) :=
      hmono.monotone (by omega)
    exact absurd hl.2.1 (not_le.2 (lt_of_lt_of_le h1 h3))
  · have h1 : ENNReal.ofReal m < blockIndex F D (originIndex (l + 1)) := by
      have h2 := hl.2.2
      rwa [parent_originIndex] at h2
    have h3 : blockIndex F D (originIndex (l + 1)) ≤ blockIndex F D (originIndex k) :=
      hmono.monotone (by omega)
    exact absurd hk.2.1 (not_le.2 (lt_of_lt_of_le h1 h3))

/-- Along the origin chain a selected square exists as soon as `κ` crosses the
level `m`, by the checked `DiameterBlockIndex.exists_selected_ancestor`. -/
theorem exists_originSelected (F : IndexedCells V) (D : Grid) (m : ℝ) (hm : 0 < m)
    {k₀ k₁ : ℤ} (hle : k₀ ≤ k₁)
    (h0 : blockIndex F D (originIndex k₀) ≤ ENNReal.ofReal m)
    (h1 : ENNReal.ofReal m < blockIndex F D (originIndex k₁)) :
    ∃ k : ℤ, OriginSelected F D m k := by
  have hchain : ancestor D (originIndex k₀) (k₁ - k₀).toNat = originIndex k₁ := by
    rw [ancestor_originIndex]
    congr 1
    omega
  obtain ⟨j, hj⟩ :=
    exists_selected_ancestor F D m hm (originIndex k₀) h0 (k₁ - k₀).toNat (by rwa [hchain])
  refine ⟨k₀ + (j : ℤ), ?_⟩
  rwa [ancestor_originIndex] at hj

/-- The selected level of the origin block, with a junk value where no selected
origin square exists. -/
noncomputable def blockLevel (F : IndexedCells V) (D : Grid) (m : ℝ) : ℤ :=
  Classical.epsilon fun k : ℤ => OriginSelected F D m k

theorem originSelected_blockLevel {F : IndexedCells V} {D : Grid} {m : ℝ}
    (h : ∃ k : ℤ, OriginSelected F D m k) : OriginSelected F D m (blockLevel F D m) :=
  Classical.epsilon_spec h

theorem blockLevel_eq {F : IndexedCells V} {D : Grid} {m : ℝ}
    (hmono : StrictMono fun k : ℤ => blockIndex F D (originIndex k))
    {k : ℤ} (hk : OriginSelected F D m k) : blockLevel F D m = k :=
  originSelected_unique hmono (originSelected_blockLevel ⟨k, hk⟩) hk

/-- The selected origin square `S_m(0)`. -/
noncomputable def blockSquareIndex (F : IndexedCells V) (D : Grid) (m : ℝ) : SquareIndex :=
  originIndex (blockLevel F D m)

/-- The manuscript's `ℓ(S_m(0))`. -/
noncomputable def blockSide (F : IndexedCells V) (D : Grid) (m : ℝ) : ℝ :=
  side D (blockLevel F D m)

theorem blockSide_pos (F : IndexedCells V) (D : Grid) (m : ℝ) : 0 < blockSide F D m :=
  side_pos D _

/-- The selected origin block, as a half-open square. -/
noncomputable def blockSet (F : IndexedCells V) (D : Grid) (m : ℝ) : Set Plane :=
  halfOpenSquare D (blockSquareIndex F D m)

theorem zero_mem_blockSet (F : IndexedCells V) (D : Grid) (m : ℝ) :
    (0 : Plane) ∈ blockSet F D m :=
  zero_mem_halfOpenSquare_originIndex D _

/-! ### Marked configurations and re-rooting -/

/-- A marked configuration space: the environment `𝓗`, any independent marks
recorded by the space itself, a further independent uniform dyadic system
`grid` (the manuscript's `𝔻'`), and the measurable re-rooting action
`shift z ω = ω - z`.  Only the action laws are required here; the invariance of
the mark law is not part of this data. -/
structure MarkedReRooting (Ω : Type*) [MeasurableSpace Ω] where
  /-- The environment observable of a marked configuration. -/
  env : Ω → Env
  /-- The further independent uniform dyadic system attached to the marks. -/
  grid : Ω → Grid
  /-- Re-rooting: `shift z ω` is the configuration `ω` seen from `z`. -/
  shift : Plane → Ω → Ω
  measurable_shift : Measurable fun p : Ω × Plane => shift p.2 p.1
  shift_zero : ∀ ω, shift 0 ω = ω
  shift_shift : ∀ (w z : Plane) (ω : Ω), shift z (shift w ω) = shift (w + z) ω

namespace MarkedReRooting

variable {Ω : Type*} [MeasurableSpace Ω] (R : MarkedReRooting Ω) (m : ℝ)

/-- The selected level of the origin block of a marked configuration. -/
noncomputable def blockLevelAt (ω : Ω) : ℤ :=
  blockLevel (decode (R.env ω)) (R.grid ω) m

/-- The manuscript's `ℓ(S_m(0))` for a marked configuration. -/
noncomputable def blockSideAt (ω : Ω) : ℝ :=
  blockSide (decode (R.env ω)) (R.grid ω) m

/-- The selected origin block `S_m(0)` of a marked configuration. -/
noncomputable def blockSetAt (ω : Ω) : Set Plane :=
  blockSet (decode (R.env ω)) (R.grid ω) m

theorem blockSideAt_pos (ω : Ω) : 0 < R.blockSideAt m ω :=
  blockSide_pos _ _ _

theorem zero_mem_blockSetAt (ω : Ω) : (0 : Plane) ∈ R.blockSetAt m ω :=
  zero_mem_blockSet _ _ _

/-- Re-rooting at a point of the selected origin block translates that block and
preserves its side length: the selected partition commutes with re-rooting.
This is the equivariance supplied by the similarity invariance of the
environment and mark laws; it is an explicit producer dependency. -/
def BlockEquivariant : Prop :=
  ∀ (ω : Ω) (w : Plane), w ∈ R.blockSetAt m ω →
    R.blockSetAt m (R.shift w ω) = (fun y => w + y) ⁻¹' R.blockSetAt m ω ∧
      R.blockSideAt m (R.shift w ω) = R.blockSideAt m ω

/-! ### The block-invariant sigma-field -/

/-- An event whose indicator is unchanged by translating a point of the selected
origin block to the origin. -/
def BlockInvariant (A : Set Ω) : Prop :=
  ∀ (ω : Ω) (w : Plane), w ∈ R.blockSetAt m ω → (R.shift w ω ∈ A ↔ ω ∈ A)

/-- The manuscript's `𝒢_m`: the measurable events that are unchanged by every
allowed re-rooting inside the selected origin block. -/
def blockSigma : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ R.BlockInvariant m A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun ω w hw => not_congr (hA.2 ω w hw)⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun ω w hw => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2 ω w hw⟩

theorem blockSigma_le : R.blockSigma m ≤ ‹MeasurableSpace Ω› := fun _ hA => hA.1

/-! ### The spatial block average -/

/-- The manuscript's `A_m`, in the nonnegative extended-real form:
`ℓ(S_m(0))⁻² ∫_{S_m(0)} U(ω - z) dz`. -/
noncomputable def blockAverageLint (U : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ *
    ∫⁻ z in R.blockSetAt m ω, U (R.shift z ω) ∂volume

/-- The manuscript's `A_m`, in Bochner form. -/
noncomputable def blockAverage (f : Ω → ℝ) (ω : Ω) : ℝ :=
  (R.blockSideAt m ω ^ 2)⁻¹ * ∫ z in R.blockSetAt m ω, f (R.shift z ω) ∂volume

variable {R m}

/-- Inside the origin block an invariant indicator is constant, so it factors out
of the block average.  This is the manuscript's step "inside the origin block,
`1_B` is unchanged", **at a single configuration**: only the invariance of `A`
along the block of `ω` is used.

The pointwise form is what the almost-sure theory of
`SpatialMaximalInequality.blockSigmaOn` needs, where the manuscript asks for
invariance only on its invariant domain and sets the construction to zero off it;
`blockAverageLint_indicator` is the original statement, recovered below. -/
theorem blockAverageLint_indicator_at
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω)) {A : Set Ω} (U : Ω → ℝ≥0∞) (ω : Ω)
    (hA : ∀ z ∈ R.blockSetAt m ω, (R.shift z ω ∈ A ↔ ω ∈ A)) :
    R.blockAverageLint m (A.indicator U) ω = A.indicator (R.blockAverageLint m U) ω := by
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    unfold blockAverageLint
    congr 1
    refine setLIntegral_congr_fun (hset ω) fun z hz => ?_
    exact Set.indicator_of_mem ((hA z hz).mpr hω) U
  · rw [Set.indicator_of_notMem hω]
    unfold blockAverageLint
    have hzero : (∫⁻ z in R.blockSetAt m ω, (A.indicator U) (R.shift z ω) ∂volume) = 0 := by
      refine setLIntegral_eq_zero (hset ω) fun z hz => ?_
      exact Set.indicator_of_notMem (fun h => hω ((hA z hz).mp h)) U
    rw [hzero, mul_zero]

/-- Inside the origin block an invariant indicator is constant, so it factors out
of the block average.  This is the manuscript's step "inside the origin block,
`1_B` is unchanged". -/
theorem blockAverageLint_indicator
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω))
    {A : Set Ω} (hA : R.BlockInvariant m A) (U : Ω → ℝ≥0∞) (ω : Ω) :
    R.blockAverageLint m (A.indicator U) ω = A.indicator (R.blockAverageLint m U) ω :=
  blockAverageLint_indicator_at hset U ω fun z hz => hA ω z hz

/-- The block average is unchanged by an allowed re-rooting, **from the equivariance
at that single configuration**: a change of variables moves the translated block back
onto the original one.  Only `hBlock`/`hSide` at `(ω, w)` are used, which is what the
almost-sure `SpatialMaximalInequality.BlockEquivariantOn` supplies. -/
theorem blockAverageLint_shift_at
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω))
    (U : Ω → ℝ≥0∞) (ω : Ω) {w : Plane}
    (hBlock : R.blockSetAt m (R.shift w ω) = (fun y => w + y) ⁻¹' R.blockSetAt m ω)
    (hSide : R.blockSideAt m (R.shift w ω) = R.blockSideAt m ω) :
    R.blockAverageLint m U (R.shift w ω) = R.blockAverageLint m U ω := by
  unfold blockAverageLint
  rw [hSide]
  congr 1
  have hpre : MeasurableSet ((fun y : Plane => w + y) ⁻¹' R.blockSetAt m ω) :=
    (measurable_const_add w) (hset ω)
  have hstep1 : (∫⁻ z in R.blockSetAt m (R.shift w ω), U (R.shift z (R.shift w ω)) ∂volume)
      = ∫⁻ z in (fun y : Plane => w + y) ⁻¹' R.blockSetAt m ω,
          U (R.shift (w + z) ω) ∂volume := by
    rw [hBlock]
    exact setLIntegral_congr_fun hpre fun z _ => congrArg U (R.shift_shift w z ω)
  have hstep2 : (∫⁻ z in (fun y : Plane => w + y) ⁻¹' R.blockSetAt m ω,
        U (R.shift (w + z) ω) ∂volume)
      = ∫⁻ z : Plane,
          (R.blockSetAt m ω).indicator (fun y : Plane => U (R.shift y ω)) (w + z) ∂volume := by
    rw [← lintegral_indicator hpre]
    refine lintegral_congr fun z => ?_
    by_cases hz : w + z ∈ R.blockSetAt m ω
    · rw [Set.indicator_of_mem (show z ∈ (fun y : Plane => w + y) ⁻¹' R.blockSetAt m ω from hz),
        Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem
        (show z ∉ (fun y : Plane => w + y) ⁻¹' R.blockSetAt m ω from hz),
        Set.indicator_of_notMem hz]
  have hstep3 : (∫⁻ z : Plane,
        (R.blockSetAt m ω).indicator (fun y : Plane => U (R.shift y ω)) (w + z) ∂volume)
      = ∫⁻ y : Plane,
          (R.blockSetAt m ω).indicator (fun y : Plane => U (R.shift y ω)) y ∂volume :=
    lintegral_add_left_eq_self _ w
  rw [hstep1, hstep2, hstep3, lintegral_indicator (hset ω)]

/-- The block average is unchanged by every allowed re-rooting: a change of
variables moves the translated block back onto the original one. -/
theorem blockAverageLint_shift (hequi : R.BlockEquivariant m)
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω))
    (U : Ω → ℝ≥0∞) (ω : Ω) {w : Plane} (hw : w ∈ R.blockSetAt m ω) :
    R.blockAverageLint m U (R.shift w ω) = R.blockAverageLint m U ω :=
  blockAverageLint_shift_at hset U ω (hequi ω w hw).1 (hequi ω w hw).2

/-! ### Measurability of the block average -/

variable (R m)

/-- Joint measurability of the selected origin block.  Together with
`Measurable (blockSideAt)` this is the measurability half of the selected-block
producer dependency. -/
def MeasurableBlockGraph : Prop :=
  MeasurableSet {p : Ω × Plane | p.2 ∈ R.blockSetAt m p.1}

variable {R m}

theorem measurableSet_blockSetAt (hgraph : R.MeasurableBlockGraph m) (ω : Ω) :
    MeasurableSet (R.blockSetAt m ω) := by
  have hmap : Measurable fun z : Plane => ((ω, z) : Ω × Plane) := measurable_prodMk_left
  exact hmap hgraph

theorem measurable_blockAverageLint (hgraph : R.MeasurableBlockGraph m)
    (hside : Measurable (R.blockSideAt m)) {U : Ω → ℝ≥0∞} (hU : Measurable U) :
    Measurable (R.blockAverageLint m U) := by
  have hcomp : Measurable fun p : Ω × Plane => U (R.shift p.2 p.1) :=
    hU.comp R.measurable_shift
  have hind : Measurable fun p : Ω × Plane =>
      {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1}.indicator
        (fun q : Ω × Plane => U (R.shift q.2 q.1)) p := hcomp.indicator hgraph
  have hinner : Measurable fun ω : Ω => ∫⁻ z : Plane,
      {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1}.indicator
        (fun q : Ω × Plane => U (R.shift q.2 q.1)) (ω, z) ∂volume :=
    hind.lintegral_prod_right'
  have hsection : ∀ ω : Ω, (∫⁻ z : Plane,
      {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1}.indicator
        (fun q : Ω × Plane => U (R.shift q.2 q.1)) (ω, z) ∂volume)
      = ∫⁻ z in R.blockSetAt m ω, U (R.shift z ω) ∂volume := by
    intro ω
    rw [← lintegral_indicator (measurableSet_blockSetAt hgraph ω)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ R.blockSetAt m ω
    · rw [Set.indicator_of_mem (show (ω, z) ∈ {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1} from hz),
        Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem
        (show (ω, z) ∉ {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1} from hz),
        Set.indicator_of_notMem hz]
  have hnorm : Measurable fun ω : Ω => (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ :=
    ((hside.pow_const 2).ennreal_ofReal).inv
  have hrw : R.blockAverageLint m U = fun ω : Ω =>
      (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ * ∫⁻ z : Plane,
        {q : Ω × Plane | q.2 ∈ R.blockSetAt m q.1}.indicator
          (fun q : Ω × Plane => U (R.shift q.2 q.1)) (ω, z) ∂volume := by
    funext ω
    simp only [blockAverageLint]
    rw [hsection ω]
  rw [hrw]
  exact hnorm.mul hinner

/-- The block average is measurable for the block-invariant sigma-field. -/
theorem measurable_blockSigma_blockAverageLint (hequi : R.BlockEquivariant m)
    (hgraph : R.MeasurableBlockGraph m) (hside : Measurable (R.blockSideAt m))
    {U : Ω → ℝ≥0∞} (hU : Measurable U) :
    Measurable[R.blockSigma m] (R.blockAverageLint m U) := by
  intro s hs
  refine ⟨measurable_blockAverageLint hgraph hside hU hs, fun ω w hw => ?_⟩
  simp only [Set.mem_preimage]
  rw [blockAverageLint_shift hequi (measurableSet_blockSetAt hgraph) U ω hw]

/-! ### The mark-averaged transport identity and the testing identity -/

variable (R m)

variable {R m}

/-! ### The conditional-expectation identity -/

theorem blockAverage_eq_toReal {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (ω : Ω) :
    R.blockAverage m f ω
      = (R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω).toReal := by
  have hmeasz : Measurable fun z : Plane => f (R.shift z ω) :=
    hf.comp (R.measurable_shift.comp measurable_prodMk_left)
  have hint : (∫ z in R.blockSetAt m ω, f (R.shift z ω) ∂volume)
      = (∫⁻ z in R.blockSetAt m ω, ENNReal.ofReal (f (R.shift z ω)) ∂volume).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hf0 _)
      hmeasz.aestronglyMeasurable
  have hs : (0 : ℝ) < R.blockSideAt m ω := R.blockSideAt_pos m ω
  have hsq : (0 : ℝ) < R.blockSideAt m ω ^ 2 := by positivity
  rw [blockAverage, blockAverageLint, hint, ENNReal.toReal_mul]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos hsq, ENNReal.toReal_ofReal (le_of_lt (inv_pos.2 hsq))]

theorem blockAverage_nonneg {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (ω : Ω) :
    0 ≤ R.blockAverage m f ω := by
  rw [blockAverage_eq_toReal hf hf0 ω]
  exact ENNReal.toReal_nonneg

theorem blockAverage_eq_toReal_fun {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) :
    R.blockAverage m f
      = fun ω => (R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω).toReal :=
  funext fun ω => blockAverage_eq_toReal hf hf0 ω

theorem measurable_blockAverage (hgraph : R.MeasurableBlockGraph m)
    (hside : Measurable (R.blockSideAt m)) {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) : Measurable (R.blockAverage m f) := by
  rw [blockAverage_eq_toReal_fun hf hf0]
  exact (measurable_blockAverageLint hgraph hside hf.ennreal_ofReal).ennreal_toReal

theorem lintegral_ofReal_ne_top {μ : Measure Ω} {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hint : Integrable f μ) : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≠ ∞ :=
  ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).1 hint.2).ne

end MarkedReRooting

/-! ### The conditional-expectation identity for a sub-sigma-field of `𝒢_m`

The manuscript's `𝒢_m` also requires invariance under common scaling, and its mass
transport is applied only to *scale-invariant* test functions `U = 1_B F`.  The variant
below therefore takes an arbitrary sub-sigma-field `𝒢 ≤ blockSigma m` together with the
transport identity tested only on `1_A · U` for `A ∈ 𝒢`; the similarity-invariant
sigma-field is an instance, and `MarkedBlockTransport` is the instance `𝒢 = blockSigma m`. -/

/-- A sub-sigma-field of `Ω` carried as data.  Wrapping it keeps it from being picked up as
an ambient `MeasurableSpace` instance on `Ω` (the same device as
`SpatialMaximalInequality.EnvSigma`). -/
structure SubSigma (Ω : Type*) where
  /-- The underlying sigma-field. -/
  sigma : MeasurableSpace Ω

namespace MarkedReRooting

variable {Ω : Type*} [MeasurableSpace Ω] (R : MarkedReRooting Ω) (m : ℝ)

/-- The mark-averaged transport identity `E[A_m (1_A U)] = E[1_A U]`, tested on the events
of a sub-sigma-field `𝒢` only. -/
def BlockTransportOn (𝒢 : SubSigma Ω) (μ : Measure Ω) (U : Ω → ℝ≥0∞) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝒢.sigma] A →
    (∫⁻ ω, R.blockAverageLint m (A.indicator U) ω ∂μ) = ∫⁻ ω, A.indicator U ω ∂μ

variable {R m}

/-- The testing identity `E[1_B A_m U] = E[1_B U]` from the transport identity for the
single test function `1_B U`, needing the block invariance of `B` only **almost surely**.

This is the manuscript's own hypothesis: §3.1 asks for invariance on a measurable invariant
domain and sets the construction to zero off it, so under the singular-set covering clause
`μH[1] (uncoveredSet F) = 0` the invariance is available only at almost every configuration.
`setLIntegral_blockAverageLint_of_identity` is the everywhere-invariant original. -/
theorem setLIntegral_blockAverageLint_of_identity_ae {μ : Measure Ω}
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω))
    {A : Set Ω} (hAmeas : MeasurableSet A)
    (hAinv : ∀ᵐ ω ∂μ, ∀ z ∈ R.blockSetAt m ω, (R.shift z ω ∈ A ↔ ω ∈ A)) {U : Ω → ℝ≥0∞}
    (hT : (∫⁻ ω, R.blockAverageLint m (A.indicator U) ω ∂μ) = ∫⁻ ω, A.indicator U ω ∂μ) :
    (∫⁻ ω in A, R.blockAverageLint m U ω ∂μ) = ∫⁻ ω in A, U ω ∂μ := by
  rw [← lintegral_indicator hAmeas, ← lintegral_indicator hAmeas]
  refine Eq.trans (lintegral_congr_ae ?_) hT
  filter_upwards [hAinv] with ω hω
  exact (blockAverageLint_indicator_at hset U ω hω).symm

/-- The testing identity `E[1_B A_m U] = E[1_B U]` for one block-invariant event `B`, from
the transport identity for the single test function `1_B U`. -/
theorem setLIntegral_blockAverageLint_of_identity {μ : Measure Ω}
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω))
    {A : Set Ω} (hA : MeasurableSet[R.blockSigma m] A) {U : Ω → ℝ≥0∞}
    (hT : (∫⁻ ω, R.blockAverageLint m (A.indicator U) ω ∂μ) = ∫⁻ ω, A.indicator U ω ∂μ) :
    (∫⁻ ω in A, R.blockAverageLint m U ω ∂μ) = ∫⁻ ω in A, U ω ∂μ :=
  setLIntegral_blockAverageLint_of_identity_ae hset hA.1
    (Filter.Eventually.of_forall fun ω z hz => hA.2 ω z hz) hT

theorem lintegral_blockAverageLint_ofReal_ne_top_of_on {μ : Measure Ω}
    {𝒢 : SubSigma Ω} {f : Ω → ℝ}
    (hT : R.BlockTransportOn m 𝒢 μ fun x => ENNReal.ofReal (f x))
    (hf0 : ∀ ω, 0 ≤ f ω) (hint : Integrable f μ) :
    (∫⁻ ω, R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω ∂μ) ≠ ∞ := by
  have h := hT Set.univ (@MeasurableSet.univ Ω 𝒢.sigma)
  simp only [Set.indicator_univ] at h
  rw [h]
  exact lintegral_ofReal_ne_top hf0 hint

/-- **Conditional block averaging on an invariant domain.**  If the block average of `f` is
measurable for a sub-sigma-field `𝒢` whose events are block invariant **almost surely**, and
the mark-averaged transport identity holds for the test functions `1_A f`, `A ∈ 𝒢`, then
`A_m f = E[f | 𝒢]`.

This is the form the manuscript actually uses: `𝒢` is the sigma-field of events invariant
under re-rooting inside the block *and* under common scaling, `1_A f` is scale invariant, and
§3.1 asks for the block invariance only on a measurable invariant domain — which, under the
singular-set covering clause `μH[1] (uncoveredSet F) = 0`, is all that is available, the
selected block being undefined at an uncovered origin.  `blockAverage_ae_eq_condExp_of_sigma`
is the everywhere-invariant original, recovered below at no loss. -/
theorem blockAverage_ae_eq_condExp_of_sigma_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hgraph : R.MeasurableBlockGraph m) (hside : Measurable (R.blockSideAt m))
    {𝒢 : SubSigma Ω} (hle : 𝒢.sigma ≤ ‹MeasurableSpace Ω›)
    (hinv : ∀ A : Set Ω, MeasurableSet[𝒢.sigma] A →
      ∀ᵐ ω ∂μ, ∀ z ∈ R.blockSetAt m ω, (R.shift z ω ∈ A ↔ ω ∈ A))
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (hint : Integrable f μ)
    (hmeasG : Measurable[𝒢.sigma] (R.blockAverage m f))
    (hT : R.BlockTransportOn m 𝒢 μ fun x => ENNReal.ofReal (f x)) :
    R.blockAverage m f =ᵐ[μ] μ[f|𝒢.sigma] := by
  have hset := measurableSet_blockSetAt hgraph
  have hmeasA : Measurable (R.blockAverageLint m fun x => ENNReal.ofReal (f x)) :=
    measurable_blockAverageLint hgraph hside hf.ennreal_ofReal
  have hfinL := lintegral_blockAverageLint_ofReal_ne_top_of_on hT hf0 hint
  have hintA : Integrable (R.blockAverage m f) μ := by
    have h := integrable_toReal_of_lintegral_ne_top hmeasA.aemeasurable hfinL
    rw [blockAverage_eq_toReal_fun hf hf0]
    exact h
  have hfinite : ∀ᵐ ω ∂μ, R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω < ∞ :=
    ae_lt_top hmeasA hfinL
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (R.blockAverage m f ω)
      = R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω := by
    filter_upwards [hfinite] with ω hω
    rw [blockAverage_eq_toReal hf hf0 ω, ENNReal.ofReal_toReal hω.ne]
  have hsetInt : ∀ A : Set Ω, MeasurableSet[𝒢.sigma] A →
      (∫ ω in A, R.blockAverage m f ω ∂μ) = ∫ ω in A, f ω ∂μ := by
    intro A hA
    have hleft : (∫ ω in A, R.blockAverage m f ω ∂μ)
        = (∫⁻ ω in A, ENNReal.ofReal (R.blockAverage m f ω) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => blockAverage_nonneg hf hf0 ω)
        (measurable_blockAverage hgraph hside hf hf0).aestronglyMeasurable
    have hright : (∫ ω in A, f ω ∂μ) = (∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
        hf.aestronglyMeasurable
    rw [hleft, hright]
    congr 1
    calc (∫⁻ ω in A, ENNReal.ofReal (R.blockAverage m f ω) ∂μ)
        = ∫⁻ ω in A, R.blockAverageLint m (fun x => ENNReal.ofReal (f x)) ω ∂μ :=
          lintegral_congr_ae (ae_restrict_of_ae hpt)
      _ = ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ :=
          setLIntegral_blockAverageLint_of_identity_ae hset (hle A hA) (hinv A hA) (hT A hA)
  exact ae_eq_condExp_of_forall_setIntegral_eq hle hint
    (fun s _ _ => hintA.integrableOn) (fun s hs _ => hsetInt s hs)
    ((hmeasG.stronglyMeasurable).aestronglyMeasurable)

/-- **Conditional block averaging for a sub-sigma-field of `𝒢_m`.**  If the block average
of `f` is measurable for a sub-sigma-field `𝒢 ≤ 𝒢_m` and the mark-averaged transport
identity holds for the test functions `1_A f`, `A ∈ 𝒢`, then `A_m f = E[f | 𝒢]`. -/
theorem blockAverage_ae_eq_condExp_of_sigma {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hgraph : R.MeasurableBlockGraph m) (hside : Measurable (R.blockSideAt m))
    {𝒢 : SubSigma Ω} (h𝒢 : 𝒢.sigma ≤ R.blockSigma m)
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (hint : Integrable f μ)
    (hmeasG : Measurable[𝒢.sigma] (R.blockAverage m f))
    (hT : R.BlockTransportOn m 𝒢 μ fun x => ENNReal.ofReal (f x)) :
    R.blockAverage m f =ᵐ[μ] μ[f|𝒢.sigma] :=
  blockAverage_ae_eq_condExp_of_sigma_ae hgraph hside (le_trans h𝒢 (R.blockSigma_le m))
    (fun A hA => Filter.Eventually.of_forall fun ω z hz => (h𝒢 A hA).2 ω z hz)
    hf hf0 hint hmeasG hT

end MarkedReRooting

end ReflectedGMS.MarkedBlockAveraging
