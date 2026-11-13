/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.DiameterBlockIndex at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The block index along a dyadic ancestor chain

This module proves the elementary part of the manuscript display
`s:eq:kappaprops` (manuscript lines 258-284) for the concrete objects of
`ReflectedGMS.Geometry.DyadicApproximation`.

With `P = S^{(1)}` the parent square, the geometric inputs used here are only
that `S` is contained in `P` and that `ℓ(P) = 2 ℓ(S)`.  They give

* `D(S) ≤ D(P)` and hence `a(P) ≤ a(S) ≤ 2 a(P)`, i.e. `b(S) ≤ b(P) ≤ 2 b(S)`;
* the recurrence `κ(S) = b(S) + κ(P)/4`, equivalently `κ(P) = 4(κ(S) - b(S))`;
* `b(S) ≤ κ(S) ≤ 2 b(S)`, so that `κ` is finite and positive as soon as the
  ancestor ratio `a` is;  in particular `FinitePositiveIndices` follows from its
  first four clauses and does not have to be assumed for `κ`;
* strict increase `κ(S) < κ(P)` along the ancestor chain whenever
  `b(S^{(j)}) → ∞`;
* the threshold characterisation of `Selected`: along one ancestor chain a
  selected square exists once `κ` crosses the level `m`, and it is unique.

The remaining inputs of the manuscript display, namely that `D` and `a` are
positive and finite (the pathwise large-cell ratio decay of the mass-transport
lemma), are not proved here and appear as explicit hypotheses.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.DiameterBlockIndex

open StatementIngredients DyadicApproximation

variable {V : Type*}

/-! ### Elementary numeric facts in `ℝ≥0∞` -/

theorem ennreal_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by simp

theorem ennreal_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by simp

theorem ennreal_four_ne_zero : (4 : ℝ≥0∞) ≠ 0 := by simp

theorem ennreal_four_ne_top : (4 : ℝ≥0∞) ≠ ∞ := by simp

/-- Multiplying by `2` cancels a factor `2` inside an inverse. -/
theorem two_mul_two_mul_inv (b : ℝ≥0∞) : 2 * (2 * b)⁻¹ = b⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl ennreal_two_ne_zero) (Or.inl ennreal_two_ne_top),
    ← mul_assoc, ENNReal.mul_inv_cancel ennreal_two_ne_zero ennreal_two_ne_top, one_mul]

/-- Multiplying by `2` cancels a factor `2` in the denominator. -/
theorem two_mul_div_two_mul (a b : ℝ≥0∞) : 2 * (a / (2 * b)) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2 : ℝ≥0∞) a, mul_assoc,
    two_mul_two_mul_inv]

theorem four_inv_mul_two : (4 : ℝ≥0∞)⁻¹ * 2 = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (Or.inl ennreal_two_ne_zero) (Or.inl ennreal_two_ne_top), mul_assoc,
    ENNReal.inv_mul_cancel ennreal_two_ne_zero ennreal_two_ne_top, mul_one]

/-! ### The parent square -/

theorem parent_fst (D : Grid) (s : SquareIndex) : (parent D s).1 = s.1 + 1 := rfl

theorem parent_snd (D : Grid) (s : SquareIndex) (i : Fin 2) :
    (parent D s).2 i = (s.2 i + ((D.digit s.1 i).val : ℤ)) / 2 := rfl

/-- The manuscript's `ℓ(P) = 2 ℓ(S)`. -/
theorem side_succ (D : Grid) (k : ℤ) : side D (k + 1) = 2 * side D k := by
  unfold side
  rw [show D.phase + ((k + 1 : ℤ) : ℝ) = (D.phase + (k : ℝ)) + 1 by push_cast; ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, mul_comm]

theorem side_parent (D : Grid) (s : SquareIndex) :
    side D (parent D s).1 = 2 * side D s.1 := by
  rw [parent_fst, side_succ]

theorem square_lower_apply (D : Grid) (s : SquareIndex) (i : Fin 2) :
    (square D s).lower i = D.origin s.1 i + side D s.1 * (s.2 i : ℝ) := rfl

theorem square_upper_apply (D : Grid) (s : SquareIndex) (i : Fin 2) :
    (square D s).upper i = D.origin s.1 i + side D s.1 * (s.2 i : ℝ) + side D s.1 := rfl

/-- Integer division really does select the containing parent lattice square. -/
theorem square_subset_parent (D : Grid) (s : SquareIndex) :
    (square D s).carrier ⊆ (square D (parent D s)).carrier := by
  intro z hz
  simp only [Rectangle.carrier, Set.mem_setOf_eq] at hz ⊢
  intro i
  obtain ⟨h1, h2⟩ := hz i
  rw [square_lower_apply] at h1
  rw [square_upper_apply] at h2
  have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
  have hcomp : D.origin s.1 i =
      D.origin (s.1 + 1) i + side D s.1 * ((D.digit s.1 i).val : ℝ) := D.compatible s.1 i
  rw [hcomp] at h1 h2
  have hq1 : 2 * ((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2) ≤
      s.2 i + ((D.digit s.1 i).val : ℤ) := by omega
  have hq2 : s.2 i + ((D.digit s.1 i).val : ℤ) ≤
      2 * ((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2) + 1 := by omega
  have hq1' : 2 * ((((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) ≤
      (s.2 i : ℝ) + ((D.digit s.1 i).val : ℝ) := by exact_mod_cast hq1
  have hq2' : (s.2 i : ℝ) + ((D.digit s.1 i).val : ℝ) ≤
      2 * ((((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) + 1 := by exact_mod_cast hq2
  have m1 := mul_le_mul_of_nonneg_left hq1' hside.le
  have m2 := mul_le_mul_of_nonneg_left hq2' hside.le
  rw [square_lower_apply, square_upper_apply, side_parent, parent_fst, parent_snd]
  constructor
  · push_cast at m1 ⊢
    linarith
  · push_cast at m2 ⊢
    linarith

/-! ### Monotonicity of the maximal cell diameter -/

theorem patchVertices_mono (F : IndexedCells V) {Q R : Rectangle}
    (h : Q.carrier ⊆ R.carrier) : patchVertices F Q ⊆ patchVertices F R := by
  intro v hv
  simp only [patchVertices, Set.mem_setOf_eq, Hits] at hv ⊢
  obtain ⟨z, hz1, hz2⟩ := hv
  exact ⟨z, hz1, h hz2⟩

theorem maxCellDiameter_mono (F : IndexedCells V) (D : Grid) {s t : SquareIndex}
    (h : (square D s).carrier ⊆ (square D t).carrier) :
    maxCellDiameter F D s ≤ maxCellDiameter F D t := by
  refine iSup_le fun v => ?_
  exact le_iSup
    (fun w : patchVertices F (square D t) =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane)))
    ⟨v.1, patchVertices_mono F h v.2⟩

/-- The manuscript's `D(S) ≤ D(P)`. -/
theorem maxCellDiameter_le_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    maxCellDiameter F D s ≤ maxCellDiameter F D (parent D s) :=
  maxCellDiameter_mono F D (square_subset_parent D s)

/-! ### The ancestor chain -/

theorem ancestor_succ (D : Grid) (s : SquareIndex) (j : ℕ) :
    ancestor D s (j + 1) = ancestor D (parent D s) j :=
  Function.iterate_succ_apply _ _ _

theorem ancestor_succ' (D : Grid) (s : SquareIndex) (j : ℕ) :
    ancestor D s (j + 1) = parent D (ancestor D s j) :=
  Function.iterate_succ_apply' _ _ _

/-- The single-square ratio `D(S)/ℓ(S)` whose ancestor supremum is `a(S)`. -/
noncomputable def cellRatio (F : IndexedCells V) (D : Grid) (s : SquareIndex) : ℝ≥0∞ :=
  maxCellDiameter F D s / ENNReal.ofReal (side D s.1)

theorem ancestorRatio_eq_iSup (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    ancestorRatio F D s = ⨆ j : ℕ, cellRatio F D (ancestor D s j) := rfl

theorem cellRatio_le_ancestorRatio (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    cellRatio F D s ≤ ancestorRatio F D s := by
  rw [ancestorRatio_eq_iSup]
  exact le_iSup (fun j : ℕ => cellRatio F D (ancestor D s j)) 0

theorem ofReal_side_parent (D : Grid) (s : SquareIndex) :
    ENNReal.ofReal (side D (parent D s).1) = 2 * ENNReal.ofReal (side D s.1) := by
  rw [side_parent, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `D(S)/ℓ(S) ≤ 2 D(P)/ℓ(P)`, using `D(S) ≤ D(P)` and `ℓ(P) = 2 ℓ(S)`. -/
theorem cellRatio_le_two_mul_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    cellRatio F D s ≤ 2 * cellRatio F D (parent D s) := by
  unfold cellRatio
  rw [ofReal_side_parent, two_mul_div_two_mul]
  exact ENNReal.div_le_div_right (maxCellDiameter_le_parent F D s) _

/-! ### The ancestor ratio `a` and its inverse `b` -/

/-- The parent supremum runs over a subfamily, so `a(P) ≤ a(S)`. -/
theorem ancestorRatio_parent_le (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    ancestorRatio F D (parent D s) ≤ ancestorRatio F D s := by
  rw [ancestorRatio_eq_iSup, ancestorRatio_eq_iSup]
  refine iSup_le fun j => ?_
  rw [← ancestor_succ]
  exact le_iSup (fun j : ℕ => cellRatio F D (ancestor D s j)) (j + 1)

/-- `a(S) ≤ 2 a(P)`: the `j = 0` term is handled by `cellRatio_le_two_mul_parent`
and the remaining terms already belong to `a(P)`. -/
theorem ancestorRatio_le_two_mul_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    ancestorRatio F D s ≤ 2 * ancestorRatio F D (parent D s) := by
  rw [ancestorRatio_eq_iSup]
  refine iSup_le fun j => ?_
  cases j with
  | zero =>
      refine le_trans (cellRatio_le_two_mul_parent F D s) ?_
      exact mul_le_mul' le_rfl (cellRatio_le_ancestorRatio F D (parent D s))
  | succ j =>
      have h : cellRatio F D (ancestor D s (j + 1)) ≤ ancestorRatio F D (parent D s) := by
        rw [ancestor_succ, ancestorRatio_eq_iSup]
        exact le_iSup (fun j : ℕ => cellRatio F D (ancestor D (parent D s) j)) j
      refine le_trans h ?_
      calc ancestorRatio F D (parent D s) = 1 * ancestorRatio F D (parent D s) :=
            (one_mul _).symm
        _ ≤ 2 * ancestorRatio F D (parent D s) :=
            mul_le_mul' (by norm_num) le_rfl

/-- The manuscript's `b(S) ≤ b(P)`. -/
theorem inverseRatio_le_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    inverseRatio F D s ≤ inverseRatio F D (parent D s) :=
  ENNReal.inv_le_inv.2 (ancestorRatio_parent_le F D s)

/-- The manuscript's `b(P) ≤ 2 b(S)`. -/
theorem inverseRatio_parent_le_two_mul (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    inverseRatio F D (parent D s) ≤ 2 * inverseRatio F D s := by
  have h : (2 * ancestorRatio F D (parent D s))⁻¹ ≤ (ancestorRatio F D s)⁻¹ :=
    ENNReal.inv_le_inv.2 (ancestorRatio_le_two_mul_parent F D s)
  have h2 : 2 * (2 * ancestorRatio F D (parent D s))⁻¹ ≤ 2 * (ancestorRatio F D s)⁻¹ :=
    mul_le_mul' le_rfl h
  rwa [two_mul_two_mul_inv] at h2

theorem inverseRatio_ancestor_mono (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    Monotone fun j : ℕ => inverseRatio F D (ancestor D s j) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [ancestor_succ']
  exact inverseRatio_le_parent F D (ancestor D s j)

/-- Iterating `b(P) ≤ 2 b(S)`. -/
theorem inverseRatio_ancestor_le (F : IndexedCells V) (D : Grid) (s : SquareIndex) (j : ℕ) :
    inverseRatio F D (ancestor D s j) ≤ 2 ^ j * inverseRatio F D s := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestor_succ']
      calc inverseRatio F D (parent D (ancestor D s j))
          ≤ 2 * inverseRatio F D (ancestor D s j) :=
            inverseRatio_parent_le_two_mul F D (ancestor D s j)
        _ ≤ 2 * (2 ^ j * inverseRatio F D s) := mul_le_mul' le_rfl ih
        _ = 2 ^ (j + 1) * inverseRatio F D s := by rw [pow_succ]; ring

/-! ### The block index `κ` -/

theorem blockIndex_eq_tsum (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    blockIndex F D s = ∑' j : ℕ, (4 : ℝ≥0∞)⁻¹ ^ j * inverseRatio F D (ancestor D s j) := by
  unfold blockIndex
  exact tsum_congr fun j => by rw [ENNReal.inv_pow]

theorem blockIndex_parent_eq_tsum (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    blockIndex F D (parent D s) =
      ∑' j : ℕ, (4 : ℝ≥0∞)⁻¹ ^ j * inverseRatio F D (ancestor D s (j + 1)) := by
  rw [blockIndex_eq_tsum]
  exact tsum_congr fun j => by rw [ancestor_succ]

/-- The manuscript's recurrence in additive form: `κ(S) = b(S) + κ(P)/4`. -/
theorem blockIndex_eq_inverseRatio_add (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    blockIndex F D s = inverseRatio F D s + 4⁻¹ * blockIndex F D (parent D s) := by
  rw [blockIndex_eq_tsum, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp
  · have hterm : ∀ j : ℕ,
        (4 : ℝ≥0∞)⁻¹ ^ (j + 1) * inverseRatio F D (ancestor D s (j + 1)) =
          4⁻¹ * ((4 : ℝ≥0∞)⁻¹ ^ j * inverseRatio F D (ancestor D (parent D s) j)) := by
      intro j
      rw [ancestor_succ, pow_succ]
      ring
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, blockIndex_eq_tsum]

/-- The manuscript's `b(S) ≤ κ(S)`. -/
theorem inverseRatio_le_blockIndex (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    inverseRatio F D s ≤ blockIndex F D s := by
  rw [blockIndex_eq_inverseRatio_add]
  exact le_self_add

/-- The manuscript's `κ(S) ≤ 2 b(S)`, from `b(S^{(j)}) ≤ 2^j b(S)` and the
geometric series `∑ 2^{-j} = 2`. -/
theorem blockIndex_le_two_mul_inverseRatio (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    blockIndex F D s ≤ 2 * inverseRatio F D s := by
  rw [blockIndex_eq_tsum]
  calc ∑' j : ℕ, (4 : ℝ≥0∞)⁻¹ ^ j * inverseRatio F D (ancestor D s j)
      ≤ ∑' j : ℕ, (4 : ℝ≥0∞)⁻¹ ^ j * (2 ^ j * inverseRatio F D s) :=
        ENNReal.tsum_le_tsum fun j =>
          mul_le_mul' le_rfl (inverseRatio_ancestor_le F D s j)
    _ = ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j * inverseRatio F D s := by
        refine tsum_congr fun j => ?_
        rw [← mul_assoc, ← mul_pow, four_inv_mul_two]
    _ = 2 * inverseRatio F D s := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]

theorem inverseRatio_pos (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (h : ancestorRatio F D s ≠ ∞) : 0 < inverseRatio F D s :=
  ENNReal.inv_pos.2 h

theorem inverseRatio_lt_top (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (h : 0 < ancestorRatio F D s) : inverseRatio F D s < ∞ :=
  ENNReal.inv_lt_top.2 h

theorem blockIndex_pos (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (h : ancestorRatio F D s ≠ ∞) : 0 < blockIndex F D s :=
  lt_of_lt_of_le (inverseRatio_pos F D s h) (inverseRatio_le_blockIndex F D s)

theorem blockIndex_lt_top (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (h : 0 < ancestorRatio F D s) : blockIndex F D s < ∞ :=
  lt_of_le_of_lt (blockIndex_le_two_mul_inverseRatio F D s)
    (ENNReal.mul_lt_top (by simp) (inverseRatio_lt_top F D s h))

/-- The `κ` clauses of `FinitePositiveIndices` are consequences of the diameter
and ancestor-ratio clauses; they need not be assumed separately. -/
theorem finitePositiveIndices_of_diam_and_ratio (F : IndexedCells V) (D : Grid)
    (hD : ∀ s : SquareIndex, 0 < maxCellDiameter F D s ∧ maxCellDiameter F D s < ∞)
    (ha : ∀ s : SquareIndex, 0 < ancestorRatio F D s ∧ ancestorRatio F D s < ∞) :
    FinitePositiveIndices F D := by
  intro s
  exact ⟨(hD s).1, (hD s).2, (ha s).1, (ha s).2,
    blockIndex_pos F D s (ha s).2.ne, blockIndex_lt_top F D s (ha s).1⟩

/-! ### Strict increase of `κ` along the ancestor chain -/

/-- If `b` is anywhere larger along the chain than at the root, then it strictly
increases at some single step. -/
theorem exists_step_lt_of_lt_ancestor (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (J : ℕ) (hJ : inverseRatio F D s < inverseRatio F D (ancestor D s J)) :
    ∃ i : ℕ, inverseRatio F D (ancestor D s i) < inverseRatio F D (ancestor D s (i + 1)) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j : ℕ, inverseRatio F D (ancestor D s j) ≤ inverseRatio F D s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => exact le_trans (hcon j) ih
  exact absurd (hall J) (not_le.2 hJ)

/-- The manuscript's strict inequality `κ(S) < κ(P)`. -/
theorem blockIndex_lt_blockIndex_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (hfin : blockIndex F D s ≠ ∞) (i : ℕ)
    (hi : inverseRatio F D (ancestor D s i) < inverseRatio F D (ancestor D s (i + 1))) :
    blockIndex F D s < blockIndex F D (parent D s) := by
  rw [blockIndex_parent_eq_tsum]
  rw [blockIndex_eq_tsum] at hfin ⊢
  refine ENNReal.tsum_lt_tsum (i := i) hfin (fun j => ?_) ?_
  · exact mul_le_mul' le_rfl (inverseRatio_ancestor_mono F D s (Nat.le_succ j))
  · have h4z : ((4 : ℝ≥0∞)⁻¹ ^ i) ≠ 0 :=
      pow_ne_zero i (ENNReal.inv_ne_zero.2 ennreal_four_ne_top)
    have h4t : ((4 : ℝ≥0∞)⁻¹ ^ i) ≠ ∞ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ennreal_four_ne_zero)
    have hmul := ENNReal.mul_lt_mul_left h4z h4t hi
    rwa [mul_comm (inverseRatio F D (ancestor D s i)),
      mul_comm (inverseRatio F D (ancestor D s (i + 1)))] at hmul

/-- Strict increase from the manuscript's reason `b(S^{(j)}) → ∞`. -/
theorem blockIndex_lt_blockIndex_parent_of_tendsto (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) (hfin : blockIndex F D s ≠ ∞)
    (htop : Filter.Tendsto (fun j : ℕ => inverseRatio F D (ancestor D s j))
      Filter.atTop (nhds ∞)) :
    blockIndex F D s < blockIndex F D (parent D s) := by
  have hbtop : inverseRatio F D s < ∞ :=
    lt_of_le_of_lt (inverseRatio_le_blockIndex F D s) (lt_top_iff_ne_top.2 hfin)
  have hmem : Set.Ioi (inverseRatio F D s) ∈ nhds (∞ : ℝ≥0∞) :=
    isOpen_Ioi.mem_nhds hbtop
  obtain ⟨J, hJ⟩ := (htop.eventually_mem hmem).exists
  obtain ⟨i, hi⟩ := exists_step_lt_of_lt_ancestor F D s J hJ
  exact blockIndex_lt_blockIndex_parent F D s hfin i hi

/-! ### The selection threshold -/

/-- Along one ancestor chain, a selected square exists as soon as `κ` crosses
the level `m`. -/
theorem exists_selected_ancestor (F : IndexedCells V) (D : Grid) (m : ℝ) (hm : 0 < m)
    (s : SquareIndex) (h0 : blockIndex F D s ≤ ENNReal.ofReal m)
    (J : ℕ) (hJ : ENNReal.ofReal m < blockIndex F D (ancestor D s J)) :
    ∃ j : ℕ, Selected F D m (ancestor D s j) := by
  classical
  have hex : ∃ j : ℕ, ENNReal.ofReal m < blockIndex F D (ancestor D s j) := ⟨J, hJ⟩
  set k := Nat.find hex with hk
  have hkspec : ENNReal.ofReal m < blockIndex F D (ancestor D s k) := Nat.find_spec hex
  have hkpos : k ≠ 0 := by
    intro h
    rw [h] at hkspec
    rw [ancestor_zero] at hkspec
    exact absurd h0 (not_le.2 hkspec)
  obtain ⟨p, hp0⟩ := Nat.exists_eq_succ_of_ne_zero hkpos
  have hp : k = p + 1 := hp0
  refine ⟨p, hm, ?_, ?_⟩
  · have hlt : p < k := by omega
    have := Nat.find_min hex hlt
    exact not_lt.1 this
  · have : ancestor D s (p + 1) = parent D (ancestor D s p) := ancestor_succ' D s p
    rw [← this, ← hp]
    exact hkspec

end ReflectedGMS.DiameterBlockIndex
