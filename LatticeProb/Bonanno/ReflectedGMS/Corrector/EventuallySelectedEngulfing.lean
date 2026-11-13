/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.EventuallySelectedEngulfing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActiveBlockEdges
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLaw
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A fixed rectangle eventually sits strictly inside a selected square

This module supplies the **geometric containment** left open by the docstring of
`MarkedRectangleHarmonicity.MarkedApproximantRectangleOrthogonality`: for almost every dyadic
grid and every environment with sublinear cell diameters, each bounded rectangle `Q` lies in
the *interior* of a `κ`-selected square once the selection parameter is large.

## Why this needs the grid law

The statement is **false for a fixed grid**.  A grid with `D.origin k i = 0` at every level
is admissible (`origin_position` allows the value `0`, and `compatible` holds with all digits
zero), and then the origin is a corner of every dyadic square at every level, so no square
whatsoever contains `[-1, 1]²`.  The randomness of the grid is therefore not a convenience:
it is the whole content of the containment, and it enters exactly once, through
`ae_eventuallyCentred`.

## The two halves

* **Probabilistic** (`ae_eventuallyCentred`).  Under `DyadicApproximation.UniformGridLaw` the
  relative origin at level `k` is uniform on `[0,1)²`, independently of the phase, so the
  probability that the level-`k` origin square fails to contain the closed box of radius `N`
  in its interior is at most `4 N 2^{-k}` — the phase is nonnegative, so the side at level
  `k` is at least `2^k`.  That is summable, and Borel–Cantelli
  (`MeasureTheory.measure_setOfPred_frequently_eq_zero`) gives the almost-sure eventual
  containment, simultaneously for every integer margin `N`.
* **Deterministic** (`eventually_exists_selected_engulfing`).  A square selected at parameter
  `m` which contains the origin has side more than `m d / 4`, where `d > 0` is the diameter
  of a cell containing the origin — which is why this half now carries the hypothesis
  `(0 : Plane) ∉ uncoveredSet F`, the covering clause of `Geometry` having been weakened to
  `μH[1] (uncoveredSet F) = 0`; see the theorem's docstring.  Its parent also contains the
  origin, so
  `NonmacroscopicSelectedBlocks.blockIndex_le_ofReal_of_mem` bounds the parent's block index
  by `2 ℓ(parent)/d`, which selection forces to exceed `m`.  Hence the level of that selected
  square tends to infinity with `m`; once it exceeds the level supplied by the centred event,
  the selected square *is* the origin square of its level — a point interior to one square of
  a level lies in no other square of that level — and it engulfs `Q`.

The dependence of the stage on the rectangle is genuine and is exactly the `∀ᶠ` in the
conclusion; no uniformity over rectangles is claimed or used.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS

namespace EventuallySelectedEngulfing

open StatementIngredients DyadicApproximation

/-! ### Open boxes -/

/-- The open box of a rectangle is open. -/
theorem isOpen_openBox (Q : Rectangle) :
    IsOpen {z : Plane | ∀ i : Fin 2, Q.lower i < z i ∧ z i < Q.upper i} := by
  have h0 : Continuous fun y : Plane => y 0 := PiLp.continuous_apply 2 _ (0 : Fin 2)
  have h1 : Continuous fun y : Plane => y 1 := PiLp.continuous_apply 2 _ (1 : Fin 2)
  have hset : {z : Plane | ∀ i : Fin 2, Q.lower i < z i ∧ z i < Q.upper i}
      = ((fun y : Plane => y 0) ⁻¹' Set.Ioo (Q.lower 0) (Q.upper 0))
        ∩ ((fun y : Plane => y 1) ⁻¹' Set.Ioo (Q.lower 1) (Q.upper 1)) := by
    apply Set.eq_of_subset_of_subset
    · intro y hy
      exact ⟨⟨(hy 0).1, (hy 0).2⟩, (hy 1).1, (hy 1).2⟩
    · intro y hy
      show ∀ i : Fin 2, Q.lower i < y i ∧ y i < Q.upper i
      rw [Fin.forall_fin_two]
      exact ⟨⟨hy.1.1, hy.1.2⟩, hy.2.1, hy.2.2⟩
  rw [hset]
  exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)

/-- The open box of a rectangle is contained in the interior of its carrier. -/
theorem openBox_subset_interior (Q : Rectangle) :
    {z : Plane | ∀ i : Fin 2, Q.lower i < z i ∧ z i < Q.upper i} ⊆ interior Q.carrier :=
  interior_maximal (fun _ hz i => ⟨(hz i).1.le, (hz i).2.le⟩) (isOpen_openBox Q)

/-! ### The origin square of a level -/

/-- The dyadic square of level `k` anchored at the grid origin. -/
def originSq (k : ℤ) : SquareIndex := (k, fun _ => 0)

@[simp] theorem originSq_fst (k : ℤ) : (originSq k).1 = k := rfl

theorem square_originSq_lower (D : Grid) (k : ℤ) (i : Fin 2) :
    (square D (originSq k)).lower i = D.origin k i := by
  show D.origin k i + side D k * ((0 : ℤ) : ℝ) = D.origin k i
  simp

theorem square_originSq_upper (D : Grid) (k : ℤ) (i : Fin 2) :
    (square D (originSq k)).upper i = D.origin k i + side D k := by
  show D.origin k i + side D k * ((0 : ℤ) : ℝ) + side D k = D.origin k i + side D k
  simp

/-- The grid is **centred with margin `N` at level `k`** when the level-`k` origin square
contains the closed box of radius `N` strictly inside. -/
def CentredAt (N : ℝ) (k : ℤ) : Set Grid :=
  {D | ∀ i : Fin 2, D.origin k i < -N ∧ N < D.origin k i + side D k}

theorem carrier_subset_interior_of_centred {N : ℝ} {k : ℤ} {D : Grid}
    (hD : D ∈ CentredAt N k) {Q : Rectangle}
    (hQ : ∀ i : Fin 2, -N ≤ Q.lower i ∧ Q.upper i ≤ N) :
    Q.carrier ⊆ interior (square D (originSq k)).carrier := by
  refine subset_trans ?_ (openBox_subset_interior (square D (originSq k)))
  intro z hz i
  refine ⟨?_, ?_⟩
  · rw [square_originSq_lower]
    exact lt_of_lt_of_le (lt_of_lt_of_le (hD i).1 (hQ i).1) (hz i).1
  · rw [square_originSq_upper]
    exact lt_of_le_of_lt (le_trans (hz i).2 (hQ i).2) (hD i).2

theorem zero_mem_interior_of_centred {N : ℝ} (hN : 0 < N) {k : ℤ} {D : Grid}
    (hD : D ∈ CentredAt N k) :
    (0 : Plane) ∈ interior (square D (originSq k)).carrier := by
  refine openBox_subset_interior (square D (originSq k)) ?_
  intro i
  have h0 : (0 : Plane) i = 0 := by simp
  rw [square_originSq_lower, square_originSq_upper, h0]
  exact ⟨by linarith [(hD i).1], by linarith [(hD i).2]⟩

/-! ### The probability that the grid is centred -/

/-- The depth-zero cylinder set asking the relative origin to be at distance more than `δ`
from both ends of its own square, in both coordinates. -/
def centredCyl (δ : ℝ) : Set (ℝ × ((Fin 2 → ℝ) × (Fin 0 → Fin 2 → Fin 2))) :=
  Set.univ ×ˢ ((Set.univ.pi fun _ : Fin 2 => Set.Ioo δ (1 - δ)) ×ˢ Set.univ)

theorem measurableSet_centredCyl (δ : ℝ) : MeasurableSet (centredCyl δ) :=
  MeasurableSet.univ.prod
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).prod MeasurableSet.univ)

/-- At a nonnegative level the side is at least `2 ^ k`, because the phase is nonnegative. -/
theorem pow_le_side (D : Grid) (k : ℕ) : ((2 : ℝ) ^ k) ≤ side D (k : ℤ) := by
  have hphase : (0 : ℝ) ≤ D.phase := D.phase_mem.1
  have hcast : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
  show ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ (D.phase + (((k : ℤ)) : ℝ))
  rw [← Real.rpow_natCast 2 k]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [hcast]
  linarith

/-- **The cylinder event really centres the grid.**  Its margin is measured in units of the
side length, and the side at level `k` is at least `2 ^ k`. -/
theorem preimage_centredCyl_subset_centredAt {N : ℝ} (hN : 0 ≤ N) (k : ℕ) :
    gridCylinder (k : ℤ) 0 ⁻¹' centredCyl (N * (2 : ℝ)⁻¹ ^ k) ⊆ CentredAt N (k : ℤ) := by
  intro D hD
  obtain ⟨-, hy, -⟩ := hD
  have hs : (0 : ℝ) < side D (k : ℤ) := side_pos D _
  have hsne : side D (k : ℤ) ≠ 0 := ne_of_gt hs
  have hδ0 : (0 : ℝ) ≤ N * (2 : ℝ)⁻¹ ^ k := by positivity
  have hNδ : N ≤ N * (2 : ℝ)⁻¹ ^ k * side D (k : ℤ) := by
    have h1 : N * (2 : ℝ)⁻¹ ^ k * ((2 : ℝ) ^ k) ≤ N * (2 : ℝ)⁻¹ ^ k * side D (k : ℤ) :=
      mul_le_mul_of_nonneg_left (pow_le_side D k) hδ0
    have h2 : N * (2 : ℝ)⁻¹ ^ k * ((2 : ℝ) ^ k) = N := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    linarith
  intro i
  have hyi : -D.origin (k : ℤ) i / side D (k : ℤ)
      ∈ Set.Ioo (N * (2 : ℝ)⁻¹ ^ k) (1 - N * (2 : ℝ)⁻¹ ^ k) := hy i (Set.mem_univ i)
  have hmul : -D.origin (k : ℤ) i / side D (k : ℤ) * side D (k : ℤ)
      = -D.origin (k : ℤ) i := by field_simp
  constructor
  · have h1 : N * (2 : ℝ)⁻¹ ^ k * side D (k : ℤ)
        < -D.origin (k : ℤ) i / side D (k : ℤ) * side D (k : ℤ) :=
      mul_lt_mul_of_pos_right hyi.1 hs
    rw [hmul] at h1
    linarith
  · have h1 : -D.origin (k : ℤ) i / side D (k : ℤ) * side D (k : ℤ)
        < (1 - N * (2 : ℝ)⁻¹ ^ k) * side D (k : ℤ) :=
      mul_lt_mul_of_pos_right hyi.2 hs
    rw [hmul, sub_mul, one_mul] at h1
    linarith

section Law

variable {ν : Measure Grid}

/-- The exact probability of the centred cylinder, for a margin at most one half. -/
theorem measure_preimage_centredCyl (hlaw : UniformGridLaw ν) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (k : ℤ) :
    ν (gridCylinder k 0 ⁻¹' centredCyl δ) = ENNReal.ofReal ((1 - 2 * δ) ^ 2) := by
  have hprob : IsProbabilityMeasure (PMF.uniformOfFintype (Fin 0 → Fin 2 → Fin 2)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hsub : Set.Ioo δ (1 - δ) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hone : (volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ioo δ (1 - δ))
      = ENNReal.ofReal (1 - 2 * δ) := by
    rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hsub,
      Real.volume_Ioo]
    congr 1
    ring
  have hpi : (Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.univ.pi fun _ : Fin 2 => Set.Ioo δ (1 - δ))
      = ENNReal.ofReal (1 - 2 * δ) ^ 2 := by
    rw [Measure.pi_pi]
    simp only [hone, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have huniv : (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    norm_num
  have hpmf : (PMF.uniformOfFintype (Fin 0 → Fin 2 → Fin 2)).toMeasure Set.univ = 1 :=
    measure_univ
  rw [← Measure.map_apply (DyadicGridLaw.measurable_gridCylinder k 0)
      (measurableSet_centredCyl δ), hlaw.2 k 0, centredCyl, Measure.prod_prod,
    Measure.prod_prod, hpi, huniv, hpmf, one_mul, mul_one,
    ← ENNReal.ofReal_pow (by linarith)]

/-- **The grid fails to be centred with probability at most `4 δ`.** -/
theorem measure_compl_preimage_centredCyl_le (hlaw : UniformGridLaw ν) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (k : ℤ) :
    ν ((gridCylinder k 0 ⁻¹' centredCyl δ)ᶜ) ≤ ENNReal.ofReal (4 * δ) := by
  haveI : IsProbabilityMeasure ν := hlaw.1
  by_cases hδ1 : δ ≤ 1 / 2
  · have hmeas : MeasurableSet (gridCylinder k 0 ⁻¹' centredCyl δ) :=
      DyadicGridLaw.measurable_gridCylinder k 0 (measurableSet_centredCyl δ)
    rw [prob_compl_eq_one_sub hmeas, measure_preimage_centredCyl hlaw hδ0 hδ1 k,
      tsub_le_iff_right, ← ENNReal.ofReal_add (by linarith) (sq_nonneg _), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ])
  · have h1 : (1 : ℝ) < 4 * δ := by
      push_neg at hδ1
      linarith
    calc ν ((gridCylinder k 0 ⁻¹' centredCyl δ)ᶜ) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (4 * δ) := ENNReal.ofReal_le_ofReal h1.le

/-- The grid is eventually centred at every integer margin. -/
def EventuallyCentred (D : Grid) : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, D ∈ CentredAt (N : ℝ) (k : ℤ)

/-- **Almost every grid is eventually centred at every margin.**  Borel–Cantelli applied to
the summable bound `4 N 2^{-k}`. -/
theorem ae_eventuallyCentred (hlaw : UniformGridLaw ν) : ∀ᵐ D ∂ν, EventuallyCentred D := by
  haveI : IsProbabilityMeasure ν := hlaw.1
  have hfix : ∀ N : ℕ, ∀ᵐ D ∂ν, ∀ᶠ k : ℕ in atTop, D ∈ CentredAt (N : ℝ) (k : ℤ) := by
    intro N
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    set s : ℕ → Set Grid := fun k =>
      (gridCylinder (k : ℤ) 0 ⁻¹' centredCyl ((N : ℝ) * (2 : ℝ)⁻¹ ^ k))ᶜ with hs
    have hbound : ∀ k : ℕ, ν (s k) ≤ ENNReal.ofReal (4 * (N : ℝ)) * (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k
      refine (measure_compl_preimage_centredCyl_le hlaw (by positivity) (k : ℤ)).trans ?_
      have hrw : 4 * ((N : ℝ) * (2 : ℝ)⁻¹ ^ k) = (4 * (N : ℝ)) * ((2 : ℝ)⁻¹ ^ k) := by ring
      rw [hrw, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      have h2 : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [h2]
    have hsum : (∑' k : ℕ, ν (s k)) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    have hae : ∀ᵐ D ∂ν, ∀ᶠ k : ℕ in atTop, D ∉ s k := by
      rw [MeasureTheory.ae_iff]
      have heq : {D : Grid | ¬ ∀ᶠ k : ℕ in atTop, D ∉ s k}
          = {D : Grid | ∃ᶠ k : ℕ in atTop, D ∈ s k} := by
        ext D
        simp only [Set.mem_setOf_eq, Filter.not_eventually, not_not]
      rw [heq]
      exact MeasureTheory.measure_setOfPred_frequently_eq_zero hsum
    filter_upwards [hae] with D hD
    filter_upwards [hD] with k hk
    refine preimage_centredCyl_subset_centredAt hN k ?_
    simpa [hs] using hk
  filter_upwards [ae_all_iff.2 hfix] with D hD
  exact hD

end Law

/-! ### A selected square containing the origin is large -/

section Selected

variable {V : Type*} [Countable V]

/-- **The lower bound on the side of a selected square through the origin.**  Its parent
contains the origin too, so the parent's block index is at most `2 ℓ(parent)/d`, and
selection forces that to exceed `m`. -/
theorem lt_side_of_selected_of_zero_mem (F : IndexedCells V) (D : Grid) {v : V}
    (hv : (0 : Plane) ∈ (F.cell v : Set Plane))
    (hd : 0 < Metric.diam (F.cell v : Set Plane)) {m : ℝ} {s : SquareIndex}
    (hs : Selected F D m s) (hz : (0 : Plane) ∈ (square D s).carrier) :
    m * Metric.diam (F.cell v : Set Plane) / 4 < side D s.1 := by
  have hzp : (0 : Plane) ∈ (square D (parent D s)).carrier :=
    DiameterBlockIndex.square_subset_parent D s hz
  have hbi := NonmacroscopicSelectedBlocks.blockIndex_le_ofReal_of_mem F D (parent D s) hzp hv hd
  have hsp : side D (parent D s).1 = 2 * side D s.1 := by
    rw [DiameterBlockIndex.parent_fst, DiameterBlockIndex.side_succ]
  have hspos : (0 : ℝ) < side D s.1 := side_pos D s.1
  have hpos : (0 : ℝ) < 2 * (side D (parent D s).1 / Metric.diam (F.cell v : Set Plane)) := by
    have hp := side_pos D (parent D s).1
    positivity
  have hlt : m < 2 * (side D (parent D s).1 / Metric.diam (F.cell v : Set Plane)) :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).1 (lt_of_lt_of_le hs.2.2 hbi)
  rw [hsp] at hlt
  have hdne : Metric.diam (F.cell v : Set Plane) ≠ 0 := ne_of_gt hd
  have hkey : m * Metric.diam (F.cell v : Set Plane) < 4 * side D s.1 := by
    have h1 : m * Metric.diam (F.cell v : Set Plane)
        < 2 * (2 * side D s.1 / Metric.diam (F.cell v : Set Plane))
          * Metric.diam (F.cell v : Set Plane) := mul_lt_mul_of_pos_right hlt hd
    have h2 : 2 * (2 * side D s.1 / Metric.diam (F.cell v : Set Plane))
        * Metric.diam (F.cell v : Set Plane) = 4 * side D s.1 := by
      field_simp
      ring
    linarith
  linarith

/-- Every rectangle sits inside a closed box with a positive integer radius. -/
theorem exists_nat_bound (Q : Rectangle) :
    ∃ N : ℕ, 0 < (N : ℝ) ∧ ∀ i : Fin 2, -(N : ℝ) ≤ Q.lower i ∧ Q.upper i ≤ (N : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_ge
    (max (max |Q.lower 0| |Q.lower 1|) (max |Q.upper 0| |Q.upper 1|))
  have hb : ∀ x : ℝ, |x| ≤ max (max |Q.lower 0| |Q.lower 1|) (max |Q.upper 0| |Q.upper 1|) →
      -((M : ℝ) + 1) ≤ x ∧ x ≤ ((M : ℝ) + 1) := by
    intro x hx
    have h2 := abs_le.1 (le_trans hx hM)
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  refine ⟨M + 1, by exact_mod_cast Nat.succ_pos M, ?_⟩
  have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [Fin.forall_fin_two, hcast]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (hb (Q.lower 0) (le_trans (le_max_left _ _) (le_max_left _ _))).1
  · exact (hb (Q.upper 0) (le_trans (le_max_left _ _) (le_max_right _ _))).2
  · exact (hb (Q.lower 1) (le_trans (le_max_right _ _) (le_max_left _ _))).1
  · exact (hb (Q.upper 1) (le_trans (le_max_right _ _) (le_max_right _ _))).2

/-- **The containment step.**  For a grid that is eventually centred and an environment with
sublinear cell diameters whose **origin lies in a cell**, every bounded rectangle lies in the
interior of a square selected at every large enough parameter.

The hypothesis `h0` is not removable.  It enters twice, and both times through the origin
specifically: the selected square through the origin is forced to be large only because its
parent still contains the origin and therefore meets a cell of a *fixed* positive diameter
(`lt_side_of_selected_of_zero_mem`), and `NonmacroscopicSelectedBlocks.exists_selected_mem`
produces a selected square containing the origin at all only for a covered point.  Since the
covering clause of `Geometry` was weakened to `μH[1] (uncoveredSet F) = 0`, cells may
accumulate at the origin with diameters shrinking faster than any dyadic scale, and then `κ`
stays bounded below along the origin chain and no square through the origin is ever selected
at a large parameter.  The manuscript makes the same restriction: the selected blocks
*"cover every point belonging to a cell … No claim is needed about an uncovered singular
point."* -/
theorem eventually_exists_selected_engulfing (F : IndexedCells V) (hF : Geometry F)
    (h0 : (0 : Plane) ∉ uncoveredSet F) (D : Grid)
    (hsub : NonmacroscopicSelectedBlocks.SublinearDiameterDecay F) (hD : EventuallyCentred D)
    (Q : Rectangle) :
    ∀ᶠ m : ℕ in atTop, ∃ s : SquareIndex, Selected F D (m : ℝ) s ∧
      Q.carrier ⊆ interior (square D s).carrier := by
  obtain ⟨N, hNpos, hQN⟩ := exists_nat_bound Q
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (hD N)
  obtain ⟨v, hv, hd⟩ :=
    NonmacroscopicSelectedBlocks.exists_mem_cell_diam_pos F hF (0 : Plane) h0
  have hdne : Metric.diam (F.cell v : Set Plane) ≠ 0 := ne_of_gt hd
  obtain ⟨M, hM⟩ := exists_nat_ge (8 * (2 : ℝ) ^ K / Metric.diam (F.cell v : Set Plane))
  filter_upwards [eventually_ge_atTop (max 1 M)] with m hm
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hmM : (M : ℝ) ≤ (m : ℝ) := by
    have : M ≤ m := le_trans (le_max_right _ _) hm
    exact_mod_cast this
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := hm1
    exact_mod_cast this
  obtain ⟨s, hs, hz⟩ :=
    NonmacroscopicSelectedBlocks.exists_selected_mem F hF D hsub (m : ℝ) hmpos (0 : Plane) h0
  have hside := lt_side_of_selected_of_zero_mem F D hv hd hs hz
  -- the level of `s` is at least `K`
  have hlev : (K : ℤ) ≤ s.1 := by
    by_contra hcon
    push_neg at hcon
    have hphase : D.phase < 1 := D.phase_mem.2
    have hcast : ((s.1 : ℤ) : ℝ) ≤ (K : ℝ) - 1 := by
      have h1 : s.1 ≤ (K : ℤ) - 1 := by omega
      have h2 : ((s.1 : ℤ) : ℝ) ≤ (((K : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_sub, Int.cast_one] at h2
      simpa using h2
    have hlt2 : side D s.1 < (2 : ℝ) ^ K := by
      show (2 : ℝ) ^ (D.phase + ((s.1 : ℤ) : ℝ)) < (2 : ℝ) ^ K
      rw [← Real.rpow_natCast 2 K]
      refine Real.rpow_lt_rpow_left_iff (by norm_num) |>.2 ?_
      linarith
    have hmd : 8 * (2 : ℝ) ^ K ≤ (m : ℝ) * Metric.diam (F.cell v : Set Plane) := by
      have h1 : 8 * (2 : ℝ) ^ K / Metric.diam (F.cell v : Set Plane)
          * Metric.diam (F.cell v : Set Plane) ≤ (m : ℝ) * Metric.diam (F.cell v : Set Plane) :=
        mul_le_mul_of_nonneg_right (le_trans hM hmM) hd.le
      have h2 : 8 * (2 : ℝ) ^ K / Metric.diam (F.cell v : Set Plane)
          * Metric.diam (F.cell v : Set Plane) = 8 * (2 : ℝ) ^ K := by field_simp
      linarith
    have hpow : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    linarith
  have hK0 : (0 : ℤ) ≤ s.1 := le_trans (Int.natCast_nonneg K) hlev
  have htoNat : ((s.1.toNat : ℕ) : ℤ) = s.1 := Int.toNat_of_nonneg hK0
  have hKle : K ≤ s.1.toNat := by omega
  have hcent : D ∈ CentredAt (N : ℝ) s.1 := by
    have := hK s.1.toNat hKle
    rwa [htoNat] at this
  have hQsub : Q.carrier ⊆ interior (square D (originSq s.1)).carrier :=
    carrier_subset_interior_of_centred hcent hQN
  have hzero : (0 : Plane) ∈ interior (square D (originSq s.1)).carrier :=
    zero_mem_interior_of_centred hNpos hcent
  have hseq : originSq s.1 = s := by
    by_contra hne
    have hne2 : (originSq s.1).2 ≠ s.2 := by
      intro h2
      exact hne (Prod.ext (originSq_fst s.1) h2)
    exact ActiveBlockEdges.notMem_square_of_mem_interior_of_same_level D
      (originSq_fst s.1) hne2 hzero hz
  exact ⟨s, hs, by rwa [hseq] at hQsub⟩

end Selected

end EventuallySelectedEngulfing

end ReflectedGMS
