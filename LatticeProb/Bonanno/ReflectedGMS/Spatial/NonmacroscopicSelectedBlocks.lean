/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DiameterBlockIndex
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts

/-!
# Fixed-parameter selected blocks are not macroscopic

This module proves the manuscript's `s:lem:smallblocks`, first display
`s:eq:smallblocks`: for a fixed block parameter `m`,

`s_m(R) = sup {ℓ(S) : S ∈ 𝒮_m, S ∩ clB R ≠ ∅}` satisfies `s_m(R)/R → 0`.

The only random input is the large-cell decay of
`ReflectedGMS.Spatial.LargeCellDiameterDecay`: `D_R < ∞` for each `R` and
`D_R ≤ ε R` for large `R`.  The bridge `maxCellDiameter_le_maxDiamHittingBall`
and the elementary block-index calculus of
`ReflectedGMS.Geometry.DiameterBlockIndex` are reused verbatim; nothing about
mass transport or the (FE) moment is reproved here.

The geometric content added here is the scale bridge of the manuscript proof.

* A dyadic square has Euclidean diameter at most `2 ℓ(S)`
  (`dist_le_two_mul_side`), so a square meeting `clB R` lies in
  `clB (R + 2 ℓ(S))`; with `ℓ(S) ≥ ε R` this is `clB (K_ε ℓ(S))` for
  `K_ε = ε⁻¹ + 2`.  Every ancestor `T = S^{(j)}` contains `S`, hence meets
  `clB R` too, and `ℓ(T) = 2^j ℓ(S)`, so the same containment holds along the
  whole chain (`ancestorRatio_ancestor_le`).
* Feeding `D_r ≤ δ r` into that containment bounds `a(S)` by `δ (K_ε + 2)`
  uniformly over the chain, so `κ(S) ≥ b(S) ≥ (δ (K_ε+2))⁻¹`.  Choosing `δ`
  with `(δ(K_ε+2))⁻¹ = 2m` contradicts `κ(S) ≤ m` for a selected square: that
  is `side_lt_of_selected_of_meets`, hence `maxSelectedSide_le_ofReal` and
  `tendsto_maxSelectedSide_div_atTop`.

The same scale bridge gives the two facts that the block interpolation needs
before the size bound is meaningful.

* `finitePositiveIndices_of_geometry_of_sublinear`: all six clauses of
  `FinitePositiveIndices` hold for the actual dyadic grid.  Finiteness of `a`
  comes from the chain estimate together with `a(S) ≤ 2^J a(S^{(J)})`;
  positivity comes from the covering property of `Geometry`.  The `κ` clauses
  are the checked `finitePositiveIndices_of_diam_and_ratio`.
* `exists_selected_mem`: every covered point of the plane lies in a selected square.
  Deep squares have small `κ` (their ratio `a` is at least `d_H/ℓ`), and `κ`
  exceeds any level along the chain because `a(S^{(J)}) → 0`; the checked
  threshold lemma `exists_selected_ancestor` then produces the block.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.NonmacroscopicSelectedBlocks

open StatementIngredients DyadicApproximation DiameterBlockIndex Spatial Code

variable {V : Type*}

/-! ### Euclidean geometry of one dyadic square -/

/-- Two points of a dyadic square are at distance at most `2 ℓ(S)`; the sharp
constant `√2` is not needed below. -/
theorem dist_le_two_mul_side (D : Grid) (s : SquareIndex) {z w : Plane}
    (hz : z ∈ (square D s).carrier) (hw : w ∈ (square D s).carrier) :
    dist z w ≤ 2 * side D s.1 := by
  simp only [Rectangle.carrier, Set.mem_setOf_eq] at hz hw
  have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
  have hcoord : ∀ i : Fin 2, dist (z i) (w i) ≤ side D s.1 := by
    intro i
    obtain ⟨h1, h2⟩ := hz i
    obtain ⟨h3, h4⟩ := hw i
    rw [square_lower_apply] at h1 h3
    rw [square_upper_apply] at h2 h4
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith
  have h0 := hcoord 0
  have h1 := hcoord 1
  have hn0 : (0 : ℝ) ≤ dist (z 0) (w 0) := dist_nonneg
  have hn1 : (0 : ℝ) ≤ dist (z 1) (w 1) := dist_nonneg
  have hsum : ∑ i : Fin 2, dist (z i) (w i) ^ 2 ≤ (2 * side D s.1) ^ 2 := by
    rw [Fin.sum_univ_two]
    nlinarith
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i : Fin 2, dist (z i) (w i) ^ 2)
      ≤ Real.sqrt ((2 * side D s.1) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * side D s.1 := Real.sqrt_sq (by positivity)

/-- The lower corner of a rectangle belongs to it, so a dyadic square is never
empty. -/
theorem mem_carrier_lowerCorner (Q : Rectangle) :
    (WithLp.toLp 2 (fun i => Q.lower i) : Plane) ∈ Q.carrier := by
  simp only [Rectangle.carrier, Set.mem_setOf_eq]
  intro i
  refine ⟨?_, ?_⟩
  · show Q.lower i ≤ Q.lower i
    exact le_rfl
  · show Q.lower i ≤ Q.upper i
    exact le_of_lt (Q.nondegenerate i)

theorem carrier_nonempty (Q : Rectangle) : Q.carrier.Nonempty :=
  ⟨_, mem_carrier_lowerCorner Q⟩

/-- A rectangle is nondegenerate, so a small ball about its midpoint stays inside its
carrier and the interior of the carrier is nonempty.  This is what replaces "every point
lies in a cell" in the block arguments: cells cover a dense set, so they meet every
nonempty open set, and a rectangle supplies one. -/
theorem interior_carrier_nonempty (Q : Rectangle) : (interior Q.carrier).Nonempty := by
  obtain ⟨ρ, hρdef⟩ :
      ∃ r : ℝ, r = min (Q.upper 0 - Q.lower 0) (Q.upper 1 - Q.lower 1) / 2 := ⟨_, rfl⟩
  have hgap0 : 0 < Q.upper 0 - Q.lower 0 := sub_pos.mpr (Q.nondegenerate 0)
  have hgap1 : 0 < Q.upper 1 - Q.lower 1 := sub_pos.mpr (Q.nondegenerate 1)
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact div_pos (lt_min hgap0 hgap1) (by norm_num)
  have hcoord : ∀ i : Fin 2, ρ ≤ (Q.upper i - Q.lower i) / 2 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [hρdef]
      linarith [min_le_left (Q.upper 0 - Q.lower 0) (Q.upper 1 - Q.lower 1)]
    · rw [hρdef]
      linarith [min_le_right (Q.upper 0 - Q.lower 0) (Q.upper 1 - Q.lower 1)]
  have hball :
      Metric.ball (WithLp.toLp 2 (fun i => (Q.lower i + Q.upper i) / 2) : Plane) ρ
        ⊆ Q.carrier := by
    intro z hz
    simp only [Rectangle.carrier, Set.mem_setOf_eq]
    intro i
    have hlt : dist z (WithLp.toLp 2 (fun i => (Q.lower i + Q.upper i) / 2) : Plane) < ρ :=
      Metric.mem_ball.mp hz
    have hdz : dist (z i) ((Q.lower i + Q.upper i) / 2)
        ≤ dist z (WithLp.toLp 2 (fun i => (Q.lower i + Q.upper i) / 2) : Plane) := by
      have h := (lipschitzWith_coordProj i).dist_le_mul z
        (WithLp.toLp 2 (fun i => (Q.lower i + Q.upper i) / 2) : Plane)
      simp only [coordProj_apply, NNReal.coe_one, one_mul] at h
      exact h
    have habs : |z i - (Q.lower i + Q.upper i) / 2| < ρ := by
      rw [← Real.dist_eq]
      linarith
    rw [abs_lt] at habs
    have hle := hcoord i
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  refine ⟨WithLp.toLp 2 (fun i => (Q.lower i + Q.upper i) / 2), interior_mono hball ?_⟩
  rw [Metric.isOpen_ball.interior_eq]
  exact Metric.mem_ball_self hρpos

/-- Every rectangle is contained in some ball about the origin. -/
theorem rectangle_carrier_subset_closedBall (Q : Rectangle) :
    ∃ r : ℝ, 0 ≤ r ∧ Q.carrier ⊆ Metric.closedBall (0 : Plane) r := by
  refine ⟨(|Q.lower 0| + |Q.upper 0|) + (|Q.lower 1| + |Q.upper 1|), by positivity, ?_⟩
  intro w hw
  simp only [Rectangle.carrier, Set.mem_setOf_eq] at hw
  have ha0 : (0 : ℝ) ≤ |Q.lower 0| + |Q.upper 0| := by positivity
  have hb0 : (0 : ℝ) ≤ |Q.lower 1| + |Q.upper 1| := by positivity
  have hw0 : |w 0| ≤ |Q.lower 0| + |Q.upper 0| := by
    obtain ⟨h1, h2⟩ := hw 0
    have h3 := neg_abs_le (Q.lower 0)
    have h4 := le_abs_self (Q.upper 0)
    have h5 := abs_nonneg (Q.lower 0)
    have h6 := abs_nonneg (Q.upper 0)
    rw [abs_le]
    constructor <;> linarith
  have hw1 : |w 1| ≤ |Q.lower 1| + |Q.upper 1| := by
    obtain ⟨h1, h2⟩ := hw 1
    have h3 := neg_abs_le (Q.lower 1)
    have h4 := le_abs_self (Q.upper 1)
    have h5 := abs_nonneg (Q.lower 1)
    have h6 := abs_nonneg (Q.upper 1)
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 2, ‖w i‖ ^ 2
      ≤ ((|Q.lower 0| + |Q.upper 0|) + (|Q.lower 1| + |Q.upper 1|)) ^ 2 := by
    rw [Fin.sum_univ_two]
    simp only [Real.norm_eq_abs]
    nlinarith [abs_nonneg (w 0), abs_nonneg (w 1), mul_nonneg ha0 hb0]
  calc Real.sqrt (∑ i : Fin 2, ‖w i‖ ^ 2)
      ≤ Real.sqrt (((|Q.lower 0| + |Q.upper 0|) + (|Q.lower 1| + |Q.upper 1|)) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = (|Q.lower 0| + |Q.upper 0|) + (|Q.lower 1| + |Q.upper 1|) :=
        Real.sqrt_sq (by positivity)

/-- The manuscript's containment: a square meeting `clB R` lies in
`clB (R + 2 ℓ(S))`. -/
theorem square_subset_closedBall_of_meets (D : Grid) (s : SquareIndex) {R : ℝ}
    (h : ((square D s).carrier ∩ Metric.closedBall (0 : Plane) R).Nonempty) :
    (square D s).carrier ⊆ Metric.closedBall (0 : Plane) (R + 2 * side D s.1) := by
  obtain ⟨z, hz, hzB⟩ := h
  intro w hw
  have h1 : dist w z ≤ 2 * side D s.1 := dist_le_two_mul_side D s hw hz
  have h2 : dist z (0 : Plane) ≤ R := Metric.mem_closedBall.mp hzB
  rw [Metric.mem_closedBall]
  calc dist w (0 : Plane) ≤ dist w z + dist z 0 := dist_triangle _ _ _
    _ ≤ 2 * side D s.1 + R := add_le_add h1 h2
    _ = R + 2 * side D s.1 := by ring

/-! ### Scales along the ancestor chain -/

/-- `ℓ(S^{(j)}) = 2^j ℓ(S)`. -/
theorem side_ancestor (D : Grid) (s : SquareIndex) (j : ℕ) :
    side D (ancestor D s j).1 = 2 ^ j * side D s.1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestor_succ', parent_fst, side_succ, ih, pow_succ]
      ring

theorem square_subset_ancestor (D : Grid) (s : SquareIndex) (j : ℕ) :
    (square D s).carrier ⊆ (square D (ancestor D s j)).carrier := by
  induction j with
  | zero => exact Set.Subset.rfl
  | succ j ih =>
      rw [ancestor_succ']
      exact ih.trans (square_subset_parent D (ancestor D s j))

/-- The sides of the ancestor chain are unbounded. -/
theorem exists_ancestor_side_ge (D : Grid) (s : SquareIndex) (t : ℝ) :
    ∃ J : ℕ, t ≤ side D (ancestor D s J).1 := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (t / side D s.1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨J, ?_⟩
  rw [side_ancestor]
  have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
  have h := (div_lt_iff₀ hside).mp hJ
  linarith

/-- Arbitrarily fine levels: `ℓ(k) → 0` as `k → -∞`. -/
theorem exists_side_le (D : Grid) {t : ℝ} (ht : 0 < t) : ∃ k : ℤ, side D k ≤ t := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / t) (by norm_num : (1 : ℝ) < 2)
  refine ⟨-(n : ℤ), ?_⟩
  have hphase : D.phase < 1 := D.phase_mem.2
  have h1 : side D (-(n : ℤ)) ≤ (2 : ℝ) ^ (1 + (-(n : ℝ))) := by
    unfold side
    rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    push_cast
    linarith
  have h2 : (2 : ℝ) ^ (1 + (-(n : ℝ))) = 2 * ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpowne : ((2 : ℝ) ^ n) ≠ 0 := ne_of_gt hpow
  have hlt : (2 : ℝ) < (2 : ℝ) ^ n * t := (div_lt_iff₀ ht).mp hn
  have h4 : 2 * ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ n * t) * ((2 : ℝ) ^ n)⁻¹ :=
    mul_le_mul_of_nonneg_right hlt.le (inv_pos.mpr hpow).le
  have h5 : ((2 : ℝ) ^ n * t) * ((2 : ℝ) ^ n)⁻¹ = t := by field_simp
  rw [h2] at h1
  linarith

/-! ### The ratio bound along a chain of squares in a controlled ball -/

/-- `D(S) ≤ c ℓ(S)` gives `D(S)/ℓ(S) ≤ c`. -/
theorem cellRatio_le_ofReal (F : IndexedCells V) (D : Grid) (s : SquareIndex) {c r : ℝ}
    (hc : 0 ≤ c) (hball : (square D s).carrier ⊆ Metric.closedBall (0 : Plane) r)
    (hD : maxDiamHittingBall F r ≤ ENNReal.ofReal (c * side D s.1)) :
    cellRatio F D s ≤ ENNReal.ofReal c := by
  have h1 : maxCellDiameter F D s ≤ ENNReal.ofReal c * ENNReal.ofReal (side D s.1) := by
    refine le_trans (maxCellDiameter_le_maxDiamHittingBall F D s hball) ?_
    rw [← ENNReal.ofReal_mul hc]
    exact hD
  exact ENNReal.div_le_of_le_mul h1

/-- The manuscript's uniform ancestor bound.  If `S` sits in `clB r₀` and the
`J`-th ancestor is already so large that `ℓ(S^{(J)}) ≥ R₀` and
`r₀ ≤ K ℓ(S^{(J)})`, then every ancestor `T` of `S^{(J)}` lies in
`clB (r₀ + 2 ℓ(T)) ⊆ clB ((K+2) ℓ(T))`, so the sublinear bound
`D_r ≤ δ r` gives `a(S^{(J)}) ≤ δ (K+2)`. -/
theorem ancestorRatio_ancestor_le (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    {r₀ δ R₀ K : ℝ} (hr₀ : 0 ≤ r₀) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hsub : ∀ r : ℝ, R₀ ≤ r → maxDiamHittingBall F r ≤ ENNReal.ofReal (δ * r))
    (hball : (square D s).carrier ⊆ Metric.closedBall (0 : Plane) r₀)
    (J : ℕ) (hJR : R₀ ≤ side D (ancestor D s J).1)
    (hJr : r₀ ≤ K * side D (ancestor D s J).1) :
    ancestorRatio F D (ancestor D s J) ≤ ENNReal.ofReal (δ * (K + 2)) := by
  rw [ancestorRatio_eq_iSup]
  refine iSup_le fun i => ?_
  set T := ancestor D (ancestor D s J) i with hT
  have hsideT : side D T.1 = 2 ^ i * side D (ancestor D s J).1 := by
    rw [hT, side_ancestor]
  have hposJ : (0 : ℝ) < side D (ancestor D s J).1 := side_pos _ _
  have hposT : (0 : ℝ) < side D T.1 := side_pos _ _
  have hge : side D (ancestor D s J).1 ≤ side D T.1 := by
    have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    rw [hsideT]
    nlinarith
  have hsq : (square D s).carrier ⊆ (square D T).carrier := by
    refine (square_subset_ancestor D s J).trans ?_
    rw [hT]
    exact square_subset_ancestor D (ancestor D s J) i
  have hmeetS : ((square D s).carrier ∩ Metric.closedBall (0 : Plane) r₀).Nonempty := by
    obtain ⟨z, hz⟩ := carrier_nonempty (square D s)
    exact ⟨z, hz, hball hz⟩
  have hmeetT : ((square D T).carrier ∩ Metric.closedBall (0 : Plane) r₀).Nonempty :=
    Set.Nonempty.mono (Set.inter_subset_inter_left _ hsq) hmeetS
  have hsubT : (square D T).carrier ⊆
      Metric.closedBall (0 : Plane) (r₀ + 2 * side D T.1) :=
    square_subset_closedBall_of_meets D T hmeetT
  have hrge : R₀ ≤ r₀ + 2 * side D T.1 := by
    have : R₀ ≤ side D T.1 := le_trans hJR hge
    linarith
  have hDb : maxDiamHittingBall F (r₀ + 2 * side D T.1)
      ≤ ENNReal.ofReal (δ * (K + 2) * side D T.1) := by
    refine le_trans (hsub _ hrge) (ENNReal.ofReal_le_ofReal ?_)
    have h1 : r₀ ≤ K * side D T.1 :=
      le_trans hJr (mul_le_mul_of_nonneg_left hge hK)
    have h2 : δ * r₀ ≤ δ * (K * side D T.1) := mul_le_mul_of_nonneg_left h1 hδ.le
    nlinarith
  exact cellRatio_le_ofReal F D T (mul_nonneg hδ.le (by linarith)) hsubT hDb

/-- Iterating `a(S) ≤ 2 a(P)`. -/
theorem ancestorRatio_le_pow_mul_ancestor (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (j : ℕ) : ancestorRatio F D s ≤ 2 ^ j * ancestorRatio F D (ancestor D s j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      refine le_trans ih ?_
      rw [ancestor_succ']
      calc (2 : ℝ≥0∞) ^ j * ancestorRatio F D (ancestor D s j)
          ≤ 2 ^ j * (2 * ancestorRatio F D (parent D (ancestor D s j))) :=
            mul_le_mul' le_rfl (ancestorRatio_le_two_mul_parent F D (ancestor D s j))
        _ = 2 ^ (j + 1) * ancestorRatio F D (parent D (ancestor D s j)) := by
            rw [pow_succ]; ring

/-! ### The finite positive indices of the actual dyadic grid -/

/-- The sublinear decay hypothesis used throughout: the `ε`-form conclusion of
`ae_maxDiamHittingBall_finite_and_sublinear`. -/
def SublinearDiameterDecay (F : IndexedCells V) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    maxDiamHittingBall F R ≤ ENNReal.ofReal (ε * R)

/-- `a(S) < ∞` for every dyadic square. -/
theorem ancestorRatio_lt_top (F : IndexedCells V) (D : Grid)
    (hsub : SublinearDiameterDecay F) (s : SquareIndex) : ancestorRatio F D s < ∞ := by
  obtain ⟨R₀, hR₀, hR₀b⟩ := hsub 1 one_pos
  obtain ⟨r₀, hr₀, hball⟩ := rectangle_carrier_subset_closedBall (square D s)
  obtain ⟨J, hJ⟩ := exists_ancestor_side_ge D s (max R₀ r₀)
  have hmain : ancestorRatio F D (ancestor D s J) ≤ ENNReal.ofReal (1 * ((1 : ℝ) + 2)) :=
    ancestorRatio_ancestor_le F D s (K := 1) hr₀ one_pos zero_le_one hR₀b hball J
      (le_trans (le_max_left _ _) hJ)
      (by rw [one_mul]; exact le_trans (le_max_right _ _) hJ)
  refine lt_of_le_of_lt (ancestorRatio_le_pow_mul_ancestor F D s J) ?_
  refine ENNReal.mul_lt_top ?_ (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top)
  exact lt_top_iff_ne_top.2 (ENNReal.pow_ne_top (by simp))

/-- `D(S) < ∞` for every dyadic square. -/
theorem maxCellDiameter_lt_top (F : IndexedCells V) (D : Grid)
    (hfin : ∀ R : ℝ, 0 ≤ R → maxDiamHittingBall F R < ∞) (s : SquareIndex) :
    maxCellDiameter F D s < ∞ := by
  obtain ⟨r, hr, hball⟩ := rectangle_carrier_subset_closedBall (square D s)
  exact lt_of_le_of_lt (maxCellDiameter_le_maxDiamHittingBall F D s hball) (hfin r hr)

/-- Every cell has positive diameter: it is compact with nonempty interior, hence of
positive volume, hence not a single point. -/
theorem diam_cell_pos_of_geometry [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (v : V) :
    0 < Metric.diam (F.cell v : Set Plane) := by
  have hvol : 0 < volume ((F.cell v : Set Plane)) :=
    Measure.measure_pos_of_nonempty_interior (μ := volume) (hF.2.1 v)
  have hnt : (F.cell v : Set Plane).Nontrivial := by
    rcases Set.subsingleton_or_nontrivial ((F.cell v : Set Plane)) with hsub | hnt
    · exact absurd (hsub.measure_zero volume) hvol.ne'
    · exact hnt
  exact Metric.diam_pos hnt (F.cell v).isCompact.isBounded

/-- Under `Geometry`, every **covered** point lies in a cell of positive diameter.  The
covering hypothesis `z ∉ uncoveredSet F` is new: since the covering clause of `Geometry`
only asks that the uncovered set be `H¹`-null, a prescribed point need no longer lie in a
cell. -/
theorem exists_mem_cell_diam_pos [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : Plane) (hz : z ∉ uncoveredSet F) :
    ∃ v : V, z ∈ (F.cell v : Set Plane) ∧ 0 < Metric.diam (F.cell v : Set Plane) := by
  obtain ⟨v, hv⟩ := exists_mem_cell_of_notMem_uncoveredSet hz
  exact ⟨v, hv, diam_cell_pos_of_geometry F hF v⟩

/-- Under `Geometry`, every nonempty open set contains a point lying in a cell of positive
diameter.  The uncovered set is `H¹`-null, hence has dense complement, so a covered point
is available in every nonempty open set — though not necessarily at a prescribed point. -/
theorem exists_mem_cell_diam_pos_of_isOpen [Countable V] (F : IndexedCells V)
    (hF : Geometry F) {U : Set Plane} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, ∃ v : V,
      z ∈ (F.cell v : Set Plane) ∧ 0 < Metric.diam (F.cell v : Set Plane) := by
  obtain ⟨z, hzU, v, hv⟩ := exists_mem_cell_of_isOpen hF hU hUne
  exact ⟨z, hzU, v, hv, diam_cell_pos_of_geometry F hF v⟩

/-- `0 < D(S)`: the square contains a point, and its cell has positive
diameter. -/
theorem maxCellDiameter_pos [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (s : SquareIndex) : 0 < maxCellDiameter F D s := by
  obtain ⟨z, hz, v, hv, hd⟩ := exists_mem_cell_diam_pos_of_isOpen F hF
    (U := interior (square D s).carrier) isOpen_interior
    (interior_carrier_nonempty (square D s))
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd) ?_
  exact le_iSup (fun w : patchVertices F (square D s) =>
    ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, ⟨z, hv, interior_subset hz⟩⟩

theorem ancestorRatio_pos (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (hD : 0 < maxCellDiameter F D s) : 0 < ancestorRatio F D s := by
  refine lt_of_lt_of_le ?_ (cellRatio_le_ancestorRatio F D s)
  exact ENNReal.div_pos hD.ne' ENNReal.ofReal_ne_top

/-- All six clauses of `FinitePositiveIndices` for the actual dyadic grid, from
the geometry of the cells and the large-cell decay.  The `κ` clauses are the
checked `finitePositiveIndices_of_diam_and_ratio`. -/
theorem finitePositiveIndices_of_geometry_of_sublinear [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid)
    (hfin : ∀ R : ℝ, 0 ≤ R → maxDiamHittingBall F R < ∞)
    (hsub : SublinearDiameterDecay F) : FinitePositiveIndices F D :=
  finitePositiveIndices_of_diam_and_ratio F D
    (fun s => ⟨maxCellDiameter_pos F hF D s, maxCellDiameter_lt_top F D hfin s⟩)
    (fun s => ⟨ancestorRatio_pos F D s (maxCellDiameter_pos F hF D s),
      ancestorRatio_lt_top F D hsub s⟩)

/-! ### Selected blocks exist -/

/-- Along the chain of `S`, the ancestor ratio becomes arbitrarily small. -/
theorem exists_ancestorRatio_ancestor_le (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (hsub : SublinearDiameterDecay F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ, ancestorRatio F D (ancestor D s J) ≤ ENNReal.ofReal (3 * δ) := by
  obtain ⟨R₀, hR₀, hR₀b⟩ := hsub δ hδ
  obtain ⟨r₀, hr₀, hball⟩ := rectangle_carrier_subset_closedBall (square D s)
  obtain ⟨J, hJ⟩ := exists_ancestor_side_ge D s (max R₀ r₀)
  refine ⟨J, ?_⟩
  have h := ancestorRatio_ancestor_le F D s (K := 1) hr₀ hδ zero_le_one hR₀b hball J
    (le_trans (le_max_left _ _) hJ)
    (by rw [one_mul]; exact le_trans (le_max_right _ _) hJ)
  have hrw : δ * ((1 : ℝ) + 2) = 3 * δ := by ring
  rwa [hrw] at h

/-- The manuscript's `κ(S^{(J)}) → ∞`: the block index exceeds any fixed level
somewhere along the chain. -/
theorem exists_blockIndex_ancestor_gt (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    (hsub : SublinearDiameterDecay F) (m : ℝ) (hm : 0 < m) :
    ∃ J : ℕ, ENNReal.ofReal m < blockIndex F D (ancestor D s J) := by
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have hδ : (0 : ℝ) < (3 * (m + 1))⁻¹ := by positivity
  obtain ⟨J, hJ⟩ := exists_ancestorRatio_ancestor_le F D s hsub hδ
  refine ⟨J, ?_⟩
  have h3δ : (3 : ℝ) * (3 * (m + 1))⁻¹ = (m + 1)⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_mul]
  rw [h3δ] at hJ
  have h1 : ancestorRatio F D (ancestor D s J) ≤ (ENNReal.ofReal (m + 1))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hm1]
    exact hJ
  have hkey : ENNReal.ofReal (m + 1) ≤ inverseRatio F D (ancestor D s J) := by
    show ENNReal.ofReal (m + 1) ≤ (ancestorRatio F D (ancestor D s J))⁻¹
    calc ENNReal.ofReal (m + 1) = ((ENNReal.ofReal (m + 1))⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (ancestorRatio F D (ancestor D s J))⁻¹ := ENNReal.inv_le_inv.2 h1
  refine lt_of_lt_of_le ?_ (le_trans hkey (inverseRatio_le_blockIndex F D (ancestor D s J)))
  exact (ENNReal.ofReal_lt_ofReal_iff hm1).2 (by linarith)

/-- Selected squares exist along any chain starting below the level `m`. -/
theorem exists_selected_ancestor_of_blockIndex_le (F : IndexedCells V) (D : Grid)
    (hsub : SublinearDiameterDecay F) (m : ℝ) (hm : 0 < m) (s : SquareIndex)
    (h0 : blockIndex F D s ≤ ENNReal.ofReal m) :
    ∃ j : ℕ, Selected F D m (ancestor D s j) := by
  obtain ⟨J, hJ⟩ := exists_blockIndex_ancestor_gt F D s hsub m hm
  exact exists_selected_ancestor F D m hm s h0 J hJ

/-- The dyadic square of level `k` containing a given point. -/
noncomputable def containingIndex (D : Grid) (k : ℤ) (z : Plane) : SquareIndex :=
  (k, fun i => ⌊(z i - D.origin k i) / side D k⌋)

@[simp] theorem containingIndex_fst (D : Grid) (k : ℤ) (z : Plane) :
    (containingIndex D k z).1 = k := rfl

theorem mem_square_containingIndex (D : Grid) (k : ℤ) (z : Plane) :
    z ∈ (square D (containingIndex D k z)).carrier := by
  simp only [Rectangle.carrier, Set.mem_setOf_eq]
  intro i
  have hside : (0 : ℝ) < side D k := side_pos D k
  have hne : side D k ≠ 0 := ne_of_gt hside
  have hsx : side D k * ((z i - D.origin k i) / side D k) = z i - D.origin k i := by
    field_simp
  have hlower : (square D (containingIndex D k z)).lower i
      = D.origin k i + side D k * (⌊(z i - D.origin k i) / side D k⌋ : ℝ) := rfl
  have hupper : (square D (containingIndex D k z)).upper i
      = D.origin k i + side D k * (⌊(z i - D.origin k i) / side D k⌋ : ℝ) + side D k := rfl
  rw [hlower, hupper]
  constructor
  · have h := Int.floor_le ((z i - D.origin k i) / side D k)
    have h2 := mul_le_mul_of_nonneg_left h hside.le
    rw [hsx] at h2
    linarith
  · have h := Int.lt_floor_add_one ((z i - D.origin k i) / side D k)
    have h2 := mul_lt_mul_of_pos_left h hside
    rw [hsx] at h2
    linarith

/-- Deep squares have small block index: `κ(S) ≤ 2 ℓ(S)/d_H` for any cell `H`
meeting `S` at a point of `S`. -/
theorem blockIndex_le_ofReal_of_mem (F : IndexedCells V) (D : Grid) (s : SquareIndex)
    {z : Plane} (hz : z ∈ (square D s).carrier) {v : V} (hv : z ∈ (F.cell v : Set Plane))
    (hd : 0 < Metric.diam (F.cell v : Set Plane)) :
    blockIndex F D s ≤
      ENNReal.ofReal (2 * (side D s.1 / Metric.diam (F.cell v : Set Plane))) := by
  have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
  have hdiam : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)) ≤ maxCellDiameter F D s :=
    le_iSup (fun w : patchVertices F (square D s) =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, ⟨z, hv, hz⟩⟩
  have hratio : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) / side D s.1)
      ≤ ancestorRatio F D s := by
    refine le_trans ?_ (cellRatio_le_ancestorRatio F D s)
    show ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) / side D s.1)
      ≤ maxCellDiameter F D s / ENNReal.ofReal (side D s.1)
    rw [ENNReal.ofReal_div_of_pos hside]
    exact ENNReal.div_le_div_right hdiam _
  have hinv : inverseRatio F D s
      ≤ ENNReal.ofReal (side D s.1 / Metric.diam (F.cell v : Set Plane)) := by
    show (ancestorRatio F D s)⁻¹
      ≤ ENNReal.ofReal (side D s.1 / Metric.diam (F.cell v : Set Plane))
    have hpos : (0 : ℝ) < Metric.diam (F.cell v : Set Plane) / side D s.1 := by positivity
    have h1 : (ancestorRatio F D s)⁻¹
        ≤ (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) / side D s.1))⁻¹ :=
      ENNReal.inv_le_inv.2 hratio
    refine le_trans h1 ?_
    rw [← ENNReal.ofReal_inv_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_div]
  have h2 : ENNReal.ofReal (2 * (side D s.1 / Metric.diam (F.cell v : Set Plane)))
      = 2 * ENNReal.ofReal (side D s.1 / Metric.diam (F.cell v : Set Plane)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h2]
  exact le_trans (blockIndex_le_two_mul_inverseRatio F D s) (mul_le_mul' le_rfl hinv)

/-- The manuscript's selected blocks really exist: every **covered** point of the plane is
contained in a square selected at the fixed level `m`.

The hypothesis `hz` is new and is the manuscript's own restriction (§3.1, *"their closures
cover every point belonging to a cell"*).  It is not removable: the whole argument runs on the
diameter of a cell *containing* `z`, and the covering clause of `Geometry` now only asks
`μH[1] (uncoveredSet F) = 0`, so an uncovered `z` supplies no such cell and the block index
along its chain need never drop below `m`.  All four call sites discharge it immediately —
three of them apply the theorem at a point they have just produced inside a cell. -/
theorem exists_selected_mem [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (hsub : SublinearDiameterDecay F) (m : ℝ) (hm : 0 < m) (z : Plane)
    (hzcov : z ∉ uncoveredSet F) :
    ∃ t : SquareIndex, Selected F D m t ∧ z ∈ (square D t).carrier := by
  obtain ⟨v, hv, hd⟩ := exists_mem_cell_diam_pos F hF z hzcov
  obtain ⟨k, hk⟩ := exists_side_le D
    (t := m * Metric.diam (F.cell v : Set Plane) / 2) (by positivity)
  have hz : z ∈ (square D (containingIndex D k z)).carrier := mem_square_containingIndex D k z
  have h0 : blockIndex F D (containingIndex D k z) ≤ ENNReal.ofReal m := by
    refine le_trans (blockIndex_le_ofReal_of_mem F D _ hz hv hd) (ENNReal.ofReal_le_ofReal ?_)
    rw [containingIndex_fst]
    have hdiv : side D k / Metric.diam (F.cell v : Set Plane) ≤ m / 2 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith
  obtain ⟨j, hj⟩ := exists_selected_ancestor_of_blockIndex_le F D hsub m hm _ h0
  exact ⟨ancestor D (containingIndex D k z) j, hj,
    square_subset_ancestor D (containingIndex D k z) j hz⟩

/-! ### The fixed-parameter blocks are submacroscopic -/

/-- The manuscript's `s_m(R)`: the supremum of the side lengths of the selected
squares meeting `clB R`. -/
noncomputable def maxSelectedSide (F : IndexedCells V) (D : Grid) (m R : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : SquareIndex // Selected F D m s ∧
      ((square D s).carrier ∩ Metric.closedBall (0 : Plane) R).Nonempty},
    ENNReal.ofReal (side D s.1.1)

/-- The core of `s:lem:smallblocks`: a selected square meeting `clB R` has side
less than `ε R` once `R` is large.  If instead `ℓ(S) ≥ ε R`, the whole ancestor
chain of `S` lies in `clB (K_ε ℓ(T))`, so `a(S) ≤ (2m)⁻¹` and
`κ(S) ≥ b(S) ≥ 2m`, contradicting `κ(S) ≤ m`. -/
theorem side_lt_of_selected_of_meets (F : IndexedCells V) (D : Grid) (m : ℝ)
    (hsub : SublinearDiameterDecay F) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R → ∀ s : SquareIndex, Selected F D m s →
      ((square D s).carrier ∩ Metric.closedBall (0 : Plane) R).Nonempty →
      side D s.1 < ε * R := by
  by_cases hm : 0 < m
  · have hεne : ε ≠ 0 := ne_of_gt hε
    have hεinv : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
    have hK : (0 : ℝ) < ε⁻¹ + 2 := by linarith
    have hK2 : (0 : ℝ) < (ε⁻¹ + 2) + 2 := by linarith
    have hprod : (0 : ℝ) < 2 * m * ((ε⁻¹ + 2) + 2) :=
      mul_pos (by linarith : (0 : ℝ) < 2 * m) hK2
    obtain ⟨R₀, hR₀, hR₀b⟩ := hsub ((2 * m * ((ε⁻¹ + 2) + 2))⁻¹) (inv_pos.mpr hprod)
    refine ⟨max 1 (R₀ / ε), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    intro R hR s hs hmeet
    by_contra hcon
    push_neg at hcon
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hRdiv : R₀ / ε ≤ R := le_trans (le_max_right _ _) hR
    have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
    have hεR : ε * R ≤ side D s.1 := hcon
    have hR₀le : R₀ ≤ side D s.1 := by
      have h1 : R₀ / ε * ε ≤ R * ε := mul_le_mul_of_nonneg_right hRdiv hε.le
      have h2 : R₀ / ε * ε = R₀ := by field_simp
      linarith
    have hball : (square D s).carrier ⊆
        Metric.closedBall (0 : Plane) (R + 2 * side D s.1) :=
      square_subset_closedBall_of_meets D s hmeet
    have hRle : R ≤ ε⁻¹ * side D s.1 := by
      have h := mul_le_mul_of_nonneg_left hεR (le_of_lt (inv_pos.mpr hε))
      rwa [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at h
    have hKr : R + 2 * side D s.1 ≤ (ε⁻¹ + 2) * side D s.1 := by
      nlinarith
    have hmain : ancestorRatio F D (ancestor D s 0)
        ≤ ENNReal.ofReal ((2 * m * ((ε⁻¹ + 2) + 2))⁻¹ * ((ε⁻¹ + 2) + 2)) :=
      ancestorRatio_ancestor_le F D s (K := ε⁻¹ + 2) (by linarith) (inv_pos.mpr hprod)
        hK.le hR₀b hball 0 (by rwa [ancestor_zero]) (by rwa [ancestor_zero])
    rw [ancestor_zero] at hmain
    have hA : (2 * m * ((ε⁻¹ + 2) + 2))⁻¹ * ((ε⁻¹ + 2) + 2) = (2 * m)⁻¹ := by
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hK2), mul_one]
    rw [hA] at hmain
    have h2m : (0 : ℝ) < 2 * m := by linarith
    have hinv : ancestorRatio F D s ≤ (ENNReal.ofReal (2 * m))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos h2m]
      exact hmain
    have hkey : ENNReal.ofReal (2 * m) ≤ inverseRatio F D s := by
      show ENNReal.ofReal (2 * m) ≤ (ancestorRatio F D s)⁻¹
      calc ENNReal.ofReal (2 * m) = ((ENNReal.ofReal (2 * m))⁻¹)⁻¹ := (inv_inv _).symm
        _ ≤ (ancestorRatio F D s)⁻¹ := ENNReal.inv_le_inv.2 hinv
    have hfinal : ENNReal.ofReal (2 * m) ≤ ENNReal.ofReal m :=
      le_trans (le_trans hkey (inverseRatio_le_blockIndex F D s)) hs.2.1
    have := (ENNReal.ofReal_le_ofReal_iff hm.le).1 hfinal
    linarith
  · exact ⟨1, one_pos, fun R _ s hs _ => absurd hs.1 hm⟩

/-- `s_m(R) ≤ ε R` for large `R`. -/
theorem maxSelectedSide_le_ofReal (F : IndexedCells V) (D : Grid) (m : ℝ)
    (hsub : SublinearDiameterDecay F) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
      maxSelectedSide F D m R ≤ ENNReal.ofReal (ε * R) := by
  obtain ⟨R₁, hR₁, h⟩ := side_lt_of_selected_of_meets F D m hsub hε
  refine ⟨R₁, hR₁, fun R hR => ?_⟩
  unfold maxSelectedSide
  refine iSup_le ?_
  rintro ⟨s, hs, hmeet⟩
  exact ENNReal.ofReal_le_ofReal (h R hR s hs hmeet).le

/-! ### The random-environment form -/

end ReflectedGMS.NonmacroscopicSelectedBlocks
