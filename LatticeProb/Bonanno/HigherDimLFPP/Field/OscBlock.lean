/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.OscBlock at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandFacts
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsAdmissiblePath
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.LfppLength
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite

/-!
# Boxes, grids and the block bound for band fields (packet P-OSC)

Source: `source/higher-dimensional-lfpp-limit.pdf`, Lemma 4.1 ("Moreover") and App. A.1 (last
paragraph); planning audits HA3 (Details D3 (b), "Blocks"/"On one block") and HA5 (Details D4,
Lemma O).

Deterministic part:

* `Osc.box x₀ R = x₀ + [-R, R]^d` and the grid `Osc.grid x₀ R a` of mesh `a` in it, with at most
  `(2R/a + 1)^d` points (`Osc.card_grid_le`); every point of the box lies in the box cell of its
  grid point `Osc.gridOf x₀ R a z`, at distance at most `√d a` (`Osc.norm_sub_gridOf_le`).
* `Osc.closure_cube_subset_box`: `closure U ⊆ [-2, 2]^d`.

Probabilistic part (HA3 D3 (b) "On one block", HA5 Lemma O): for a continuous version `H` of a
band field `H_{a,b}` whose kernel increments satisfy `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²`
(`norm_bandVec_sub_sq_le`), the process `z ↦ H z - H g` on the closed ball `B̄(g, r a)` is a
continuous centered Gaussian process with `E (Δ H)² ≤ (2 r L √d / a) ‖z - w‖_∞`, so chaining
(`LQGMetric.SupTail.integral_iSup_family_le`, built on `LQGDimension.ChainBox.chainingBox_bound`)
gives `E sup ≤ Osc.blockConst d L r` and Borell–TIS (`LQGMetric.SupTail.tail_iSup_abs_le`, with
`Var ≤ r² L`) gives

`P(∃ z ∈ B̄(g, r a), blockConst + u < |H z - H g|) ≤ 2 exp(-u² / (2 r² L))`  (`Osc.block_tail`).

`Osc.box_osc_tail` is the resulting oscillation tail on a box `x₀ + [-ρa, ρa]^d` (HA5 D4,
Lemma O).  The helpers `Osc.memLp_two_of_isBandVersion`, `Osc.isGaussianProcess_sub`,
`Osc.variance_sub_eq`, `Osc.integral_sub_sq` record the Gaussian increments of versions.

The 2D template is `LQGDimension/LFPP/OscillationAux.lean` (`Osc37.std_block_bound`,
`block_finset_bound`, `block_event_bound`), where the chaining and concentration were done in the
Gram space of the circle-average field; here they are done on the probability space directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace Osc

variable {d : ℕ}

/-! ### Coordinates -/

/-- The sup norm of the coordinates is at most the Euclidean norm. -/
theorem norm_ofLp_sub_le (z w : Rd d) : ‖WithLp.ofLp z - WithLp.ofLp w‖ ≤ ‖z - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := PiLp.norm_apply_le (z - w) i
  simpa only [Pi.sub_apply, PiLp.sub_apply] using h

/-- The Euclidean norm is at most `√d` times the sup norm of the coordinates. -/
theorem norm_sub_le_sqrt_mul (z w : Rd d) :
    ‖z - w‖ ≤ √(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by
  have h := norm_toLp_sq_le_dim_mul (d := d) (WithLp.ofLp z - WithLp.ofLp w)
  have e : (WithLp.toLp 2 (WithLp.ofLp z - WithLp.ofLp w) : Rd d) = z - w := by
    rw [← WithLp.ofLp_sub, WithLp.toLp_ofLp]
  rw [e] at h
  have h0 : 0 ≤ √(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (z - w)), ← Real.sqrt_sq h0, mul_pow,
    Real.sq_sqrt (by positivity)]
  exact Real.sqrt_le_sqrt h

/-! ### Boxes and grids -/

/-- The closed box `x₀ + [-R, R]^d`. -/
def box (x₀ : Rd d) (R : ℝ) : Set (Rd d) := {z | ∀ i, |z i - x₀ i| ≤ R}

/-- The point `x₀ - (R, …, R) + a k` of the grid of mesh `a` in `box x₀ R`. -/
def gridPt (x₀ : Rd d) (R a : ℝ) (k : Fin d → ℕ) : Rd d :=
  WithLp.toLp 2 fun i => x₀ i - R + a * k i

/-- The grid of mesh `a` in `box x₀ R`: the points `x₀ - (R, …, R) + a k` with
`0 ≤ kᵢ ≤ ⌊2R/a⌋`. -/
def grid (x₀ : Rd d) (R a : ℝ) : Finset (Rd d) :=
  (Finset.univ : Finset (Fin d → Fin (⌊2 * R / a⌋₊ + 1))).image
    fun k => gridPt x₀ R a fun i => (k i : ℕ)

/-- The grid point of the cell of `z` (coordinatewise floor). -/
def gridOf (x₀ : Rd d) (R a : ℝ) (z : Rd d) : Rd d :=
  gridPt x₀ R a fun i => ⌊(z i - x₀ i + R) / a⌋₊

/-- Coordinates of a grid point. -/
theorem gridPt_apply (x₀ : Rd d) (R a : ℝ) (k : Fin d → ℕ) (i : Fin d) :
    gridPt x₀ R a k i = x₀ i - R + a * k i := rfl

/-- The grid has at most `(⌊2R/a⌋ + 1)^d` points. -/
theorem card_grid_le_nat (x₀ : Rd d) (R a : ℝ) :
    (grid x₀ R a).card ≤ (⌊2 * R / a⌋₊ + 1) ^ d := by
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The grid has at most `(2R/a + 1)^d` points. -/
theorem card_grid_le (x₀ : Rd d) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    ((grid x₀ R a).card : ℝ) ≤ (2 * R / a + 1) ^ d := by
  have h1 : ((grid x₀ R a).card : ℝ) ≤ ((⌊2 * R / a⌋₊ + 1) ^ d : ℕ) := by
    exact_mod_cast card_grid_le_nat x₀ R a
  refine h1.trans ?_
  push_cast
  gcongr
  exact Nat.floor_le (by positivity)

/-- The grid is nonempty. -/
theorem one_le_card_grid (x₀ : Rd d) (R a : ℝ) : 1 ≤ (grid x₀ R a).card := by
  refine Finset.card_pos.2 ⟨gridPt x₀ R a fun _ => 0, ?_⟩
  exact Finset.mem_image.2 ⟨fun _ => 0, Finset.mem_univ _, rfl⟩

/-- The grid point of a point of the box belongs to the grid. -/
theorem gridOf_mem_grid (x₀ : Rd d) {R a : ℝ} (ha : 0 < a) {z : Rd d} (hz : z ∈ box x₀ R) :
    gridOf x₀ R a z ∈ grid x₀ R a := by
  refine Finset.mem_image.2 ⟨fun i => ⟨⌊(z i - x₀ i + R) / a⌋₊, ?_⟩, Finset.mem_univ _, rfl⟩
  refine Nat.lt_succ_of_le (Nat.floor_le_floor ?_)
  have h := (abs_le.1 (hz i)).2
  exact div_le_div_of_nonneg_right (by linarith) ha.le

/-- Coordinates of a point of the box relative to its grid point lie in `[0, a)`. -/
theorem gridOf_coord (x₀ : Rd d) {R a : ℝ} (ha : 0 < a) {z : Rd d} (hz : z ∈ box x₀ R)
    (i : Fin d) : 0 ≤ z i - gridOf x₀ R a z i ∧ z i - gridOf x₀ R a z i < a := by
  have hy : 0 ≤ (z i - x₀ i + R) / a := by
    have h := (abs_le.1 (hz i)).1
    exact div_nonneg (by linarith) ha.le
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one ((z i - x₀ i + R) / a)
  have e : z i - gridOf x₀ R a z i = a * ((z i - x₀ i + R) / a - ⌊(z i - x₀ i + R) / a⌋₊) := by
    rw [gridOf, gridPt_apply, mul_sub, mul_div_cancel₀ _ ha.ne']
    ring
  rw [e]
  constructor
  · exact mul_nonneg ha.le (by linarith)
  · have : (z i - x₀ i + R) / a - ⌊(z i - x₀ i + R) / a⌋₊ < 1 := by linarith
    calc a * ((z i - x₀ i + R) / a - ⌊(z i - x₀ i + R) / a⌋₊) < a * 1 :=
          mul_lt_mul_of_pos_left this ha
      _ = a := mul_one a

/-- Every point of the box is within `√d a` of its grid point. -/
theorem norm_sub_gridOf_le (x₀ : Rd d) {R a : ℝ} (ha : 0 < a) {z : Rd d} (hz : z ∈ box x₀ R) :
    ‖z - gridOf x₀ R a z‖ ≤ √(d : ℝ) * a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(z - gridOf x₀ R a z) i‖ ^ 2 ≤ (d : ℝ) * a ^ 2 := by
    calc ∑ i, ‖(z - gridOf x₀ R a z) i‖ ^ 2 ≤ ∑ _i : Fin d, a ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨h1, h2⟩ := gridOf_coord x₀ ha hz i
          rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          exact pow_le_pow_left₀ h1 h2.le 2
      _ = (d : ℝ) * a ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc √(∑ i, ‖(z - gridOf x₀ R a z) i‖ ^ 2) ≤ √((d : ℝ) * a ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √(d : ℝ) * a := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq ha.le]

/-- Grid points lie in the box. -/
theorem grid_subset_box (x₀ : Rd d) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) {g : Rd d}
    (hg : g ∈ grid x₀ R a) : g ∈ box x₀ R := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hg
  intro i
  rw [gridPt_apply]
  have hk : ((k i : ℕ) : ℝ) ≤ 2 * R / a := by
    have h1 : (k i : ℕ) ≤ ⌊2 * R / a⌋₊ := Nat.lt_succ_iff.1 (k i).2
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
  have hk' : a * ((k i : ℕ) : ℝ) ≤ 2 * R := by
    rw [le_div_iff₀ ha] at hk
    linarith
  have hk0 : 0 ≤ a * ((k i : ℕ) : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Boxes are compact. -/
theorem isCompact_box (x₀ : Rd d) (R : ℝ) : IsCompact (box x₀ R) := by
  have hcl : IsClosed (box x₀ R) := by
    have : box x₀ R = ⋂ i, {z : Rd d | |z i - x₀ i| ≤ R} := by
      ext z
      simp only [box, mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_abs.comp ((PiLp.continuous_apply 2 _ i).sub continuous_const))
        continuous_const
  have hb : Bornology.IsBounded (box x₀ R) := by
    refine (isBounded_closedBall (x := x₀) (r := √(d : ℝ) * |R|)).subset fun z hz => ?_
    rw [mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖(z - x₀) i‖ ^ 2 ≤ (d : ℝ) * R ^ 2 := by
      calc ∑ i, ‖(z - x₀) i‖ ^ 2 ≤ ∑ _i : Fin d, R ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
            have h := hz i
            have h0 := abs_nonneg (z i - x₀ i)
            exact sq_le_sq' (by linarith [abs_le.1 h]) (abs_le.1 h).2
        _ = (d : ℝ) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc √(∑ i, ‖(z - x₀) i‖ ^ 2) ≤ √((d : ℝ) * R ^ 2) := Real.sqrt_le_sqrt hsum
      _ = √(d : ℝ) * |R| := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq_eq_abs]
  exact Metric.isCompact_of_isClosed_isBounded hcl hb

/-- Points of the box `x₀ + [-R, R]^d` are within `√d R` of `x₀`. -/
theorem norm_sub_le_of_mem_box {x₀ : Rd d} {R : ℝ} (hR : 0 ≤ R) {z : Rd d} (hz : z ∈ box x₀ R) :
    ‖z - x₀‖ ≤ √(d : ℝ) * R := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(z - x₀) i‖ ^ 2 ≤ (d : ℝ) * R ^ 2 := by
    calc ∑ i, ‖(z - x₀) i‖ ^ 2 ≤ ∑ _i : Fin d, R ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          have h := hz i
          exact sq_le_sq' (by linarith [abs_le.1 h]) (abs_le.1 h).2
      _ = (d : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc √(∑ i, ‖(z - x₀) i‖ ^ 2) ≤ √((d : ℝ) * R ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √(d : ℝ) * R := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hR]

/-- `closure U ⊆ [-2, 2]^d`. -/
theorem closure_cube_subset_box : closure (cube d) ⊆ box 0 2 := by
  refine closure_minimal (fun z hz i => ?_) ?_
  · simp only [PiLp.zero_apply, sub_zero]
    exact (hz i).le
  · have : box (0 : Rd d) 2 = ⋂ i, {z : Rd d | |z i - (0 : Rd d) i| ≤ 2} := by
      ext z
      simp only [box, mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_abs.comp ((PiLp.continuous_apply 2 _ i).sub continuous_const))
        continuous_const

/-! ### Band versions: increments -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {H : Rd d → Ω → ℝ}

/-- Values of a version are in `L²`. -/
theorem memLp_two_of_isBandVersion (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (z : Rd d) : MemLp (H z) 2 P :=
  (hW.memLp _ 2 ENNReal.ofNat_ne_top).ae_eq (hH.ae_eq z).symm

/-- Values of a version are integrable. -/
theorem integrable_of_isBandVersion (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (z : Rd d) : Integrable (H z) P := by
  have := hW.isProbabilityMeasure
  exact (memLp_two_of_isBandVersion hH hW z).integrable one_le_two

/-- `z ↦ H (p z) - H g` is a Gaussian process. -/
theorem isGaussianProcess_sub (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    {T : Type*} (p : T → Rd d) (g : Rd d) :
    IsGaussianProcess (fun t ω => H (p t) ω - H g ω) P := by
  refine (hW.isGaussianProcess_comp fun t => bandVec κ a b (p t) - bandVec κ a b g).congr
    fun t => ?_
  filter_upwards [hW.sub_ae (bandVec κ a b (p t)) (bandVec κ a b g), hH.ae_eq (p t), hH.ae_eq g]
    with ω h1 h2 h3
  rw [h1, h2, h3]

/-- Increments of a version are centered. -/
theorem integral_sub_eq_zero (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (z w : Rd d) : ∫ ω, (H z ω - H w ω) ∂P = 0 := by
  rw [integral_sub (integrable_of_isBandVersion hH hW z) (integrable_of_isBandVersion hH hW w),
    hH.integral_eq_zero hW, hH.integral_eq_zero hW, sub_zero]

/-- `Var(H z - H w) = ‖k_z - k_w‖²`. -/
theorem variance_sub_eq (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (z w : Rd d) :
    Var[fun ω => H z ω - H w ω; P] = ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 := by
  rw [(hH.hasLaw_sub hW z w).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (sq_nonneg _)]

/-- `E (H z - H w)² = ‖k_z - k_w‖²`. -/
theorem integral_sub_sq (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (z w : Rd d) :
    ∫ ω, (H z ω - H w ω) ^ 2 ∂P = ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 := by
  rw [← variance_of_integral_eq_zero (hH.hasLaw_sub hW z w).aemeasurable
    (integral_sub_eq_zero hH hW z w), variance_sub_eq hH hW]

end Band

/-! ### The block bound -/

/-- The chaining constant of a block of radius `r a`: `20 √5 · 2 r √(L √d (d + 1))`. -/
def blockConst (d : ℕ) (L r : ℝ) : ℝ := 20 * √5 * (2 * r * √(L * √(d : ℝ) * (d + 1)))

/-- `blockConst d L r ≥ 0` for `r ≥ 0`. -/
theorem blockConst_nonneg (d : ℕ) {L r : ℝ} (hr : 0 ≤ r) : 0 ≤ blockConst d L r := by
  unfold blockConst
  positivity

/-- The chaining bound `20 √5 L_ch √((d+1) a_ch)` with `L_ch² = 2 r L √d / a` and
`a_ch = 2 r a` equals `blockConst d L r` (the mesh `a` cancels). -/
theorem chain_identity {L r a : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (ha : 0 < a) :
    20 * √5 * √(2 * r * L * √(d : ℝ) / a) * √(((d : ℝ) + 1) * (2 * r * a)) =
      blockConst d L r := by
  unfold blockConst
  rw [mul_assoc (20 * √5), ← Real.sqrt_mul (by positivity)]
  congr 1
  have e : 2 * r * L * √(d : ℝ) / a * (((d : ℝ) + 1) * (2 * r * a)) =
      (2 * r) ^ 2 * (L * √(d : ℝ) * (d + 1)) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The increment bound in the form required by the chaining lemmas: if `‖z - w‖ ≤ 2 r a`, then
`L ‖z - w‖² / a² ≤ (√(2 r L √d / a))² ‖z - w‖_∞`. -/
theorem incr_le_chain {L r a : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (ha : 0 < a) {z w : Rd d}
    (hzw : ‖z - w‖ ≤ 2 * r * a) :
    L * ‖z - w‖ ^ 2 / a ^ 2 ≤
      √(2 * r * L * √(d : ℝ) / a) ^ 2 * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by
  rw [Real.sq_sqrt (by positivity)]
  have h2 : ‖z - w‖ ^ 2 ≤ (2 * r * a) * (√(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖) := by
    rw [sq]
    exact mul_le_mul hzw (norm_sub_le_sqrt_mul z w) (norm_nonneg _) (by positivity)
  calc L * ‖z - w‖ ^ 2 / a ^ 2
      ≤ L * ((2 * r * a) * (√(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖)) / a ^ 2 := by gcongr
    _ = 2 * r * L * √(d : ℝ) / a * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by field_simp

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- **Block bound** (HA3 D3 (b) "On one block"; HA5 Lemma O).  Let `H` be a continuous version
of the band field `H_{a,b}` (`0 < a`) whose kernel increments satisfy
`‖k_z - k_w‖² ≤ L ‖z - w‖² / a²`.  Then for every `g`, `r ≥ 0` and `u ≥ 0`,
`P(∃ z ∈ B̄(g, r a), blockConst d L r + u < |H z - H g|) ≤ 2 exp(-u² / (2 r² L))`
(outer measure). -/
theorem block_tail (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) {H : Rd d → Ω → ℝ}
    (hH : IsBandVersion P W κ a b H) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    (g : Rd d) {r : ℝ} (hr : 0 ≤ r) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ z ∈ closedBall g (r * a), blockConst d L r + u < |H z ω - H g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * (r ^ 2 * L)))) := by
  have := hW.isProbabilityMeasure
  set K : Set (Rd d) := closedBall g (r * a) with hK
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall g _)
  have : Nonempty K := ⟨⟨g, mem_closedBall_self (by positivity)⟩⟩
  set X : K → Ω → ℝ := fun z ω => H z ω - H g ω with hXdef
  have hX : IsGaussianProcess X P := isGaussianProcess_sub hH hW (fun z : K => (z : Rd d)) g
  have h0 : ∀ z, ∫ ω, X z ω ∂P = 0 := fun z => integral_sub_eq_zero hH hW z g
  have hc : ∀ ω, Continuous fun z => X z ω := fun ω =>
    ((hH.continuous ω).comp continuous_subtype_val).sub continuous_const
  have hnorm : ∀ z : K, ‖(z : Rd d) - g‖ ≤ r * a := fun z => by
    have h : (z : Rd d) ∈ closedBall g (r * a) := z.2
    rwa [mem_closedBall, dist_eq_norm] at h
  -- chaining on the block, for `X` and `-X`
  have hchain : ∀ Y : K → Ω → ℝ, IsGaussianProcess Y P → (∀ z, ∫ ω, Y z ω ∂P = 0) →
      (∀ z w : K, ∫ ω, (Y z ω - Y w ω) ^ 2 ∂P =
        ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2) →
      ∀ (n : ℕ) (t : Fin (n + 1) → K), ∫ ω, ⨆ i, Y (t i) ω ∂P ≤ blockConst d L r := by
    intro Y hY hY0 hYinc n t
    have hdiam : ∀ z w : K, ‖(z : Rd d) - w‖ ≤ 2 * r * a := fun z w => by
      calc ‖(z : Rd d) - w‖ = ‖((z : Rd d) - g) - ((w : Rd d) - g)‖ := by
            rw [sub_sub_sub_cancel_right]
        _ ≤ ‖(z : Rd d) - g‖ + ‖(w : Rd d) - g‖ := norm_sub_le _ _
        _ ≤ 2 * r * a := by linarith [hnorm z, hnorm w]
    have h := LQGMetric.SupTail.integral_iSup_family_le hY hY0 (n := n + 1) (d := d)
      (Nat.succ_pos n) t (fun z => WithLp.ofLp (z : Rd d))
      (L := √(2 * r * L * √(d : ℝ) / a)) (a := 2 * r * a) (Real.sqrt_nonneg _)
      (fun i j => (norm_ofLp_sub_le _ _).trans (hdiam _ _)) (fun i j => ?_)
    · rwa [chain_identity hL0 hr ha] at h
    · rw [hYinc]
      exact (hL _ _).trans (incr_le_chain hL0 hr ha (hdiam _ _))
  have hXinc : ∀ z w : K, ∫ ω, (X z ω - X w ω) ^ 2 ∂P =
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 := fun z w => by
    simp only [hXdef, sub_sub_sub_cancel_right]
    exact integral_sub_sq hH hW z w
  have hnX : IsGaussianProcess (fun z ω => -X z ω) P := LQGMetric.SupTail.isGaussianProcess_neg hX
  have hnX0 : ∀ z, ∫ ω, -X z ω ∂P = 0 := fun z => by rw [integral_neg, h0, neg_zero]
  have hnXinc : ∀ z w : K, ∫ ω, (-X z ω - -X w ω) ^ 2 ∂P =
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 := fun z w => by
    have e : ∀ ω, (-X z ω - -X w ω) ^ 2 = (X z ω - X w ω) ^ 2 := fun ω => by ring
    simp_rw [e]
    exact hXinc z w
  obtain ⟨hint, hM⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hX hc
    (hchain X hX h0 hXinc)
  obtain ⟨hint', hM'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hnX
    (fun ω => (hc ω).neg) (hchain _ hnX hnX0 hnXinc)
  have hvar : ∀ z : K, Var[X z; P] ≤ (r * √L) ^ 2 := fun z => by
    rw [show X z = fun ω => H z ω - H g ω from rfl, variance_sub_eq hH hW]
    refine (hL z g).trans ?_
    rw [mul_pow, Real.sq_sqrt hL0]
    have h1 : ‖(z : Rd d) - g‖ ^ 2 ≤ (r * a) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2
    calc L * ‖(z : Rd d) - g‖ ^ 2 / a ^ 2 ≤ L * (r * a) ^ 2 / a ^ 2 := by gcongr
      _ = r ^ 2 * L := by field_simp
  have htail := LQGMetric.SupTail.tail_iSup_abs_le hX h0 hc hint hint' hM hM' hvar hu
  have hsub : {ω | ∃ z ∈ K, blockConst d L r + u < |H z ω - H g ω|} ⊆
      {ω | blockConst d L r + u ≤ ⨆ z, |X z ω|} := by
    rintro ω ⟨z, hz, hlt⟩
    have hb : BddAbove (range fun z : K => |X z ω|) :=
      (isCompact_range (continuous_abs.comp (hc ω))).bddAbove
    exact hlt.le.trans (le_ciSup (f := fun z : K => |X z ω|) hb ⟨z, hz⟩)
  calc P {ω | ∃ z ∈ K, blockConst d L r + u < |H z ω - H g ω|}
      ≤ P {ω | blockConst d L r + u ≤ ⨆ z, |X z ω|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | blockConst d L r + u ≤ ⨆ z, |X z ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * (r ^ 2 * L)))) := by
        refine ENNReal.ofReal_le_ofReal (htail.trans_eq ?_)
        rw [mul_pow, Real.sq_sqrt hL0]

/-- **Oscillation on a box** (HA5 D4, Lemma O): for a continuous version `H` of `H_{a,b}` with
the increment bound of `block_tail`, the oscillation of `H` on the box `x₀ + [-ρa, ρa]^d`
(`ρ ≥ 0`) satisfies
`P(∃ z, w ∈ x₀ + [-ρa, ρa]^d, 2 (blockConst d L (√d ρ) + u) < |H z - H w|) ≤ 2 exp(-u²/(2 d ρ² L))`.
(With `a = 2^{-n}` and `ρ = 3` this is DGZ's Lemma 2.3 (2) in the oscillation form of HA5.) -/
theorem box_osc_tail (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) {H : Rd d → Ω → ℝ}
    (hH : IsBandVersion P W κ a b H) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    (x₀ : Rd d) {ρ : ℝ} (hρ : 0 ≤ ρ) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ z ∈ box x₀ (ρ * a), ∃ w ∈ box x₀ (ρ * a),
        2 * (blockConst d L (√(d : ℝ) * ρ) + u) < |H z ω - H w ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * ((√(d : ℝ) * ρ) ^ 2 * L)))) := by
  refine (measure_mono fun ω hω => ?_).trans
    (block_tail hW ha hH hL0 hL x₀ (r := √(d : ℝ) * ρ) (by positivity) hu)
  obtain ⟨z, hz, w, hw, hlt⟩ := hω
  have hmem : ∀ y ∈ box x₀ (ρ * a), y ∈ closedBall x₀ (√(d : ℝ) * ρ * a) := fun y hy => by
    rw [mem_closedBall, dist_eq_norm, mul_assoc]
    exact norm_sub_le_of_mem_box (by positivity) hy
  have htri : |H z ω - H w ω| ≤ |H z ω - H x₀ ω| + |H w ω - H x₀ ω| := by
    have := abs_sub_le (H z ω) (H x₀ ω) (H w ω)
    rwa [abs_sub_comm (H x₀ ω) (H w ω)] at this
  by_cases h1 : blockConst d L (√(d : ℝ) * ρ) + u < |H z ω - H x₀ ω|
  · exact ⟨z, hmem z hz, h1⟩
  · exact ⟨w, hmem w hw, by linarith⟩

end Block

end Osc

end HigherDimLFPP
