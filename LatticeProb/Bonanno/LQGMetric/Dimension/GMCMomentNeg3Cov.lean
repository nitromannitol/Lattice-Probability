/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg3Cov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Fin

/-!
# Negative moments on a small square: covering and Jensen (P2-NEGMOM2, step 3, tools)

* `Neg3.rpow_lintegral_le_of_neg` : Jensen's inequality `(∫ g dν)^p ≤ ∫ g^p dν` for `p < 0` on a
  probability space, in `ℝ≥0∞` (from Hölder's inequality `lintegral_mul_le_Lp_mul_Lq` with the
  exponents `1 + q`, `(1 + q)/q`, `q = −p`; own elementary proof of a standard fact);
* `Neg3.sqQ z₀ m = z₀ + 2^{-m}[0,1)²` and the change of variables `Neg3.lintegral_sqQ`;
* `Neg3.lintegral_W_le_sqQ` : the reversed covering: averaging the level-`j` Riemann sums over a
  uniform offset inside the cells gives at most the integral over the square (the cells of
  `[0,1)²` are disjoint), the `≥` counterpart of `setLIntegral_sqIn_le` (GMCMomentPos2Cell.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

namespace Neg3

/-- `x ↦ x^p` is antitone on `ℝ≥0∞` for `p ≤ 0` -/
lemma ennrpow_anti {x y : ℝ≥0∞} {p : ℝ} (hp : p ≤ 0) (h : x ≤ y) : y ^ p ≤ x ^ p := by
  calc y ^ p = (y ^ (-p))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
    _ ≤ (x ^ (-p))⁻¹ := ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h (neg_nonneg.2 hp))
    _ = x ^ p := by rw [← ENNReal.rpow_neg, neg_neg]

/-- **Jensen for `x ↦ x^p`, `p < 0`**, on a probability space, in `ℝ≥0∞` -/
lemma rpow_lintegral_le_of_neg {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ} (hp : p < 0) :
    (∫⁻ a, g a ∂ν) ^ p ≤ ∫⁻ a, g a ^ p ∂ν := by
  set q := -p with hq
  have hq0 : 0 < q := by linarith
  set I := ∫⁻ a, g a ∂ν
  set J := ∫⁻ a, g a ^ p ∂ν
  by_cases hJ : J = ⊤
  · rw [hJ]; exact le_top
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.top_rpow_of_neg hp]; exact zero_le
  have h1 : ∀ᵐ a ∂ν, g a ^ p < ⊤ := ae_lt_top' (hg.pow_const p) hJ
  have h2 : ∀ᵐ a ∂ν, g a < ⊤ := ae_lt_top' hg hI
  set b := q / (1 + q)
  have hpq := Real.HolderConjugate.conjExponent (show (1 : ℝ) < 1 + q by linarith)
  have hcE : Real.conjExponent (1 + q) = (1 + q) / q := by
    rw [Real.conjExponent]; congr 1; ring
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (hg.pow_const (-b)) (hg.pow_const b)
  have hone : ∀ᵐ a ∂ν, ((fun a => g a ^ (-b)) * fun a => g a ^ b) a = 1 := by
    filter_upwards [h1, h2] with a ha1 ha2
    have h0 : g a ≠ 0 := fun h => by
      rw [h, ENNReal.zero_rpow_of_neg hp] at ha1; exact lt_irrefl _ ha1
    simp only [Pi.mul_apply]
    rw [← ENNReal.rpow_add _ _ h0 ha2.ne, neg_add_cancel, ENNReal.rpow_zero]
  rw [lintegral_congr_ae hone, lintegral_const, measure_univ, mul_one] at hH
  have e1 : ∀ a, (g a ^ (-b)) ^ (1 + q) = g a ^ p := fun a => by
    rw [← ENNReal.rpow_mul]; congr 1
    simp only [b]
    rw [neg_mul, div_mul_cancel₀ _ (by linarith : (1 : ℝ) + q ≠ 0), hq, neg_neg]
  have e2 : ∀ a, (g a ^ b) ^ Real.conjExponent (1 + q) = g a := fun a => by
    rw [← ENNReal.rpow_mul, hcE]
    have : b * ((1 + q) / q) = 1 := by simp only [b]; field_simp
    rw [this, ENNReal.rpow_one]
  simp only [e1, e2] at hH
  rw [hcE] at hH
  -- `hH : 1 ≤ J^{1/(1+q)} * I^{q/(1+q)}`
  have hH' : 1 ≤ J * I ^ q := by
    have := ENNReal.rpow_le_rpow hH (show (0 : ℝ) ≤ 1 + q by linarith)
    rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul] at this
    convert this using 2
    · rw [one_div, inv_mul_cancel₀ (by linarith), ENNReal.rpow_one]
    · congr 1; field_simp
  have hI0 : I ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_rpow_of_pos hq0, mul_zero] at hH'
    exact absurd hH' (by simp)
  calc I ^ p = I ^ p * 1 := (mul_one _).symm
    _ ≤ I ^ p * (J * I ^ q) := by gcongr
    _ = J * (I ^ p * I ^ q) := by ring
    _ = J := by rw [← ENNReal.rpow_add _ _ hI0 hI, hq, add_neg_cancel, ENNReal.rpow_zero, mul_one]

/-- the square `z₀ + 2^{-m}[0,1)²` -/
def sqQ (z₀ : ℂ) (m : ℕ) : Set ℂ := {z | (radius m)⁻¹ • (z - z₀) ∈ cell0}

lemma measurableSet_sqQ (z₀ : ℂ) (m : ℕ) : MeasurableSet (sqQ z₀ m) :=
  measurableSet_cell0.preimage (by fun_prop)

lemma mem_sqQ_iff (z₀ : ℂ) (m : ℕ) (w : ℂ) : z₀ + radius m • w ∈ sqQ z₀ m ↔ w ∈ cell0 := by
  simp only [sqQ, mem_ofPred_eq, add_sub_cancel_left, inv_smul_smul₀ (radius_pos m).ne']

lemma eq_of_mem_sqQ {z₀ : ℂ} {m : ℕ} {z : ℂ} (hz : z ∈ sqQ z₀ m) :
    ∃ w ∈ cell0, z = z₀ + radius m • w :=
  ⟨(radius m)⁻¹ • (z - z₀), hz, by rw [smul_inv_smul₀ (radius_pos m).ne', add_sub_cancel]⟩

lemma cell0_subset_unitSq : cell0 ⊆ unitSq := fun _ ⟨a, b, c, d⟩ => ⟨a, b.le, c, d.le⟩

/-- change of variables onto the square -/
lemma lintegral_sqQ (F : ℂ → ℝ≥0∞) (hF : Measurable F) (z₀ : ℂ) (m : ℕ) :
    ∫⁻ z in sqQ z₀ m, F z =
      ENNReal.ofReal (radius m ^ 2) * ∫⁻ w in cell0, F (z₀ + radius m • w) := by
  set a := radius m
  have ha : 0 < a := radius_pos m
  set G : ℂ → ℝ≥0∞ := (sqQ z₀ m).indicator F
  have hG : Measurable G := hF.indicator (measurableSet_sqQ z₀ m)
  have hφm : Measurable fun w : ℂ => z₀ + a • w := by fun_prop
  have hmap : Measure.map (fun w : ℂ => z₀ + a • w) (volume : Measure ℂ) =
      ENNReal.ofReal |(a ^ Module.finrank ℝ ℂ)⁻¹| • volume := by
    rw [show (fun w : ℂ => z₀ + a • w) = (fun z => z₀ + z) ∘ (fun w => a • w) from rfl,
      ← Measure.map_map (measurable_const_add z₀) (measurable_const_smul a),
      Measure.map_addHaar_smul volume ha.ne', Measure.map_smul,
      Measure.IsAddLeftInvariant.map_add_left_eq_self]
    exact (measurable_const_add z₀).aemeasurable
  have h1 : ∫⁻ w, G (z₀ + a • w) = ENNReal.ofReal |(a ^ Module.finrank ℝ ℂ)⁻¹| * ∫⁻ z, G z := by
    rw [← lintegral_map hG hφm, hmap, lintegral_smul_measure, smul_eq_mul]
  have h2 : (fun w => G (z₀ + a • w)) = cell0.indicator (fun w => F (z₀ + a • w)) := by
    funext w
    by_cases hw : w ∈ cell0
    · simp only [G]
      rw [indicator_of_mem hw, indicator_of_mem ((mem_sqQ_iff z₀ m w).2 hw)]
    · simp only [G]
      rw [indicator_of_notMem hw, indicator_of_notMem (fun h => hw ((mem_sqQ_iff z₀ m w).1 h))]
  rw [← lintegral_indicator (measurableSet_sqQ z₀ m), ← lintegral_indicator measurableSet_cell0,
    ← h2, h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Complex.finrank_real_complex,
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

lemma cell_subset_cell0 {j : ℕ} {i : ℕ × ℕ} (hi : i ∈ grid j) : cell j i ⊆ cell0 := by
  intro z ⟨c1, c2, c3, c4⟩
  obtain ⟨h1, h2⟩ := mem_grid.1 hi
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have e1 : (i.1 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast h1
  have e2 : (i.2 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast h2
  have p1 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ i.2 := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

lemma pairwiseDisjoint_cell (j : ℕ) : Set.PairwiseDisjoint (↑(grid j)) (cell j) := by
  intro i _ i' _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro z ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
  apply hne
  have x1 : i.1 < i'.1 + 1 := by exact_mod_cast (lt_of_le_of_lt a1 b2)
  have x2 : i'.1 < i.1 + 1 := by exact_mod_cast (lt_of_le_of_lt b1 a2)
  have y1 : i.2 < i'.2 + 1 := by exact_mod_cast (lt_of_le_of_lt a3 b4)
  have y2 : i'.2 < i.2 + 1 := by exact_mod_cast (lt_of_le_of_lt b3 a4)
  exact Prod.ext (by omega) (by omega)

/-- **the reversed covering**: the offset-averaged Riemann sums are at most the square integral -/
theorem lintegral_W_le_sqQ (F : ℂ → ℝ≥0∞) (hF : Measurable F) (z₀ : ℂ) (m j : ℕ) :
    ∫⁻ t in cell0, ∑ i ∈ grid j, ENNReal.ofReal (radius m ^ 2 * (4 : ℝ)⁻¹ ^ j) *
      F (z₀ + radius m • cellMap j i t) ≤ ∫⁻ z in sqQ z₀ m, F z := by
  set H : ℂ → ℝ≥0∞ := fun w => F (z₀ + radius m • w)
  have hH : Measurable H := hF.comp (by fun_prop)
  rw [lintegral_sqQ F hF z₀ m]
  have hm : ∀ i ∈ grid j, Measurable fun t => ENNReal.ofReal (radius m ^ 2 * (4 : ℝ)⁻¹ ^ j) *
      F (z₀ + radius m • cellMap j i t) := fun i _ =>
    (hH.comp (measurable_cellMap j i)).const_mul _
  rw [lintegral_finsetSum _ hm]
  calc ∑ i ∈ grid j, ∫⁻ t in cell0, ENNReal.ofReal (radius m ^ 2 * (4 : ℝ)⁻¹ ^ j) *
        F (z₀ + radius m • cellMap j i t)
      = ∑ i ∈ grid j, ENNReal.ofReal (radius m ^ 2) * ∫⁻ z in cell j i, H z := by
        refine sum_congr rfl fun i _ => ?_
        rw [lintegral_cell H hH j i, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← lintegral_const_mul _ (f := fun t => H (cellMap j i t)) (hH.comp (measurable_cellMap j i))]
    _ = ENNReal.ofReal (radius m ^ 2) * ∫⁻ z in ⋃ i ∈ grid j, cell j i, H z := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset (pairwiseDisjoint_cell j)
          (fun i _ => measurableSet_cell j i)]
    _ ≤ ENNReal.ofReal (radius m ^ 2) * ∫⁻ w in cell0, H w :=
        by gcongr; exact iUnion₂_subset fun i hi => cell_subset_cell0 hi

end Neg3

end DGMC

end LQGMetric
