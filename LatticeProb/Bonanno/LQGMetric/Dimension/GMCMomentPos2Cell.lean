/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Cell at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2GFF
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqTRL

/-!
# Inner squares are covered by shifted dyadic Riemann sums (P2-KAHANE3)

`DGMC.setLIntegral_sqIn_le`: for measurable `F ≥ 0`, `0 < s'` and `2^{-j} ≤ s − s'`,
`∫_{sqIn s} F ≤ ∫_{t ∈ [0,1)²} ∑_{i ∈ oS j s'} 4^{-j} F(2^{-j}(i + t)) dt`.

This is the exact averaging identity behind the comparison of `areaApprox` with the discrete sums
`oM`: averaging the Riemann sum over a uniformly random offset of the evaluation points inside
the cells gives the integral over the union of the cells (change of variables in each cell, mathlib
`Measure.map_addHaar_smul`). Own elementary device replacing an `L¹` Riemann-sum approximation;
it lets the discrete moment bound pass to `areaApprox` by Jensen in the offset `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

/-- the unit cell `[0,1)²` -/
def cell0 : Set ℂ := {t | 0 ≤ t.re ∧ t.re < 1 ∧ 0 ≤ t.im ∧ t.im < 1}

/-- the affine map from `[0,1)²` onto the level-`j` cell `i` -/
def cellMap (j : ℕ) (i : ℕ × ℕ) (t : ℂ) : ℂ := ((2 : ℝ)⁻¹ ^ j : ℝ) • ((⟨i.1, i.2⟩ : ℂ) + t)

/-- the level-`j` cell `i` -/
def cell (j : ℕ) (i : ℕ × ℕ) : Set ℂ :=
  {z | (i.1 : ℝ) ≤ 2 ^ j * z.re ∧ 2 ^ j * z.re < i.1 + 1 ∧ (i.2 : ℝ) ≤ 2 ^ j * z.im ∧
    2 ^ j * z.im < i.2 + 1}

lemma measurableSet_cell0 : MeasurableSet cell0 := by
  unfold cell0
  refine (measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_lt Complex.measurable_re measurable_const).inter
      ((measurableSet_le measurable_const Complex.measurable_im).inter
        (measurableSet_lt Complex.measurable_im measurable_const)))

lemma measurableSet_cell (j : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell j i) := by
  unfold cell
  refine (measurableSet_le measurable_const (Complex.measurable_re.const_mul _)).inter
    ((measurableSet_lt (Complex.measurable_re.const_mul _) measurable_const).inter
      ((measurableSet_le measurable_const (Complex.measurable_im.const_mul _)).inter
        (measurableSet_lt (Complex.measurable_im.const_mul _) measurable_const)))

lemma cellMap_re (j : ℕ) (i : ℕ × ℕ) (t : ℂ) :
    2 ^ j * (cellMap j i t).re = i.1 + t.re := by
  simp only [cellMap, Complex.smul_re, Complex.add_re, smul_eq_mul]
  rw [← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]

lemma cellMap_im (j : ℕ) (i : ℕ × ℕ) (t : ℂ) :
    2 ^ j * (cellMap j i t).im = i.2 + t.im := by
  simp only [cellMap, Complex.smul_im, Complex.add_im, smul_eq_mul]
  rw [← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]

lemma cellMap_mem_cell_iff (j : ℕ) (i : ℕ × ℕ) (t : ℂ) : cellMap j i t ∈ cell j i ↔ t ∈ cell0 := by
  simp only [cell, cell0, mem_setOf_eq, cellMap_re, cellMap_im]
  constructor <;> rintro ⟨a, b, c, d⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma measurable_cellMap (j : ℕ) (i : ℕ × ℕ) : Measurable (cellMap j i) := by
  unfold cellMap; fun_prop

/-- change of variables on one cell -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (hF : Measurable F) (j : ℕ) (i : ℕ × ℕ) :
    ∫⁻ z in cell j i, F z = ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) * ∫⁻ t in cell0, F (cellMap j i t) := by
  set l : ℝ := (2 : ℝ)⁻¹ ^ j
  have hl : 0 < l := by positivity
  set a : ℂ := l • (⟨i.1, i.2⟩ : ℂ)
  have hφ : cellMap j i = (fun z => a + z) ∘ (fun t => l • t) := by
    funext t; simp only [cellMap, Function.comp, a, smul_add]; rfl
  set G : ℂ → ℝ≥0∞ := (cell j i).indicator F
  have hG : Measurable G := hF.indicator (measurableSet_cell j i)
  have hmap : Measure.map (cellMap j i) (volume : Measure ℂ) =
      ENNReal.ofReal |(l ^ Module.finrank ℝ ℂ)⁻¹| • volume := by
    rw [hφ, ← Measure.map_map (measurable_const_add a) (measurable_const_smul l),
      Measure.map_addHaar_smul volume hl.ne', Measure.map_smul,
      Measure.IsAddLeftInvariant.map_add_left_eq_self]
    exact (measurable_const_add a).aemeasurable
  have h1 : ∫⁻ t, G (cellMap j i t) = ENNReal.ofReal |(l ^ Module.finrank ℝ ℂ)⁻¹| * ∫⁻ z, G z := by
    rw [← lintegral_map hG (measurable_cellMap j i), hmap, lintegral_smul_measure, smul_eq_mul]
  have h2 : (fun t => G (cellMap j i t)) = cell0.indicator (fun t => F (cellMap j i t)) := by
    funext t
    by_cases ht : t ∈ cell0
    · simp only [G]
      rw [indicator_of_mem ht, indicator_of_mem ((cellMap_mem_cell_iff j i t).2 ht)]
    · simp only [G]
      rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht ((cellMap_mem_cell_iff j i t).1 h))]
  rw [← lintegral_indicator (measurableSet_cell j i), ← lintegral_indicator measurableSet_cell0,
    ← h2, h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h4 : (4 : ℝ)⁻¹ ^ j * |(l ^ 2)⁻¹| = 1 := by
    rw [abs_of_pos (by positivity)]
    simp only [l]
    have e : ((2 : ℝ)⁻¹ ^ j) ^ 2 = (4 : ℝ)⁻¹ ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e, mul_comm]
    exact inv_mul_cancel₀ (by positivity)
  rw [Complex.finrank_real_complex, h4, ENNReal.ofReal_one, one_mul]

/-- the index of the level-`j` cell containing `z` -/
def cellIdx (j : ℕ) (z : ℂ) : ℕ × ℕ := (⌊2 ^ j * z.re⌋₊, ⌊2 ^ j * z.im⌋₊)

lemma mem_cell_cellIdx (j : ℕ) {z : ℂ} (h1 : 0 ≤ z.re) (h2 : 0 ≤ z.im) :
    z ∈ cell j (cellIdx j z) := by
  have a1 : 0 ≤ 2 ^ j * z.re := by positivity
  have a2 : 0 ≤ 2 ^ j * z.im := by positivity
  exact ⟨Nat.floor_le a1, Nat.lt_floor_add_one _, Nat.floor_le a2, Nat.lt_floor_add_one _⟩

end DGMC

end LQGMetric
