/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.GridTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.Basic




 





set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped Convex

 
def rectGridPoint (z₀ : ℂ) (h : ℝ) (a : ℤ × ℤ) : ℂ :=
  z₀ + Exponent.LatticePath.gridPoint h a

 
theorem rectGridPoint_adjK_dist_le (z₀ : ℂ) (h : ℝ) (hh : 0 ≤ h)
    {a b : ℤ × ℤ} (hab : LQGMetric.PercAdjK a b) :
    dist (rectGridPoint z₀ h a) (rectGridPoint z₀ h b) ≤ 2 * h := by
  simpa only [rectGridPoint, dist_add_left] using Exponent.LatticePath.gridPoint_adjK_dist_le h hh hab

 
theorem grid_coord_bounds (N : ℤ) (h : ℝ) (hh : 0 ≤ h)
    (hN : h * (N : ℝ) = 1) {k : ℤ} (hk0 : 0 ≤ k) (hkN : k ≤ N) :
    0 ≤ h * (k : ℝ) ∧ h * (k : ℝ) ≤ 1 := by
  have hk0r : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hkNr : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  constructor
  · positivity
  · calc
      h * (k : ℝ) ≤ h * (N : ℝ) := mul_le_mul_of_nonneg_left hkNr hh
      _ = 1 := hN

 
theorem rectGridPoint_mem_unitRect (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a) :
    rectGridPoint ⟨x₀, y₀⟩ h a ∈
      Set.Icc x₀ (x₀ + 1) ×ℂ Set.Icc y₀ (y₀ + 1) := by
  obtain ⟨ha₁₀, ha₁N, ha₂₀, ha₂N⟩ :
      0 ≤ a.1 ∧ a.1 ≤ N ∧ 0 ≤ a.2 ∧ a.2 ≤ N := by
    dsimp [LQGMetric.percInGrid] at ha
    omega
  have h₁ := grid_coord_bounds N h hh hN ha₁₀ ha₁N
  have h₂ := grid_coord_bounds N h hh hN ha₂₀ ha₂N
  simp only [rectGridPoint, Exponent.LatticePath.gridPoint, Complex.mem_reProdIm, Complex.add_re,
    Complex.add_im, mem_Icc]
  constructor <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

 
theorem rectGridPoint_left_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = 0) :
    rectGridPoint ⟨x₀, y₀⟩ h a ∈ {x₀} ×ℂ Set.Icc y₀ (y₀ + 1) := by
  have hmem := rectGridPoint_mem_unitRect x₀ y₀ h N hh hN ha
  change (rectGridPoint ⟨x₀, y₀⟩ h a).re = x₀ ∧
    (rectGridPoint ⟨x₀, y₀⟩ h a).im ∈ Set.Icc y₀ (y₀ + 1)
  exact ⟨by simp [rectGridPoint, Exponent.LatticePath.gridPoint, ha₁], hmem.2⟩

 
theorem rectGridPoint_right_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = N) :
    rectGridPoint ⟨x₀, y₀⟩ h a ∈ {x₀ + 1} ×ℂ Set.Icc y₀ (y₀ + 1) := by
  have hmem := rectGridPoint_mem_unitRect x₀ y₀ h N hh hN ha
  change (rectGridPoint ⟨x₀, y₀⟩ h a).re = x₀ + 1 ∧
    (rectGridPoint ⟨x₀, y₀⟩ h a).im ∈ Set.Icc y₀ (y₀ + 1)
  refine ⟨?_, hmem.2⟩
  simp only [rectGridPoint, Exponent.LatticePath.gridPoint, Complex.add_re, ha₁]
  linarith

 
theorem rectGridPoint_bottom_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = 0) :
    rectGridPoint ⟨x₀, y₀⟩ h a ∈ Set.Icc x₀ (x₀ + 1) ×ℂ {y₀} := by
  have hmem := rectGridPoint_mem_unitRect x₀ y₀ h N hh hN ha
  change (rectGridPoint ⟨x₀, y₀⟩ h a).re ∈ Set.Icc x₀ (x₀ + 1) ∧
    (rectGridPoint ⟨x₀, y₀⟩ h a).im = y₀
  exact ⟨hmem.1, by simp [rectGridPoint, Exponent.LatticePath.gridPoint, ha₂]⟩

 
theorem rectGridPoint_top_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = N) :
    rectGridPoint ⟨x₀, y₀⟩ h a ∈ Set.Icc x₀ (x₀ + 1) ×ℂ {y₀ + 1} := by
  have hmem := rectGridPoint_mem_unitRect x₀ y₀ h N hh hN ha
  change (rectGridPoint ⟨x₀, y₀⟩ h a).re ∈ Set.Icc x₀ (x₀ + 1) ∧
    (rectGridPoint ⟨x₀, y₀⟩ h a).im = y₀ + 1
  refine ⟨hmem.1, ?_⟩
  simp only [rectGridPoint, Exponent.LatticePath.gridPoint, Complex.add_im, ha₂]
  linarith

 
def swapGridPoint (z₀ : ℂ) (h : ℝ) (a : ℤ × ℤ) : ℂ :=
  rectGridPoint z₀ h (a.2, a.1)

theorem swapGridPoint_mem_unitRect (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a) :
    swapGridPoint ⟨x₀, y₀⟩ h a ∈
      Set.Icc x₀ (x₀ + 1) ×ℂ Set.Icc y₀ (y₀ + 1) := by
  apply rectGridPoint_mem_unitRect x₀ y₀ h N hh hN
  exact ⟨ha.2.2.1, ha.2.2.2, ha.1, ha.2.1⟩

theorem swapGridPoint_adjK_dist_le (z₀ : ℂ) (h : ℝ) (hh : 0 ≤ h)
    {a b : ℤ × ℤ} (hab : LQGMetric.PercAdjK a b) :
    dist (swapGridPoint z₀ h a) (swapGridPoint z₀ h b) ≤ 2 * h := by
  have hswap : LQGMetric.PercAdjK (a.2, a.1) (b.2, b.1) := by
    dsimp [LQGMetric.PercAdjK] at hab ⊢
    omega
  exact rectGridPoint_adjK_dist_le z₀ h hh hswap

theorem swapGridPoint_left_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = 0) :
    swapGridPoint ⟨x₀, y₀⟩ h a ∈ Set.Icc x₀ (x₀ + 1) ×ℂ {y₀} := by
  exact rectGridPoint_bottom_side x₀ y₀ h N hh hN
    ⟨ha.2.2.1, ha.2.2.2, ha.1, ha.2.1⟩ ha₁

theorem swapGridPoint_right_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = N) :
    swapGridPoint ⟨x₀, y₀⟩ h a ∈ Set.Icc x₀ (x₀ + 1) ×ℂ {y₀ + 1} := by
  exact rectGridPoint_top_side x₀ y₀ h N hh hN
    ⟨ha.2.2.1, ha.2.2.2, ha.1, ha.2.1⟩ ha₁

theorem swapGridPoint_bottom_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = 0) :
    swapGridPoint ⟨x₀, y₀⟩ h a ∈ {x₀} ×ℂ Set.Icc y₀ (y₀ + 1) := by
  exact rectGridPoint_left_side x₀ y₀ h N hh hN
    ⟨ha.2.2.1, ha.2.2.2, ha.1, ha.2.1⟩ ha₂

theorem swapGridPoint_top_side (x₀ y₀ h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = N) :
    swapGridPoint ⟨x₀, y₀⟩ h a ∈ {x₀ + 1} ×ℂ Set.Icc y₀ (y₀ + 1) := by
  exact rectGridPoint_right_side x₀ y₀ h N hh hN
    ⟨ha.2.2.1, ha.2.2.2, ha.1, ha.2.1⟩ ha₂

end SupercriticalLQGUniqueness.Exponent.PaidDuality

