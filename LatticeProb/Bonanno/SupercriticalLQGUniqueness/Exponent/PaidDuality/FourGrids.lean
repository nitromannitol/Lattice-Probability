/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.FourGrids at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.GridTransfer




 





set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped Convex

 
def centralRect : Fin 4 → LQGMetric.DDDF.MarkedRect
  | 0 => ⟨0, 1, 1, 1, true⟩
  | 1 => ⟨0, -1, 1, 1, true⟩
  | 2 => ⟨-1, 0, 1, 1, false⟩
  | 3 => ⟨1, 0, 1, 1, false⟩

 
def centralGrid (k : Fin 4) (h : ℝ) (a : ℤ × ℤ) : ℂ :=
  match k with
  | 0 => rectGridPoint ⟨0, 1⟩ h a
  | 1 => rectGridPoint ⟨0, -1⟩ h a
  | 2 => swapGridPoint ⟨-1, 0⟩ h a
  | 3 => swapGridPoint ⟨1, 0⟩ h a

 
theorem centralGrid_mem_rect (k : Fin 4) (h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a) :
    centralGrid k h a ∈ (centralRect k).toSet := by
  fin_cases k
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.toSet] using
      rectGridPoint_mem_unitRect 0 1 h N hh hN ha
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.toSet] using
      rectGridPoint_mem_unitRect 0 (-1) h N hh hN ha
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.toSet] using
      swapGridPoint_mem_unitRect (-1) 0 h N hh hN ha
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.toSet] using
      swapGridPoint_mem_unitRect 1 0 h N hh hN ha

 
theorem centralGrid_side₁ (k : Fin 4) (h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = 0) :
    centralGrid k h a ∈ (centralRect k).side₁ := by
  fin_cases k
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₁] using
      rectGridPoint_left_side 0 1 h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₁] using
      rectGridPoint_left_side 0 (-1) h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₁] using
      swapGridPoint_left_side (-1) 0 h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₁] using
      swapGridPoint_left_side 1 0 h N hh hN ha ha₁

 
theorem centralGrid_side₂ (k : Fin 4) (h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₁ : a.1 = N) :
    centralGrid k h a ∈ (centralRect k).side₂ := by
  fin_cases k
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₂] using
      rectGridPoint_right_side 0 1 h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₂] using
      rectGridPoint_right_side 0 (-1) h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₂] using
      swapGridPoint_right_side (-1) 0 h N hh hN ha ha₁
  · simpa [centralGrid, centralRect, LQGMetric.DDDF.MarkedRect.side₂] using
      swapGridPoint_right_side 1 0 h N hh hN ha ha₁

 
def centralRadialTop : Fin 4 → Set ℂ
  | 0 => Set.Icc 0 1 ×ℂ {(2 : ℝ)}
  | 1 => Set.Icc 0 1 ×ℂ {(0 : ℝ)}
  | 2 => {(0 : ℝ)} ×ℂ Set.Icc 0 1
  | 3 => {(2 : ℝ)} ×ℂ Set.Icc 0 1

 
def centralRadialBottom : Fin 4 → Set ℂ
  | 0 => Set.Icc 0 1 ×ℂ {(1 : ℝ)}
  | 1 => Set.Icc 0 1 ×ℂ {(-1 : ℝ)}
  | 2 => {(-1 : ℝ)} ×ℂ Set.Icc 0 1
  | 3 => {(1 : ℝ)} ×ℂ Set.Icc 0 1

theorem centralGrid_top_side (k : Fin 4) (h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = N) :
    centralGrid k h a ∈ centralRadialTop k := by
  fin_cases k
  · simpa [centralGrid, centralRadialTop, show (1 : ℝ) + 1 = 2 by norm_num] using
      rectGridPoint_top_side 0 1 h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialTop, show (1 : ℝ) + 1 = 2 by norm_num] using
      rectGridPoint_top_side 0 (-1) h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialTop] using
      swapGridPoint_top_side (-1) 0 h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialTop, show (1 : ℝ) + 1 = 2 by norm_num] using
      swapGridPoint_top_side 1 0 h N hh hN ha ha₂

theorem centralGrid_bottom_side (k : Fin 4) (h : ℝ) (N : ℤ)
    (hh : 0 ≤ h) (hN : h * (N : ℝ) = 1)
    {a : ℤ × ℤ} (ha : LQGMetric.percInGrid (N + 1) (N + 1) a)
    (ha₂ : a.2 = 0) :
    centralGrid k h a ∈ centralRadialBottom k := by
  fin_cases k
  · simpa [centralGrid, centralRadialBottom] using
      rectGridPoint_bottom_side 0 1 h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialBottom] using
      rectGridPoint_bottom_side 0 (-1) h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialBottom] using
      swapGridPoint_bottom_side (-1) 0 h N hh hN ha ha₂
  · simpa [centralGrid, centralRadialBottom] using
      swapGridPoint_bottom_side 1 0 h N hh hN ha ha₂

theorem centralGrid_adjK_dist_le (k : Fin 4) (h : ℝ) (hh : 0 ≤ h)
    {a b : ℤ × ℤ} (hab : LQGMetric.PercAdjK a b) :
    dist (centralGrid k h a) (centralGrid k h b) ≤ 2 * h := by
  fin_cases k
  · exact rectGridPoint_adjK_dist_le ⟨0, 1⟩ h hh hab
  · exact rectGridPoint_adjK_dist_le ⟨0, -1⟩ h hh hab
  · exact swapGridPoint_adjK_dist_le ⟨-1, 0⟩ h hh hab
  · exact swapGridPoint_adjK_dist_le ⟨1, 0⟩ h hh hab

end SupercriticalLQGUniqueness.Exponent.PaidDuality

