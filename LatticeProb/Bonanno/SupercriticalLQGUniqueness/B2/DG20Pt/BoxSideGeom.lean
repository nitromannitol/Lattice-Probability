/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BoxSideGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxLower
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom

 




set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem horizontal_side_geometry {a b y : ℝ} (hab : a < b) :
    IsCompact (Icc a b ×ℂ ({y} : Set ℝ)) ∧
      IsConnected (Icc a b ×ℂ ({y} : Set ℝ)) ∧
      (Icc a b ×ℂ ({y} : Set ℝ)).Nontrivial := by
  refine ⟨isCompact_Icc.reProdIm isCompact_singleton,
    LQGMetric.DZZ.isConnected_reProdIm (isConnected_Icc hab.le) isConnected_singleton, ?_⟩
  refine ⟨⟨a, y⟩, ?_, ⟨b, y⟩, ?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    exact ⟨left_mem_Icc.mpr hab.le, mem_singleton y⟩
  · rw [Complex.mem_reProdIm]
    exact ⟨right_mem_Icc.mpr hab.le, mem_singleton y⟩
  · intro h
    have heq := congrArg Complex.re h
    exact hab.ne (by simpa using heq)

 

theorem vertical_side_geometry {a b x : ℝ} (hab : a < b) :
    IsCompact (({x} : Set ℝ) ×ℂ Icc a b) ∧
      IsConnected (({x} : Set ℝ) ×ℂ Icc a b) ∧
      (({x} : Set ℝ) ×ℂ Icc a b).Nontrivial := by
  refine ⟨isCompact_singleton.reProdIm isCompact_Icc,
    LQGMetric.DZZ.isConnected_reProdIm isConnected_singleton (isConnected_Icc hab.le), ?_⟩
  refine ⟨⟨x, a⟩, ?_, ⟨x, b⟩, ?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    exact ⟨mem_singleton x, left_mem_Icc.mpr hab.le⟩
  · rw [Complex.mem_reProdIm]
    exact ⟨mem_singleton x, right_mem_Icc.mpr hab.le⟩
  · intro h
    have heq := congrArg Complex.im h
    exact hab.ne (by simpa using heq)

 

theorem open_box_geometry {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsOpen (Ioo a b ×ℂ Ioo c d) ∧
      Bornology.IsBounded (Ioo a b ×ℂ Ioo c d) ∧
      IsConnected (Ioo a b ×ℂ Ioo c d) := by
  exact ⟨isOpen_Ioo.reProdIm isOpen_Ioo,
    (Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo c d),
    LQGMetric.DZZ.isConnected_reProdIm (isConnected_Ioo hab) (isConnected_Ioo hcd)⟩

 
theorem horizontal_sides_disjoint (a b y₁ y₂ : ℝ) (hy : y₁ ≠ y₂) :
    Disjoint (Icc a b ×ℂ ({y₁} : Set ℝ))
      (Icc a b ×ℂ ({y₂} : Set ℝ)) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  rw [Complex.mem_reProdIm] at hz₁ hz₂
  exact hy (hz₁.2.symm.trans hz₂.2)

 
theorem vertical_sides_disjoint (a b x₁ x₂ : ℝ) (hx : x₁ ≠ x₂) :
    Disjoint (({x₁} : Set ℝ) ×ℂ Icc a b)
      (({x₂} : Set ℝ) ×ℂ Icc a b) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  rw [Complex.mem_reProdIm] at hz₁ hz₂
  exact hx (hz₁.1.symm.trans hz₂.1)

end SupercriticalLQGUniqueness.B2.DG20Pt
