/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossPercConcrete at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossPercAdapter

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem square_cross_upper_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | T * lambdaN ξ W P n <
            lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  let U : Opens ℂ :=
    ⟨Ioo (-1 : ℝ) 2 ×ℂ Ioo (0 : ℝ) 1,
      (open_box_geometry (by norm_num : (-1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 1)).1⟩
  let A : Set ℂ := ({(-1 / 2 : ℝ)} : Set ℝ) ×ℂ Icc (1 / 4 : ℝ) (3 / 4)
  let B : Set ℂ := ({(3 / 2 : ℝ)} : Set ℝ) ×ℂ Icc (1 / 4 : ℝ) (3 / 4)
  have hA := vertical_side_geometry (x := (-1 / 2 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 3 / 4)
  have hB := vertical_side_geometry (x := (3 / 2 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 3 / 4)
  have hAU : A ⊆ U := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (0 : ℝ) 1
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [mem_singleton_iff] at hz
    constructor
    · rw [hz.1]; norm_num
    · rcases hz.2 with ⟨h1, h2⟩
      constructor <;> linarith
  have hBU : B ⊆ U := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (0 : ℝ) 1
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [mem_singleton_iff] at hz
    constructor
    · rw [hz.1]; norm_num
    · rcases hz.2 with ⟨h1, h2⟩
      constructor <;> linarith
  have hStrip : ∀ z ∈ U, z.im ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (0 : ℝ) 1 at hz
    rw [Complex.mem_reProdIm] at hz
    exact ⟨hz.2.1.le, hz.2.2.le⟩
  have hLeft : ∀ z ∈ A, z.re ≤ 0 := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [mem_singleton_iff] at hz
    rw [hz.1]; norm_num
  have hRight : ∀ z ∈ B, 1 ≤ z.re := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [mem_singleton_iff] at hz
    rw [hz.1]; norm_num
  exact square_cross_upper_tail_of_perc hPerc ξ U A B
    hA.1 hB.1 hA.2.1 hB.2.1 hA.2.2 hB.2.2
    hAU hBU (vertical_sides_disjoint _ _ _ _ (by norm_num))
    (open_box_geometry (by norm_num : (-1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1)).2.2
    hStrip hLeft hRight

 

theorem square_cross_lower_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
            T⁻¹ * lambdaN ξ W P n} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let U : Opens ℂ :=
    ⟨Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2,
      (open_box_geometry (by norm_num : (-1 : ℝ) < 2)
        (by norm_num : (-1 : ℝ) < 2)).1⟩
  let A : Set ℂ := ({(0 : ℝ)} : Set ℝ) ×ℂ Icc (0 : ℝ) 1
  let B : Set ℂ := ({(1 : ℝ)} : Set ℝ) ×ℂ Icc (0 : ℝ) 1
  have hA := vertical_side_geometry (x := (0 : ℝ))
    (by norm_num : (0 : ℝ) < 1)
  have hB := vertical_side_geometry (x := (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1)
  have hAU : A ⊆ U := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [mem_singleton_iff] at hz
    constructor
    · rw [hz.1]; norm_num
    · rcases hz.2 with ⟨h1, h2⟩
      constructor <;> linarith
  have hBU : B ⊆ U := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [mem_singleton_iff] at hz
    constructor
    · rw [hz.1]; norm_num
    · rcases hz.2 with ⟨h1, h2⟩
      constructor <;> linarith
  have hSq : (rectAB 1 1).toSet ⊆ U := by
    intro z hz
    change z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2
    rw [mem_rectAB_toSet] at hz
    rw [Complex.mem_reProdIm]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hLeft : (rectAB 1 1).side₁ ⊆ A := by
    intro z hz
    rw [mem_rectAB_side₁] at hz
    exact Complex.mem_reProdIm.mpr ⟨hz.1, hz.2⟩
  have hRight : (rectAB 1 1).side₂ ⊆ B := by
    intro z hz
    rw [mem_rectAB_side₂] at hz
    exact Complex.mem_reProdIm.mpr ⟨hz.1, hz.2⟩
  exact square_cross_lower_tail_of_perc hPerc ξ U A B
    hA.1 hB.1 hA.2.1 hB.2.1 hA.2.2 hB.2.2
    hAU hBU (vertical_sides_disjoint _ _ _ _ (by norm_num))
    (open_box_geometry (by norm_num : (-1 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 2)).2.2
    hSq hLeft hRight

end SupercriticalLQGUniqueness.B2.DG20Pt
