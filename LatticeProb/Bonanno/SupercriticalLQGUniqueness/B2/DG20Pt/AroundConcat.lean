/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundConcat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundSeg
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat

 




set_option autoImplicit false
noncomputable section

open Set LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem concatPath_image_Icc (P R : ℝ → ℂ) (hPR : P 1 = R 0) :
    concatPath P R '' Icc (0 : ℝ) 1 =
      P '' Icc (0 : ℝ) 1 ∪ R '' Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases h : u ≤ 1 / 2
    · left
      refine ⟨2 * u, ⟨by linarith [hu.1], by linarith⟩, ?_⟩
      rw [concatPath, if_pos h]
      simp
    · right
      refine ⟨2 * u - 1, ⟨by linarith, by linarith [hu.2]⟩, ?_⟩
      rw [concatPath, if_neg h]
      congr 1
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      have hleft : u / 2 ≤ (1 / 2 : ℝ) := by linarith [hu.2]
      rw [concatPath, if_pos hleft]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      by_cases hu0 : u = 0
      · subst u
        rw [concatPath, if_pos (by norm_num : (0 + 1 : ℝ) / 2 ≤ 1 / 2)]
        norm_num [hPR]
      · have hu0' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hright : ¬ (u + 1) / 2 ≤ (1 / 2 : ℝ) := by linarith
        rw [concatPath, if_neg hright]
        congr 1
        ring

 

theorem glue4_image_subset (P₀ P₁ P₂ P₃ : ℝ → ℂ) :
    Strong.glue4 P₀ P₁ P₂ P₃ '' Icc (0 : ℝ) 4 ⊆
      P₀ '' Icc (0 : ℝ) 1 ∪ P₁ '' Icc (0 : ℝ) 1 ∪
        P₂ '' Icc (0 : ℝ) 1 ∪ P₃ '' Icc (0 : ℝ) 1 := by
  rintro z ⟨u, hu, rfl⟩
  by_cases h₁ : u ≤ 1
  · exact Or.inl (Or.inl (Or.inl ⟨u, ⟨hu.1, h₁⟩,
      by simp [Strong.glue4, h₁]⟩))
  by_cases h₂ : u ≤ 2
  · exact Or.inl (Or.inl (Or.inr ⟨u - 1, ⟨by linarith, by linarith⟩,
      by simp [Strong.glue4, h₁, h₂]⟩))
  by_cases h₃ : u ≤ 3
  · exact Or.inl (Or.inr ⟨u - 2, ⟨by linarith, by linarith⟩,
      by simp [Strong.glue4, h₁, h₂, h₃]⟩)
  · exact Or.inr ⟨u - 3, ⟨by linarith, by linarith [hu.2]⟩,
      by simp [Strong.glue4, h₁, h₂, h₃]⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
