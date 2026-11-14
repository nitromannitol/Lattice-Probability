/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRectMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterWalk
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric

 

theorem laneB_rect_crossings_meet {x₀ x₁ y₀ y₁ : ℝ}
    {P Q : ℝ → ℂ}
    (hPc : ContinuousOn P (Icc (0 : ℝ) 1))
    (hQc : ContinuousOn Q (Icc (0 : ℝ) 1))
    (hPm : MapsTo P (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁))
    (hQm : MapsTo Q (Icc (0 : ℝ) 1) (RectCross.rect x₀ x₁ y₀ y₁))
    (hP : ((P 0).re = x₀ ∧ (P 1).re = x₁) ∨
      ((P 0).re = x₁ ∧ (P 1).re = x₀))
    (hQ : ((Q 0).im = y₀ ∧ (Q 1).im = y₁) ∨
      ((Q 0).im = y₁ ∧ (Q 1).im = y₀)) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P s = Q t := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hrev_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hrev (F : ℝ → ℂ) (t : ℝ) : Strong.seg F 1 0 t = F (1 - t) := by
    congr 1
    dsimp [Strong.seg]
    ring
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · obtain ⟨s, hs, t, ht, he⟩ :=
      RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ P (Strong.seg Q 1 0)
        hPc (Strong.continuousOn_seg hQc hone hzero)
        hPm (Strong.mapsTo_seg hQm hone hzero) hP.1 hP.2
        (by simpa using hQ.2) (by simpa using hQ.1)
    exact ⟨s, hs, 1 - t, hrev_mem t ht, by simpa [hrev] using he⟩
  · obtain ⟨s, hs, t, ht, he⟩ :=
      RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ P Q hPc hQc hPm hQm
        hP.1 hP.2 hQ.1 hQ.2
    exact ⟨s, hs, t, ht, he⟩
  · obtain ⟨s, hs, t, ht, he⟩ :=
      RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ (Strong.seg P 1 0) (Strong.seg Q 1 0)
        (Strong.continuousOn_seg hPc hone hzero)
        (Strong.continuousOn_seg hQc hone hzero)
        (Strong.mapsTo_seg hPm hone hzero)
        (Strong.mapsTo_seg hQm hone hzero)
        (by simpa using hP.2) (by simpa using hP.1)
        (by simpa using hQ.2) (by simpa using hQ.1)
    exact ⟨1 - s, hrev_mem s hs, 1 - t, hrev_mem t ht, by simpa [hrev] using he⟩
  · obtain ⟨s, hs, t, ht, he⟩ :=
      RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ (Strong.seg P 1 0) Q
        (Strong.continuousOn_seg hPc hone hzero) hQc
        (Strong.mapsTo_seg hPm hone hzero) hQm
        (by simpa using hP.2) (by simpa using hP.1) hQ.1 hQ.2
    exact ⟨1 - s, hrev_mem s hs, t, ht, by simpa [hrev] using he⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
