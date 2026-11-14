/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLengthSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundSeg

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

 


theorem laneB_lfppLen_split (ξ : ℝ) (f : ℂ → ℝ) (P : ℝ → ℂ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    lfppLen ξ f (Strong.seg P 0 s) + lfppLen ξ f (Strong.seg P s 1) =
      lfppLen ξ f P := by
  by_cases hs0 : s = 0
  · subst s
    have hconst : Strong.seg P 0 0 = fun _ => P 0 := by
      funext u
      simp [Strong.seg]
    have hfull : Strong.seg P 0 1 = P := by
      funext u
      simp [Strong.seg]
    rw [hconst, hfull]
    simp [lfppLen_eq, lenDens]
  by_cases hs1 : s = 1
  · subst s
    have hconst : Strong.seg P 1 1 = fun _ => P 1 := by
      funext u
      simp [Strong.seg]
    have hfull : Strong.seg P 0 1 = P := by
      funext u
      simp [Strong.seg]
    rw [hconst, hfull]
    simp [lfppLen_eq, lenDens]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hsone : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hleft : Strong.seg P 0 s = subPath P 0 s := by
    funext u
    simp [Strong.seg, subPath, mul_comm]
  have hright : Strong.seg P s 1 = subPath P s 1 := by
    funext u
    simp [Strong.seg, subPath, mul_comm, add_comm]
  rw [hleft, hright, lfppLen_subPath P hspos, lfppLen_subPath P hsone,
    lfppLen_eq]
  have hunion : Ioc (0 : ℝ) s ∪ Ioc s 1 = Ioc 0 1 := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans hsone.le⟩
      · exact ⟨hspos.trans h.1, h.2⟩
    · intro h
      by_cases hxs : x ≤ s
      · exact Or.inl ⟨h.1, hxs⟩
      · exact Or.inr ⟨lt_of_not_ge hxs, h.2⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) s) (Ioc s 1) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  simp only [← restrict_Ioc_eq_restrict_Icc]
  rw [← lintegral_union measurableSet_Ioc hdisj, hunion]

end SupercriticalLQGUniqueness.B2.DG20Conc
