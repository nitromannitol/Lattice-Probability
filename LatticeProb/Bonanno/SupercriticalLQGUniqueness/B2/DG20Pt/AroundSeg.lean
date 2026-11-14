/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundSeg at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.AroundFinite
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath

 




set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem isPiecewiseC1Path_aroundSeg {γ : ℝ → ℂ} {a b : ℂ}
    (hγ : IsPiecewiseC1Path γ a b) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsPiecewiseC1Path (Strong.seg γ s t) (γ s) (γ t) := by
  rcases lt_trichotomy s t with hst | hst | hst
  · have hsub := isPiecewiseC1Path_subPath hγ hs.1 hst ht.2
    have heq : Strong.seg γ s t = subPath γ s t := by
      funext u
      simp only [Strong.seg, subPath]
      congr 1
      ring
    rwa [heq]
  · subst t
    have heq : Strong.seg γ s s = fun _ => γ s := by
      funext u
      simp [Strong.seg]
    rw [heq]
    exact LQGMetric.DDDF.isPiecewiseC1Path_const _
  · have hsub := isPiecewiseC1Path_subPath hγ ht.1 hst hs.2
    have hrev := isPiecewiseC1Path_revPath hsub
    have heq : Strong.seg γ s t = revPath (subPath γ t s) := by
      funext u
      simp only [Strong.seg, revPath, subPath]
      congr 1
      ring
    rwa [heq]

 


theorem lfppLen_aroundSeg_le (ξ : ℝ) (φ : ℂ → ℝ) (γ : ℝ → ℂ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    lfppLen ξ φ (Strong.seg γ s t) ≤ lfppLen ξ φ γ := by
  by_cases hst : s = t
  · subst t
    have heq : Strong.seg γ s s = fun _ => γ s := by
      funext u
      simp [Strong.seg]
    rw [heq, lfppLen_eq]
    simp [lenDens]
  · have heq : Strong.seg γ s t = fun u => γ ((t - s) * u + s) := by
      funext u
      simp only [Strong.seg]
      congr 1
      ring
    rw [heq, lfppLen_comp_affine ξ φ γ (sub_ne_zero.mpr (Ne.symm hst)) s,
      lfppLen_eq]
    apply lintegral_mono_set
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    convert Strong.seg_param_mem hs ht hv using 1
    ring

end SupercriticalLQGUniqueness.B2.DG20Pt
