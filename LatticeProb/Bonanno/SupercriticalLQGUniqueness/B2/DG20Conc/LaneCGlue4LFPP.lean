/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCGlue4LFPP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeConnector
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

def laneCConcat4 (g₀ g₁ g₂ g₃ : ℝ → ℂ) : ℝ → ℂ :=
  concatPath (concatPath g₀ g₁) (concatPath g₂ g₃)

 
theorem laneC_concat4_piecewise {g₀ g₁ g₂ g₃ : ℝ → ℂ} {z₀ z₁ z₂ z₃ z₄ : ℂ}
    (h₀ : IsPiecewiseC1Path g₀ z₀ z₁)
    (h₁ : IsPiecewiseC1Path g₁ z₁ z₂)
    (h₂ : IsPiecewiseC1Path g₂ z₂ z₃)
    (h₃ : IsPiecewiseC1Path g₃ z₃ z₄) :
    IsPiecewiseC1Path (laneCConcat4 g₀ g₁ g₂ g₃) z₀ z₄ := by
  exact isPiecewiseC1Path_concatPath
    (isPiecewiseC1Path_concatPath h₀ h₁)
    (isPiecewiseC1Path_concatPath h₂ h₃)

 
theorem laneC_concat4_length {ξ : ℝ} {f : ℂ → ℝ} {g₀ g₁ g₂ g₃ : ℝ → ℂ}
    (h₀₁ : g₀ 1 = g₁ 0) (h₁₂ : g₁ 1 = g₂ 0) (h₂₃ : g₂ 1 = g₃ 0) :
    lfppLen ξ f (laneCConcat4 g₀ g₁ g₂ g₃) =
      lfppLen ξ f g₀ + lfppLen ξ f g₁ + lfppLen ξ f g₂ + lfppLen ξ f g₃ := by
  unfold laneCConcat4
  rw [lfppLen_concatPath (by norm_num [concatPath, h₁₂]),
    lfppLen_concatPath h₀₁, lfppLen_concatPath h₂₃]
  simp only [add_assoc]

 

theorem laneC_concat4_eq_strong_glue4 (g₀ g₁ g₂ g₃ : ℝ → ℂ) :
    EqOn (laneCConcat4 g₀ g₁ g₂ g₃)
      (fun t => Strong.glue4 g₀ g₁ g₂ g₃ (4 * t)) (Icc 0 1) := by
  intro t ht
  simp only [laneCConcat4, concatPath, Strong.glue4]
  split_ifs <;> try (congr 1 <;> ring) <;> linarith

 

theorem laneC_strong_seg_len_le {ξ : ℝ} {f : ℂ → ℝ} (g : ℝ → ℂ)
    {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) :
    lfppLen ξ f (Strong.seg g s s') ≤ lfppLen ξ f g := by
  rcases lt_trichotomy s s' with h | h | h
  · have heq : Strong.seg g s s' = subPath g s s' := by
      funext t
      simp [Strong.seg, subPath]
      ring
    rw [heq]
    exact laneC_subpath_len_le hs.1 h hs'.2
  · subst s'
    have heq : Strong.seg g s s = fun _ => g s := by
      funext t
      simp [Strong.seg]
    rw [heq, LQGMetric.DDDF.lfppLen_const]
    exact bot_le
  · have heq : Strong.seg g s s' = revPath (subPath g s' s) := by
      funext t
      simp [Strong.seg, revPath, subPath]
      ring
    rw [heq, lfppLen_revPath]
    exact laneC_subpath_len_le hs'.1 h hs.2

 
theorem laneC_strong_seg_piecewise {g : ℝ → ℂ} {z w : ℂ}
    (hg : IsPiecewiseC1Path g z w)
    {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) :
    IsPiecewiseC1Path (Strong.seg g s s') (g s) (g s') := by
  rcases lt_trichotomy s s' with h | h | h
  · have heq : Strong.seg g s s' = subPath g s s' := by
      funext t
      simp [Strong.seg, subPath]
      ring
    rw [heq]
    exact isPiecewiseC1Path_subPath hg hs.1 h hs'.2
  · subst s'
    have heq : Strong.seg g s s = fun _ => g s := by
      funext t
      simp [Strong.seg]
    rw [heq]
    exact LQGMetric.DDDF.isPiecewiseC1Path_const _
  · have heq : Strong.seg g s s' = revPath (subPath g s' s) := by
      funext t
      simp [Strong.seg, revPath, subPath]
      ring
    rw [heq]
    exact isPiecewiseC1Path_revPath
      (isPiecewiseC1Path_subPath hg hs'.1 h hs.2)

 

theorem laneC_concat4_mapsTo {g₀ g₁ g₂ g₃ : ℝ → ℂ} {S : Set ℂ}
    (h₀ : MapsTo g₀ (Icc (0 : ℝ) 1) S)
    (h₁ : MapsTo g₁ (Icc (0 : ℝ) 1) S)
    (h₂ : MapsTo g₂ (Icc (0 : ℝ) 1) S)
    (h₃ : MapsTo g₃ (Icc (0 : ℝ) 1) S) :
    MapsTo (laneCConcat4 g₀ g₁ g₂ g₃) (Icc 0 1) S := by
  intro t ht
  rw [laneC_concat4_eq_strong_glue4 g₀ g₁ g₂ g₃ ht]
  exact Strong.mapsTo_glue4 g₀ g₁ g₂ g₃ h₀ h₁ h₂ h₃
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

 
end SupercriticalLQGUniqueness.B2.DG20Conc
