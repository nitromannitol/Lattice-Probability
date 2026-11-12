/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

/-!
# Crossing lengths of sub-arcs (RSW, DDDF Prop 14)

Task P2-DDDFRSW. DDDF (`tightness.tex` l. 794, 800; DF arXiv:1809.02607 DF:650–670) use that if a
crossing `π` of a domain contains a sub-arc crossing a smaller domain, then the crossing length
of the smaller domain is at most the length of `π`. Here: if a piecewise-C¹ path `P` has a
sub-arc `P([s,t])` (either time direction) in `K` from `A` to `B`, then
`crossLenIn ξ f K A B ≤ lfppLen ξ f P` (sub-path and reversal from `LFPP.PathOps`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

variable {ξ : ℝ} {f : ℂ → ℝ}

theorem lfppLen_const (z : ℂ) : lfppLen ξ f (fun _ => z) = 0 := by
  simp [lfppLen]

theorem isPiecewiseC1Path_const (z : ℂ) : IsPiecewiseC1Path (fun _ => z) z z := by
  have h := isPiecewiseC1Path_segPath z z
  have e : segPath z z = fun _ => z := funext fun u => by simp [segPath]
  rwa [e] at h

/-- the length of a sub-arc in `K` from `A` to `B` bounds the crossing length of `(K, A, B)` -/
theorem crossLenIn_le_of_sub {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {K A B : Set ℂ} {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hK : ∀ u ∈ uIcc s t, P u ∈ K) (hA : P s ∈ A) (hB : P t ∈ B) :
    crossLenIn ξ f K A B ≤ lfppLen ξ f P := by
  rcases lt_trichotomy s t with h | rfl | h
  · have hsub := isPiecewiseC1Path_subPath hP hs.1 h ht.2
    calc crossLenIn ξ f K A B ≤ lfppLen ξ f (subPath P s t) :=
          crossLenIn_le_lfppLen ⟨P s, hA, P t, hB, hsub, fun u hu => hK _ (by
            rw [uIcc_of_le h.le]; constructor <;> nlinarith [hu.1, hu.2])⟩
      _ = ∫⁻ x in Icc s t, lenDens ξ f P x := lfppLen_subPath P h
      _ ≤ ∫⁻ x in Icc 0 1, lenDens ξ f P x := lintegral_mono_set (Icc_subset_Icc hs.1 ht.2)
      _ = lfppLen ξ f P := (lfppLen_eq _ _ _).symm
  · calc crossLenIn ξ f K A B ≤ lfppLen ξ f (fun _ => P s) :=
          crossLenIn_le_lfppLen ⟨P s, hA, P s, hB, isPiecewiseC1Path_const _,
            fun _ _ => hK s (by simp)⟩
      _ = 0 := lfppLen_const _
      _ ≤ _ := bot_le
  · have hsub := isPiecewiseC1Path_revPath (isPiecewiseC1Path_subPath hP ht.1 h hs.2)
    calc crossLenIn ξ f K A B ≤ lfppLen ξ f (revPath (subPath P t s)) :=
          crossLenIn_le_lfppLen ⟨P s, hA, P t, hB, hsub, fun u hu => hK _ (by
            rw [uIcc_of_ge h.le]; constructor <;> nlinarith [hu.1, hu.2])⟩
      _ = lfppLen ξ f (subPath P t s) := lfppLen_revPath _
      _ = ∫⁻ x in Icc t s, lenDens ξ f P x := lfppLen_subPath P h
      _ ≤ ∫⁻ x in Icc 0 1, lenDens ξ f P x := lintegral_mono_set (Icc_subset_Icc ht.1 hs.2)
      _ = lfppLen ξ f P := (lfppLen_eq _ _ _).symm

/-- a piecewise-C¹ path as a `Path` -/
def pathOf {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) : Path z w where
  toFun τ := P τ
  continuous_toFun := hP.continuousOn.comp_continuous continuous_subtype_val fun τ => τ.2
  source' := by simpa using hP.source
  target' := by simpa using hP.target

theorem pathOf_extend {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : (pathOf hP).extend u = P u := by
  rw [Path.extend_apply _ hu]; rfl

theorem crossLenIn_le_of_crossData {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {K A B : Set ℂ} (h : CrossData (pathOf hP).extend K A B) :
    crossLenIn ξ f K A B ≤ lfppLen ξ f P := by
  obtain ⟨s, hs, t, ht, hK, hA, hB⟩ := h
  rw [pathOf_extend hP hs] at hA
  rw [pathOf_extend hP ht] at hB
  exact crossLenIn_le_of_sub hP hs ht
    (fun u hu => pathOf_extend hP (uIcc_subset_Icc hs ht hu) ▸ hK u hu) hA hB

end DDDF
end LQGMetric
