/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath

/-!
# Disjoint sub-crossings (for DDDF Prop 18, Step 3) (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 915–918, Prop 18 Step 3) bound the length of a
left–right crossing `π_n` of `[0,1]²` from below by the sum, over `2^k` blocks visited, of the
lengths of the sub-arcs crossing the rectangles around the blocks. The additivity input is
`sum_crossLenIn_le_lfppLen`: if a piecewise `C¹` path `P` has sub-arcs on pairwise disjoint time
intervals `(s_i, t_i) ⊆ [0,1]`, the `i`-th lying in `K_i` and running from `A_i` to `B_i`, then
`∑_i L(A_i, B_i; K_i) ≤ L(P)`. (Same argument as `crossLenIn_le_of_sub`, RSWPath.lean, plus
additivity of the length integral over disjoint intervals.)
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

/-- a sub-arc on `[s, t]` from `A` to `B` inside `K` bounds the crossing length by the length
integral over `(s, t)` -/
theorem crossLenIn_le_setLIntegral_Ioo {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {K A B : Set ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hK : ∀ u ∈ Icc s t, P u ∈ K) (hA : P s ∈ A) (hB : P t ∈ B) :
    crossLenIn ξ f K A B ≤ ∫⁻ x in Ioo s t, lenDens ξ f P x := by
  rcases hst.lt_or_eq with h | rfl
  · have hsub := isPiecewiseC1Path_subPath hP hs h ht
    calc crossLenIn ξ f K A B ≤ lfppLen ξ f (subPath P s t) :=
          crossLenIn_le_lfppLen ⟨P s, hA, P t, hB, hsub, fun u hu => hK _ (by
            constructor <;> nlinarith [hu.1, hu.2])⟩
      _ = ∫⁻ x in Icc s t, lenDens ξ f P x := lfppLen_subPath P h
      _ = ∫⁻ x in Ioo s t, lenDens ξ f P x := (setLIntegral_congr Ioo_ae_eq_Icc).symm
  · calc crossLenIn ξ f K A B ≤ lfppLen ξ f (fun _ => P s) :=
          crossLenIn_le_lfppLen ⟨P s, hA, P s, hB, isPiecewiseC1Path_const _,
            fun _ _ => hK s (by simp)⟩
      _ = 0 := lfppLen_const _
      _ ≤ _ := bot_le

/-- reversed version: a sub-arc on `[s, t]` from `B` (at `s`) to `A` (at `t`) inside `K` -/
theorem crossLenIn_le_setLIntegral_Ioo_rev {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {K A B : Set ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hK : ∀ u ∈ Icc s t, P u ∈ K) (hA : P t ∈ A) (hB : P s ∈ B) :
    crossLenIn ξ f K A B ≤ ∫⁻ x in Ioo s t, lenDens ξ f P x := by
  rcases hst.lt_or_eq with h | rfl
  · have hsub := isPiecewiseC1Path_revPath (isPiecewiseC1Path_subPath hP hs h ht)
    calc crossLenIn ξ f K A B ≤ lfppLen ξ f (revPath (subPath P s t)) :=
          crossLenIn_le_lfppLen ⟨P t, hA, P s, hB, hsub, fun u hu => hK _ (by
            constructor <;> nlinarith [hu.1, hu.2])⟩
      _ = lfppLen ξ f (subPath P s t) := lfppLen_revPath _
      _ = ∫⁻ x in Icc s t, lenDens ξ f P x := lfppLen_subPath P h
      _ = ∫⁻ x in Ioo s t, lenDens ξ f P x := (setLIntegral_congr Ioo_ae_eq_Icc).symm
  · exact crossLenIn_le_setLIntegral_Ioo hP hs le_rfl ht hK hA hB

/-- length integrals over pairwise disjoint subintervals of `[0, 1]` add up to at most `L(P)` -/
theorem sum_setLIntegral_le_lfppLen (P : ℝ → ℂ) {ι : Type*} (F : Finset ι) (s t : ι → ℝ)
    (hs : ∀ i ∈ F, 0 ≤ s i) (ht : ∀ i ∈ F, t i ≤ 1)
    (hdisj : (F : Set ι).PairwiseDisjoint fun i => Ioo (s i) (t i)) :
    ∑ i ∈ F, ∫⁻ x in Ioo (s i) (t i), lenDens ξ f P x ≤ lfppLen ξ f P := by
  calc ∑ i ∈ F, ∫⁻ x in Ioo (s i) (t i), lenDens ξ f P x
      = ∫⁻ x in ⋃ i ∈ F, Ioo (s i) (t i), lenDens ξ f P x :=
        (lintegral_biUnion_finset hdisj (fun i _ => measurableSet_Ioo) _).symm
    _ ≤ ∫⁻ x in Icc (0 : ℝ) 1, lenDens ξ f P x := by
        refine lintegral_mono_set ?_
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨i, hi, hx⟩ := hx
        exact ⟨(hs i hi).trans hx.1.le, hx.2.le.trans (ht i hi)⟩
    _ = lfppLen ξ f P := (lfppLen_eq _ _ _).symm

end DDDF
end LQGMetric
