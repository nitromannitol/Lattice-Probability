/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EStrip
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn

/-!
# DDDF Prop 27, Step 1: the chaining bound, generic part (task P2-DDDF6d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1340–1345 (`eq:Chaining`), which refers to
Dubédat–Falconet, *Liouville metric of star-scale invariant fields: tails and Weyl scaling*
(arXiv:1809.02607, `LiouvilleMetricStarScale.tex` l. 1013–1021, "(6.1)"): at each dyadic scale
`k ≤ n` and each dyadic square of side `2^{-k}` one takes the four crossings (in the long
direction) of the two horizontal and the two vertical halves of the square (the "system" of the
square); consecutive systems along the nested squares containing `x` meet, and a straight segment
joins `x` to the system at scale `n`.

This file: the abstract chaining along nested systems (`chain_center`), the meeting of a
horizontal and a vertical crossing of a rectangle (`meet_of_cross`, from
`RectMeet.rect_crossings_meet`), and the distance between two points of a path
(`dOn_le_len`). The choice of the paths and the dyadic bookkeeping are in `S6DiamGeo`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP

/-- **Chaining along nested systems** (DF l. 1017–1019): if every point of the system `Sys k`
is within `r k` of its centre `c k`, consecutive systems meet, and `x` is within `E` of a point
of `Sys n`, then `x` is within `E + 2 Σ_{k ≤ n} r k` of `c 0`. -/
theorem chain_center {d : ℂ → ℂ → ℝ≥0∞} (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (hsymm : ∀ a b, d a b = d b a) (n : ℕ) (Sys : ℕ → Set ℂ) (c : ℕ → ℂ) (r : ℕ → ℝ≥0∞)
    (hS : ∀ k ≤ n, ∀ u ∈ Sys k, d (c k) u ≤ r k)
    (hmeet : ∀ k < n, (Sys k ∩ Sys (k + 1)).Nonempty) (x : ℂ) (E : ℝ≥0∞)
    (hx : ∃ p ∈ Sys n, d x p ≤ E) :
    d x (c 0) ≤ E + 2 * ∑ k ∈ Finset.range (n + 1), r k := by
  -- `d x (c (n - m)) + r (n - m) ≤ E + 2 Σ_{k ∈ [n-m, n]} r k`
  have key : ∀ m ≤ n, d x (c (n - m)) + r (n - m) ≤
      E + 2 * ∑ k ∈ Finset.Icc (n - m) n, r k := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨p, hp, hxp⟩ := hx
      simp only [Nat.sub_zero, Finset.Icc_self, Finset.sum_singleton]
      calc d x (c n) + r n ≤ d x p + d p (c n) + r n := by gcongr; exact htri _ _ _
        _ ≤ E + r n + r n := by gcongr; rw [hsymm]; exact hS n le_rfl p hp
        _ = E + 2 * r n := by rw [two_mul, add_assoc]
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      obtain ⟨q, hq1, hq2⟩ := hmeet (n - (m + 1)) (by omega)
      have e : n - (m + 1) + 1 = n - m := by omega
      rw [e] at hq2
      have hI : Finset.Icc (n - (m + 1)) n = insert (n - (m + 1)) (Finset.Icc (n - m) n) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : n - (m + 1) ∉ Finset.Icc (n - m) n := by
        simp only [Finset.mem_Icc]; omega
      rw [hI, Finset.sum_insert hnot]
      calc d x (c (n - (m + 1))) + r (n - (m + 1))
          ≤ d x (c (n - m)) + d (c (n - m)) q + d q (c (n - (m + 1))) + r (n - (m + 1)) := by
            gcongr; exact (htri _ q _).trans (by gcongr; exact htri _ _ _)
        _ ≤ d x (c (n - m)) + r (n - m) + r (n - (m + 1)) + r (n - (m + 1)) := by
            gcongr
            · exact hS _ (by omega) q hq2
            · rw [hsymm]; exact hS _ (by omega) q hq1
        _ ≤ E + 2 * ∑ k ∈ Finset.Icc (n - m) n, r k + r (n - (m + 1)) + r (n - (m + 1)) := by
            gcongr
        _ = E + 2 * (r (n - (m + 1)) + ∑ k ∈ Finset.Icc (n - m) n, r k) := by
            rw [mul_add, two_mul (r _)]; ring
  have h := key n le_rfl
  rw [Nat.sub_self] at h
  have hR : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hR] at h
  exact le_trans le_self_add h

/-- two points of `S` joined by a sub-arc of a path in `S` are within its length -/
theorem dOn_le_len {ξ : ℝ} {f : ℂ → ℝ} {S : Set ℂ} {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) (hS : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    lfppDOn ξ f S (P s) (P t) ≤ lfppLen ξ f P := by
  have h := crossLenIn_le_of_sub (ξ := ξ) (f := f) hP hs ht (K := S) (A := {P s}) (B := {P t})
    (fun u hu => hS u (uIcc_subset_Icc hs ht hu)) rfl rfl
  have e : crossLenIn ξ f S {P s} {P t} = lfppDOn ξ f S (P s) (P t) := by
    simp only [crossLenIn, Set.mem_singleton_iff, iInf_iInf_eq_left]; rfl
  rw [← e]; exact h

/-- **a horizontal and a vertical crossing of a rectangle meet** (`RectMeet.rect_crossings_meet`;
DF l. 1013 "each system is connected") -/
theorem meet_of_cross {γ δ : ℝ → ℂ} {z₁ w₁ z₂ w₂ : ℂ} (hγ : IsPiecewiseC1Path γ z₁ w₁)
    (hδ : IsPiecewiseC1Path δ z₂ w₂) {x₀ x₁ y₀ y₁ : ℝ}
    (hγR : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ RectCross.rect x₀ x₁ y₀ y₁)
    (hδR : ∀ t ∈ Icc (0 : ℝ) 1, δ t ∈ RectCross.rect x₀ x₁ y₀ y₁)
    (hγ0 : (γ 0).re = x₀) (hγ1 : (γ 1).re = x₁) (hδ0 : (δ 0).im = y₀) (hδ1 : (δ 1).im = y₁) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, γ s = δ t := by
  have hmaps : MapsTo (fun t => 1 - t) (Icc (0 : ℝ) 1) (Icc 0 1) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨s, hs, t, ht, h⟩ := RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ γ (fun t => δ (1 - t))
    hγ.continuousOn (hδ.continuousOn.comp (by fun_prop) hmaps) (fun t ht => hγR t ht)
    (fun t ht => hδR _ (hmaps ht)) hγ0 hγ1 (by simpa using hδ1) (by simpa using hδ0)
  exact ⟨s, hs, 1 - t, hmaps ht, h⟩

end S6D
end DDDF
end LQGMetric
