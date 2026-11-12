/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EGlue at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EMeet

/-!
# DDDF Theorem 20, Step 4: the length of the glued path (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105: "We upper-bound `L_n^P(ψ)` by taking the
concatenation of the part of `π_n(ψ)` outside of `P^K` together with … long crossings in rectangles
comprising a circuit around `P^K` (for the field `ψ_{0,n}` which coincides with the field
`ψ^P_{0,n}` outside of `P^K`)". `T20E.glue_le` is this bound at the level of `U`-distances:
the resampled field `g` equals `f` on `Fr` (the complement of the `2s`-neighbourhood of the
block), the crossings `pc j`, `j ∈ R`, lie in `[0,1]² ∩ Fr` and form a connected meet graph, the
near-geodesic `γ` reaches a crossing at time `r₀` and leaves one at time `r₁ ≥ r₀` (or the
circuit itself touches the left/right side of `[0,1]²`, the boundary case D-DDDF-22); then
`L(g) ≤ L(γ, f) + Σ_{j ∈ R} L(pc j, f)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

open LFPP

variable {ξ : ℝ}

/-- the crossing length is at most the distance between points of the two marked sides -/
lemma rectLen_le_dOn {f : ℂ → ℝ} {R : MarkedRect} {z w : ℂ} (hz : z ∈ R.side₁)
    (hw : w ∈ R.side₂) : rectLen ξ f R ≤ lfppDOn ξ f R.toSet z w :=
  (iInf₂_le z hz).trans (iInf₂_le w hw)

/-- a piece of a path inside `S ∩ Fr`, where `g = f`, costs at most its `f`-length -/
lemma dOn_piece_le {f g : ℂ → ℝ} {S Fr : Set ℂ} (hfg : ∀ x ∈ Fr, g x = f x) {γ : ℝ → ℂ}
    {z w : ℂ} (hγ : IsPiecewiseC1Path γ z w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hS : ∀ r ∈ Icc a b, γ r ∈ S ∩ Fr) :
    lfppDOn ξ g S (γ a) (γ b) ≤ ∫⁻ r in Icc a b, lenDens ξ f γ r := by
  rcases hab.lt_or_eq with hab | rfl
  · have hmap : ∀ τ ∈ Icc (0 : ℝ) 1, (b - a) * τ + a ∈ Icc a b := fun τ hτ =>
      ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
    calc lfppDOn ξ g S (γ a) (γ b) ≤ lfppLen ξ g (subPath γ a b) :=
          lfppDOn_le (isPiecewiseC1Path_subPath hγ ha hab hb) fun τ hτ => (hS _ (hmap τ hτ)).1
      _ = lfppLen ξ f (subPath γ a b) :=
          T20B.lfppLen_congr_path fun τ hτ => hfg _ (hS _ (hmap τ hτ)).2
      _ = _ := lfppLen_subPath γ hab
  · calc lfppDOn ξ g S (γ a) (γ a) ≤ lfppLen ξ g (fun _ => γ a) :=
          lfppDOn_le (isPiecewiseC1Path_const _) fun _ _ => (hS a ⟨le_rfl, le_rfl⟩).1
      _ = 0 := lfppLen_const _
      _ ≤ _ := bot_le

/-- two pieces `[0, r₀]` and `[r₁, 1]`, `r₀ ≤ r₁`, cost at most the whole path -/
lemma two_pieces_le {f : ℂ → ℝ} {γ : ℝ → ℂ} {r₀ r₁ : ℝ} (h0 : 0 ≤ r₀) (h01 : r₀ ≤ r₁)
    (h1 : r₁ ≤ 1) :
    (∫⁻ r in Icc 0 r₀, lenDens ξ f γ r) + ∫⁻ r in Icc r₁ 1, lenDens ξ f γ r ≤ lfppLen ξ f γ := by
  rw [lfppLen_eq, ← setLIntegral_congr (Ioc_ae_eq_Icc (a := r₁) (b := 1)),
    ← lintegral_union measurableSet_Ioc]
  · exact lintegral_mono_set fun r hr => by
      rcases hr with hr | hr
      · exact ⟨hr.1, by linarith [hr.2]⟩
      · exact ⟨by linarith [hr.1, hr.2], hr.2⟩
  · exact Set.disjoint_left.2 fun r h1 h2 => by linarith [h1.2, h2.1]

/-- **The glued path** (DDDF l. 1103–1105), at the level of `[0,1]²`-distances. -/
theorem glue_le {f g : ℂ → ℝ} {Fr : Set ℂ} (hfg : ∀ x ∈ Fr, g x = f x) {γ : ℝ → ℂ}
    (hγ : lfppLen ξ f γ ≠ ⊤) {R : Finset (Circle × ℂ)} {pc : Circle × ℂ → ℝ → ℂ}
    (hpc : ∀ j ∈ R, IsPiecewiseC1Path (pc j) (pc j 0) (pc j 1))
    (hRsq : ∀ j ∈ R, ∀ t ∈ Icc (0 : ℝ) 1, pc j t ∈ (rectAB 1 1).toSet ∩ Fr)
    (hfin : ∀ k ∈ R, lfppLen ξ f (pc k) ≠ ⊤)
    (hconn : ∀ i ∈ R, ∀ j ∈ R, (meetGraph pc (R : Set (Circle × ℂ))).Reachable i j)
    {r₀ r₁ : ℝ} (h0 : 0 ≤ r₀) (h01 : r₀ ≤ r₁) (h1 : r₁ ≤ 1) {i j : Circle × ℂ} (hi : i ∈ R) (hj : j ∈ R) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ (rectAB 1 1).side₁)
    (hz₁ : z₁ ∈ (rectAB 1 1).side₂)
    (hS : lfppDOn ξ g (rectAB 1 1).toSet z₀ (pc i s) ≤ ∫⁻ r in Icc 0 r₀, lenDens ξ f γ r)
    (hE : lfppDOn ξ g (rectAB 1 1).toSet (pc j t) z₁ ≤ ∫⁻ r in Icc r₁ 1, lenDens ξ f γ r) :
    (rectLen ξ g (rectAB 1 1)).toReal ≤
      (lfppLen ξ f γ).toReal + ∑ k ∈ R, (lfppLen ξ f (pc k)).toReal := by
  classical
  set S := (rectAB 1 1).toSet
  have hmid : lfppDOn ξ g S (pc i s) (pc j t) ≤ ∑ k ∈ R, lfppLen ξ f (pc k) := by
    refine (reach_dOn_le_sum (ξ := ξ) (f := g) (U := S) (V := R) hpc
      (fun k hk t ht => (hRsq k hk t ht).1) hi (hconn i hi j hj) hs ht).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun k hk => ?_)
    exact T20B.lfppLen_congr_path fun τ hτ => hfg _ (hRsq k hk τ hτ).2
  have htot : rectLen ξ g (rectAB 1 1) ≤ lfppLen ξ f γ + ∑ k ∈ R, lfppLen ξ f (pc k) := by
    calc rectLen ξ g (rectAB 1 1) ≤ lfppDOn ξ g S z₀ z₁ := rectLen_le_dOn hz₀ hz₁
      _ ≤ lfppDOn ξ g S z₀ (pc i s) + lfppDOn ξ g S (pc i s) (pc j t) +
            lfppDOn ξ g S (pc j t) z₁ :=
          (lfppDOn_triangle _ (pc j t) _).trans
            (add_le_add (lfppDOn_triangle _ (pc i s) _) le_rfl)
      _ ≤ (∫⁻ r in Icc 0 r₀, lenDens ξ f γ r) + ∑ k ∈ R, lfppLen ξ f (pc k) +
            ∫⁻ r in Icc r₁ 1, lenDens ξ f γ r := add_le_add (add_le_add hS hmid) hE
      _ = ((∫⁻ r in Icc 0 r₀, lenDens ξ f γ r) + ∫⁻ r in Icc r₁ 1, lenDens ξ f γ r) +
            ∑ k ∈ R, lfppLen ξ f (pc k) := by ring
      _ ≤ _ := add_le_add (two_pieces_le h0 h01 h1) le_rfl
  have hsum : ∑ k ∈ R, lfppLen ξ f (pc k) ≠ ⊤ := by
    rw [ne_eq, ENNReal.sum_eq_top]; push Not; exact hfin
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hγ, hsum⟩) htot).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hγ hsum, ENNReal.toReal_sum hfin]

end T20E
end DDDF
end LQGMetric
