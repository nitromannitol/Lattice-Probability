/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S1Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# DDDF Prop 18, Step 1: a crossing of `R_{3k,k}` from a chain of open sites (task P2-DDDF18S1)

DDDF (arXiv:1904.08021, `tightness.tex` l. 902–905): a left–right `4`-connected chain of open
sites (each with four `3 × 1` crossings of total length `≤ c` around it, `SiteCirc`) gives a
left–right crossing of `R_{3k,k}` of length `≤ (2KL + 2) c`, `K × L` the grid of sites
(`splice_rectLen`). Hubs of the circuits (`SiteCirc.hub`) are joined along a simple path of the
graph of open sites (`chain_dOn`), consecutive circuits meeting (`SiteCirc.meet`). Own
elementary argument (DDDF leave the gluing implicit).
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

/-- **Gluing along a walk**: hubs `m x` at distance `≤ c` from the points of `On x`, and
`On x`, `On y` meeting for adjacent `x, y`. -/
lemma chain_dOn {V : Type*} {G : SimpleGraph V} {U : Set ℂ} {c : ℝ≥0∞} (On : V → ℂ → Prop)
    (m : V → ℂ) (hhub : ∀ x a, On x a → lfppDOn ξ f U a (m x) ≤ c)
    (hmeet : ∀ x y, G.Adj x y → ∃ q, On x q ∧ On y q) {u v : V} (p : G.Walk u v) :
    ∀ a, On u a → lfppDOn ξ f U a (m v) ≤ (2 * p.length + 1) * c := by
  induction p with
  | nil => intro a ha; simpa using hhub _ a ha
  | @cons u w v h p ih =>
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hmeet u w h
    have h1 : lfppDOn ξ f U a q ≤ 2 * c := by
      calc lfppDOn ξ f U a q ≤ lfppDOn ξ f U a (m u) + lfppDOn ξ f U (m u) q :=
            lfppDOn_triangle _ _ _
        _ ≤ c + c := add_le_add (hhub _ a ha) (by rw [lfppDOn_comm]; exact hhub _ q hq1)
        _ = 2 * c := (two_mul c).symm
    calc lfppDOn ξ f U a (m v) ≤ lfppDOn ξ f U a q + lfppDOn ξ f U q (m v) :=
          lfppDOn_triangle _ _ _
      _ ≤ 2 * c + (2 * p.length + 1) * c := add_le_add h1 (ih q hq2)
      _ = (2 * (SimpleGraph.Walk.cons h p).length + 1) * c := by
          simp only [SimpleGraph.Walk.length_cons]; push_cast; ring

lemma percAdj4_ne {x y : ℤ × ℤ} (h : PercAdj4 x y) : x ≠ y := by
  rintro rfl
  rcases h with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> omega

/-- the site of the grid index `x` -/
def sh (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + 1, x.2 + 1)

/-- the grid of sites of `R_{3k,k}`: indices `[0, 3k−2) × [0, k−2)` -/
lemma sub_sh {k : ℕ} {x : ℤ × ℤ} (hx : percInGrid (3 * k - 2) (k - 2) x) :
    SiteCirc.Sub (rectAB (3 * k) k).toSet (sh x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have r1 : (0 : ℝ) ≤ x.1 := by exact_mod_cast h1
  have r2 : (x.1 : ℝ) + 3 ≤ 3 * k := by
    have : x.1 + 3 ≤ 3 * (k : ℤ) := by omega
    exact_mod_cast this
  have r3 : (0 : ℝ) ≤ x.2 := by exact_mod_cast h3
  have r4 : (x.2 : ℝ) + 3 ≤ k := by
    have : x.2 + 3 ≤ (k : ℤ) := by omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro w hw <;> rw [mem_toSet_iff] at hw <;>
    rw [mem_rectAB_toSet] <;>
    simp only [sB, sT, sL, sR, sh, Int.cast_add, Int.cast_one] at hw <;>
    exact ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩⟩

lemma percAdj4_sh {x y : ℤ × ℤ} (h : PercAdj4 x y ∨ PercAdj4 y x) : PercAdj4 (sh x) (sh y) := by
  unfold PercAdj4 sh at *
  simp only at *
  omega

/-- **DDDF l. 902–905, gluing**: a left–right chain of open sites of the `(3k−2) × (k−2)` grid
(open: four `3 × 1` crossings of total length `≤ c` around the site) gives
`L(R_{3k,k}) ≤ (6k² + 2) c`. -/
theorem splice_rectLen {k : ℕ} {c : ℝ≥0∞} {good : ℤ × ℤ → Prop}
    (hcirc : ∀ x, good x → percInGrid (3 * k - 2) (k - 2) x → Nonempty (SiteCirc ξ f (sh x) c))
    (hLR : PercGoodLR (3 * k - 2) (k - 2) good) :
    rectLen ξ f (rectAB (3 * k) k) ≤ (2 * ((3 * k * k : ℕ) : ℝ≥0∞) + 2) * c := by
  classical
  set U := (rectAB (3 * k) k).toSet
  set K : ℤ := 3 * k - 2
  set L : ℤ := k - 2
  let Cx : ∀ x, good x → percInGrid K L x → SiteCirc ξ f (sh x) c :=
    fun x h1 h2 => (hcirc x h1 h2).some
  let On : ℤ × ℤ → ℂ → Prop := fun x a => ∃ (h1 : good x) (h2 : percInGrid K L x),
    (Cx x h1 h2).On a
  let m : ℤ × ℤ → ℂ := fun x => if h : good x ∧ percInGrid K L x then
    (SiteCirc.hub (U := U) (Cx x h.1 h.2) (sub_sh h.2)).choose else 0
  have hhub : ∀ x a, On x a → lfppDOn ξ f U a (m x) ≤ c := by
    rintro x a ⟨h1, h2, ha⟩
    have hh : good x ∧ percInGrid K L x := ⟨h1, h2⟩
    simp only [m, dite_eq_left_of_eq_true (eq_true hh)]
    exact (SiteCirc.hub (U := U) (Cx x hh.1 hh.2) (sub_sh hh.2)).choose_spec a ha
  set G : SimpleGraph (ℤ × ℤ) := SimpleGraph.fromRel (PercGoodStep K L good)
  have hmeet : ∀ x y, G.Adj x y → ∃ q, On x q ∧ On y q := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    have key : ∀ x y, PercGoodStep K L good x y → PercAdj4 (sh x) (sh y) →
        ∃ q, On x q ∧ On y q := by
      intro x y hs had
      obtain ⟨gx, hx, gy, hy, _⟩ := hs
      obtain ⟨q, h1, h2⟩ := SiteCirc.meet (Cx x hx gx) (Cx y hy gy) had
      exact ⟨q, ⟨hx, gx, h1⟩, ⟨hy, gy, h2⟩⟩
    rcases hxy.2 with hs | hs
    · exact key x y hs (percAdj4_sh (Or.inl hs.2.2.2.2))
    · obtain ⟨q, h1, h2⟩ := key y x hs (percAdj4_sh (Or.inl hs.2.2.2.2))
      exact ⟨q, h2, h1⟩
  obtain ⟨a, b, ha1, hb1, hag, hga, hab⟩ := hLR
  have hgb : percInGrid K L b ∧ good b := by
    induction hab with
    | refl => exact ⟨hag, hga⟩
    | tail _ hs _ => exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hrt : Relation.ReflTransGen G.Adj a b := by
    clear hgb hb1
    induction hab with
    | refl => exact .refl
    | tail _ h ih =>
      refine ih.tail ?_
      show (SimpleGraph.fromRel (PercGoodStep K L good)).Adj _ _
      rw [SimpleGraph.fromRel_adj]; exact ⟨percAdj4_ne h.2.2.2.2, Or.inl h⟩
  have hreach : G.Reachable a b := (SimpleGraph.reachable_iff_reflTransGen a b).2 hrt
  obtain ⟨p⟩ := hreach
  set q := p.toPath
  -- the path stays in the grid, so it has at most `3k · k` vertices
  have hsupp : ∀ {u v : ℤ × ℤ} (w : G.Walk u v), percInGrid K L u →
      ∀ x ∈ w.support, percInGrid K L x := by
    intro u v w
    induction w with
    | nil => intro hu x hx; simp at hx; exact hx ▸ hu
    | @cons u w v h w ih =>
      intro hu x hx
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · have hh := h
        rw [SimpleGraph.fromRel_adj] at hh
        exact ih (hh.2.elim (fun hs => hs.2.2.1) (fun hs => hs.1)) x hx
  have hlen : q.1.length ≤ 3 * k * k := by
    have hsub : q.1.support.toFinset ⊆ Finset.Ico 0 K ×ˢ Finset.Ico 0 L := by
      intro x hx
      have := hsupp q.1 hag x (List.mem_toFinset.1 hx)
      simp only [Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨this.1, this.2.1⟩, ⟨this.2.2.1, this.2.2.2⟩⟩
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup q.2.support_nodup, SimpleGraph.Walk.length_support,
      Finset.card_product, Int.card_Ico, Int.card_Ico] at h1
    have h2 : (K - 0).toNat * (L - 0).toNat ≤ 3 * k * k := by
      have e1 : (K - 0).toNat ≤ 3 * k := by omega
      have e2 : (L - 0).toNat ≤ k := by omega
      exact Nat.mul_le_mul e1 e2
    omega
  -- endpoints on the left and right sides
  obtain ⟨z0, hz0, w0, _, hp0, _⟩ := (Cx a hga hag).hB
  obtain ⟨z1, _, w1, hw1, hp1, _⟩ := (Cx b hgb.2 hgb.1).hB
  have hOa : On a z0 := ⟨hga, hag, Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hp0.source⟩⟩
  have hOb : On b w1 := ⟨hgb.2, hgb.1, Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, hp1.target⟩⟩
  simp only [MarkedRect.side₁, MarkedRect.side₂, sB, sh, ite_true, Complex.mem_reProdIm,
    mem_singleton_iff, Int.cast_add, Int.cast_one] at hz0 hw1
  have ga := hag; have gb := hgb.1
  obtain ⟨_, _, ga3, ga4⟩ := ga
  obtain ⟨_, _, gb3, gb4⟩ := gb
  have hz0s : z0 ∈ (rectAB (3 * k) k).side₁ := by
    rw [mem_rectAB_side₁]
    have r3 : (0 : ℝ) ≤ a.2 := by exact_mod_cast ga3
    have r4 : (a.2 : ℝ) + 1 ≤ k := by
      have : a.2 + 1 ≤ (k : ℤ) := by omega
      exact_mod_cast this
    refine ⟨by rw [hz0.1, ha1]; simp, ⟨by linarith [hz0.2.1], by linarith [hz0.2.2]⟩⟩
  have hw1s : w1 ∈ (rectAB (3 * k) k).side₂ := by
    rw [mem_rectAB_side₂]
    have r3 : (0 : ℝ) ≤ b.2 := by exact_mod_cast gb3
    have r4 : (b.2 : ℝ) + 1 ≤ k := by
      have : b.2 + 1 ≤ (k : ℤ) := by omega
      exact_mod_cast this
    have rb : (b.1 : ℝ) = 3 * k - 3 := by
      have : b.1 = 3 * (k : ℤ) - 3 := by omega
      rw [this]; push_cast; ring
    refine ⟨by rw [hw1.1, rb]; ring, ⟨by linarith [hw1.2.1], by linarith [hw1.2.2]⟩⟩
  have hd := chain_dOn (ξ := ξ) (f := f) (U := U) On m hhub hmeet q.1 z0 hOa
  have hd2 : lfppDOn ξ f U (m b) w1 ≤ c := by rw [lfppDOn_comm]; exact hhub b w1 hOb
  calc rectLen ξ f (rectAB (3 * k) k) ≤ lfppDOn ξ f U z0 w1 :=
        iInf₂_le_of_le z0 hz0s (iInf₂_le_of_le w1 hw1s le_rfl)
    _ ≤ lfppDOn ξ f U z0 (m b) + lfppDOn ξ f U (m b) w1 := lfppDOn_triangle _ _ _
    _ ≤ (2 * q.1.length + 1) * c + c := add_le_add hd hd2
    _ = (2 * (q.1.length : ℝ≥0∞) + 2) * c := by ring
    _ ≤ _ := by gcongr

end DDDF
end LQGMetric
