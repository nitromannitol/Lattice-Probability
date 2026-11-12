/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Glue at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Chain

/-!
# DDDF Prop 26, Step 1: tools for the gluing `S6Step1Glue` (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1289–1294 ("`Γ_{k,n}` contains a left-right crossing of `[0,1]²`"). The visited blocks of a
crossing are `*`-connected (`S6.reach_end`, S6P21Path.lean), so the gluing of P18S1Chain
(`chain_dOn`, uniform cost per site, `4`-adjacent sites) is needed with per-site costs and
`*`-adjacency:

* `chain_dOn_sum`: along a walk, the `U`-distance from a point of the first circuit to the hub of
  the last one is at most twice the sum of the circuit lengths along the walk;
* `SiteCirc.meet_adjK`: the circuits of `*`-adjacent sites meet (`SiteCirc.meet` for the
  `4`-adjacent ones, `hv_meet` for the diagonal ones).

Own elementary arguments (DDDF leave the gluing to the figure), extending P18S1Chain/P18S1Geom.
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

/-- **Gluing along a walk, per-site costs**: hubs `m x` at distance `≤ c x` from the points of
`On x`, and `On x`, `On y` meeting for adjacent `x, y`. -/
lemma chain_dOn_sum {V : Type*} {G : SimpleGraph V} {U : Set ℂ} (On : V → ℂ → Prop)
    (m : V → ℂ) (c : V → ℝ≥0∞) (hhub : ∀ x a, On x a → lfppDOn ξ f U a (m x) ≤ c x)
    (hmeet : ∀ x y, G.Adj x y → ∃ q, On x q ∧ On y q) {u v : V} (p : G.Walk u v) :
    ∀ a, On u a → lfppDOn ξ f U a (m v) ≤ 2 * (p.support.map c).sum := by
  induction p with
  | nil =>
    intro a ha
    simp only [SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    exact (hhub _ a ha).trans (by rw [two_mul]; exact le_self_add)
  | @cons u w v h p ih =>
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hmeet u w h
    have h1 : lfppDOn ξ f U a q ≤ 2 * c u := by
      calc lfppDOn ξ f U a q ≤ lfppDOn ξ f U a (m u) + lfppDOn ξ f U (m u) q :=
            lfppDOn_triangle _ _ _
        _ ≤ c u + c u := add_le_add (hhub _ a ha) (by rw [lfppDOn_comm]; exact hhub _ q hq1)
        _ = 2 * c u := (two_mul _).symm
    calc lfppDOn ξ f U a (m v) ≤ lfppDOn ξ f U a q + lfppDOn ξ f U q (m v) :=
          lfppDOn_triangle _ _ _
      _ ≤ 2 * c u + 2 * (p.support.map c).sum := add_le_add h1 (ih q hq2)
      _ = 2 * ((SimpleGraph.Walk.cons h p).support.map c).sum := by
          simp only [SimpleGraph.Walk.support_cons, List.map_cons, List.sum_cons, mul_add]

/-- **Gluing along a walk inside `S`**: the bound of `chain_dOn_sum` along the bypass of the walk,
each site of `S` counted once. -/
lemma chain_dOn_finset {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U : Set ℂ}
    (On : V → ℂ → Prop) (m : V → ℂ) (c : V → ℝ≥0∞)
    (hhub : ∀ x a, On x a → lfppDOn ξ f U a (m x) ≤ c x)
    (hmeet : ∀ x y, G.Adj x y → ∃ q, On x q ∧ On y q) (S : Finset V) {u v : V}
    (p : G.Walk u v) (hS : ∀ x ∈ p.support, x ∈ S) :
    ∀ a, On u a → lfppDOn ξ f U a (m v) ≤ 2 * ∑ x ∈ S, c x := by
  intro a ha
  refine (chain_dOn_sum On m c hhub hmeet p.bypass a ha).trans ?_
  gcongr
  rw [← List.sum_toFinset c p.bypass_isPath.support_nodup]
  exact Finset.sum_le_sum_of_subset fun x hx =>
    hS x (p.support_bypass_subset_support (List.mem_toFinset.1 hx))

/-- clamping an index into `[lo, hi]` -/
def clampZ (lo hi x : ℤ) : ℤ := max lo (min hi x)

/-- clamping a block index into `[lo, hi]²` -/
def clampB (lo hi : ℤ) (b : ℤ × ℤ) : ℤ × ℤ := (clampZ lo hi b.1, clampZ lo hi b.2)

lemma clampZ_mem {lo hi : ℤ} (h : lo ≤ hi) (x : ℤ) : lo ≤ clampZ lo hi x ∧ clampZ lo hi x ≤ hi := by
  unfold clampZ; omega

lemma clampZ_near {lo hi x y : ℤ} (h1 : x ≤ y + 1) (h2 : y ≤ x + 1) :
    clampZ lo hi x ≤ clampZ lo hi y + 1 ∧ clampZ lo hi y ≤ clampZ lo hi x + 1 := by
  unfold clampZ; omega

/-- clamping maps `*`-adjacent blocks to equal or `*`-adjacent blocks -/
lemma clampB_adj (lo hi : ℤ) {a b : ℤ × ℤ} (h1 : |a.1 - b.1| ≤ 1) (h2 : |a.2 - b.2| ≤ 1) :
    clampB lo hi a = clampB lo hi b ∨ PercAdjK (clampB lo hi a) (clampB lo hi b) := by
  rw [abs_le] at h1 h2
  obtain ⟨e1, e2⟩ := clampZ_near (lo := lo) (hi := hi) (x := a.1) (y := b.1) (by omega) (by omega)
  obtain ⟨e3, e4⟩ := clampZ_near (lo := lo) (hi := hi) (x := a.2) (y := b.2) (by omega) (by omega)
  by_cases h : clampB lo hi a = clampB lo hi b
  · exact Or.inl h
  · refine Or.inr ⟨?_, e1, e2, e3, e4⟩
    by_contra hc
    push_neg at hc
    exact h (Prod.ext hc.1 hc.2)

namespace SiteCirc

variable {z z' : ℤ × ℤ} {c c' : ℝ≥0∞}

/-- circuits of diagonally adjacent sites `y' = y + (1, 1)` meet -/
lemma meet_diag_up {y y' : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d)
    (D' : SiteCirc ξ f y' d') (e1 : y'.1 = y.1 + 1) (e2 : y'.2 = y.2 + 1) :
    ∃ q, D.On q ∧ D'.On q := by
  obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sT y) (V := sL y') rfl rfl
    (by simp [sL]) (by simp [sT]) (by simp [sT, sL, e1]) (by simp [sT, sL, e1] <;> linarith)
    (by simp [sT, sL, e2]) (by simp [sT, sL, e2] <;> linarith) D.hT D'.hL
  exact ⟨D.T s, Or.inr (Or.inl ⟨s, hs, rfl⟩), Or.inr (Or.inr (Or.inl ⟨t, ht, e.symm⟩))⟩

/-- circuits of diagonally adjacent sites `y' = y + (1, -1)` meet -/
lemma meet_diag_down {y y' : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d)
    (D' : SiteCirc ξ f y' d') (e1 : y'.1 = y.1 + 1) (e2 : y.2 = y'.2 + 1) :
    ∃ q, D.On q ∧ D'.On q := by
  obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sB y) (V := sL y') rfl rfl
    (by simp [sL]) (by simp [sB]) (by simp [sB, sL, e1]) (by simp [sB, sL, e1] <;> linarith)
    (by simp [sB, sL, e2] <;> linarith) (by simp [sB, sL, e2] <;> linarith) D.hB D'.hL
  exact ⟨D.B s, Or.inl ⟨s, hs, rfl⟩, Or.inr (Or.inr (Or.inl ⟨t, ht, e.symm⟩))⟩

/-- two circuits around the same site meet -/
lemma meet_same {y : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d) (D' : SiteCirc ξ f y d') :
    ∃ q, D.On q ∧ D'.On q := by
  obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sT y) (V := sL y) rfl rfl
    (by simp [sL]) (by simp [sT]) (by simp [sT, sL]) (by simp [sT, sL] <;> linarith)
    (by simp [sT, sL] <;> linarith) (by simp [sT, sL] <;> linarith) D.hT D'.hL
  exact ⟨D.T s, Or.inr (Or.inl ⟨s, hs, rfl⟩), Or.inr (Or.inr (Or.inl ⟨t, ht, e.symm⟩))⟩

lemma meet_eq {y y' : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d) (D' : SiteCirc ξ f y' d')
    (h : y = y') : ∃ q, D.On q ∧ D'.On q := by
  subst h; exact meet_same D D'

/-- **Circuits of `*`-adjacent sites meet.** -/
lemma meet_adjK (C : SiteCirc ξ f z c) (C' : SiteCirc ξ f z' c') (h : PercAdjK z z') :
    ∃ q, C.On q ∧ C'.On q := by
  obtain ⟨hne, h1, h2, h3, h4⟩ := h
  by_cases hx : z.1 = z'.1
  · have hy : z.2 ≠ z'.2 := hne.resolve_left (not_not.2 hx)
    exact meet C C' (Or.inl ⟨hx, by omega⟩)
  by_cases hy : z.2 = z'.2
  · exact meet C C' (Or.inr ⟨hy, by omega⟩)
  rcases (show (z'.1 = z.1 + 1 ∨ z.1 = z'.1 + 1) by omega) with ex | ex <;>
    rcases (show (z'.2 = z.2 + 1 ∨ z.2 = z'.2 + 1) by omega) with ey | ey
  · exact meet_diag_up C C' ex ey
  · exact meet_diag_down C C' ex ey
  · obtain ⟨q, q1, q2⟩ := meet_diag_down C' C ex ey; exact ⟨q, q2, q1⟩
  · obtain ⟨q, q1, q2⟩ := meet_diag_up C' C ex ey; exact ⟨q, q2, q1⟩

end SiteCirc

lemma clampZ_of_le {lo hi x : ℤ} (h : lo ≤ hi) (hx : x ≤ lo) : clampZ lo hi x = lo := by
  unfold clampZ; omega

lemma clampZ_of_ge {lo hi x : ℤ} (h : lo ≤ hi) (hx : hi ≤ x) : clampZ lo hi x = hi := by
  unfold clampZ; omega

lemma sub_rectAB_of {N : ℝ} {R : MarkedRect} (h1 : 0 ≤ R.x0) (h2 : R.x0 + R.w ≤ N)
    (h3 : 0 ≤ R.y0) (h4 : R.y0 + R.h ≤ N) : R.toSet ⊆ (rectAB N N).toSet := by
  intro x hx
  rw [mem_toSet_iff] at hx ⊢
  simp only [rectAB, mem_Icc, zero_add] at hx ⊢
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, by linarith [hx.2.1], by linarith [hx.2.2]⟩

/-- the circuits of the sites of `[1, N-2]²` lie in `[0, N]²` -/
lemma sub_clampB {N : ℕ} (hN : 3 ≤ N) (x : ℤ × ℤ) :
    SiteCirc.Sub (rectAB N N).toSet (clampB 1 ((N : ℤ) - 2) x) := by
  have hle : (1 : ℤ) ≤ (N : ℤ) - 2 := by omega
  obtain ⟨a1, a2⟩ := clampZ_mem hle x.1
  obtain ⟨b1, b2⟩ := clampZ_mem hle x.2
  have r1 : (1 : ℝ) ≤ (clampZ 1 ((N : ℤ) - 2) x.1 : ℝ) := by exact_mod_cast a1
  have r2 : (clampZ 1 ((N : ℤ) - 2) x.1 : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast a2
  have r3 : (1 : ℝ) ≤ (clampZ 1 ((N : ℤ) - 2) x.2 : ℝ) := by exact_mod_cast b1
  have r4 : (clampZ 1 ((N : ℤ) - 2) x.2 : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast b2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact sub_rectAB_of (by simp [sB, sT, sL, sR, clampB] <;> linarith)
      (by simp [sB, sT, sL, sR, clampB] <;> linarith)
      (by simp [sB, sT, sL, sR, clampB] <;> linarith)
      (by simp [sB, sT, sL, sR, clampB] <;> linarith)

/-- **The gluing at unit scale**: a walk of blocks from `u` (with `u.1 ≤ 1`) to `v` (with
`v.1 ≥ N - 2`) through `S`, `*`-steps, and circuits of cost `c x` around the clamped sites
`clampB 1 (N-2) x` give `L(R_{N,N}) ≤ 2 Σ_{x ∈ S} c x + c v`. -/
theorem rectLen_le_glue {N : ℕ} (hN : 3 ≤ N) {G : SimpleGraph (ℤ × ℤ)}
    (hG : ∀ x y, G.Adj x y → |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1) (S : Finset (ℤ × ℤ))
    {u v : ℤ × ℤ} (p : G.Walk u v) (hS : ∀ x ∈ p.support, x ∈ S) (hu : u.1 ≤ 1)
    (hv : (N : ℤ) - 2 ≤ v.1) (c : ℤ × ℤ → ℝ≥0∞)
    (C : ∀ x, SiteCirc ξ f (clampB 1 ((N : ℤ) - 2) x) (c x)) :
    rectLen ξ f (rectAB N N) ≤ 2 * ∑ x ∈ S, c x + c v := by
  classical
  set U := (rectAB N N).toSet
  have hle : (1 : ℤ) ≤ (N : ℤ) - 2 := by omega
  let m : ℤ × ℤ → ℂ := fun x => (SiteCirc.hub (U := U) (C x) (sub_clampB hN x)).choose
  have hhub : ∀ x a, (C x).On a → lfppDOn ξ f U a (m x) ≤ c x := fun x a ha =>
    (SiteCirc.hub (U := U) (C x) (sub_clampB hN x)).choose_spec a ha
  have hmeet : ∀ x y, G.Adj x y → ∃ q, (C x).On q ∧ (C y).On q := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hG x y hxy
    rcases clampB_adj 1 ((N : ℤ) - 2) h1 h2 with e | e
    · exact SiteCirc.meet_eq (C x) (C y) e
    · exact SiteCirc.meet_adjK (C x) (C y) e
  have hd := chain_dOn_finset (ξ := ξ) (f := f) (U := U) (fun x a => (C x).On a) m c hhub hmeet
    S p hS
  -- endpoints on the left and right sides
  obtain ⟨z0, hz0, w0, _, hp0, _⟩ := (C u).hB
  obtain ⟨z1, _, w1, hw1, hp1, _⟩ := (C v).hB
  have hOa : (C u).On z0 := Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hp0.source⟩
  have hOb : (C v).On w1 := Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, hp1.target⟩
  have eu : clampZ 1 ((N : ℤ) - 2) u.1 = 1 := clampZ_of_le hle hu
  have ev : clampZ 1 ((N : ℤ) - 2) v.1 = (N : ℤ) - 2 := clampZ_of_ge hle hv
  obtain ⟨b1, b2⟩ := clampZ_mem hle u.2
  obtain ⟨b3, b4⟩ := clampZ_mem hle v.2
  have r1 : (1 : ℝ) ≤ (clampZ 1 ((N : ℤ) - 2) u.2 : ℝ) := by exact_mod_cast b1
  have r2 : (clampZ 1 ((N : ℤ) - 2) u.2 : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast b2
  have r3 : (1 : ℝ) ≤ (clampZ 1 ((N : ℤ) - 2) v.2 : ℝ) := by exact_mod_cast b3
  have r4 : (clampZ 1 ((N : ℤ) - 2) v.2 : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast b4
  have eu' : ((clampZ 1 ((N : ℤ) - 2) u.1 : ℤ) : ℝ) = 1 := by rw [eu]; simp
  have ev' : ((clampZ 1 ((N : ℤ) - 2) v.1 : ℤ) : ℝ) = (N : ℝ) - 2 := by rw [ev]; push_cast; ring
  simp only [MarkedRect.side₁, MarkedRect.side₂, sB, clampB, ite_true, Complex.mem_reProdIm,
    mem_singleton_iff, mem_Icc] at hz0 hw1
  have hz0s : z0 ∈ (rectAB N N).side₁ := by
    rw [mem_rectAB_side₁]
    refine ⟨by rw [hz0.1, eu']; ring, ⟨by linarith [hz0.2.1], by linarith [hz0.2.2]⟩⟩
  have hw1s : w1 ∈ (rectAB N N).side₂ := by
    rw [mem_rectAB_side₂]
    refine ⟨by rw [hw1.1, ev']; ring, ⟨by linarith [hw1.2.1], by linarith [hw1.2.2]⟩⟩
  have hd2 : lfppDOn ξ f U (m v) w1 ≤ c v := by rw [lfppDOn_comm]; exact hhub v w1 hOb
  calc rectLen ξ f (rectAB N N) ≤ lfppDOn ξ f U z0 w1 :=
        iInf₂_le_of_le z0 hz0s (iInf₂_le_of_le w1 hw1s le_rfl)
    _ ≤ lfppDOn ξ f U z0 (m v) + lfppDOn ξ f U (m v) w1 := lfppDOn_triangle _ _ _
    _ ≤ 2 * ∑ x ∈ S, c x + c v := add_le_add (hd z0 hOa) hd2

end DDDF
end LQGMetric
