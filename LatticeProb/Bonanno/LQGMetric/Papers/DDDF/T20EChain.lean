/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Convex.PathConnected

/-!
# DDDF Theorem 20, Step 4: gluing a family of crossings (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 and l. 1117–1119: the circuit around the
neighbourhood `P^K` of a visited block is obtained by "gluing `O(K^{ε₀})` rectangle crossings of
size `2^{-K}(3,1)`". Here are the two planar/metric facts behind the gluing, for an arbitrary
family of crossings `p i` (paths in `U` on `[0,1]`):
* `T20E.reach_dOn_le_sum`: if the "meet" graph on a finite set `V` of crossings joins `i` to `j`,
  then any point of `p i` is at `U`-distance at most `Σ_{k ∈ V} L(p k)` from any point of `p j`
  (follow a simple path of the graph, each crossing used at most once);
* `T20E.meet_of_joined`: a top–bottom crossing of a rectangle meets every path-connected subset
  of the rectangle joining its left side to its right side (`RectMeet.rect_crossings_meet`);
  the union of a chain of pairwise meeting crossings is path connected (`T20E.isPathConnected_chain`).
Own elementary arguments (DDDF leave the gluing to the figure).
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

variable {ξ : ℝ} {f : ℂ → ℝ} {ι : Type*}

/-- the crossings `p i` and `p j` meet -/
def Meet (p : ι → ℝ → ℂ) (i j : ι) : Prop :=
  ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, p i s = p j t

/-- the meet graph on the finite set `V` -/
def meetGraph (p : ι → ℝ → ℂ) (V : Set ι) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => i ∈ V ∧ j ∈ V ∧ Meet p i j

lemma support_mem {p : ι → ℝ → ℂ} {V : Set ι} {i j : ι} (hi : i ∈ V)
    (w : (meetGraph p V).Walk i j) : ∀ k ∈ w.support, k ∈ V := by
  induction w with
  | nil => intro k hk; simp at hk; exact hk ▸ hi
  | @cons i k' j h w ih =>
    intro k hk
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hi
    · refine ih ?_ k hk
      rw [meetGraph, SimpleGraph.fromRel_adj] at h
      rcases h.2 with h | h
      · exact h.2.1
      · exact h.1

/-- distance along a walk of the meet graph: bounded by the sum over the support -/
lemma walk_dOn_le {U : Set ℂ} {p : ι → ℝ → ℂ} {V : Set ι}
    (hp : ∀ i ∈ V, IsPiecewiseC1Path (p i) (p i 0) (p i 1))
    (hU : ∀ i ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, p i t ∈ U) {i j : ι} (hi : i ∈ V)
    (w : (meetGraph p V).Walk i j) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      lfppDOn ξ f U (p i s) (p j t) ≤ (w.support.map fun k => lfppLen ξ f (p k)).sum := by
  induction w with
  | nil =>
    intro s hs t ht
    simpa using dOn_pt_le (ξ := ξ) (f := f) (hp _ hi) (hU _ hi) hs ht
  | @cons i k j h w ih =>
    intro s hs t ht
    have hk : k ∈ V := support_mem hi (SimpleGraph.Walk.cons h w) k (by simp)
    have hm : Meet p i k := by
      rw [meetGraph, SimpleGraph.fromRel_adj] at h
      rcases h.2 with h | h
      · exact h.2.2
      · obtain ⟨a, ha, b, hb, e⟩ := h.2.2; exact ⟨b, hb, a, ha, e.symm⟩
    obtain ⟨a, ha, b, hb, e⟩ := hm
    rw [SimpleGraph.Walk.support_cons, List.map_cons, List.sum_cons]
    calc lfppDOn ξ f U (p i s) (p j t)
        ≤ lfppDOn ξ f U (p i s) (p i a) + lfppDOn ξ f U (p i a) (p j t) :=
          lfppDOn_triangle _ _ _
      _ ≤ _ := by
          refine add_le_add (dOn_pt_le (hp _ hi) (hU _ hi) hs ha) ?_
          rw [e]; exact ih hk b hb t ht

/-- **Gluing a connected family of crossings**: a point of `p i` and a point of `p j` are at
`U`-distance at most `Σ_{k ∈ V} L(p k)` when `i` and `j` are joined in the meet graph on `V`. -/
theorem reach_dOn_le_sum [DecidableEq ι] {U : Set ℂ} {p : ι → ℝ → ℂ} {V : Finset ι}
    (hp : ∀ i ∈ V, IsPiecewiseC1Path (p i) (p i 0) (p i 1))
    (hU : ∀ i ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, p i t ∈ U) {i j : ι} (hi : i ∈ V)
    (hij : (meetGraph p (V : Set ι)).Reachable i j) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    lfppDOn ξ f U (p i s) (p j t) ≤ ∑ k ∈ V, lfppLen ξ f (p k) := by
  obtain ⟨w⟩ := hij
  set q := w.toPath
  refine (walk_dOn_le (ξ := ξ) (f := f) (fun i hi => hp i hi) (fun i hi => hU i hi)
    (Finset.mem_coe.2 hi) q.1 s hs t ht).trans ?_
  rw [← List.sum_toFinset _ q.2.support_nodup]
  refine Finset.sum_le_sum_of_subset fun k hk => ?_
  exact Finset.mem_coe.1 (support_mem (Finset.mem_coe.2 hi) q.1 k (List.mem_toFinset.1 hk))

/-- consecutive meeting crossings are joined in the meet graph -/
lemma reach_of_chain {p : ι → ℝ → ℂ} {V : Set ι} (e : ℕ → ι) (N : ℕ) (hV : ∀ k ≤ N, e k ∈ V)
    (hm : ∀ k < N, Meet p (e k) (e (k + 1))) : (meetGraph p V).Reachable (e 0) (e N) := by
  induction N with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ N ih =>
    refine (ih (fun k hk => hV k (by omega)) fun k hk => hm k (by omega)).trans ?_
    by_cases he : e N = e (N + 1)
    · rw [he]
    · refine SimpleGraph.Adj.reachable ?_
      rw [meetGraph, SimpleGraph.fromRel_adj]
      exact ⟨he, Or.inl ⟨hV N (by omega), hV (N + 1) le_rfl, hm N (by omega)⟩⟩

/-! ### Meeting a connected set -/

lemma isPathConnected_image {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) :
    IsPathConnected (p '' Icc 0 1) :=
  ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.2 zero_le_one)).image' hp

/-- the union of a chain of pairwise meeting crossings is path connected -/
lemma isPathConnected_chain {p : ι → ℝ → ℂ} (hp : ∀ i, ContinuousOn (p i) (Icc 0 1))
    (e : ℕ → ι) (N : ℕ) (hm : ∀ k < N, Meet p (e k) (e (k + 1))) :
    IsPathConnected (⋃ k ∈ Finset.range (N + 1), p (e k) '' Icc 0 1) := by
  induction N with
  | zero => simpa using isPathConnected_image (hp (e 0))
  | succ N ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    refine (ih fun k hk => hm k (by omega)).union (isPathConnected_image (hp _)) ?_
    obtain ⟨a, ha, b, hb, eab⟩ := hm N (by omega)
    exact ⟨p (e N) a, mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self N)) ⟨a, ha, rfl⟩,
      ⟨b, hb, eab.symm⟩⟩

/-- **A top–bottom crossing meets a left–right connected set** of the same rectangle. -/
lemma meet_of_joined {F : Set ℂ} {x₀ x₁ y₀ y₁ : ℝ} {a b : ℂ} (hF : IsPathConnected F)
    (ha : a ∈ F) (hb : b ∈ F) (hFR : F ⊆ RectCross.rect x₀ x₁ y₀ y₁) (har : a.re = x₀)
    (hbr : b.re = x₁) {c : ℝ → ℂ} (hc : ContinuousOn c (Icc 0 1))
    (hcR : MapsTo c (Icc 0 1) (RectCross.rect x₀ x₁ y₀ y₁)) (hc0 : (c 0).im = y₁)
    (hc1 : (c 1).im = y₀) : ∃ t ∈ Icc (0 : ℝ) 1, c t ∈ F := by
  set γ := (hF.joinedIn a ha b hb).somePath
  have hmem : ∀ t, γ.extend t ∈ F := fun t => by
    rw [Path.extend]; exact (hF.joinedIn a ha b hb).somePath_mem _
  obtain ⟨s, -, t, ht, e⟩ := RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ γ.extend c
    γ.continuous_extend.continuousOn hc (fun t _ => hFR (hmem t)) hcR
    (by rw [Path.extend_zero]; exact har) (by rw [Path.extend_one]; exact hbr) hc0 hc1
  exact ⟨t, ht, e ▸ hmem s⟩

/-- **A left–right crossing meets a bottom–top connected set** of the same rectangle. -/
lemma meet_of_joined' {F : Set ℂ} {x₀ x₁ y₀ y₁ : ℝ} {a b : ℂ} (hF : IsPathConnected F)
    (ha : a ∈ F) (hb : b ∈ F) (hFR : F ⊆ RectCross.rect x₀ x₁ y₀ y₁) (har : a.im = y₀)
    (hbr : b.im = y₁) {c : ℝ → ℂ} (hc : ContinuousOn c (Icc 0 1))
    (hcR : MapsTo c (Icc 0 1) (RectCross.rect x₀ x₁ y₀ y₁)) (hc0 : (c 0).re = x₀)
    (hc1 : (c 1).re = x₁) : ∃ t ∈ Icc (0 : ℝ) 1, c t ∈ F := by
  set γ := (hF.joinedIn b hb a ha).somePath
  have hmem : ∀ t, γ.extend t ∈ F := fun t => by
    rw [Path.extend]; exact (hF.joinedIn b hb a ha).somePath_mem _
  obtain ⟨t, ht, s, -, e⟩ := RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ c γ.extend
    hc γ.continuous_extend.continuousOn hcR (fun t _ => hFR (hmem t)) hc0 hc1
    (by rw [Path.extend_zero]; exact hbr) (by rw [Path.extend_one]; exact har)
  exact ⟨t, ht, e ▸ hmem s⟩

end T20E
end DDDF
end LQGMetric
