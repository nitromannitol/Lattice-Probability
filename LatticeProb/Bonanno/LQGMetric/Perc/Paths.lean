/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Paths at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: in mem_percChainsFrom the case split on the tail is done on the goal (the rfl-substitution after it times out at whnf), and the linter constructorNameAsVariable, which times out on this file, is disabled after the imports. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.constructorNameAsVariable false

/-!
# `*`-paths of sites: simple paths and their number

* `percBadTB_exists_list`: a top–bottom `*`-crossing of bad sites of the `K × L` rectangle
  contains a *simple* one: a duplicate-free list of bad grid sites, `*`-adjacent in
  succession, starting in the top row, of length at least `L`.
* `percChainsFrom x n`: an explicit finset containing every `*`-path `x :: t` with `n` steps;
  `card_percChainsFrom_le`: it has at most `8 ^ n` elements ("8 choices for each step of the
  path", Ding–Gwynne arXiv:1807.01072, proof of Lemma 3.11, `metric-comparison-final.tex`
  line 1272; Ding–Zhang–Zeitouni arXiv:1807.00422, `LBM_LGDarXiv.tex` line 1010, "at most
  `4(2K+1) × 8^ℓ` such sequences").

The simple path is obtained from mathlib's `SimpleGraph.Walk.bypass`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

lemma percAdjK_symm {x y : ℤ × ℤ} (h : PercAdjK x y) : PercAdjK y x := by
  simp only [PercAdjK] at h ⊢; omega

section SimplePath

variable {K L : ℤ} {good : ℤ × ℤ → Prop}

/-- The graph of `*`-adjacent bad grid sites. -/
def percBadGraph (K L : ℤ) (good : ℤ × ℤ → Prop) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel (PercBadStep K L good)

lemma percBadGraph_adj {x y : ℤ × ℤ} (h : (percBadGraph K L good).Adj x y) :
    PercBadStep K L good x y := by
  obtain ⟨-, h | h⟩ := h
  · exact h
  · obtain ⟨a, b, c, d, e⟩ := h
    exact ⟨c, d, a, b, percAdjK_symm e⟩

lemma percBadGraph_walk_mem {u v : ℤ × ℤ} (q : (percBadGraph K L good).Walk u v)
    (hu : percInGrid K L u ∧ ¬ good u) :
    ∀ y ∈ q.support, percInGrid K L y ∧ ¬ good y := by
  induction q with
  | nil => intro y hy; simp at hy; exact hy ▸ hu
  | @cons a b c h q ih =>
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hu
    · have := percBadGraph_adj h
      exact ih ⟨this.2.2.1, this.2.2.2.1⟩ y hy

lemma percBadGraph_walk_length {u v : ℤ × ℤ} (q : (percBadGraph K L good).Walk u v) :
    u.2 - v.2 ≤ q.length := by
  induction q with
  | nil => simp
  | @cons a b c h q ih =>
    have := (percBadGraph_adj h).2.2.2.2
    simp only [PercAdjK] at this
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

lemma percBadGraph_walk_chain {u v : ℤ × ℤ} (q : (percBadGraph K L good).Walk u v) :
    q.support.IsChain PercAdjK :=
  q.isChain_adj_support.imp fun _ _ h => (percBadGraph_adj h).2.2.2.2

/-- A top–bottom `*`-crossing of bad sites contains a simple one of length at least `L`. -/
theorem percBadTB_exists_list (h : PercBadTB K L good) :
    ∃ l : List (ℤ × ℤ), l.Nodup ∧ l.IsChain PercAdjK ∧
      (∃ x : ℤ × ℤ, l.head? = some x ∧ x.2 = L - 1) ∧
      (∀ y ∈ l, percInGrid K L y ∧ ¬ good y) ∧ L ≤ l.length := by
  obtain ⟨a, b, ha, hb, hagrid, habad, hab⟩ := h
  have hr : (percBadGraph K L good).Reachable a b := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.ReflTransGen.mono (r := PercBadStep K L good)
      (fun x y (hxy : PercBadStep K L good x y) => (⟨?_, Or.inl hxy⟩ :
        (percBadGraph K L good).Adj x y)) a b hab
    have := hxy.2.2.2.2
    simp only [PercAdjK] at this
    intro hxy'
    rw [hxy'] at this
    omega
  obtain ⟨p⟩ := hr
  set q := p.bypass
  refine ⟨q.support, (p.bypass_isPath).support_nodup, percBadGraph_walk_chain q,
    ⟨a, ?_, ha⟩, percBadGraph_walk_mem q ⟨hagrid, habad⟩, ?_⟩
  · cases q <;> simp
  · have := percBadGraph_walk_length q
    rw [SimpleGraph.Walk.length_support]
    push_cast
    omega

end SimplePath

section Counting

/-- The eight `*`-neighbours of a site. -/
def percNbrs (x : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1).erase (0, 0)).image
    fun d => (x.1 + d.1, x.2 + d.2)

lemma card_percNbrs_le (x : ℤ × ℤ) : (percNbrs x).card ≤ 8 := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_erase_of_mem (by simp), Finset.card_product]
  simp

lemma mem_percNbrs {x y : ℤ × ℤ} (h : PercAdjK x y) : y ∈ percNbrs x := by
  simp only [PercAdjK] at h
  refine Finset.mem_image.mpr ⟨(y.1 - x.1, y.2 - x.2), ?_, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq, Prod.mk.injEq]
    omega
  · ext <;> simp

/-- A finset containing all `*`-paths with `n` steps started at `x`. -/
def percChainsFrom : ℤ × ℤ → ℕ → Finset (List (ℤ × ℤ))
  | x, 0 => {[x]}
  | x, n + 1 => (percNbrs x).biUnion fun y => (percChainsFrom y n).image (List.cons x)

lemma card_percChainsFrom_le (x : ℤ × ℤ) (n : ℕ) : (percChainsFrom x n).card ≤ 8 ^ n := by
  induction n generalizing x with
  | zero => simp [percChainsFrom]
  | succ n ih =>
    simp only [percChainsFrom]
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ y ∈ percNbrs x, ((percChainsFrom y n).image (List.cons x)).card
        ≤ ∑ _y ∈ percNbrs x, 8 ^ n :=
          Finset.sum_le_sum fun y _ => (Finset.card_image_le).trans (ih y)
      _ = (percNbrs x).card * 8 ^ n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 8 * 8 ^ n := Nat.mul_le_mul_right _ (card_percNbrs_le x)
      _ = 8 ^ (n + 1) := (pow_succ' 8 n).symm

lemma mem_percChainsFrom (n : ℕ) : ∀ (x : ℤ × ℤ) (t : List (ℤ × ℤ)),
    (x :: t).IsChain PercAdjK → t.length = n → x :: t ∈ percChainsFrom x n := by
  induction n with
  | zero =>
    intro x t _ ht
    rw [List.length_eq_zero_iff] at ht
    subst ht
    simp [percChainsFrom]
  | succ n ih =>
    intro x t hc ht
    cases t with
    | nil => simp at ht
    | cons y t' =>
      rw [List.isChain_cons_cons] at hc
      simp only [percChainsFrom, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨y, mem_percNbrs hc.1, y :: t', ih y t' hc.2 (by simpa using ht), rfl⟩

lemma length_of_mem_percChainsFrom (n : ℕ) : ∀ (x : ℤ × ℤ) (l : List (ℤ × ℤ)),
    l ∈ percChainsFrom x n → l.length = n + 1 := by
  induction n with
  | zero => intro x l hl; simp [percChainsFrom] at hl; simp [hl]
  | succ n ih =>
    intro x l hl
    simp only [percChainsFrom, Finset.mem_biUnion, Finset.mem_image] at hl
    obtain ⟨y, -, t, ht, rfl⟩ := hl
    simp [ih y t ht]

end Counting

end LQGMetric
