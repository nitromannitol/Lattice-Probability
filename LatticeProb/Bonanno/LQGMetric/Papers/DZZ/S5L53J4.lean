/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E4
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# DZZ Lemma 5.3, node 3: chains of open boxes inside the good cluster

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1953–1966, used at l. 2504–2514): "for each
`L ∈ 𝕃'` we denote by `𝖡_1, …, 𝖡_ℓ` with `ℓ ≤ K²` the sequence of pre-fast boxes … from `L`
to `𝕃`", and along it the hitting points are chained box by box. Here the boxes are the sites
of a `4`-connected cluster `C ⊆ Box` (a finite set of boxes) of open boxes
(`l53_perc_cluster`); each box `x` has
a boundary `Bd x`, adjacent boxes share an interface `I x y ⊆ Bd x ∩ Bd y` of mass `≥ c`, and
open boxes satisfy the hypothesis `hopen` of `l53_open_chain` (S5L53E4).

`l53_cluster_chain`: for any two boxes `p, q` of `C` and any `Λ ⊆ Bd q` of mass `≥ b` there
is a start point `z₀ ∈ Bd p` with small bad set and an `R`-chain of at most `#Box - 1`
pieces from `z₀` to `Λ`, i.e. exactly the inputs `hbad`, `hchain` of `l53_desirable_of_chains`
(S5L53E5). The box path is a simple path of the cluster graph (`Walk.bypass`), hence has at
most `#Box` boxes (DZZ's `ℓ ≤ K²` for the `K²` boxes of a cell).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- The graph of `4`-adjacent sites of `C`. -/
def l53ClusterGraph (C : Set (ℤ × ℤ)) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel (PercStepIn C PercAdj4)

lemma l53ClusterGraph_adj {C : Set (ℤ × ℤ)} {x y : ℤ × ℤ} (h : (l53ClusterGraph C).Adj x y) :
    x ∈ C ∧ y ∈ C ∧ PercAdj4 x y := by
  obtain ⟨-, h | h⟩ := h
  · exact h
  · exact ⟨h.2.1, h.1, percAdj4_symm h.2.2⟩

lemma l53ClusterGraph_walk_mem {C : Set (ℤ × ℤ)} {u v : ℤ × ℤ}
    (w : (l53ClusterGraph C).Walk u v) (hu : u ∈ C) : ∀ y ∈ w.support, y ∈ C := by
  induction w with
  | nil => intro y hy; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
           exact hy ▸ hu
  | @cons a b c h w ih =>
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hu
    · exact ih (l53ClusterGraph_adj h).2.1 y hy

/-- **Chains of open boxes inside the good cluster** (DZZ l. 1953–1966). -/
theorem l53_cluster_chain {α : Type*} [MeasurableSpace α] (ν : Measure α) (R : α → α → Prop)
    (Box : Finset (ℤ × ℤ)) (C : Set (ℤ × ℤ)) (hCbox : ∀ z ∈ C, z ∈ Box)
    (hCc : ∀ x ∈ C, ∀ y ∈ C, Relation.ReflTransGen (PercStepIn C PercAdj4) x y)
    (Bd : ℤ × ℤ → Set α) (I : ℤ × ℤ → ℤ × ℤ → Set α) {a b c : ℝ≥0∞} (ha : a ≠ ⊤)
    (hc : b + a ≤ c)
    (hI : ∀ x ∈ C, ∀ y ∈ C, PercAdj4 x y → I x y ⊆ Bd x ∩ Bd y)
    (hIc : ∀ x ∈ C, ∀ y ∈ C, PercAdj4 x y → c ≤ ν (I x y))
    (hBdc : ∀ x ∈ C, c ≤ ν (Bd x))
    (hopen : ∀ x ∈ C, ∀ Λ ⊆ Bd x, b ≤ ν Λ → ∃ z ∈ Λ, ν {z' ∈ Bd x | ¬ R z z'} ≤ a) :
    ∀ p ∈ C, ∀ q ∈ C, ∀ Λ ⊆ Bd q, b ≤ ν Λ → ∃ z₀ ∈ Bd p, ν {z' ∈ Bd p | ¬ R z₀ z'} ≤ a ∧
      ∃ n < Box.card, ∃ y : ℕ → α, y 0 = z₀ ∧ y n ∈ Λ ∧ ∀ k < n, R (y (k + 1)) (y k) := by
  classical
  intro p hp q hq Λ hΛ hb
  have hr : (l53ClusterGraph C).Reachable p q := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.ReflTransGen.mono (r := PercStepIn C PercAdj4)
      (fun x y (hxy : PercStepIn C PercAdj4 x y) => (⟨?_, Or.inl hxy⟩ :
        (l53ClusterGraph C).Adj x y)) p q (hCc p hp q hq)
    have := hxy.2.2
    intro hxy'
    rw [hxy'] at this
    simp only [PercAdj4] at this
    omega
  obtain ⟨w⟩ := hr
  set w' := w.bypass with hw'
  have hmem : ∀ y ∈ w'.support, y ∈ C := l53ClusterGraph_walk_mem w' hp
  set n := w'.length with hn
  set s : ℕ → ℤ × ℤ := fun k => w'.getVert k with hs
  have hsC : ∀ k, s k ∈ C := fun k => hmem _ (w'.getVert_mem_support k)
  have hsn : ∀ k, n ≤ k → s k = q := fun k hk => w'.getVert_of_length_le hk
  have hadj : ∀ k < n, PercAdj4 (s k) (s (k + 1)) := fun k hk =>
    (l53ClusterGraph_adj (w'.adj_getVert_succ hk)).2.2
  -- the length bound: a simple path in `Box`
  have hlen : n < Box.card := by
    have hsub : w'.support.toFinset ⊆ Box := fun y hy =>
      hCbox y (hmem y (List.mem_toFinset.mp hy))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (w.bypass_isPath).support_nodup,
      SimpleGraph.Walk.length_support] at hcard
    have : n = w.bypass.length := rfl
    omega
  set I' : ℕ → Set α := fun j => if j < n then I (s j) (s (j + 1)) else Bd (s j) with hI'
  have hI'1 : ∀ j, I' j ⊆ Bd (s j) ∩ Bd (s (j + 1)) := by
    intro j
    by_cases hj : j < n
    · simp only [hI', hj, ↓reduceIte]
      exact hI _ (hsC j) _ (hsC (j + 1)) (hadj j hj)
    · simp only [hI', hj, ↓reduceIte]
      rw [hsn (j + 1) (by omega), ← hsn j (by omega), inter_self]
  have hI'2 : ∀ j, c ≤ ν (I' j) := by
    intro j
    by_cases hj : j < n
    · simp only [hI', hj, ↓reduceIte]
      exact hIc _ (hsC j) _ (hsC (j + 1)) (hadj j hj)
    · simp only [hI', hj, ↓reduceIte]
      exact hBdc _ (hsC j)
  have hΛ' : Λ ⊆ Bd (s n) := by rw [hsn n le_rfl]; exact hΛ
  obtain ⟨z₀, hz₀, hz₀a, y, hy0, hyn, hyR⟩ :=
    l53_open_chain ν R (fun j => Bd (s j)) I' ha hc hI'1 hI'2
      (fun j => hopen _ (hsC j)) n Λ hΛ' hb
  have hs0 : s 0 = p := w'.getVert_zero
  rw [hs0] at hz₀ hz₀a
  exact ⟨z₀, hz₀, hz₀a, n, hlen, y, hy0, hyn, hyR⟩

end LQGMetric.DZZ
