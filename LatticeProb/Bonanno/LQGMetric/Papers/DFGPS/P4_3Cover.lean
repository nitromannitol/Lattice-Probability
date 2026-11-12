/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Cover at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3, Step 2: covering by a maximal chain (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 2 (T:2699–2708): the times `τ_k` ("the first time after the exit time of `P` from
`B_{4ε^{1−ζ}𝕣}(P(τ_{k−1}))` at which `P(t) ∈ B_{ε𝕣}(∂𝓑_s)`") give a covering of
`P ∩ B_{ε𝕣}(∂𝓑_s)` by the balls `B_{4ε^{1−ζ}𝕣}(P(τ_k))`. We replace the inductive first-hitting
times (which need not be attained for an open neighbourhood) by a *chain* — a finite set of times
in `T` whose consecutive elements have images `≥ r` apart — of maximal cardinality: if the
cardinality of chains is bounded, a maximal chain covers `P(T)` by balls of radius `r` (a point
not covered could be inserted). Own elementary reformulation (DEV-DF-A10-4).
-/

noncomputable section

open Set Metric Finset

namespace LQGMetric.DFGPS
namespace P43

/-- `S` is an `r`-chain for `f`: consecutive elements of `S` have images `≥ r` apart -/
def IsChain (f : ℝ → ℂ) (r : ℝ) (S : Finset ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ c ∈ S, ¬ (a < c ∧ c < b)) → r ≤ ‖f b - f a‖

lemma isChain_empty (f : ℝ → ℂ) (r : ℝ) : IsChain f r ∅ := by
  intro a ha; simp at ha

/-- inserting a time whose image is `≥ r` away from all images of the chain -/
lemma IsChain.insert {f : ℝ → ℂ} {r : ℝ} {S : Finset ℝ} (hS : IsChain f r S) {t : ℝ}
    (ht : ∀ a ∈ S, r ≤ ‖f t - f a‖) : IsChain f r (insert t S) := by
  intro a ha b hb hab hcons
  rcases Finset.mem_insert.1 ha with rfl | ha'
  · rcases Finset.mem_insert.1 hb with rfl | hb'
    · exact absurd hab (lt_irrefl _)
    · have := ht b hb'; rwa [norm_sub_rev] at this
  · rcases Finset.mem_insert.1 hb with rfl | hb'
    · exact ht a ha'
    · exact hS a ha' b hb' hab fun c hc => hcons c (Finset.mem_insert_of_mem hc)

/-- **a maximal chain covers** (T:2704–2706): if every `r`-chain in `T` has at most `N`
elements (`r > 0`), some `r`-chain `S ⊆ T` has `f(T) ⊆ ⋃_{a∈S} B_r(f(a))`. -/
theorem exists_covering_chain {f : ℝ → ℂ} {r : ℝ} (hr : 0 < r) {T : Set ℝ} {N : ℕ}
    (hN : ∀ S : Finset ℝ, ↑S ⊆ T → IsChain f r S → S.card ≤ N) :
    ∃ S : Finset ℝ, ↑S ⊆ T ∧ IsChain f r S ∧ ∀ t ∈ T, ∃ a ∈ S, f t ∈ ball (f a) r := by
  classical
  set A : Set ℕ := {n | ∃ S : Finset ℝ, ↑S ⊆ T ∧ IsChain f r S ∧ S.card = n} with hA
  have hA0 : (0 : ℕ) ∈ A := ⟨∅, by simp, isChain_empty f r, rfl⟩
  have hAb : BddAbove A := ⟨N, fun n ⟨S, hST, hS, hn⟩ => hn ▸ hN S hST hS⟩
  obtain ⟨S, hST, hS, hcard⟩ := Nat.sSup_mem ⟨0, hA0⟩ hAb
  refine ⟨S, hST, hS, fun t ht => ?_⟩
  by_contra hno
  push Not at hno
  have hfar : ∀ a ∈ S, r ≤ ‖f t - f a‖ := fun a ha => by
    have := hno a ha
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  have htS : t ∉ S := fun h => by
    have := hfar t h; rw [sub_self, norm_zero] at this; linarith
  have hmem : (insert t S).card ∈ A :=
    ⟨insert t S, by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact ht
      · exact hST hx', hS.insert hfar, rfl⟩
  have := le_csSup hAb hmem
  rw [Finset.card_insert_of_notMem htS, hcard] at this
  omega

/-- the `k`-th smallest element of `S` (`0` past the end) -/
def chainSeq (S : Finset ℝ) (k : ℕ) : ℝ :=
  if h : k < S.card then S.orderEmbOfFin rfl ⟨k, h⟩ else 0

lemma chainSeq_mem {S : Finset ℝ} {k : ℕ} (hk : k < S.card) : chainSeq S k ∈ S := by
  rw [chainSeq, dif_pos hk]; exact S.orderEmbOfFin_mem rfl _

lemma chainSeq_lt {S : Finset ℝ} {j k : ℕ} (hjk : j < k) (hk : k < S.card) :
    chainSeq S j < chainSeq S k := by
  rw [chainSeq, chainSeq, dif_pos (hjk.trans hk), dif_pos hk]
  exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hjk)

/-- consecutive elements of the sorted chain have images `≥ r` apart -/
lemma IsChain.seq_sep {f : ℝ → ℂ} {r : ℝ} {S : Finset ℝ} (hS : IsChain f r S) {k : ℕ}
    (hk : k + 1 < S.card) : r ≤ ‖f (chainSeq S (k + 1)) - f (chainSeq S k)‖ := by
  refine hS _ (chainSeq_mem (by omega)) _ (chainSeq_mem hk) (chainSeq_lt (by omega) hk) ?_
  rintro c hc ⟨h1, h2⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, S.orderEmbOfFin rfl j = c := by
    have : c ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hc
    exact this
  have hjc : chainSeq S j = c := by rw [chainSeq, dif_pos j.2]; exact hj
  rw [← hjc] at h1 h2
  rcases lt_trichotomy (j : ℕ) k with h | h | h
  · exact absurd h1 (not_lt.2 (chainSeq_lt h (by omega)).le)
  · rw [h] at h1; exact lt_irrefl _ h1
  · rcases lt_trichotomy (j : ℕ) (k + 1) with h' | h' | h'
    · omega
    · rw [h'] at h2; exact lt_irrefl _ h2
    · exact absurd h2 (not_lt.2 (chainSeq_lt h' j.2).le)

end P43
end LQGMetric.DFGPS
