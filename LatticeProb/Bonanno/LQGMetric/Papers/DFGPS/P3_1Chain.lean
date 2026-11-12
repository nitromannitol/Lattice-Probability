/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1Chain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Chain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 3.1,
T:1522–1568.

* `le_setDistIn_of_cross` (Step 1, T:1537–1540): if every point `x ∈ A` lies in `B̄_r(w)` for
  some `(w, r)` with `B ∩ B_{2r}(w) = ∅`, then `D(A, B; V)` is at least the infimum of the
  distances `D(∂B_r(w), ∂B_{2r}(w))`: each path from `A` to `B` crosses from `∂B_r(w)` to
  `∂B_{2r}(w)`.
* `chain_bound` (Step 2, T:1549–1553, "the total number of such circles is at most … so by the
  triangle inequality"): if a connected set `S` is covered by finitely many closed sets `C_i`,
  `i ∈ I`, on each of which a function `d` with the triangle inequality is at most `L`, then
  `d(x, y) ≤ (#I + 1) L` for `x, y ∈ S`. The paper leaves this chaining step implicit; the
  proof here (grow the set of indices reachable from `x`; it stabilizes after `≤ #I` steps and
  then covers `S` by connectedness) is an own elementary argument.
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

namespace P31

/-- **Crossing bound** (T:1537–1540). -/
lemma le_setDistIn_of_cross (D : ContMetric) {A B V : Set ℂ} {L : ℝ≥0∞}
    (H : ∀ x ∈ A, ∃ w : ℂ, ∃ r : ℝ, ‖x - w‖ ≤ r ∧ (∀ y ∈ B, 2 * r ≤ ‖y - w‖) ∧
      L ≤ setDist D (Metric.sphere w r) (Metric.sphere w (2 * r))) :
    L ≤ setDistIn D A B V := by
  by_contra hlt
  push Not at hlt
  obtain ⟨P, hP, hP0, hP1, hPV, hlen⟩ := exists_path_of_setDistIn_lt D hlt
  obtain ⟨w, r, hx, hy, hL⟩ := H _ hP0
  have hg : ContinuousOn (fun t => ‖P t - w‖) (Icc 0 1) :=
    (hP.sub continuousOn_const).norm
  have h1 := hy _ hP1
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  obtain ⟨t₁, ht₁, e₁⟩ := intermediate_value_Icc zero_le_one hg
    (show r ∈ Icc ‖P 0 - w‖ ‖P 1 - w‖ from ⟨hx, by linarith⟩)
  obtain ⟨t₂, ht₂, e₂⟩ := intermediate_value_Icc zero_le_one hg
    (show 2 * r ∈ Icc ‖P 0 - w‖ ‖P 1 - w‖ from ⟨by linarith, h1⟩)
  have hs : setDist D (Metric.sphere w r) (Metric.sphere w (2 * r)) ≤
      ENNReal.ofReal (D.1 (P t₁, P t₂)) := by
    rw [L32.setDist_eq_iInf']
    exact iInf₂_le_of_le (P t₁) (by simpa [dist_eq_norm] using e₁)
      (iInf₂_le_of_le (P t₂) (by simpa [dist_eq_norm] using e₂) le_rfl)
  have hi : ENNReal.ofReal (D.1 (P t₁, P t₂)) ≤ D.internal V (P t₁) (P t₂) := by
    rw [← ContMetric.edist_pt]
    exact edist_le_internalEDist _ _ _
  have := (hL.trans hs).trans (hi.trans (internal_le_len_of_path D hP hPV ht₁ ht₂))
  exact absurd (this.trans_lt hlen) (lt_irrefl _)

/-- the strict chain of finsets: if no step stabilizes, the sizes grow linearly -/
lemma card_ge_of_strict {ι : Type*} (G : ℕ → Finset ι) (hmono : ∀ n, G n ⊆ G (n + 1))
    (N : ℕ) (hne : ∀ n < N, G n ≠ G (n + 1)) : ∀ n ≤ N, n ≤ (G n).card := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 : (G n).card < (G (n + 1)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hmono n, hne n (by omega)⟩)
    omega

/-- **Chaining** (T:1549–1553). -/
lemma chain_bound {ι : Type*} (I : Finset ι) {S : Set ℂ} (hS : IsPreconnected S)
    (C : ι → Set ℂ) (hC : ∀ i, IsClosed (C i)) (d : ℂ → ℂ → ℝ≥0∞)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) (L : ℝ≥0∞)
    (hcov : ∀ p ∈ S, ∃ i ∈ I, p ∈ C i)
    (hdiam : ∀ i ∈ I, ∀ p ∈ C i ∩ S, ∀ q ∈ C i ∩ S, d p q ≤ L)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) (hxx : d x x = 0) :
    d x y ≤ ((I.card : ℝ≥0∞) + 1) * L := by
  classical
  set G : ℕ → Finset ι := fun n => I.filter fun i => ∃ p ∈ C i ∩ S, d x p ≤ n * L with hG
  have hstep : ∀ n, ∀ i ∈ G n, ∀ q ∈ C i ∩ S, d x q ≤ ((n : ℝ≥0∞) + 1) * L := by
    intro n i hi q hq
    obtain ⟨hiI, p, hp, hpL⟩ := Finset.mem_filter.1 hi
    calc d x q ≤ d x p + d p q := htri _ _ _
      _ ≤ n * L + L := add_le_add hpL (hdiam i hiI p hp q hq)
      _ = ((n : ℝ≥0∞) + 1) * L := by rw [add_mul, one_mul]
  have hmono : ∀ n, G n ⊆ G (n + 1) := by
    intro n i hi
    obtain ⟨hiI, p, hp, hpL⟩ := Finset.mem_filter.1 hi
    refine Finset.mem_filter.2 ⟨hiI, p, hp, hpL.trans ?_⟩
    gcongr
    exact_mod_cast Nat.le_succ n
  obtain ⟨n, hnN, hn⟩ : ∃ n ≤ I.card, G n = G (n + 1) := by
    by_contra hcon
    push Not at hcon
    have := card_ge_of_strict G hmono (I.card + 1) (fun n hn => hcon n (by omega))
      (I.card + 1) le_rfl
    have h2 : (G (I.card + 1)).card ≤ I.card := Finset.card_filter_le _ _
    omega
  set t : Set ℂ := ⋃ i ∈ G n, C i
  set t' : Set ℂ := ⋃ i ∈ I \ G n, C i
  have ht : IsClosed t := isClosed_biUnion_finset fun i _ => hC i
  have ht' : IsClosed t' := isClosed_biUnion_finset fun i _ => hC i
  have hcov' : S ⊆ t ∪ t' := by
    intro p hp
    obtain ⟨i, hiI, hpi⟩ := hcov p hp
    by_cases hiG : i ∈ G n
    · exact Or.inl (mem_biUnion hiG hpi)
    · exact Or.inr (mem_biUnion (Finset.mem_sdiff.2 ⟨hiI, hiG⟩) hpi)
  have hxt : (S ∩ t).Nonempty := by
    obtain ⟨i, hiI, hxi⟩ := hcov x hx
    exact ⟨x, hx, mem_biUnion (Finset.mem_filter.2 ⟨hiI, x, ⟨hxi, hx⟩, by simp [hxx]⟩) hxi⟩
  have hyt : y ∈ t := by
    by_contra hyt
    have hyt' : y ∈ t' := (hcov' hy).resolve_left hyt
    obtain ⟨p, hpS, hpt, hpt'⟩ := isPreconnected_closed_iff.1 hS t t' ht ht' hcov' hxt
      ⟨y, hy, hyt'⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hpt
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.1 hpt'
    obtain ⟨hjI, hjG⟩ := Finset.mem_sdiff.1 hj
    apply hjG
    rw [hn]
    refine Finset.mem_filter.2 ⟨hjI, p, ⟨hpj, hpS⟩, ?_⟩
    have := hstep n i hi p ⟨hpi, hpS⟩
    exact_mod_cast this
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hyt
  refine (hstep n i hi y ⟨hyi, hy⟩).trans ?_
  gcongr

end P31

end LQGMetric.DFGPS
