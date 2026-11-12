/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12S1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Enc

/-!
# DZZ Lemma 3.12: the iteration of the path surgery (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1436–1460 (proof of
(Eq.sequence-good-cells)).

* `l312Bad ε l` = `ψ(𝒞)`: the cells of `l` with a neighbour in the sequence of side `< ε s_𝖢`.
* `L312Progress ε l l'`: DZZ's alternative (i) `|ψ(𝒞_{i+1})| ≤ |ψ(𝒞_i)| − 1` or
  (ii) `|ψ(𝒞_{i+1})| ≤ |ψ(𝒞_i)|` and `q(𝒞_{i+1}) ≥ 2 q(𝒞_i)` (`q` = largest side in `ψ`).
* `isGoodSeq_of_bad_empty`: a `Neighbour`-chain with `ψ = ∅` is a good sequence.
* **`l312_iterate`**: DZZ's counting (l. 1455–1458): if every sequence with `ψ ≠ ∅` can be
  improved as in the claim, adding at most `K` cells, and all cells have level `≤ M`, then one
  reaches `ψ = ∅` adding at most `K (|l| (M + 1) + M)` cells (potential `|ψ| (M+1) + min level`;
  DZZ: "(ii) cannot occur more than `C_mc log₂ δ⁻¹` times in a row").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

open Classical in
/-- `ψ(𝒞)` (DZZ l. 1440): the bad cells of the sequence `l`. -/
def l312Bad (ε : ℝ) (l : List DyBox) : Finset DyBox :=
  l.toFinset.filter fun c => ∃ c', ([c, c'] <:+: l ∨ [c', c] <:+: l) ∧ c'.side < ε * c.side

/-- DZZ's claim (i) or (ii) (l. 1449–1453) for the step `l ↦ l'`. -/
def L312Progress (ε : ℝ) (l l' : List DyBox) : Prop :=
  (l312Bad ε l').card + 1 ≤ (l312Bad ε l).card ∨
    ((l312Bad ε l').card ≤ (l312Bad ε l).card ∧
      ∃ c' ∈ l312Bad ε l', ∀ c ∈ l312Bad ε l, 2 * c.side ≤ c'.side)

lemma isGoodSeq_of_pairs {ε : ℝ} (hε : 0 < ε) :
    ∀ l : List DyBox, l.IsChain Neighbour →
      (∀ c c', [c, c'] <:+: l → ε * c.side ≤ c'.side ∧ ε * c'.side ≤ c.side) → IsGoodSeq ε l
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | a :: b :: t, hch, hp => by
    rw [List.isChain_cons_cons] at hch
    unfold IsGoodSeq
    rw [List.isChain_cons_cons]
    have hab := hp a b (List.prefix_append [a, b] t).isInfix
    refine ⟨⟨hch.1, hab.1, by rw [le_div_iff₀ hε, mul_comm]; exact hab.2⟩, ?_⟩
    exact isGoodSeq_of_pairs hε (b :: t) hch.2 fun c c' h =>
      hp c c' (h.trans (List.suffix_cons a _).isInfix)

lemma infix_mem_left {c c' : DyBox} {l : List DyBox} (h : [c, c'] <:+: l) : c ∈ l :=
  h.subset (by simp)

lemma infix_mem_right {c c' : DyBox} {l : List DyBox} (h : [c, c'] <:+: l) : c' ∈ l :=
  h.subset (by simp)

/-- A `Neighbour`-chain without bad cells is a good sequence. -/
theorem isGoodSeq_of_bad_empty {ε : ℝ} (hε : 0 < ε) {l : List DyBox} (hch : l.IsChain Neighbour)
    (h : l312Bad ε l = ∅) : IsGoodSeq ε l := by
  refine isGoodSeq_of_pairs hε l hch fun c c' hcc => ⟨?_, ?_⟩
  · by_contra hlt; push_neg at hlt
    have : c ∈ l312Bad ε l := by
      simp only [l312Bad, Finset.mem_filter, List.mem_toFinset]
      exact ⟨infix_mem_left hcc, c', Or.inl hcc, hlt⟩
    rw [h] at this; simp at this
  · by_contra hlt; push_neg at hlt
    have : c' ∈ l312Bad ε l := by
      simp only [l312Bad, Finset.mem_filter, List.mem_toFinset]
      exact ⟨infix_mem_right hcc, c, Or.inr hcc, hlt⟩
    rw [h] at this; simp at this

open Classical in
lemma card_l312Bad_le (ε : ℝ) (l : List DyBox) : (l312Bad ε l).card ≤ l.length :=
  (Finset.card_filter_le _ _).trans (List.toFinset_card_le l)

lemma mem_of_mem_l312Bad {ε : ℝ} {l : List DyBox} {c : DyBox} (h : c ∈ l312Bad ε l) : c ∈ l := by
  simp only [l312Bad, Finset.mem_filter, List.mem_toFinset] at h; exact h.1

open Classical in
/-- The least level of a bad cell (`0` if there is none): `q(𝒞) = 2^{-l312MinLevel}`. -/
def l312MinLevel (ε : ℝ) (l : List DyBox) : ℕ :=
  if h : (l312Bad ε l).Nonempty then (l312Bad ε l).inf' h DyBox.n else 0

/-- The potential `|ψ(l)| (M + 1) + min level`. -/
def l312Pot (ε : ℝ) (M : ℕ) (l : List DyBox) : ℕ :=
  (l312Bad ε l).card * (M + 1) + l312MinLevel ε l

lemma l312MinLevel_le {ε : ℝ} {M : ℕ} {l : List DyBox} (hlev : ∀ c ∈ l, c.n ≤ M) :
    l312MinLevel ε l ≤ M := by
  unfold l312MinLevel
  split_ifs with h
  · obtain ⟨c, hc⟩ := h
    exact (Finset.inf'_le _ hc).trans (hlev c (mem_of_mem_l312Bad hc))
  · exact Nat.zero_le _

lemma n_lt_of_two_mul_side_le {c c' : DyBox} (h : 2 * c.side ≤ c'.side) : c'.n < c.n := by
  by_contra hn; push_neg at hn
  have h1 : c'.side ≤ c.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have := side_pos' c
  linarith

lemma l312Pot_lt {ε : ℝ} {M : ℕ} {l l' : List DyBox} (hlev' : ∀ c ∈ l', c.n ≤ M)
    (hne : (l312Bad ε l).Nonempty) (hp : L312Progress ε l l') :
    l312Pot ε M l' < l312Pot ε M l := by
  have h1 := l312MinLevel_le (ε := ε) hlev'
  unfold l312Pot
  rcases hp with hp | ⟨hc, c', hc', hall⟩
  · have : (l312Bad ε l').card * (M + 1) + (M + 1) ≤ (l312Bad ε l).card * (M + 1) := by
      have := Nat.mul_le_mul_right (M + 1) hp
      rwa [add_mul, one_mul] at this
    omega
  · have hm' : l312MinLevel ε l' ≤ c'.n := by
      unfold l312MinLevel; rw [dif_pos ⟨c', hc'⟩]; exact Finset.inf'_le _ hc'
    obtain ⟨c₀, hc₀, he⟩ := Finset.exists_mem_eq_inf' hne DyBox.n
    have hm : l312MinLevel ε l = c₀.n := by unfold l312MinLevel; rw [dif_pos hne, he]
    have := n_lt_of_two_mul_side_le (hall c₀ hc₀)
    have := Nat.mul_le_mul_right (M + 1) hc
    omega

/-- **DZZ's iteration** (l. 1455–1458). -/
theorem l312_iterate {Q : List DyBox → Prop} (ε : ℝ) (M K : ℕ)
    (hlev : ∀ l, Q l → ∀ c ∈ l, c.n ≤ M)
    (hstep : ∀ l, Q l → (l312Bad ε l).Nonempty →
      ∃ l', Q l' ∧ l'.length ≤ l.length + K ∧ L312Progress ε l l') :
    ∀ l, Q l → ∃ l', Q l' ∧ l312Bad ε l' = ∅ ∧ l'.length ≤ l.length + K * l312Pot ε M l := by
  suffices H : ∀ n l, Q l → l312Pot ε M l ≤ n →
      ∃ l', Q l' ∧ l312Bad ε l' = ∅ ∧ l'.length ≤ l.length + K * l312Pot ε M l from
    fun l hl => H _ l hl le_rfl
  intro n
  induction n with
  | zero =>
    intro l hl hn
    by_cases he : l312Bad ε l = ∅
    · exact ⟨l, hl, he, by omega⟩
    · obtain ⟨l', hl', -, hp⟩ := hstep l hl (Finset.nonempty_iff_ne_empty.2 he)
      have := l312Pot_lt (hlev l' hl') (Finset.nonempty_iff_ne_empty.2 he) hp
      omega
  | succ n ih =>
    intro l hl hn
    by_cases he : l312Bad ε l = ∅
    · exact ⟨l, hl, he, by omega⟩
    · obtain ⟨l', hl', hlen, hp⟩ := hstep l hl (Finset.nonempty_iff_ne_empty.2 he)
      have hlt := l312Pot_lt (hlev l' hl') (Finset.nonempty_iff_ne_empty.2 he) hp
      obtain ⟨l'', h1, h2, h3⟩ := ih l' hl' (by omega)
      refine ⟨l'', h1, h2, ?_⟩
      have : K * l312Pot ε M l' + K ≤ K * l312Pot ε M l := by
        have := Nat.mul_le_mul_left K hlt
        rwa [Nat.mul_succ] at this
      omega

lemma l312Pot_le {ε : ℝ} {M : ℕ} {l : List DyBox} (hlev : ∀ c ∈ l, c.n ≤ M) :
    l312Pot ε M l ≤ l.length * (M + 1) + M := by
  unfold l312Pot
  have := Nat.mul_le_mul_right (M + 1) (card_l312Bad_le ε l)
  have := l312MinLevel_le (ε := ε) hlev
  omega

end DZZ
end LQGMetric
