/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J1 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Finset.Powerset

/-!
# DZZ Lemma 5.3, node 3: the counting bound for bad columns

Part of the percolation step of DZZ (Ding–Zeitouni–Zhang, arXiv:1807.00422,
`LBM_LGDarXiv.tex` l. 2504–2514, "similar to (eq-par)", l. 1927–2000). In DZZ's Peierls
argument the probability that a prescribed family of pairwise far boxes are all bad is bounded
by a product (l. 1992–1995, "for each such choice the probability for all these boxes … to be
not prefast is at most `(C'K^{-2})^{L/25}`"), and the choices are counted.

`l53_count_bad` is the same union bound for disjoint "columns" `Y i` of at most `m` sites:
the probability that `j` given-size families of columns are all bad (each contains a bad site)
is at most `C(#I, j) (m ε)^j`, provided that every family of sites with at most one site per
column is bad with probability `≤ ε^{#F}`. Own elementary proof (union bound over the choice of
the columns and of a bad site in each).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

variable {Ω ι α : Type*} [MeasurableSpace Ω]

/-- The key step of `l53_count_bad`: `j` bad columns, with a family `F` of bad sites of other
columns. -/
lemma l53_count_bad_aux (μ : Measure Ω) [DecidableEq ι] [DecidableEq α] (I : Finset ι)
    (Y : ι → Finset α) (B : α → Set Ω) {ε : ℝ≥0∞} {m : ℕ} (hY : ∀ i ∈ I, (Y i).card ≤ m)
    (hdisj : ∀ i ∈ I, ∀ i' ∈ I, ∀ x ∈ Y i, x ∈ Y i' → i = i')
    (hind : ∀ F : Finset α, (∀ x ∈ F, ∃ i ∈ I, x ∈ Y i) →
      (∀ i ∈ I, ∀ x ∈ F, ∀ x' ∈ F, x ∈ Y i → x' ∈ Y i → x = x') →
      μ (⋂ x ∈ F, B x) ≤ ε ^ F.card) :
    ∀ S : Finset ι, S ⊆ I → ∀ F : Finset α, (∀ x ∈ F, ∃ i ∈ I, i ∉ S ∧ x ∈ Y i) →
      (∀ i ∈ I, ∀ x ∈ F, ∀ x' ∈ F, x ∈ Y i → x' ∈ Y i → x = x') →
      μ ((⋂ x ∈ F, B x) ∩ ⋂ i ∈ S, ⋃ y ∈ Y i, B y) ≤ ε ^ F.card * ((m : ℝ≥0∞) * ε) ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ F hF hF1
    rw [show (⋂ i ∈ (∅ : Finset ι), ⋃ y ∈ Y i, B y) = univ by simp, inter_univ,
      Finset.card_empty, pow_zero, mul_one]
    exact hind F (fun x hx => by
      obtain ⟨i, hi, -, hx⟩ := hF x hx
      exact ⟨i, hi, hx⟩) hF1
  | insert i S hiS ih =>
    intro hSI F hF hF1
    have hiI : i ∈ I := hSI (Finset.mem_insert_self i S)
    have hSI' : S ⊆ I := (Finset.subset_insert i S).trans hSI
    have hset : (⋂ x ∈ F, B x) ∩ ⋂ i' ∈ insert i S, ⋃ y ∈ Y i', B y ⊆
        ⋃ y ∈ Y i, ((⋂ x ∈ insert y F, B x) ∩ ⋂ i' ∈ S, ⋃ y' ∈ Y i', B y') := by
      intro ω hω
      simp only [mem_inter_iff, mem_iInter, mem_iUnion, Finset.mem_insert] at hω ⊢
      obtain ⟨hω1, hω2⟩ := hω
      obtain ⟨y, hy, hyω⟩ := hω2 i (Or.inl rfl)
      refine ⟨y, hy, fun x hx => ?_, fun i' hi' => hω2 i' (Or.inr hi')⟩
      rcases hx with rfl | hx
      · exact hyω
      · exact hω1 x hx
    have hterm : ∀ y ∈ Y i, μ ((⋂ x ∈ insert y F, B x) ∩ ⋂ i' ∈ S, ⋃ y' ∈ Y i', B y') ≤
        ε ^ (F.card + 1) * ((m : ℝ≥0∞) * ε) ^ S.card := by
      intro y hy
      have hyF : y ∉ F := by
        intro hyF
        obtain ⟨i', hi', hi'S, hyi'⟩ := hF y hyF
        exact hi'S (hdisj i hiI i' hi' y hy hyi' ▸ Finset.mem_insert_self i S)
      rw [← Finset.card_insert_of_notMem hyF]
      refine ih hSI' (insert y F) (fun x hx => ?_) (fun i0 hi0 x hx x' hx' hxi hx'i => ?_)
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨i, hiI, hiS, hy⟩
        · obtain ⟨i', hi', hi'S, hxi'⟩ := hF x hx
          exact ⟨i', hi', fun h => hi'S (Finset.mem_insert_of_mem h), hxi'⟩
      · have key : ∀ x' ∈ F, x' ∈ Y i0 → y ∈ Y i0 → False := by
          intro x' hx' hx'i hyi
          obtain ⟨i', hi', hi'S, hx'i'⟩ := hF x' hx'
          have h1 := hdisj i0 hi0 i hiI y hyi hy
          have h2 := hdisj i0 hi0 i' hi' x' hx'i hx'i'
          exact hi'S (h2 ▸ h1 ▸ Finset.mem_insert_self i S)
        rcases Finset.mem_insert.mp hx with hxy | hxF <;>
          rcases Finset.mem_insert.mp hx' with hx'y | hx'F
        · rw [hxy, hx'y]
        · exact (key x' hx'F hx'i (hxy ▸ hxi)).elim
        · exact (key x hxF hxi (hx'y ▸ hx'i)).elim
        · exact hF1 i0 hi0 x hxF x' hx'F hxi hx'i
    calc μ ((⋂ x ∈ F, B x) ∩ ⋂ i' ∈ insert i S, ⋃ y ∈ Y i', B y)
        ≤ ∑ y ∈ Y i, μ ((⋂ x ∈ insert y F, B x) ∩ ⋂ i' ∈ S, ⋃ y' ∈ Y i', B y') :=
          (measure_mono hset).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _y ∈ Y i, ε ^ (F.card + 1) * ((m : ℝ≥0∞) * ε) ^ S.card := Finset.sum_le_sum hterm
      _ = ((Y i).card : ℝ≥0∞) * (ε ^ (F.card + 1) * ((m : ℝ≥0∞) * ε) ^ S.card) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ≥0∞) * (ε ^ (F.card + 1) * ((m : ℝ≥0∞) * ε) ^ S.card) := by
          gcongr
          exact_mod_cast hY i hiI
      _ = ε ^ F.card * ((m : ℝ≥0∞) * ε) ^ (insert i S).card := by
          rw [Finset.card_insert_of_notMem hiS]
          ring

/-- **Counting bound for bad columns** (the union bound of DZZ l. 1990–1997). If every family
of sites with at most one site in each of the disjoint columns `Y i` (`i ∈ I`, `#Y i ≤ m`) is
bad with probability `≤ ε^{#F}`, then `j` columns are all bad (each contains a bad site) with
probability `≤ C(#I, j) (m ε)^j`. -/
theorem l53_count_bad (μ : Measure Ω) (I : Finset ι) (Y : ι → Finset α) (B : α → Set Ω)
    {ε : ℝ≥0∞} {m : ℕ} (hY : ∀ i ∈ I, (Y i).card ≤ m)
    (hdisj : ∀ i ∈ I, ∀ i' ∈ I, ∀ x ∈ Y i, x ∈ Y i' → i = i')
    (hind : ∀ F : Finset α, (∀ x ∈ F, ∃ i ∈ I, x ∈ Y i) →
      (∀ i ∈ I, ∀ x ∈ F, ∀ x' ∈ F, x ∈ Y i → x' ∈ Y i → x = x') →
      μ (⋂ x ∈ F, B x) ≤ ε ^ F.card) (j : ℕ) :
    μ {ω | ∃ S ⊆ I, S.card = j ∧ ∀ i ∈ S, ∃ y ∈ Y i, ω ∈ B y} ≤
      (I.card.choose j : ℝ≥0∞) * ((m : ℝ≥0∞) * ε) ^ j := by
  classical
  have hset : {ω | ∃ S ⊆ I, S.card = j ∧ ∀ i ∈ S, ∃ y ∈ Y i, ω ∈ B y} ⊆
      ⋃ S ∈ I.powersetCard j, ⋂ i ∈ S, ⋃ y ∈ Y i, B y := by
    intro ω ⟨S, hSI, hSc, hS⟩
    simp only [mem_iUnion, mem_iInter, Finset.mem_powersetCard]
    exact ⟨S, ⟨hSI, hSc⟩, fun i hi => by
      obtain ⟨y, hy, hyω⟩ := hS i hi
      exact ⟨y, hy, hyω⟩⟩
  have hterm : ∀ S ∈ I.powersetCard j, μ (⋂ i ∈ S, ⋃ y ∈ Y i, B y) ≤ ((m : ℝ≥0∞) * ε) ^ j := by
    intro S hS
    obtain ⟨hSI, hSc⟩ := Finset.mem_powersetCard.mp hS
    have h := l53_count_bad_aux μ I Y B hY hdisj hind S hSI ∅ (by simp) (by simp)
    simpa [hSc] using h
  calc μ {ω | ∃ S ⊆ I, S.card = j ∧ ∀ i ∈ S, ∃ y ∈ Y i, ω ∈ B y}
      ≤ ∑ S ∈ I.powersetCard j, μ (⋂ i ∈ S, ⋃ y ∈ Y i, B y) :=
        (measure_mono hset).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _S ∈ I.powersetCard j, ((m : ℝ≥0∞) * ε) ^ j := Finset.sum_le_sum hterm
    _ = (I.card.choose j : ℝ≥0∞) * ((m : ℝ≥0∞) * ε) ^ j := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

end LQGMetric.DZZ
