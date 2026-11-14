/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteCellSelector at commit fdb5cad; local import paths and deprecated lemma names are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FixedBallCover
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Measurable cell labels and ball selectors. A point outside every bounded
cell receives `none`, so a default label cannot certify a successful match. -/

open MeasureTheory Set Metric
open scoped Classical

namespace BouRabeeGwynne

variable {X ι : Type*}

noncomputable def cellLabel (E : ι → Set X) (x : X) : Option ι :=
  if h : ∃ i, x ∈ E i then some h.choose else none

lemma cellLabel_eq_none_iff (E : ι → Set X) (x : X) :
    cellLabel E x = none ↔ ∀ i, x ∉ E i := by
  by_cases h : ∃ i, x ∈ E i
  · simp only [cellLabel, dite_eq_left h, Option.some_ne_none, false_iff]
    exact fun hn => h.elim (fun i hi => hn i hi)
  · simp only [cellLabel, dite_eq_right h, true_iff]
    simpa only [not_exists] using h

lemma cellLabel_some_mem (E : ι → Set X) {x : X} {i : ι}
    (h : cellLabel E x = some i) : x ∈ E i := by
  unfold cellLabel at h
  split at h
  next hx =>
    have hi : hx.choose = i := Option.some.inj h
    exact hi ▸ hx.choose_spec
  next hx => cases h

lemma cellLabel_eq_some_iff (E : ι → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (x : X) (i : ι) :
    cellLabel E x = some i ↔ x ∈ E i := by
  refine ⟨cellLabel_some_mem E, fun hx => ?_⟩
  have he : ∃ j, x ∈ E j := ⟨i, hx⟩
  have hi : he.choose = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) he.choose_spec hx
  simp only [cellLabel, dite_eq_left he, hi]

lemma measurable_cellLabel [MeasurableSpace X] [Countable ι]
    [MeasurableSpace (Option ι)] (E : ι → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE : ∀ i, MeasurableSet (E i)) : Measurable (cellLabel E) := by
  apply measurable_to_countable'
  intro j
  cases j with
  | none =>
    have he : cellLabel E ⁻¹' {none} = (⋃ i, E i)ᶜ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, cellLabel_eq_none_iff,
        mem_compl_iff, mem_iUnion, not_exists]
    rw [he]
    exact (MeasurableSet.iUnion hE).compl
  | some i =>
    have he : cellLabel E ⁻¹' {some i} = E i := by
      ext x
      exact cellLabel_eq_some_iff E hdisj x i
    rw [he]
    exact hE i

lemma same_valid_cell_dist_lt [PseudoMetricSpace X] (E : ι → Set X) {ε : ℝ}
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y < ε)
    {x y : X} {i : ι} (hx : cellLabel E x = some i) (hy : cellLabel E y = some i) :
    dist x y < ε :=
  hdiam i x (cellLabel_some_mem E hx) y (cellLabel_some_mem E hy)

noncomputable def cellSelector {J : Type*} (E : ι → Set X) (select : ι → Option J)
    (x : X) : Option J := (cellLabel E x).bind select

lemma measurable_cellSelector {J : Type*} [MeasurableSpace X] [Fintype ι]
    [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
    [MeasurableSpace (Option J)] (E : ι → Set X) (select : ι → Option J)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE : ∀ i, MeasurableSet (E i)) : Measurable (cellSelector E select) :=
  (measurable_of_finite (fun j : Option ι => j.bind select)).comp
    (measurable_cellLabel E hdisj hE)

lemma cellSelector_of_label {J : Type*} (E : ι → Set X) (select : ι → Option J)
    {x : X} {i : ι} (hx : cellLabel E x = some i) :
    cellSelector E select x = select i := by
  simp only [cellSelector, hx, Option.bind_some]

lemma cellSelector_some_mem {J : Type*} (E : ι → Set X) (select : ι → Option J)
    {x : X} {j : J} (hx : cellSelector E select x = some j) :
    ∃ i, x ∈ E i ∧ select i = some j := by
  cases hl : cellLabel E x with
  | none =>
    simp only [cellSelector, hl, Option.bind_none] at hx
    cases hx
  | some i =>
    exact ⟨i, cellLabel_some_mem E hl, (cellSelector_of_label E select hl).symm.trans hx⟩

/-- Each cell meeting the active compact collar receives a fixed ball with
the same half-radius margin; all other cells stop. Later refinements do not
change the radius or the fixed family of balls. -/
theorem exists_cell_ball_choices {d : ℕ} {K : Set (Euc d)} {r : ℝ}
    {centers : Finset (Euc d)} (E : ι → Set (Euc d))
    (hcover : ∀ z ∈ K, ∃ c ∈ centers, z ∈ ball c (r / 4))
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y ≤ r / 4) :
    ∃ select : ι → Option ↥centers,
      (∀ i, select i = none ↔ E i ∩ K = ∅) ∧
      ∀ i c, select i = some c → E i ⊆ ball c.val (r / 2) := by
  classical
  have hchoice (i : ι) : ∃ b : Option ↥centers,
      (b = none ↔ E i ∩ K = ∅) ∧
      ∀ c, b = some c → E i ⊆ ball c.val (r / 2) := by
    by_cases he : (E i ∩ K).Nonempty
    · obtain ⟨c, hc, hEc⟩ := exists_inner_ball_for_cell hcover he (hdiam i)
      refine ⟨some ⟨c, hc⟩, ?_, ?_⟩
      · simp only [Option.some_ne_none, false_iff]
        exact he.ne_empty
      · intro b hb
        have hb' : (⟨c, hc⟩ : ↥centers) = b := Option.some.inj hb
        simpa only [← hb'] using hEc
    · refine ⟨none, ?_, ?_⟩
      · simp only [true_iff]
        exact Set.not_nonempty_iff_eq_empty.mp he
      · intro c hc
        cases hc
  choose select hs hball using hchoice
  exact ⟨select, hs, hball⟩

end BouRabeeGwynne
