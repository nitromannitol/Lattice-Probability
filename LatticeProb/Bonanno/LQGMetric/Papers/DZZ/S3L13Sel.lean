/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13Sel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi

/-!
# DZZ Lemma 3.13: explored boxes, the partition determined by them, measurable selection (P2-DZZ313)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1314–1340 (Lemma 3.13 and its proof).
DZZ's (Eq.fine-field-independent) "the construction of `𝒱_δ` does not explore the white noise …" is
the stopping-set principle for the partition. Its deterministic content (own elementary proofs):

* `Explored c b`: no strict ancestor of `b` is a cell (`c` is the cell predicate). For `c = IsCell m δ`
  these are exactly the boxes whose mass `m b` the partition rule reads (`explored_isCell_iff`).
* `isCell_iff_of_eqOn_explored`: if `m = m'` on the boxes explored by `m`, the two partitions coincide.
* `selMin`: the `key`-least element satisfying a predicate (deterministic tie-break), with the fibre
  characterization `selMin_eq_iff`; used to choose the box sequence as a measurable function of `𝒱_δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- `b` is explored by the cell predicate `c`: no strict ancestor of `b` is a cell. -/
def Explored (c : DyBox → Prop) (b : DyBox) : Prop := ∀ i < b.n, ¬ c (b.anc i)

lemma anc_n_of_lt {b : DyBox} {i : ℕ} (h : i < b.n) : (b.anc i).n = i := by
  simp [DyBox.anc, min_eq_left h.le]

/-- For the partition rule, a box is explored iff all its strict ancestors were split. -/
lemma explored_isCell_iff (m : DyBox → ℝ) (δ : ℝ) (b : DyBox) :
    Explored (IsCell m δ) b ↔ ∀ i < b.n, δ ^ 2 ≤ m (b.anc i) := by
  constructor
  · intro h i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_contra hlt
      refine h i hi ⟨lt_of_not_ge hlt, fun j hj => ?_⟩
      rw [anc_n_of_lt hi] at hj
      rw [anc_anc b hj.le]
      exact ih j hj (hj.trans hi)
  · intro h i hi hc
    exact absurd (h i hi) (not_le.2 hc.1)

/-- If `m = m'` on all boxes explored by `m`, then `m'` explores the same boxes. -/
lemma explored_iff_of_eqOn (m m' : DyBox → ℝ) (δ : ℝ)
    (h : ∀ b, Explored (IsCell m δ) b → m b = m' b) (b : DyBox) :
    Explored (IsCell m δ) b ↔ Explored (IsCell m' δ) b := by
  rw [explored_isCell_iff, explored_isCell_iff]
  have hanc : ∀ i < b.n, (∀ j < i, δ ^ 2 ≤ m (b.anc j)) → m (b.anc i) = m' (b.anc i) := by
    intro i hi hj
    refine h _ ((explored_isCell_iff m δ _).2 fun j hj' => ?_)
    rw [anc_n_of_lt hi] at hj'
    rw [anc_anc b hj'.le]
    exact hj j hj'
  constructor
  · intro hm i hi
    rw [← hanc i hi fun j hj => hm j (hj.trans hi)]
    exact hm i hi
  · intro hm' i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rw [hanc i hi fun j hj => ih j hj (hj.trans hi)]
      exact hm' i hi

/-- **The partition is determined by the masses of the explored boxes.** -/
theorem isCell_iff_of_eqOn_explored (m m' : DyBox → ℝ) (δ : ℝ)
    (h : ∀ b, Explored (IsCell m δ) b → m b = m' b) (b : DyBox) :
    IsCell m δ b ↔ IsCell m' δ b := by
  have he := explored_iff_of_eqOn m m' δ h b
  have e1 : IsCell m δ b ↔ m b < δ ^ 2 ∧ Explored (IsCell m δ) b := by
    rw [explored_isCell_iff]; rfl
  have e2 : IsCell m' δ b ↔ m' b < δ ^ 2 ∧ Explored (IsCell m' δ) b := by
    rw [explored_isCell_iff]; rfl
  rw [e1, e2, ← he]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h b h2 ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(h b h2).symm ▸ h1, h2⟩

/-- `IsCell m δ = IsCell m' δ` (as predicates) under the hypothesis of `isCell_iff_of_eqOn_explored`. -/
theorem isCell_eq_of_eqOn_explored (m m' : DyBox → ℝ) (δ : ℝ)
    (h : ∀ b, Explored (IsCell m δ) b → m b = m' b) :
    (fun b => IsCell m δ b) = fun b => IsCell m' δ b :=
  funext fun b => propext (isCell_iff_of_eqOn_explored m m' δ h b)

/-! ### Deterministic selection of the least element -/

section Sel

variable {α : Type*}

lemma exists_keyMin (key : α → ℕ) {Q : α → Prop} (h : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ a', Q a' → key a ≤ key a' := by
  classical
  have hn : ∃ n, ∃ a, Q a ∧ key a = n := let ⟨a, ha⟩ := h; ⟨_, a, ha, rfl⟩
  obtain ⟨a, ha, hk⟩ := Nat.find_spec hn
  exact ⟨a, ha, fun a' ha' => hk ▸ Nat.find_min' hn ⟨a', ha', rfl⟩⟩

open Classical in
/-- The `key`-least `a` with `Q a` (`d` if there is none). -/
def selMin (key : α → ℕ) (Q : α → Prop) (d : α) : α :=
  if h : ∃ a, Q a then (exists_keyMin key h).choose else d

theorem selMin_eq_iff {key : α → ℕ} (hk : Function.Injective key) (Q : α → Prop) (d a₀ : α) :
    selMin key Q d = a₀ ↔ (Q a₀ ∧ ∀ a, Q a → key a₀ ≤ key a) ∨ (a₀ = d ∧ ∀ a, ¬ Q a) := by
  unfold selMin
  split_ifs with h
  · have hs := (exists_keyMin key h).choose_spec
    constructor
    · rintro rfl; exact Or.inl hs
    · rintro (⟨hQ, hmin⟩ | ⟨-, hn⟩)
      · exact hk (le_antisymm (hs.2 a₀ hQ) (hmin _ hs.1))
      · exact absurd hs.1 (hn _)
  · push Not at h
    constructor
    · rintro rfl; exact Or.inr ⟨rfl, h⟩
    · rintro (⟨hQ, -⟩ | ⟨rfl, -⟩)
      · exact absurd hQ (h a₀)
      · rfl

lemma selMin_spec {key : α → ℕ} (hk : Function.Injective key) {Q : α → Prop} {d a₀ : α}
    (h : selMin key Q d = a₀) (hd : a₀ ≠ d) : Q a₀ ∧ ∀ a, Q a → key a₀ ≤ key a := by
  rcases (selMin_eq_iff hk Q d a₀).1 h with h' | h'
  · exact h'
  · exact absurd h'.1 hd

/-- Measurability of the fibres of `selMin` for a countable family of measurable predicates. -/
theorem measurableSet_selMin_eq {β : Type*} [MeasurableSpace β] [Countable α] {key : α → ℕ}
    (hk : Function.Injective key) {Q : β → α → Prop} (hQ : ∀ a, Measurable fun x => Q x a)
    (d a₀ : α) : MeasurableSet {x | selMin key (Q x) d = a₀} := by
  simp_rw [selMin_eq_iff hk]
  refine measurableSet_setOfPred.2 (Measurable.or (Measurable.and (hQ a₀) (Measurable.forall fun a =>
    (hQ a).imp measurable_const)) (Measurable.and measurable_const (Measurable.forall fun a =>
      (hQ a).not)))

end Sel

end DZZ
end LQGMetric
