/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53L5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L2

/-!
# DZZ Lemma 5.3, part 1: P-131A of DEC-131 — the selected chain of `𝓔*` and R3 (P2-DZZ53L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2363–2378 (`𝓔*`), l. 1314–1340
(Lemma 3.13, (Eq.fine-field-independent)). The interface names of DEC-131 §2:

* `L53Q` (`L313Q` restricted to boxes meeting `R`, with `d ≤ e^T`), `L53QMin`, `l53Sel`, `l53Chain`,
  `l53D1EventB`.
* **`measurableSet_l53Chain_eq`** (`{chain = c₀} ∈ σ(𝒱_δ)`), **`measurableSet_l53Chain_eq_wn`**
  (R3: `{chain = c₀} ∈ wnSigma W (fineReg c₀)ᶜ`, by the stopping-set principle
  `measurableSet_inter_sel_eq`, S5L53L1), `measurableSet_inter_l53Chain_eq` (any `A ∈ σ(𝒱_δ)`),
  **`l53Chain_spec`**, **`disjoint_compl_fineReg`** (sub-box regions `⊆ (0, s_b²) × S`,
  `S ⊆ b_large`, `b ∈ c₀`, are disjoint from `(fineReg c₀)ᶜ`).

Own elementary formalization (copies of the `l313Sel` lemmas, S3L13Reg).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

/-- DZZ `𝓔*` (l. 2363–2378), deterministic part: `L313Q` restricted to `R`, and the length bound. -/
def L53Q (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (c : DyBox → Prop) (l : List DyBox) : Prop :=
  L313Q ε u v c l ∧ (∀ b ∈ l, b ∈ cellsMeeting R) ∧ (l.length : ℝ) ≤ Real.exp T

def L53QMin (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (c : DyBox → Prop) (l : List DyBox) : Prop :=
  L53Q ε u v R T c l ∧ ∀ l', L53Q ε u v R T c l' → l.length ≤ l'.length

/-- The selected box chain (`[]` if there is none). -/
def l53Sel (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (c : DyBox → Prop) : List DyBox :=
  selMin listKey (L53QMin ε u v R T c) []

variable {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ}

/-- The chain of `ω`. -/
def l53Chain (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (ω : Ω) :
    List DyBox :=
  l53Sel (epsStar αs δ) u v R T (fun b => IsCell (approxLQG γ W ω) δ b)

/-- `𝓔* ∩ 𝒟₁` on the box chain. -/
def l53D1EventB (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) :
    Set Ω :=
  cellSizeEvent γ W δ ∩ {ω | l53Chain γ W αs δ u v R T ω ≠ []}

lemma measurable_l53Q (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (l : List DyBox) :
    Measurable fun c : DyBox → Prop => L53Q ε u v R T c l :=
  (measurable_l313Q ε u v l).and measurable_const

lemma measurable_l53QMin (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (l : List DyBox) :
    Measurable fun c : DyBox → Prop => L53QMin ε u v R T c l :=
  (measurable_l53Q ε u v R T l).and
    (Measurable.forall fun l' => (measurable_l53Q ε u v R T l').imp measurable_const)

lemma measurableSet_l53Sel_eq (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (l₀ : List DyBox) :
    MeasurableSet {c : DyBox → Prop | l53Sel ε u v R T c = l₀} :=
  measurableSet_selMin_eq listKey_injective (fun l => measurable_l53QMin ε u v R T l) [] l₀

lemma disjoint_of_l53Sel (ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (c : DyBox → Prop) (b : DyBox)
    (hb : Explored c b) : Disjoint (boxReg b) (fineReg (l53Sel ε u v R T c)) := by
  by_cases hl : l53Sel ε u v R T c = []
  · rw [hl]; simp
  · exact (selMin_spec listKey_injective rfl hl).1.1.1.2.2 b hb

omit [MeasurableSpace Ω] in
theorem measurableSet_l53Chain_eq (γ αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ)
    (c₀ : List DyBox) :
    MeasurableSet[cellSigma γ W δ] {ω | l53Chain γ W αs δ u v R T ω = c₀} :=
  MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_l53Sel_eq _ u v R T c₀, rfl⟩

/-- **R3 for the chain of `𝓔*`**, with any further `σ(𝒱_δ)`-event `A`. -/
theorem measurableSet_inter_l53Chain_eq (γ αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ)
    (c₀ : List DyBox) {A : Set Ω} (hA : MeasurableSet[cellSigma γ W δ] A) :
    MeasurableSet[wnSigma W (fineReg c₀)ᶜ] (A ∩ {ω | l53Chain γ W αs δ u v R T ω = c₀}) :=
  measurableSet_inter_sel_eq (l53Sel (epsStar αs δ) u v R T)
    (measurableSet_l53Sel_eq _ u v R T) (disjoint_of_l53Sel _ u v R T) c₀ hA

/-- **R3** (DEC-131 §2): `{l53Chain = c₀} ∈ wnSigma W (fineReg c₀)ᶜ`. -/
theorem measurableSet_l53Chain_eq_wn (γ αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ)
    (c₀ : List DyBox) :
    MeasurableSet[wnSigma W (fineReg c₀)ᶜ] {ω | l53Chain γ W αs δ u v R T ω = c₀} := by
  have h := measurableSet_inter_l53Chain_eq (W := W) γ αs δ u v R T c₀
    (A := univ) MeasurableSet.univ
  rwa [univ_inter] at h

omit [MeasurableSpace Ω] in
/-- A nonempty selected chain satisfies `L53Q`. -/
theorem l53Chain_spec {γ αs δ : ℝ} {u v : ℂ} {R : Set ℂ} {T : ℝ} {ω : Ω}
    (h : l53Chain γ W αs δ u v R T ω ≠ []) :
    L53Q (epsStar αs δ) u v R T (fun b => IsCell (approxLQG γ W ω) δ b)
      (l53Chain γ W αs δ u v R T ω) :=
  (selMin_spec listKey_injective rfl h).1.1

omit [MeasurableSpace Ω] in
/-- If some sequence satisfies `L53Q`, the chain is nonempty. -/
theorem l53Chain_ne_nil {γ αs δ : ℝ} {u v : ℂ} {R : Set ℂ} {T : ℝ} {ω : Ω} {l : List DyBox}
    (hl : L53Q (epsStar αs δ) u v R T (fun b => IsCell (approxLQG γ W ω) δ b) l) :
    l53Chain γ W αs δ u v R T ω ≠ [] := by
  intro h0
  obtain ⟨l₁, h1, h1m⟩ := exists_keyMin List.length ⟨l, hl⟩
  rcases (selMin_eq_iff listKey_injective _ [] (l53Chain γ W αs δ u v R T ω)).1 rfl with h | h
  · rw [h0] at h
    exact (h.1.1.1.1.1.1) rfl
  · exact h.2 l₁ ⟨h1, h1m⟩

/-- **Sub-box regions are disjoint from `(fineReg c₀)ᶜ`**: `R ⊆ (0, s_b²) × S` with `S ⊆ b_large`,
`b ∈ c₀` (e.g. `S = sqBox c_B (6 s_b/K)` or `sqBox c_B (7 s_B)`, `sqBox_seven_subset_largeBox`). -/
theorem disjoint_compl_fineReg {c₀ : List DyBox} {b : DyBox} (hb : b ∈ c₀) {S : Set ℂ}
    (hS : S ⊆ b.largeBox) {R : Set (ℝ × ℂ)} (hR : R ⊆ Ioo (0 : ℝ) (b.side ^ 2) ×ˢ S) :
    Disjoint (fineReg c₀)ᶜ R :=
  disjoint_compl_left_iff_subset.2 (hR.trans (prod_sqBox_subset_fineReg hb hS))

end DZZ
end LQGMetric
