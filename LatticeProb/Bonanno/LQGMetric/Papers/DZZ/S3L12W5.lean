/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W4

/-!
# DZZ Lemma 3.12: the parents `𝔠_parents` (D93, packets P-5/P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1462–1497.

* `IsParent`: a cell of side `> s_𝖢` meeting `𝖢_large` (`𝔠_parents`, l. 1462–1466);
* `quad_complete`, **`no_four_parents`**: at most three parents;
* **`parents_nbr`**: two parents are neighbours, or both neighbour `𝖢` (Case 3, l. 1489–1497);
* **`diag_nbr`**: the cells next to the diagonal parent `𝖢_lt` that meet `𝖢_large` are the
  other two parents (D93's zone argument replacing "by connectivity", l. 1476–1477).

Own elementary arguments (integer arithmetic), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- DZZ's parents of `𝖢` (l. 1462–1466). -/
def IsParent (m : DyBox → ℝ) (δ : ℝ) (C P : DyBox) : Prop :=
  IsCell m δ P ∧ C.side < P.side ∧ (P.closedBox ∩ C.largeBox).Nonempty

/-- Which quadrant (`0`: same column as the parent, `1`: same row, `2`: diagonal). -/
def qcode (C Q : DyBox) : ℕ := if Q.j = C.j / 2 then 0 else if Q.k = C.k / 2 then 1 else 2

lemma qcode_lt (C Q : DyBox) : qcode C Q < 3 := by
  unfold qcode; split_ifs <;> omega

lemma quad_eq_of_qcode {C Q Q' : DyBox} (h : IsQuad C Q) (h' : IsQuad C Q')
    (hc : qcode C Q = qcode C Q') : Q = Q' := by
  obtain ⟨-, a1, a2, a3, a4, a5⟩ := quad_facts h
  obtain ⟨-, b1, b2, b3, b4, b5⟩ := quad_facts h'
  unfold qcode at hc
  refine quad_eq h h' ?_ ?_ <;> split_ifs at hc <;> omega

lemma quad_complete {C Q₁ Q₂ Q₃ Q : DyBox} (h₁ : IsQuad C Q₁) (h₂ : IsQuad C Q₂)
    (h₃ : IsQuad C Q₃) (h : IsQuad C Q) (h12 : Q₁ ≠ Q₂) (h13 : Q₁ ≠ Q₃) (h23 : Q₂ ≠ Q₃) :
    Q = Q₁ ∨ Q = Q₂ ∨ Q = Q₃ := by
  have c12 : qcode C Q₁ ≠ qcode C Q₂ := fun e => h12 (quad_eq_of_qcode h₁ h₂ e)
  have c13 : qcode C Q₁ ≠ qcode C Q₃ := fun e => h13 (quad_eq_of_qcode h₁ h₃ e)
  have c23 : qcode C Q₂ ≠ qcode C Q₃ := fun e => h23 (quad_eq_of_qcode h₂ h₃ e)
  have := qcode_lt C Q₁; have := qcode_lt C Q₂; have := qcode_lt C Q₃; have := qcode_lt C Q
  have key : qcode C Q = qcode C Q₁ ∨ qcode C Q = qcode C Q₂ ∨ qcode C Q = qcode C Q₃ := by
    omega
  rcases key with e | e | e
  · exact Or.inl (quad_eq_of_qcode h h₁ e)
  · exact Or.inr (Or.inl (quad_eq_of_qcode h h₂ e))
  · exact Or.inr (Or.inr (quad_eq_of_qcode h h₃ e))

lemma quad_ne_of_parent_ne {C P P' Q Q' : DyBox} (hP : IsParent m δ C P)
    (hP' : IsParent m δ C P') (hne : P ≠ P') (hQ : IsQuad C Q)
    (hQP : Q.closedBox ⊆ P.closedBox) (hQP' : Q'.closedBox ⊆ P'.closedBox) : Q ≠ Q' := by
  rintro rfl
  exact hne (parent_eq_of_quad hP.1 hP'.1 hP.2.1 hP'.2.1 hQ hQP hQP')

/-- **At most three parents.** -/
theorem no_four_parents {C a b c e : DyBox} (hC : IsCell m δ C) (ha : IsParent m δ C a)
    (hb : IsParent m δ C b) (hc : IsParent m δ C c) (he : IsParent m δ C e)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    False := by
  obtain ⟨Qa, qa, sa⟩ := exists_quad_of_parent hC ha.1 ha.2.1 ha.2.2
  obtain ⟨Qb, qb, sb⟩ := exists_quad_of_parent hC hb.1 hb.2.1 hb.2.2
  obtain ⟨Qc, qc, sc⟩ := exists_quad_of_parent hC hc.1 hc.2.1 hc.2.2
  obtain ⟨Qe, qe, se⟩ := exists_quad_of_parent hC he.1 he.2.1 he.2.2
  rcases quad_complete qa qb qc qe (quad_ne_of_parent_ne ha hb hab qa sa sb)
    (quad_ne_of_parent_ne ha hc hac qa sa sc) (quad_ne_of_parent_ne hb hc hbc qb sb sc)
    with h | h | h
  · exact quad_ne_of_parent_ne ha he hae qa sa se h.symm
  · exact quad_ne_of_parent_ne hb he hbe qb sb se h.symm
  · exact quad_ne_of_parent_ne hc he hce qc sc se h.symm

/-- A grid point of level `N`. -/
def gpt (N a c : ℕ) : ℂ := ⟨(a : ℝ) * (2 : ℝ)⁻¹ ^ N, (c : ℝ) * (2 : ℝ)⁻¹ ^ N⟩

lemma gpt_mem {b : DyBox} {N : ℕ} (hb : b.n ≤ N) {a c : ℕ} (h1 : b.j * 2 ^ (N - b.n) ≤ a)
    (h2 : a ≤ (b.j + 1) * 2 ^ (N - b.n)) (h3 : b.k * 2 ^ (N - b.n) ≤ c)
    (h4 : c ≤ (b.k + 1) * 2 ^ (N - b.n)) : gpt N a c ∈ b.closedBox := by
  rw [bx_mem_closedBox hb]
  have e : (2 : ℝ)⁻¹ ^ N * 2 ^ N = 1 := by rw [← mul_pow]; norm_num
  simp only [gpt, mul_assoc, e, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact_mod_cast (by assumption)

lemma gpt_ne {N a c a' c' : ℕ} (h : a ≠ a' ∨ c ≠ c') : gpt N a c ≠ gpt N a' c' := by
  intro he
  have hp : (2 : ℝ)⁻¹ ^ N ≠ 0 := by positivity
  rcases h with h | h
  · have := congrArg Complex.re he
    simp only [gpt] at this
    exact h (by exact_mod_cast mul_right_cancel₀ hp this)
  · have := congrArg Complex.im he
    simp only [gpt] at this
    exact h (by exact_mod_cast mul_right_cancel₀ hp this)

lemma neighbour_of_two {b b' : DyBox} (hne : b ≠ b') {p q : ℂ} (hp : p ∈ b.closedBox)
    (hp' : p ∈ b'.closedBox) (hq : q ∈ b.closedBox) (hq' : q ∈ b'.closedBox) (hpq : p ≠ q) :
    Neighbour b b' :=
  ⟨hne, fun h => hpq (h ⟨hp, hp'⟩ ⟨hq, hq'⟩)⟩

end DZZ
end LQGMetric
