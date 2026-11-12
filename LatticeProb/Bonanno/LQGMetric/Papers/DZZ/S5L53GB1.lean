/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GB1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J6

/-!
# DZZ Lemma 5.3, node 3: glue G-J1, G-J2 of DEC-131-IF (P2-DZZ53GB)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2510–2514; DEC-131-IF §2 J-1, J-3 and §3.
* `l53_cell_desirable_prob_on` (G-J1): `l53_cell_desirable_prob` (S5L53J6) with the openness only
  on an event `E`, conclusion on `E ∩ {¬ clause}` (same proof, copied and modified).
* `L53DesClause.mono` (G-J2): the clause is monotone in the exponent (`lgdLeExp.mono`, S5L53E1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- **G-J2**: `L53DesClause` is monotone in the exponent. -/
lemma L53DesClause.mono {ν M : Measure ℂ} {δ T T' : ℝ} (h : T ≤ T') {Λp Λn : Set ℂ}
    (hD : L53DesClause ν M δ T Λp Λn) : L53DesClause ν M δ T' Λp Λn := by
  intro E hE hEν
  obtain ⟨S, hS, hSν, hSx⟩ := hD E hE hEν
  exact ⟨S, hS, hSν, fun x hx => (hSx x hx).imp fun x' hx' => ⟨hx'.1, hx'.2.mono h⟩⟩

/-- **G-J1: desirability of one cell on an event `E`** (DZZ l. 2510–2514; DEC-131-IF §3 G-J1).
Copy of `l53_cell_desirable_prob` (S5L53J6, P2-DZZ53J) with the openness `hopen` required only
for `ω ∈ E` (the domination behind it holds only on `l53E4`); the conclusion bounds
`μ (E ∩ {¬ clause})`. Same proof. -/
theorem l53_cell_desirable_prob_on {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n N : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (Box : Finset (ℤ × ℤ)) (hBox : ∀ z, annBox N z → z ∈ Box)
    (tb : PercDir → ℤ) (htb : ∀ d, (N : ℤ) - n ≤ tb d ∧ tb d ≤ N - n + 1)
    (hcolB : ∀ d a, (N : ℤ) - n < a → a < N + n → ∀ t, 0 ≤ t → t ≤ tb d →
      l53Col n N d a t ∈ Box)
    (Bad : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ε ≤ θ ^ ((r + 1) ^ 2)) (hε : ∀ z ∈ Box, μ (Bad z) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ Box) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, Bad x) ≤ ∏ x ∈ F, μ (Bad x))
    (j : ℕ) (E : Set Ω) (ν : Measure ℂ) (M : Ω → Measure ℂ) {δ T : ℝ}
    (Bd : ℤ × ℤ → Set ℂ) (I : ℤ × ℤ → ℤ × ℤ → Set ℂ) {a b c : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) (hc : b + a ≤ c)
    (hI : ∀ x ∈ Box, ∀ y ∈ Box, PercAdj4 x y → I x y ⊆ Bd x ∩ Bd y)
    (hIc : ∀ x ∈ Box, ∀ y ∈ Box, PercAdj4 x y → c ≤ ν (I x y))
    (hBdc : ∀ x ∈ Box, c ≤ ν (Bd x))
    (hopen : ∀ ω ∈ E, ∀ x ∈ Box, ω ∉ Bad x → ∀ Λ ⊆ Bd x, b ≤ ν Λ →
      ∃ z ∈ Λ, ν {z' ∈ Bd x | ¬ lgdLeExp (M ω) δ T z z'} ≤ a)
    (seg : PercDir × ℤ → Set ℂ)
    (hseg : ∀ p, seg p ⊆ Bd (l53Col n N p.1 p.2 (tb p.1)))
    (Prev Next : Finset (PercDir × ℤ))
    (hrange : ∀ p, (p ∈ Prev ∨ p ∈ Next) → (N : ℤ) - n < p.2 ∧ p.2 < N + n)
    {Λprev Λnext : Set ℂ} (hΛp : ν Λprev ≠ ⊤) (hΛn : ν Λnext ≠ ⊤)
    (hPrev : ∀ p ∈ Prev, seg p ⊆ Λprev) (hNext : ∀ p ∈ Next, seg p ⊆ Λnext)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : ∀ p, ν.real (seg p) ≤ σ)
    (hcovP : 0.2 * ν.real Λprev + 4 * (r + 1) * j * σ ≤ ν.real (⋃ p ∈ Prev, seg p))
    (hcardP : (Prev.card : ℝ) * a.toReal ≤ 0.1 * ν.real Λprev)
    (hcovN : ν.real (Λnext \ ⋃ p ∈ Next, seg p) + Next.card * b.toReal + 4 * (r + 1) * j * σ <
      0.1 * ν.real Λnext) :
    μ (E ∩ {ω | ¬ L53DesClause ν (M ω) δ (T + Real.log ((Box.card : ℝ) + 1)) Λprev Λnext}) ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (r + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) := by
  classical
  refine le_trans (measure_mono fun ω hω => ?_)
    (l53_perc_cluster μ n N hn hnN Box hBox tb htb hcolB Bad r hθ hεθ hε hind j)
  intro hcl
  obtain ⟨hωE, hω⟩ := hω
  apply hω
  obtain ⟨C, hC, hCc, hEd⟩ := hcl
  choose Ed hEdc hEd using hEd
  set Exc : Finset (PercDir × ℤ) :=
    (((Ed .T).image fun a => (PercDir.T, a)) ∪ ((Ed .B).image fun a => (PercDir.B, a))) ∪
      (((Ed .R).image fun a => (PercDir.R, a)) ∪ ((Ed .L).image fun a => (PercDir.L, a)))
    with hExc
  have hExcc : (Exc.card : ℝ) ≤ 4 * (r + 1) * j := by
    have h : Exc.card ≤ ((Ed .T).card + (Ed .B).card) + ((Ed .R).card + (Ed .L).card) := by
      refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_) <;>
        refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_) <;> exact Finset.card_image_le
    have := hEdc .T; have := hEdc .B; have := hEdc .R; have := hEdc .L
    have h' : Exc.card ≤ 4 * (r + 1) * j := by nlinarith
    exact_mod_cast h'
  have hExcσ : (Exc.card : ℝ) * σ ≤ 4 * (r + 1) * j * σ := mul_le_mul_of_nonneg_right hExcc hσ0
  have hsite : ∀ p : PercDir × ℤ, p ∉ Exc → (p ∈ Prev ∨ p ∈ Next) →
      l53Col n N p.1 p.2 (tb p.1) ∈ C := by
    rintro ⟨d, a⟩ hp hpPN
    obtain ⟨h1, h2⟩ := hrange _ hpPN
    refine hEd d a h1 h2 fun ha => hp ?_
    simp only [hExc, Finset.mem_union, Finset.mem_image]
    cases d
    · exact Or.inl (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  have hCbox : ∀ z ∈ C, z ∈ Box := fun z hz => (hC z hz).1
  exact l53_desirable_of_cluster ν (M ω) Box C hCbox hCc Bd I ha hb hc
    (fun x hx y hy hxy => hI x (hCbox x hx) y (hCbox y hy) hxy)
    (fun x hx y hy hxy => hIc x (hCbox x hx) y (hCbox y hy) hxy)
    (fun x hx => hBdc x (hCbox x hx))
    (fun x hx => hopen ω hωE x (hCbox x hx) (hC x hx).2)
    (fun p => l53Col n N p.1 p.2 (tb p.1)) seg hseg Prev Next Exc hsite hΛp hΛn hPrev hNext
    hσ0 hσ (by linarith) hcardP (by linarith)

end LQGMetric.DZZ
