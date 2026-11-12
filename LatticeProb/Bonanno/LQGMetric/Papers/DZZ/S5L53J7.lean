/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J6

/-!
# DZZ Lemma 5.3, node 3: the even grid of a dyadic cell

A dyadic cell `𝖢_i` is split into `K × K` sub-boxes with `K = 2^k` even (DZZ l. 2425,
`K = 2^{⌊(log δ⁻¹)^{0.51}⌋}`). We write `K = 2N + 2` and index the sub-boxes by the sites of
`l53EvenBox N = [-N, N+1]²` (sub-box `(i, j)`, `0 ≤ i, j < K`, is the site `(i - N, j - N)`).
The annulus `n ≤ ‖z‖_∞ ≤ N` of S5L53J2/J3 then lies in the cell; the boundary boxes of the cell
are `l53Col n N d a (l53EvenTb n N d)` (`l53EvenTb = N - n` on the sides `B`, `L`, the boundary
row of `annBox N`, and `N - n + 1` on `T`, `R`, one row outside it).

`l53_even_hBox`, `l53_even_htb`, `l53_even_hcolB`: the grid hypotheses of `l53_perc_cluster` and
`l53_cell_desirable_prob`; `l53_even_site`: the cell index of a boundary box (bottom row `j = 0`,
top row `j = K - 1`, left column `i = 0`, right column `i = K - 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- The `(2N+2) × (2N+2)` grid `[-N, N+1]²` of the sub-boxes of a cell. -/
def l53EvenBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N + 1) ×ˢ Finset.Icc (-(N : ℤ)) (N + 1)

/-- The boundary depths of the even grid. -/
def l53EvenTb (n N : ℕ) : PercDir → ℤ
  | .T => (N : ℤ) - n + 1
  | .B => (N : ℤ) - n
  | .R => (N : ℤ) - n + 1
  | .L => (N : ℤ) - n

lemma mem_l53EvenBox {N : ℕ} {z : ℤ × ℤ} :
    z ∈ l53EvenBox N ↔ -(N : ℤ) ≤ z.1 ∧ z.1 ≤ N + 1 ∧ -(N : ℤ) ≤ z.2 ∧ z.2 ≤ N + 1 := by
  simp only [l53EvenBox, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma card_l53EvenBox (N : ℕ) : (l53EvenBox N).card = (2 * N + 2) ^ 2 := by
  rw [l53EvenBox, Finset.card_product, Int.card_Icc]
  have : ((N : ℤ) + 1 + 1 - -(N : ℤ)).toNat = 2 * N + 2 := by omega
  rw [this, sq]

lemma l53_even_hBox (N : ℕ) : ∀ z, annBox N z → z ∈ l53EvenBox N := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact mem_l53EvenBox.2 ⟨h1, by omega, h3, by omega⟩

lemma l53_even_htb (n N : ℕ) :
    ∀ d, (N : ℤ) - n ≤ l53EvenTb n N d ∧ l53EvenTb n N d ≤ N - n + 1 := by
  intro d
  cases d <;> simp only [l53EvenTb] <;> omega

lemma l53_even_hcolB (n N : ℕ) (hnN : n ≤ N) :
    ∀ d a, (N : ℤ) - n < a → a < N + n → ∀ t, 0 ≤ t → t ≤ l53EvenTb n N d →
      l53Col n N d a t ∈ l53EvenBox N := by
  intro d a ha₁ ha₂ t ht₁ ht₂
  rw [mem_l53EvenBox]
  cases d <;> simp only [l53EvenTb] at ht₂ <;> simp only [l53Col, annFromStd] <;> omega

/-- The cell index `(i, j) = z + (N, N)` of the boundary box at position `a` of side `d`:
bottom row `j = 0` (`B`), top row `j = 2N + 1` (`T`), left column `i = 0` (`L`), right column
`i = 2N + 1` (`R`); the position along the side is `a`. -/
lemma l53_even_site (n N : ℕ) (a : ℤ) :
    l53Col n N .B a (l53EvenTb n N .B) = (a - N, -(N : ℤ)) ∧
    l53Col n N .T a (l53EvenTb n N .T) = (a - N, (N : ℤ) + 1) ∧
    l53Col n N .L a (l53EvenTb n N .L) = (-(N : ℤ), a - N) ∧
    l53Col n N .R a (l53EvenTb n N .R) = ((N : ℤ) + 1, a - N) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [l53Col, annFromStd, l53EvenTb, Prod.ext_iff] <;>
    simp only [true_and, and_true] <;> ring

end LQGMetric.DZZ
