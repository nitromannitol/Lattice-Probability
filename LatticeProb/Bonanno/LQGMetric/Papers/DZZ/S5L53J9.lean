/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinGeom

/-!
# DZZ Lemma 5.3, node 3: the sub-box grid of a cell

The `K × K` dyadic sub-boxes of a cell `𝖢` (DZZ l. 2425), `K = 2^k = 2N + 2`, indexed by the
sites of `l53EvenBox N = [-N, N+1]²` (S5L53J7): the site `z` is the box `siteBox (n + k) c z`
(S3L7FinGeom) of level `n + k = 𝖢.n + k` with index `c + z`, `c = (2^k j_𝖢 + N, 2^k k_𝖢 + N)`.

`l53_sub_inGrid`, `l53_sub_n`, `l53_sub_side`; the grid inputs of `l53_cell_desirable_prob`
for `Bd z = ∂ 𝖡̄_z`, `I x y = 𝖡̄_x ∩ 𝖡̄_y`, `c = s_𝖢 / K`: **`l53_sub_hI`**, **`l53_sub_hIc`**,
**`l53_sub_hBdc`**, and the frontier bound `l53_sub_frontier_le` (for the uniform openness
thresholds `a = b = K'⁻¹ · 4 s_𝖢 / K` of `l53_zopen_dyBox`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

/-- The base index of the sub-box grid of `𝖢`. -/
def l53SubBase (C : DyBox) (k N : ℕ) : ℤ × ℤ :=
  ((2 : ℤ) ^ k * C.j + N, (2 : ℤ) ^ k * C.k + N)

/-- The sub-box of `𝖢` at the site `z`. -/
def l53Sub (C : DyBox) (k N : ℕ) (z : ℤ × ℤ) : DyBox := siteBox (C.n + k) (l53SubBase C k N) z

lemma l53_sub_side (C : DyBox) (k N : ℕ) (z : ℤ × ℤ) :
    (l53Sub C k N z).side = (2 : ℝ)⁻¹ ^ (C.n + k) := rfl

lemma l53_sub_inGrid (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {z : ℤ × ℤ}
    (hz : z ∈ l53EvenBox N) : InGrid (C.n + k) (l53SubBase C k N) z := by
  rw [mem_l53EvenBox] at hz
  have hj : (C.j : ℤ) + 1 ≤ 2 ^ C.n := by exact_mod_cast C.hj
  have hk : (C.k : ℤ) + 1 ≤ 2 ^ C.n := by exact_mod_cast C.hk
  have hK' : (2 : ℤ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  have hpow : (2 : ℤ) ^ (C.n + k) = 2 ^ C.n * 2 ^ k := pow_add _ _ _
  have h0 : (0 : ℤ) ≤ C.j := Int.natCast_nonneg _
  have h0' : (0 : ℤ) ≤ C.k := Int.natCast_nonneg _
  have hP : (0 : ℤ) < 2 ^ C.n := by positivity
  simp only [InGrid, l53SubBase]
  refine ⟨by nlinarith, ?_, by nlinarith, ?_⟩
  · rw [hpow, hK']; nlinarith
  · rw [hpow, hK']; nlinarith

/-- The indices of the sub-box at a site of the grid. -/
lemma l53_sub_jk (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {z : ℤ × ℤ}
    (hz : z ∈ l53EvenBox N) :
    ((l53Sub C k N z).j : ℤ) = 2 ^ k * C.j + N + z.1 ∧
      ((l53Sub C k N z).k : ℤ) = 2 ^ k * C.k + N + z.2 := by
  have h := l53_sub_inGrid C hK hz
  exact ⟨by rw [l53Sub, siteBox_j h]; rfl, by rw [l53Sub, siteBox_k h]; rfl⟩

/-- `4`-adjacent sites give boxes with `4`-adjacent indices. -/
lemma l53_sub_adj (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {x y : ℤ × ℤ}
    (hx : x ∈ l53EvenBox N) (hy : y ∈ l53EvenBox N) (hxy : PercAdj4 x y) :
    ((l53Sub C k N x).j = (l53Sub C k N y).j ∧
        ((l53Sub C k N x).k = (l53Sub C k N y).k + 1 ∨
          (l53Sub C k N y).k = (l53Sub C k N x).k + 1)) ∨
      ((l53Sub C k N x).k = (l53Sub C k N y).k ∧
        ((l53Sub C k N x).j = (l53Sub C k N y).j + 1 ∨
          (l53Sub C k N y).j = (l53Sub C k N x).j + 1)) := by
  obtain ⟨hx1, hx2⟩ := l53_sub_jk C hK hx
  obtain ⟨hy1, hy2⟩ := l53_sub_jk C hK hy
  simp only [PercAdj4] at hxy
  omega

/-- `I x y ⊆ Bd x ∩ Bd y` for the sub-box grid. -/
lemma l53_sub_hI (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) :
    ∀ x ∈ l53EvenBox N, ∀ y ∈ l53EvenBox N, PercAdj4 x y →
      (l53Sub C k N x).closedBox ∩ (l53Sub C k N y).closedBox ⊆
        frontier (l53Sub C k N x).closedBox ∩ frontier (l53Sub C k N y).closedBox :=
  fun x hx y hy hxy => (l53_adj_iface (b := l53Sub C k N x) (b' := l53Sub C k N y) rfl
    (l53_sub_adj C hK hx hy hxy)).1

/-- `c ≤ μH¹(I x y)` with `c = s_𝖢 / K` for the sub-box grid. -/
lemma l53_sub_hIc (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) :
    ∀ x ∈ l53EvenBox N, ∀ y ∈ l53EvenBox N, PercAdj4 x y →
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + k)) ≤
        μH[1] ((l53Sub C k N x).closedBox ∩ (l53Sub C k N y).closedBox) :=
  fun x hx y hy hxy => (l53_adj_iface (b := l53Sub C k N x) (b' := l53Sub C k N y) rfl
    (l53_sub_adj C hK hx hy hxy)).2

/-- `c ≤ μH¹(Bd x)` for the sub-box grid. -/
lemma l53_sub_hBdc (C : DyBox) (k N : ℕ) (x : ℤ × ℤ) :
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + k)) ≤ μH[1] (frontier (l53Sub C k N x).closedBox) :=
  l53_frontier_closedBox_ge (l53Sub C k N x)

/-- `μH¹(Bd x) ≤ 4 s_𝖢 / K` for the sub-box grid. -/
lemma l53_sub_frontier_le (C : DyBox) (k N : ℕ) (x : ℤ × ℤ) :
    μH[1] (frontier (l53Sub C k N x).closedBox) ≤ 4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + k)) :=
  l53_frontier_closedBox_le (l53Sub C k N x)

end LQGMetric.DZZ
