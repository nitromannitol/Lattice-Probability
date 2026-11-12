/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Paths at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Red
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event4RadEnd

/-!
# GM Lemma 5.8: the Euclidean paths of Step 2, as a statement (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 1–2 (l. 3068–3091).

`L58Paths` is the planar (grid-free) part of the construction of `U_r^{x,y}`: the points `𝒵`
(l. 3069), the arcs (l. 3076–3077, as sets `a ∈ A` of at least `n` points, `#A · δ ≤ 100`), and,
for `x, y ∈ ∂B_{2r}(0)` with `|x − y| ≥ δr`, an arc `a = {z_0, …, z_{m−1}}` with compact connected
paths `P_0` (GM's `L̂_x`, from `x` to `z_0 − 2R`), `P_i` (GM's `L_k`, from `z_{i−1} + 2R` to
`z_i − 2R`) and `P_m` (GM's `L̂_y`, from `z_{m−1} + 2R` to `y`), `R = ρr`, `ρ = δ/(500n)`, in the
closed annulus `cl 𝔸_{r/2,2r}(0)`, pairwise at distance `≥ R` (GM: `≥ ρr`), and at distance `≥ 3R`
from each `z_j` except on the horizontal stubs at their own end points (decision D69: the paths
arrive at `z_j − 2R` horizontally from the left and leave `z_j + 2R` horizontally to the right).

The paths `P_0`, `P_m` end radially at `x`, `y` (`RadEnd`, decision D83 (c)). Proved in
`l58Paths` (`Geom58T4`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

/-- the Euclidean paths of GM Lemma 5.8, Step 2 (with D69's horizontal stubs); see the module
docstring; with radial ends at `x` and `y` (`RadEnd`, decision D83 (c)) -/
def L58Paths : Prop := ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ, 0 < n → ∀ r : ℝ, 0 < r →
  ∃ (Z : Finset ℂ) (A : Finset (Finset ℂ)), (A.card : ℝ) * δ ≤ 100 ∧
    (∀ a ∈ A, a ⊆ Z ∧ n ≤ a.card) ∧ (∀ z ∈ Z, ‖z‖ = r) ∧
    (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 8 * (δ / (500 * n) * r) ≤ ‖z - w‖) ∧
  ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
  ∃ a ∈ A, ∃ (m : ℕ) (zs : ℕ → ℂ) (P : ℕ → Set ℂ),
    a = (Finset.range m).image zs ∧ a.card = m ∧
    (∀ i ≤ m, IsCompact (P i) ∧ IsConnected (P i) ∧
      P i ⊆ {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) ∧
    x ∈ P 0 ∧ y ∈ P m ∧
    (∀ j < m, zs j - 2 * ((δ / (500 * n) * r : ℝ) : ℂ) ∈ P j ∧
      zs j + 2 * ((δ / (500 * n) * r : ℝ) : ℂ) ∈ P (j + 1)) ∧
    (∀ i ≤ m, ∀ i' ≤ m, i ≠ i' → ∀ p ∈ P i, ∀ q ∈ P i', δ / (500 * n) * r ≤ dist p q) ∧
    (∀ i ≤ m, ∀ j < m, ∀ p ∈ P i, dist p (zs j) < 3 * (δ / (500 * n) * r) →
      (i = j ∧ p.im = (zs j).im ∧ p.re ≤ (zs j).re - 2 * (δ / (500 * n) * r)) ∨
      (i = j + 1 ∧ p.im = (zs j).im ∧ (zs j).re + 2 * (δ / (500 * n) * r) ≤ p.re)) ∧
    RadEnd (P 0) x (r / 4) (δ / (500 * n) * r) ∧ RadEnd (P m) y (r / 4) (δ / (500 * n) * r)

end LQGMetric.GM
