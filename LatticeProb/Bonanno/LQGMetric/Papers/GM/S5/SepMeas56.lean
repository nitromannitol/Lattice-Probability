/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.SepMeas56 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes56Geom

/-!
# GM Lemma 5.6: the corrected deterministic geometry statement (decision D69, task P2-SEPDEC)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6 (l. 2959–2995).

`L56GeomN` is `L56Geom` (`Tubes56Geom.lean`) with the two corrections of D69:

* the squares are those of `𝓢_{ε₁r}(cl B_{2r}(z))`. With GM's open ball `B_{2r}(z)` the statement
  is false: if `z − 2r` lies on a vertical grid line `Re w = m ε₁ r`, the squares to its left do
  not meet the open ball, so `z − 2r` lies on the boundary of every union of squares of
  `𝓢_{ε₁r}(B_{2r}(z))` (e.g. `z = 2r`, `z − 2r = 0`); with the closed ball every square containing
  `z ± 2r` belongs to `𝒦` (they meet `P̃′ ∋ z ± 2r`);
* condition 2 in the robust form `SepDiscNear` (`Defs.lean`; D69, with GM's disconnection clause
  `z ± 2r ∉` the component of `z ∓ 2r` in `V ∖ O_{u'}` added by D77): GM's argument (l. 2982–2989) uses only
  that the squares near the junction of `π₋ ∪ L₋` and `H` lie in `B_{10ε₁r}(u)`, hence in
  `O_{u'}` for every `u'` close to `u`, so it gives condition 2 at every point of a neighbourhood of
  `u`. (Caution for the prover: with GM's literal `𝒦` (all squares meeting the radial segment `L₋`),
  the staircase of squares along `L₋` can leave, at the sphere `∂B_{20ε₁r}(u)`, a corner piece of a
  square outside `O_u` that is a separate component of `V ∖ O_u` at distance `< ε₁r` from the
  component of `z − 2r`; near `u` use instead an axis-parallel corridor of squares, whose part
  outside `B_{20ε₁r}(u')` is connected.)

`squareSet_closedBall_subset_box`: the square count with the closed ball (box of `𝓢(B_{3r}(z))`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- **the deterministic part of GM Lemma 5.6**, corrected (D69); see the module docstring -/
def L56GeomN : Prop := ∀ α : ℝ, 3 / 4 ≤ α → α < 1 → ∀ χ : ℝ, 0 < χ →
  ∃ b₁ κ ε' : ℝ, b₁ ∈ Ioo (0 : ℝ) (1 / 100) ∧ b₁ ≤ 1 - α ∧ 0 < κ ∧ 0 < ε' ∧
  ∀ ε₁ ∈ Ioo (0 : ℝ) ε', ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ H : Set ℂ, IsHalfAnnulus H z (α * r) r →
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, ∀ T : Set ℂ, T ⊆ closure H → IsConnected T →
    u ∈ T → v ∈ T →
  ∃ F : Finset (ℤ × ℤ), (↑F : Set (ℤ × ℤ)) ⊆ squareSet (ε₁ * r) (closedBall z (2 * r)) ∧
    IsConnected (tubeOf (ε₁ * r) F) ∧ tubeOf (ε₁ * r) F ⊆ ball z ((2 + 2 * ε₁) * r) ∧
    z - 2 * r ∈ tubeOf (ε₁ * r) F ∧ z + 2 * r ∈ tubeOf (ε₁ * r) F ∧ T ⊆ tubeOf (ε₁ * r) F ∧
    SepDiscNear (tubeOf (ε₁ * r) F) (20 * ε₁ * r) u (z - 2 * r) (z + 2 * r) (ε₁ * r) ∧
    SepDiscNear (tubeOf (ε₁ * r) F) (20 * ε₁ * r) v (z + 2 * r) (z - 2 * r) (ε₁ * r) ∧
    ∀ d : ContMetric, d.IsLength → ∀ t : ℝ, 0 ≤ t →
      (∀ (j : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m ∩ ball z (3 * r)).Nonempty →
        internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m)
          (gridSquare ((2 : ℝ)⁻¹ ^ j * ε₁ * r) m) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) →
      (∀ w ∈ nearComp (tubeOf (ε₁ * r) F) (20 * ε₁ * r) u,
        d.internal (tubeOf (ε₁ * r) F) u w ≤ ENNReal.ofReal (κ * t)) ∧
      (∀ w ∈ nearComp (tubeOf (ε₁ * r) F) (20 * ε₁ * r) v,
        d.internal (tubeOf (ε₁ * r) F) v w ≤ ENNReal.ofReal (κ * t))

/-- `𝓢_s(X)` is monotone in `X` -/
lemma squareSet_mono (s : ℝ) {X Y : Set ℂ} (h : X ⊆ Y) : squareSet s X ⊆ squareSet s Y :=
  fun _ ⟨x, hx1, hx2⟩ => ⟨x, hx1, h hx2⟩

/-- `𝓢_s(cl B_{2r}(z))` lies in the index box of `𝓢_s(B_{3r}(z))` -/
lemma squareSet_closedBall_subset_box {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : ℂ) :
    squareSet s (closedBall z (2 * r)) ⊆ ↑(sqBox s (3 * r) z) :=
  (squareSet_mono s (closedBall_subset_ball (by linarith))).trans
    (squareSet_ball_subset_box hs _ _)

lemma boxLen_eq3 {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    boxLen (ε * r) (3 * r) = ⌈6 / ε⌉₊ + 1 := by
  unfold boxLen; congr 2; field_simp; ring

end LQGMetric.GM
