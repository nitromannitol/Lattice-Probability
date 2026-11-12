/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Cross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Start
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Lower
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCells

/-!
# DZZ Lemma 3.5: the deterministic crossing claim (statement) and the final inequality

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1083). DZZ's crossing claim:
"`(⋃ᵢ ℂᵢ) ∪ ℂ_start ∪ ℂ_end` contains a crossing between `A_δ` and `B_δ`" (justified by the
`i_r` recursion, l. 1076), whence (Eq.boundDprime)
`min D'_{δ'}(A, B) ≤ d λ/ε² + 2 δ^{-ι}(δ/δ')³`, `d = min D'_δ(A, B)`.

`L35Crossing` is this deterministic claim, stated for an arbitrary box-mass function `m`,
with generous constants (`4^{k+2}(λ+1)` cells per cell of the `δ`-geodesic, `2R + 8` for the two
ends) to absorb the discrete corner effects that DZZ's topological argument ignores. It is an
OPEN node (plane topology: Jordan-type separation by the enclosures, see the handoff).

* `StartCond`: the hypothesis on each end (`A = {u}` with the `ℂ_start` bound, or `A` connected
  and not inside any `𝖢_large`).
* `ennreal_chain`: the final arithmetic `D' ≤ d a + b`, `a ≤ Q/2`, `b ≤ N Q/2`, `N ≤ d` ⇒
  `D' ≤ d Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- The end condition of DZZ l. 1058–1066 for `A`: either `A = {u}` and
`D'_{δ'}(u, ∂𝖢_large ∩ 𝕍) ≤ R` for every cell `𝖢` with `u ∈ 𝖢_large`, or `A` is connected and
lies in no `𝖢_large`. -/
def StartCond (m : DyBox → ℝ) (δ δ' R : ℝ) (A : Set ℂ) : Prop :=
  (∃ u, A = {u} ∧ ∀ b, IsCell m δ b → u ∈ b.largeBox →
      ((approxDistSet m δ' {u} (frontier b.largeBox ∩ dzzV) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal R) ∨
    (IsConnected A ∧ ∀ b, IsCell m δ b → ¬ A ⊆ b.largeBox)

/-- **DZZ's crossing claim (l. 1071–1079), deterministic form** (open). The `δ'`-cells have
bounded level `≤ N₀` (Lemma 3.1 at `δ'`, `cellSizeEvent`; decision D84: without it, infinitely
fine `δ'`-cells accumulating at a corner where two ring cells touch break the count). If every
`δ`-cell has an enclosure (Def 3.6, `ε = 2^{-k}`) by boxes with `Ψ_{·,δ'} ≤ λ`, and both ends satisfy
`StartCond`, then `min D'_{δ'}(A,B) ≤ min D'_δ(A,B) · 4^{k+2}(λ+1) + (2R + 8)`. -/
def L35Crossing : Prop :=
  ∀ (m : DyBox → ℝ) (δ δ' lam R : ℝ) (k N₀ : ℕ) (A B : Set ℂ), 0 < δ' → δ' ≤ δ → 1 ≤ lam →
    0 ≤ R → (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) → (∀ b, IsCell m δ' b → b.n ≤ N₀) →
    (∀ b, IsCell m δ b → 1 ≤ b.n) →
    (∀ b, IsCell m δ b → HasEnclosure b k fun b' => PsiLe m δ' b' lam) →
    A ⊆ dzzV → B ⊆ dzzV → A.Nonempty → B.Nonempty →
    StartCond m δ δ' R A → StartCond m δ δ' R B →
    ((approxDistSet m δ' A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) +
        ENNReal.ofReal (2 * R + 8)

/-- The final arithmetic of DZZ l. 1079–1083. -/
lemma ennreal_chain {D d : ℝ≥0∞} {a b Q N : ℝ} (hD : D ≤ d * ENNReal.ofReal a + ENNReal.ofReal b)
    (ha : a ≤ Q / 2) (hb : b ≤ N * (Q / 2)) (hN0 : 0 ≤ N) (hN : ENNReal.ofReal N ≤ d)
    (hQ : 0 ≤ Q) : D ≤ d * ENNReal.ofReal Q := by
  have h1 : ENNReal.ofReal b ≤ d * ENNReal.ofReal (Q / 2) := by
    calc ENNReal.ofReal b ≤ ENNReal.ofReal (N * (Q / 2)) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal N * ENNReal.ofReal (Q / 2) := ENNReal.ofReal_mul hN0
      _ ≤ d * ENNReal.ofReal (Q / 2) := by gcongr
  have h2 : d * ENNReal.ofReal a ≤ d * ENNReal.ofReal (Q / 2) := by
    gcongr
  calc D ≤ d * ENNReal.ofReal a + ENNReal.ofReal b := hD
    _ ≤ d * ENNReal.ofReal (Q / 2) + d * ENNReal.ofReal (Q / 2) := add_le_add h2 h1
    _ = d * ENNReal.ofReal Q := by
      rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2; ring

end DZZ
end LQGMetric
