/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XSq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Cross
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XBridge

/-!
# DZZ Lemma 3.5: the crossing claim on the square grid (P2-DEC84, decision D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1079). Decision D84 keeps the
path-based enclosure of Definition 3.6 (`EnclosesBox`); `sqSep_of_enclosesBox` (S3L5XBridge)
turns it into the discrete separation `SqSep` of 4-paths of squares at every fine level `N`.

* `EncSq b k lam m δ'`: the data of an enclosure of `b` used by the crossing argument
  (the boxes of Def 3.6 with `Ψ_{·,δ'} ≤ λ`, separating 4-paths of level-`N` squares for all
  `N ≥ n_b + k + 1`).
* `L35CrossingSq`: `L35Crossing` with the enclosure hypothesis in this discrete form (open; purely
  combinatorial on the level-`N` grid, `N` beyond every `δ'`-cell level).
* **`l35Crossing_of_sq : L35CrossingSq → L35Crossing`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- The enclosure data of Def 3.6 in grid form: neighbouring boxes of `𝓑(b, 2^{-k})` in
`b_large \ b` with `Ψ_{·,δ'} ≤ λ`, separating 4-paths of level-`N` squares for `N ≥ n_b + k + 1`. -/
def EncSq (m : DyBox → ℝ) (δ' lam : ℝ) (b : DyBox) (k : ℕ) : Prop :=
  ∃ l : List DyBox, l ≠ [] ∧ l.IsChain DyBox.Neighbour ∧
    (∀ b' ∈ l, b' ∈ boxColl b k ∧ Disjoint (interior b'.closedBox) b.closedBox ∧
      PsiLe m δ' b' lam) ∧
    ∀ N, b.n + k + 1 ≤ N → SqSep N b {b' | b' ∈ l}

lemma encSq_of_hasEnclosure {m : DyBox → ℝ} {δ' lam : ℝ} {b : DyBox} {k : ℕ}
    (h : HasEnclosure b k fun b' => PsiLe m δ' b' lam) : EncSq m δ' lam b k := by
  obtain ⟨l, hne, hch, hall, henc⟩ := h
  refine ⟨l, hne, hch, hall, fun N hN => sqSep_of_enclosesBox henc (fun b' hb' => ?_) (by omega)⟩
  have := (hall b' hb').1.1
  omega

/-- **DZZ's crossing claim on the square grid** (open): `L35Crossing` with the enclosures given
by `EncSq` (discrete separation, D84). -/
def L35CrossingSq : Prop :=
  ∀ (m : DyBox → ℝ) (δ δ' lam R : ℝ) (k N₀ : ℕ) (A B : Set ℂ), 0 < δ' → δ' ≤ δ → 1 ≤ lam →
    0 ≤ R → (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) → (∀ b, IsCell m δ' b → b.n ≤ N₀) →
    (∀ b, IsCell m δ b → 1 ≤ b.n) →
    (∀ b, IsCell m δ b → EncSq m δ' lam b k) →
    A ⊆ dzzV → B ⊆ dzzV → A.Nonempty → B.Nonempty →
    StartCond m δ δ' R A → StartCond m δ δ' R B →
    ((approxDistSet m δ' A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) +
        ENNReal.ofReal (2 * R + 8)

theorem l35Crossing_of_sq (h : L35CrossingSq) : L35Crossing := by
  intro m δ δ' lam R k N₀ A B h1 h2 h3 h4 h5 h6 h7 h8 henc
  exact h m δ δ' lam R k N₀ A B h1 h2 h3 h4 h5 h6 h7 h8
    fun b hb => encSq_of_hasEnclosure (henc b hb)

end DZZ
end LQGMetric
