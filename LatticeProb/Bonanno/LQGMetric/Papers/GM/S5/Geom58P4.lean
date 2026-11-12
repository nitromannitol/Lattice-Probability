/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58P4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P3

/-!
# GM Lemma 5.8: the paths of one window (task P2-M2L58c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086). For a window `z_j = winPt r R c j` (`j < n`) whose angular band
avoids `x`, the family `P_0 = L̂_x`, `P_{k+1} = ` staircase `z_k → z_{k+1}` (`k + 1 < n`),
`P_n = L̂_y` (`pathFam`); `window_paths` (`Geom58T3`) shows it has all the properties required in
`L58Paths`. Own elementary construction (GM leave the paths implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

/-- the family `P_0 = L`, `P_{k+1} = S k` for `k + 1 < n`, `P_i = Rt` otherwise -/
def pathFam (L Rt : Set ℂ) (n : ℕ) (S : ℕ → Set ℂ) : ℕ → Set ℂ
  | 0 => L
  | k + 1 => if k + 1 < n then S k else Rt

lemma pathFam_cases {L Rt : Set ℂ} {n i : ℕ} {S : ℕ → Set ℂ} (hn : 0 < n) (hi : i ≤ n) :
    (i = 0 ∧ pathFam L Rt n S i = L) ∨ (∃ k, i = k + 1 ∧ k + 1 < n ∧ pathFam L Rt n S i = S k) ∨
      (i = n ∧ pathFam L Rt n S i = Rt) := by
  rcases i with _ | k
  · exact Or.inl ⟨rfl, rfl⟩
  · by_cases h : k + 1 < n
    · exact Or.inr (Or.inl ⟨k, rfl, h, if_pos h⟩)
    · exact Or.inr (Or.inr ⟨by omega, if_neg h⟩)

lemma pathFam_n {L Rt : Set ℂ} {n : ℕ} {S : ℕ → Set ℂ} (hn : 0 < n) : pathFam L Rt n S n = Rt := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact if_neg (lt_irrefl _)

end LQGMetric.GM
