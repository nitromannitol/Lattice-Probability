/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Cond3

/-!
# GM Lemma 5.6, deterministic node: condition 3 discharged (task P2-M2L56)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6 (l. 2959–2995).
`l56GeomN_of_constr : L56ConstrN → L56GeomN`: condition 3 of `L56GeomN` (GM l. 2991–2994) holds for
every square tube (`geom56_cond3`, with `κ = (2 + 2·43²)·whitC χ`, independent of `ε₁`), so
`L56GeomN` reduces to `L56ConstrN`: the construction of the tube (GM l. 2963–2968: paths `π±`,
`L±`, the squares meeting `P̃′`, with the axis-parallel corridor of decision D69 near `u`, `v`),
its connectivity, `z ± 2r ∈ V`, `T ⊆ V`, and condition 2 (`SepDiscNear`: separation and
disconnection, GM l. 2982–2989; decisions D69, D77).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `L56GeomN` without condition 3: the construction of the tube and condition 2 (GM l. 2963–2968,
2982–2989; decision D69) -/
def L56ConstrN : Prop := ∀ α : ℝ, 3 / 4 ≤ α → α < 1 →
  ∃ b₁ ε' : ℝ, b₁ ∈ Ioo (0 : ℝ) (1 / 100) ∧ b₁ ≤ 1 - α ∧ 0 < ε' ∧
  ∀ ε₁ ∈ Ioo (0 : ℝ) ε', ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ H : Set ℂ, IsHalfAnnulus H z (α * r) r →
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, ∀ T : Set ℂ, T ⊆ closure H → IsConnected T →
    u ∈ T → v ∈ T →
  ∃ F : Finset (ℤ × ℤ), (↑F : Set (ℤ × ℤ)) ⊆ squareSet (ε₁ * r) (closedBall z (2 * r)) ∧
    IsConnected (tubeOf (ε₁ * r) F) ∧ tubeOf (ε₁ * r) F ⊆ ball z ((2 + 2 * ε₁) * r) ∧
    z - 2 * r ∈ tubeOf (ε₁ * r) F ∧ z + 2 * r ∈ tubeOf (ε₁ * r) F ∧ T ⊆ tubeOf (ε₁ * r) F ∧
    SepDiscNear (tubeOf (ε₁ * r) F) (20 * ε₁ * r) u (z - 2 * r) (z + 2 * r) (ε₁ * r) ∧
    SepDiscNear (tubeOf (ε₁ * r) F) (20 * ε₁ * r) v (z + 2 * r) (z - 2 * r) (ε₁ * r)

/-- **condition 3 of GM Lemma 5.6 is automatic**: `L56ConstrN` implies `L56GeomN` -/
theorem l56GeomN_of_constr (h : L56ConstrN) : L56GeomN := by
  intro α hα1 hα2 χ hχ
  obtain ⟨b₁, ε', hb, hb', hε', hmain⟩ := h α hα1 hα2
  have hW := whitC_pos hχ
  refine ⟨b₁, (2 + 2 * 43 ^ 2) * whitC χ, min ε' (1 / 100), hb, hb', by positivity,
    lt_min hε' (by norm_num), ?_⟩
  intro ε₁ hε₁ z r hr H hH u hu v hv T hT hTc huT hvT
  obtain ⟨F, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hmain ε₁
    ⟨hε₁.1, hε₁.2.trans_le (min_le_left _ _)⟩ z r hr H hH u hu v hv T hT hTc huT hvT
  refine ⟨F, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  intro d _hd t ht hsq
  have hs : 0 < ε₁ * r := mul_pos hε₁.1 hr
  have hε1 : ε₁ < 1 / 100 := hε₁.2.trans_le (min_le_right _ _)
  have hball : ∀ x : ℂ, dist x z ≤ r → ∀ (j : ℕ) (m : ℤ × ℤ),
      (gridSquare ((2 : ℝ)⁻¹ ^ j * (ε₁ * r)) m ∩ ball x (25 * (ε₁ * r))).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * (ε₁ * r)) m)
        (gridSquare ((2 : ℝ)⁻¹ ^ j * (ε₁ * r)) m) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t) := by
    intro x hx j m ⟨y, hy1, hy2⟩
    have e : (2 : ℝ)⁻¹ ^ j * (ε₁ * r) = (2 : ℝ)⁻¹ ^ j * ε₁ * r := (mul_assoc _ _ _).symm
    rw [e] at hy1 ⊢
    refine hsq j m ⟨y, hy1, ?_⟩
    rw [mem_ball] at hy2 ⊢
    calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ < 25 * (ε₁ * r) + r := add_lt_add_of_lt_of_le hy2 hx
      _ ≤ 3 * r := by nlinarith
  have e20 : 20 * ε₁ * r = 20 * (ε₁ * r) := mul_assoc _ _ _
  have hαr : α * r ≤ r := mul_le_of_le_one_left hr.le hα2.le
  rw [e20]
  refine ⟨geom56_cond3 d hs F u hχ ht (hball u ?_), geom56_cond3 d hs F v hχ ht (hball v ?_)⟩
  · rw [mem_sphere] at hu; rw [hu]; exact hαr
  · rw [mem_sphere] at hv; rw [hv]

end LQGMetric.GM
