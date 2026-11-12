/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TreeInequalityAux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
* Combinatorics of well-formed cut trees (`CutTree.WF`): prefix closure, positivity of the
  chord lengths, consecutive child times, the unit flow, and the decomposition of the leaves
  below an internal node into the leaves below its children.
* An abstract "tree Jensen" inequality (`tree_jensen_root`): if a node function `L` is additive
  over children and dominates `R_v e^{F v}` at leaves, then
  `F [] + Σ_v θ(v) Σ_{j<|v|} Y(v.take j) ≤ log L []` whenever
  `Y u ≤ A_u + Σ_i q_i F(u i) - F u` at internal nodes.
* Analytic facts about admissible paths: integrability of `|γ'|`, chord ≤ arclength, additivity
  of the LFPP length over the tree, and the leaf bound.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Classical

namespace LQGDimension.TreeIneqJ42

open Blueprint.Draft

/-! ## Combinatorics of well-formed cut trees -/

section Tree

variable {T : CutTree} {γ : ℝ → ℂ} {M : ℕ} {ε : ℝ}

/-! ### Leaves below a node -/

/-! ### Chain sums and the tree Jensen inequality -/

/-! ### The local bound (4.3) -/

end Tree

/-! ## Analytic lemmas on admissible paths -/

section Path

variable {γ : ℝ → ℂ}

theorem abs_sub_le_osc {φ : ℂ → ℝ} (hφ : Continuous φ) {r : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ 3)
    (hw : ‖w‖ ≤ 3) (hzw : ‖z - w‖ ≤ r) : |φ z - φ w| ≤ osc φ r := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn
    hφ.continuousOn
  refine le_csSup ⟨2 * C, ?_⟩ ⟨z, w, hz, hw, hzw, rfl⟩
  rintro x ⟨z', w', hz', hw', -, rfl⟩
  have h1 := hC z' (mem_closedBall_zero_iff.2 hz')
  have h2 := hC w' (mem_closedBall_zero_iff.2 hw')
  rw [Real.norm_eq_abs] at h1 h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

theorem exists_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) :
    ∃ i : Fin k, t i.castSucc < x ∧ x < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < x :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < x := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hx.1)⟩
  have hm : t (S.max' hne) < x := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hx.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge x (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hxt ⟨_, h⟩

theorem hasDerivAt_of_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) : HasDerivAt γ (deriv γ x) x := by
  obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
  exact ((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt

theorem deriv_bound_piece {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖deriv γ x‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact (hC' x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

/-! ### The LFPP length along the tree -/

variable {T : CutTree} {M : ℕ} {ε : ℝ}

end Path

end LQGDimension.TreeIneqJ42
