/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_6Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.CircleUnion
import LatticeProb.Bonanno.LQGMetric.Statement.Metric

/-!
# LM Theorem 1.6: the deterministic chaining step (task P2-LM16)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.6 (`thm-bilip`), l. 838–882: along a path `P`
from `z₁` to `z₂`, the successive times `t_j` at which `P` crosses a good annulus
`A_{r_j/2, r_j}(w_j)` (l. 844–846), the bound (4.3) `sup_{u,v ∈ ∂B_{r_j}(w_j)} D̃(u,v) ≤
C(t_j − t_{j-1})` (l. 852–856), Lemma 4.3 (`lem-connected`, l. 858–875) and the triangle
inequality give `D̃(B_{2ε}(z₁), B_{2ε}(z₂)) ≤ C · len(P)` (l. 877–880).

* `chain_back`, `chain_main`: given the crossing data `(t_j, w_j, r_j)_{j ≤ J}`, every point of
  the last circle is within `D̃`-distance `C (T_J − T_0)` of a point of `cl B_{2ε}(z₁)`.
* `exists_crossings`: the construction of the times `t_j` (l. 844–847), from a cover of the path
  by good balls `B_{r/2}(w)` with `r ∈ [ρ, ε]`; the sequence stops after finitely many steps by
  uniform continuity of `P` (each step moves `P` by at least `ρ/2`).
* `lm_chain_det`: the conclusion of l. 877–880.

Departure (own elementary argument, see report): LM combine Lemma 4.3 (the union of the circles
contains a path) with "the triangle inequality". We instead run the triangle inequality along the
crossing sequence directly: for the circle `j`, go back to the last earlier circle `i` meeting it;
every circle in between lies inside `B_{r_j}(w_j)` (`TopoCircle.sphere_inter_sphere_nonempty`, the
same step as in LM's proof of Lemma 4.3, l. 869–871), and if there is none then `z₁ ∈ B_{r_j}(w_j)`.
This avoids turning a path in a union of circles into a chain of circles. The times `t_j` are
"some exit time" (by the intermediate value theorem) instead of LM's "smallest" exit time; only
the crossing property is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.LM

/-- Backward search (LM l. 869–871): if `p_i ∈ B_{r_j}(w_j)` for some `i < j`, then either an
earlier circle `∂B_{r_{i'}}(w_{i'})`, `1 ≤ i' ≤ i`, meets `∂B_{r_j}(w_j)`, or `p_0 ∈ B_{r_j}(w_j)`. -/
theorem chain_back (p w : ℕ → ℂ) (r : ℕ → ℝ) (J : ℕ)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i ≤ J → ‖p i - w i‖ = r i) (hr : ∀ i, 0 < r i)
    (j : ℕ) (hj : j ≤ J) : ∀ i, i < j → ‖p i - w j‖ < r j →
      (∃ i', 1 ≤ i' ∧ i' ≤ i ∧ (sphere (w i') (r i') ∩ sphere (w j) (r j)).Nonempty) ∨
        ‖p 0 - w j‖ < r j := by
  intro i
  induction i with
  | zero => intro _ h; exact Or.inr h
  | succ i ih =>
    intro hij hpi
    by_cases hmeet : (sphere (w (i + 1)) (r (i + 1)) ∩ sphere (w j) (r j)).Nonempty
    · exact Or.inl ⟨i + 1, le_add_self, le_rfl, hmeet⟩
    · have hsub : ball (w (i + 1)) (r (i + 1)) ⊆ ball (w j) (r j) := by
        by_contra hns
        exact hmeet (TopoCircle.sphere_inter_sphere_nonempty (hr _).le hns
          (x := p (i + 1)) (by rw [mem_sphere, dist_eq_norm]; exact hon _ le_add_self (by omega))
          (by rw [mem_ball, dist_eq_norm]; exact hpi))
      have hpi' : ‖p i - w j‖ < r j := by
        have h1 := hin (i + 1) le_add_self (by omega)
        simp only [Nat.add_sub_cancel] at h1
        have : p i ∈ ball (w (i + 1)) (r (i + 1)) := by
          rw [mem_ball, dist_eq_norm]; linarith [hr (i + 1)]
        have := hsub this
        rwa [mem_ball, dist_eq_norm] at this
      rcases ih (by omega) hpi' with ⟨i', h1, h2, h3⟩ | h
      · exact Or.inl ⟨i', h1, by omega, h3⟩
      · exact Or.inr h

/-- The chaining bound (LM l. 877–880): every point `u` of the circle `∂B_{r_j}(w_j)` is within
`D̃`-distance `C (T_j − T_0)` of a point of `cl B_{2ε}(p_0)`. -/
theorem chain_main (D' : ContMetric) {C ε : ℝ} (hC : 0 ≤ C) (p w : ℕ → ℂ) (r T : ℕ → ℝ)
    (J : ℕ) (hT : Monotone T)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i ≤ J → ‖p i - w i‖ = r i) (hr : ∀ i, 0 < r i) (hrε : ∀ i, r i ≤ ε)
    (hdiam : ∀ i, 1 ≤ i → i ≤ J → ∀ u ∈ sphere (w i) (r i), ∀ v ∈ sphere (w i) (r i),
      D'.1 (u, v) ≤ C * (T i - T (i - 1))) :
    ∀ j, 1 ≤ j → j ≤ J → ∀ u ∈ sphere (w j) (r j),
      ∃ x, ‖x - p 0‖ ≤ 2 * ε ∧ D'.1 (x, u) ≤ C * (T j - T 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjJ u hu
    have hpj : ‖p (j - 1) - w j‖ < r j := by linarith [hin j hj1 hjJ, hr j]
    rcases chain_back p w r J hin hon hr j hjJ (j - 1) (by omega) hpj with
      ⟨i', h1, h2, y, hy1, hy2⟩ | h0
    · obtain ⟨x, hx, hxy⟩ := ih i' (by omega) h1 (by omega) y hy1
      refine ⟨x, hx, ?_⟩
      have htri := D'.2.triangle x y u
      have hyu := hdiam j hj1 hjJ y hy2 u hu
      have hmono : T i' ≤ T (j - 1) := hT (by omega)
      nlinarith
    · refine ⟨u, ?_, ?_⟩
      · have hu' : ‖u - w j‖ = r j := by rw [mem_sphere, dist_eq_norm] at hu; exact hu
        calc ‖u - p 0‖ = ‖(u - w j) - (p 0 - w j)‖ := by congr 1; ring
          _ ≤ ‖u - w j‖ + ‖p 0 - w j‖ := norm_sub_le _ _
          _ ≤ 2 * ε := by linarith [hrε j]
      · rw [D'.2.self_eq_zero]
        exact mul_nonneg hC (by linarith [hT (Nat.zero_le j)])

end LQGMetric.LM
