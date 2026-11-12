/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36Poly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Adapter
import LatticeProb.Bonanno.LQGDimension.LFPP.PolygonRiemann

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.6, deterministic part: LFPP length of a polygonal path

For DFGPS Lemma 3.6 (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:1628–1650) the
discretized LFPP `D̃^δ_h` is compared with continuum LFPP; the easy direction ("the upper bound in
DG Prop 3.16", DG arXiv:1807.01072 l. 1447–1452: concatenate the segments between consecutive
squares/vertices and bound the field on each segment by its value at a vertex plus the
oscillation) needs: a polygon through `V 0, …, V m` is a DG path and its LFPP length is at most
`Σ_i |V(i+1) − V i| e^{ξ (φ(V i) + osc φ r)}`.

Reuse: the polygon `polyPath`, its continuity and the edge decomposition `lfppLength_eq_sum`
come from LQGDimension (`LQGDimension.PolygonRiemannAux`); `osc`/`le_osc` likewise.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace LQGMetric.DFGPS.L36

open LQGDimension.PolygonRiemannAux

/-- A polygon through `V 0, …, V m` is a DG path in `ℂ` from `V 0` to `V m`. -/
theorem isDGPath_polyPath (V : ℕ → ℂ) (m : ℕ) (hm : 0 < m) :
    DG.IsDGPath univ (V 0) (V m) (polyPath V m) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  refine ⟨?_, ?_, mapsTo_univ _ _, continuousOn_polyPath V m hm, ?_⟩
  · have h00 : (0:ℝ) ∈ Icc ((0:ℝ)/m) (((0:ℝ)+1)/m) := ⟨by norm_num, by positivity⟩
    have h0eq : polyPath V m 0 = edgeAff V m 0 0 := by
      have := polyPath_eq_edgeAff V m hm 0 hm 0 (by simpa using h00)
      simpa using this
    rw [h0eq]
    unfold edgeAff
    simp
  · have hcast : ((m-1:ℕ):ℝ) + 1 = (m:ℝ) := by
      have hnat : (m-1)+1 = m := Nat.sub_add_cancel hm
      exact_mod_cast hnat
    have hlast : (1:ℝ) ∈ Icc (((m-1:ℕ):ℝ)/m) ((((m-1:ℕ):ℝ)+1)/m) := by
      rw [hcast]
      refine ⟨?_, by rw [div_self hm'.ne']⟩
      rw [div_le_one hm']
      have := Nat.sub_le m 1
      exact_mod_cast this
    have hm1lt : m - 1 < m := Nat.sub_lt hm Nat.one_pos
    have h11 : polyPath V m 1 = edgeAff V m (m-1) 1 :=
      polyPath_eq_edgeAff V m hm (m-1) hm1lt 1 hlast
    rw [h11]
    unfold edgeAff
    have hstep : (1:ℝ)*(m:ℝ) - ((m-1:ℕ):ℝ) = 1 := by rw [← hcast]; ring
    rw [hstep, one_smul]
    have hnat2 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hnat2]
    ring
  · refine ⟨m, fun j => (j:ℝ)/m, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
      show (a:ℝ)/m < (b:ℝ)/m
      exact div_lt_div_of_pos_right hab' hm'
    · simp
    · show ((Fin.last m : Fin (m+1)):ℝ)/m = 1
      rw [Fin.val_last]
      exact div_self hm'.ne'
    · intro i
      have hcd : ContDiff ℝ 1 (edgeAff V m i) := by unfold edgeAff; fun_prop
      have heq1 : (fun j : Fin (m+1) => (j:ℝ)/m) i.castSucc = (i:ℝ)/m := by simp
      have heq2 : (fun j : Fin (m+1) => (j:ℝ)/m) i.succ = ((i:ℝ)+1)/m := by simp
      rw [heq1, heq2]
      apply (hcd.contDiffOn (s := Icc ((i:ℝ)/m) (((i:ℝ)+1)/m))).congr
      intro t ht
      exact polyPath_eq_edgeAff V m hm i i.2 t ht

/-- The field on an edge is at most its value at the first vertex plus the oscillation. -/
theorem integral_seg_le (V : ℕ → ℂ) (φ : ℂ → ℝ) (hφ : Continuous φ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (r : ℝ) (i : ℕ) (hVi : ‖V i‖ ≤ 3) (hVi1 : ‖V (i+1)‖ ≤ 3) (hlen : ‖V (i+1) - V i‖ ≤ r) :
    (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s))) ≤
      Real.exp (ξ * (φ (V i) + LQGDimension.Blueprint.Draft.osc φ r)) := by
  have hcont : Continuous fun s : ℝ => Real.exp (ξ * φ (segAff V i s)) := by
    unfold segAff; fun_prop
  have hb : ∀ s ∈ Icc (0:ℝ) 1, Real.exp (ξ * φ (segAff V i s)) ≤
      Real.exp (ξ * (φ (V i) + LQGDimension.Blueprint.Draft.osc φ r)) := by
    intro s hs
    have hcombo : segAff V i s = (1-s) • (V i) + s • (V (i+1)) := by unfold segAff; module
    have hball : ‖segAff V i s‖ ≤ 3 := by
      rw [hcombo]
      calc ‖(1-s) • V i + s • V (i+1)‖ ≤ ‖(1-s) • V i‖ + ‖s • V (i+1)‖ := norm_add_le _ _
        _ = (1-s) * ‖V i‖ + s * ‖V (i+1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2]),
            Real.norm_of_nonneg hs.1]
        _ ≤ (1-s) * 3 + s * 3 := by
          gcongr
          · linarith [hs.2]
          · exact hs.1
        _ = 3 := by ring
    have hd : ‖segAff V i s - V i‖ ≤ r := by
      have : segAff V i s - V i = s • (V (i+1) - V i) := by unfold segAff; abel
      rw [this, norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖V (i+1) - V i‖ ≤ 1 * ‖V (i+1) - V i‖ := by gcongr; exact hs.2
        _ ≤ r := by rw [one_mul]; exact hlen
    have hosc := le_osc hφ hball hVi hd
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hξ
    have := (abs_le.1 hosc).2
    linarith
  calc (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)))
      ≤ ∫ _s in (0:ℝ)..1, Real.exp (ξ * (φ (V i) + LQGDimension.Blueprint.Draft.osc φ r)) :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
          intervalIntegrable_const hb
    _ = _ := by simp

/-- **Polygon bound.** If the vertices `V 0, …, V m` lie in `closedBall 0 3` and the edges have
length `≤ r`, then `D^δ(V 0, V m) ≤ Σ_{i<m} |V(i+1) − V i| e^{ξ (φ(V i) + osc φ r)}`. -/
theorem dgLFPP_le_poly (V : ℕ → ℂ) (m : ℕ) (hm : 0 < m) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (r : ℝ) (hV : ∀ i ≤ m, ‖V i‖ ≤ 3)
    (hlen : ∀ i < m, ‖V (i+1) - V i‖ ≤ r) :
    DG.dgLFPP ξ φ univ (V 0) (V m) ≤ ∑ i ∈ Finset.range m,
      ‖V (i+1) - V i‖ * Real.exp (ξ * (φ (V i) + LQGDimension.Blueprint.Draft.osc φ r)) := by
  have h1 : DG.dgLFPP ξ φ univ (V 0) (V m) ≤ LQGDimension.lfppLength ξ φ (polyPath V m) :=
    ciInf_le (DG.bddBelow_dg ξ φ univ (V 0) (V m)) ⟨polyPath V m, isDGPath_polyPath V m hm⟩
  refine h1.trans ?_
  rw [lfppLength_eq_sum V m φ hφ ξ hm]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact mul_le_mul_of_nonneg_left (integral_seg_le V φ hφ ξ hξ r i (hV i hi'.le) (hV (i+1) hi')
    (hlen i hi')) (norm_nonneg _)

end LQGMetric.DFGPS.L36
