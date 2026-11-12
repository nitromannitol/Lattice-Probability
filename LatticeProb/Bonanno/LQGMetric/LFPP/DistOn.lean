/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.DistOn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathAnalytic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP

/-!
# The LFPP distance with a general density, internal to a set

Task P2-LFPP. For `φ : ℂ → ℝ` and `S ⊆ ℂ`, `lfppDOn ξ φ S z w` is the infimum of
`∫₀¹ e^{ξ φ(P)} |P'|` over piecewise C¹ paths `P : z → w` staying in `S` (GM (1.4),
`uniqueness-final.tex` l. 216–220, for `S = ℂ`; DFGPS l. 285, `lqg-metric-estimates-final.tex`,
for `S = [0,1]²`). Both `lfppDistE` (Statement) and DFGPS's `lfppCrossIn` (Blueprint) are
instances. Elementary properties: triangle inequality, symmetry, `D(z,z) = 0`, segment bound,
chain bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ}

/-- `D^φ(z, w; S)` -/
def lfppDOn (ξ : ℝ) (φ : ℂ → ℝ) (S : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w ∧ ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S},
    lfppLen ξ φ P.1

theorem lfppDistE_eq_lfppDOn (ξ ε : ℝ) (h : DistC) (z w : ℂ) :
    lfppDistE ξ ε h z w = lfppDOn ξ (heatMollify ε h) univ z w :=
  le_antisymm (le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1⟩ le_rfl)
    (le_iInf fun P => iInf_le_of_le ⟨P.1, P.2, fun _ _ => mem_univ _⟩ le_rfl)

theorem lfppCrossIn_eq (ξ ε : ℝ) (h : DistC) :
    Blueprint.lfppCrossIn ξ ε h = (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
      lfppDOn ξ (heatMollify ε h) Blueprint.closedUnitSquare z w).toReal := rfl

theorem lfppCross_eq (ξ ε : ℝ) (h : DistC) :
    lfppCross ξ ε h = (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
      lfppDOn ξ (heatMollify ε h) univ z w).toReal := by
  simp only [lfppCross, lfppDistE_eq_lfppDOn]

theorem lfppDOn_le {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    (hPS : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S) : lfppDOn ξ φ S z w ≤ lfppLen ξ φ P :=
  iInf_le_of_le ⟨P, hP, hPS⟩ le_rfl

/-- **Triangle inequality.** -/
theorem lfppDOn_triangle (x y z : ℂ) :
    lfppDOn ξ φ S x z ≤ lfppDOn ξ φ S x y + lfppDOn ξ φ S y z := by
  refine ENNReal.le_iInf_add_iInf fun P R => ?_
  have hPR : P.1 1 = R.1 0 := P.2.1.target.trans R.2.1.source.symm
  rw [← lfppLen_concatPath hPR]
  refine lfppDOn_le (isPiecewiseC1Path_concatPath P.2.1 R.2.1) fun t ht => ?_
  simp only [concatPath]
  split_ifs with h
  · exact P.2.2 _ ⟨by linarith [ht.1], by linarith⟩
  · exact R.2.2 _ ⟨by linarith, by linarith [ht.2]⟩

/-- **Symmetry.** -/
theorem lfppDOn_comm (z w : ℂ) : lfppDOn ξ φ S z w = lfppDOn ξ φ S w z := by
  have key : ∀ z w : ℂ, lfppDOn ξ φ S w z ≤ lfppDOn ξ φ S z w := fun z w =>
    le_iInf fun P => by
      rw [← lfppLen_revPath P.1]
      exact lfppDOn_le (isPiecewiseC1Path_revPath P.2.1) fun t ht =>
        P.2.2 _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact le_antisymm (key w z) (key z w)

theorem segPath_mem (hS : Convex ℝ S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : segPath z w u ∈ S :=
  hS.add_smul_sub_mem hz hw hu

/-- the cost of the straight segment from `a` to `b` -/
def segCost (ξ : ℝ) (φ : ℂ → ℝ) (a b : ℂ) : ℝ≥0∞ := lfppLen ξ φ (segPath a b)

theorem lfppDOn_le_segCost (hS : Convex ℝ S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    lfppDOn ξ φ S z w ≤ segCost ξ φ z w :=
  lfppDOn_le (isPiecewiseC1Path_segPath z w) fun _ hu => segPath_mem hS hz hw hu

theorem segCost_le {z w : ℂ} {B : ℝ}
    (hB : ∀ x ∈ Metric.closedBall z ‖w - z‖, Real.exp (ξ * φ x) ≤ B) :
    segCost ξ φ z w ≤ ENNReal.ofReal (B * ‖w - z‖) :=
  lfppLen_segPath_le z w hB

theorem lfppDOn_self (hS : Convex ℝ S) {z : ℂ} (hz : z ∈ S) : lfppDOn ξ φ S z z = 0 := by
  refine le_antisymm ((lfppDOn_le_segCost hS hz hz).trans ((segCost_le
    (B := Real.exp (ξ * φ z)) fun x hx => ?_).trans (by simp))) bot_le
  simp only [sub_self, norm_zero, Metric.closedBall_zero, mem_singleton_iff] at hx
  rw [hx]

/-- **Chain bound**: `D(v₀, v_N) ≤ Σ_{i<N} segCost(v_i, v_{i+1})` for vertices in convex `S`. -/
theorem lfppDOn_le_sum_segCost (hS : Convex ℝ S) (v : ℕ → ℂ) (hv : ∀ i, v i ∈ S) (N : ℕ) :
    lfppDOn ξ φ S (v 0) (v N) ≤ ∑ i ∈ Finset.range N, segCost ξ φ (v i) (v (i + 1)) := by
  induction N with
  | zero => simp [lfppDOn_self hS (hv 0)]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (lfppDOn_triangle _ (v N) _).trans
      (add_le_add ih (lfppDOn_le_segCost hS (hv N) (hv (N + 1))))

end LFPP
end LQGMetric
