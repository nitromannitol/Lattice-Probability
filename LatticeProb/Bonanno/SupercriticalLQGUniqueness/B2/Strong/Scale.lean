/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Scale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Bridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Dilate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Tight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import LatticeProb.Bonanno.NV1Evidence

 












set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC ofCont addFun addConst IsGFFPlusCont affineComp circleAvg)

namespace SupercriticalLQGUniqueness.B2.Strong

 
def rescaledField (h : DistC) (r : Set.Ioi (0 : ℝ)) : DistC :=
  addConst (affineComp (r : ℝ) 0 h) (-circleAvg h r 0)

theorem measurable_rescaledField (r : Set.Ioi (0 : ℝ)) :
    Measurable fun h : DistC => rescaledField h r :=
  LQGMetric.DFGPS.L219.measurable_addConst_of (LQGMetric.measurable_affineComp _ _)
    (LQGMetric.measurable_circleAvg_left _ _).neg

theorem exp_scale_eq (ξ Q r a : ℝ) (hr : 0 < r) :
    Real.exp (ξ * (-(Q * Real.log r) - a)) = r ^ (-(ξ * Q)) * Real.exp (-(ξ * a)) := by
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  congr 1
  ring

 


theorem ae_annulus_scale {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hS : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) (r : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ A : EuclideanAnnulus,
      acrossDist (D (rescaledField (h ω) r)) A =
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * circleAvg (h ω) r 0))) *
            acrossDist (D (h ω)) (A.dilate r r.2) ∧
        aroundDist (D (rescaledField (h ω) r)) A =
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * circleAvg (h ω) r 0))) *
            aroundDist (D (h ω)) (A.dilate r r.2) := by
  set ht : Ω → DistC := fun ω => addConst (scaleTranslateDist r 0 (h ω)) (Q * Real.log r)
  have hht : IsGFFPlusCont ht P := by
    have e : ht = fun ω => addConst (affineComp (r : ℝ) 0 (h ω)) (Q * Real.log r) := by
      funext ω; simp only [ht, scaleTranslateDist_eq_affineComp]
    rw [e]
    exact Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
      (LQGMetric.GM.isGFFPlusCont_affineComp hh r.2 0) measurable_const
  filter_upwards [hS.2.2.2.2.1 P h hh r 0, hS.2.2.2.1 P ht hht, hS.2.1 P ht hht] with ω h4 h3 h1
  intro A
  set c : ℝ := -(Q * Real.log r) - circleAvg (h ω) r 0
  have hg : rescaledField (h ω) r = addFun (ht ω) (ContinuousMap.const ℂ c) := by
    simp only [ht, rescaledField, addFun_addConst_const, scaleTranslateDist_eq_affineComp, c]
    congr 1
    ring
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c))
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hw : ∀ x y : ℂ, D (rescaledField (h ω) r) (x, y) = k * D (ht ω) (x, y) := by
    intro x y
    have := congrFun (h3 (ContinuousMap.const ℂ c)) (x, y)
    rw [weylScale_const _ _ _ h1] at this
    rw [hg]
    exact this.symm
  have hm : ∀ x y : ℂ, D (ht ω) (x, y) = D (h ω) ((r : ℝ) • x, (r : ℝ) • y) := by
    intro x y
    have := h4 x y
    simp only [add_zero] at this
    exact this.symm
  have hk : k = ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r 0))) := by
    simp only [k, c, exp_scale_eq _ _ _ _ r.2]
  rw [← hk, Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale (D (ht ω)) _ k hk0 hkt hw,
    Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale (D (ht ω)) _ k hk0 hkt hw,
    acrossDist_eq_of_dilate _ _ r.2 hm, aroundDist_eq_of_dilate _ _ r.2 hm]
  exact ⟨rfl, rfl⟩

end SupercriticalLQGUniqueness.B2.Strong
