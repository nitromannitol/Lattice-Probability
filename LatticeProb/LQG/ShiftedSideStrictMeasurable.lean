import LatticeProb.LQG.BrownianShiftedGridSideStrict
import LatticeProb.LQG.ShiftedMeshEdgeCode
import Mathlib.MeasureTheory.Measure.Prod

/-! # Measurability of strict side conditions on shifted grids -/

set_option autoImplicit false

open MeasureTheory Set Filter

namespace MatedCRTHarmonic.RouteM

open MatedCRTHarmonic.MatedCRT

/-- Strict side conditions form a Borel set of continuous paths. -/
theorem measurableSet_sideStrict (ε : ℝ) :
    MeasurableSet {w : Path2 | SideStrict ε w} := by
  have hm (b : Bool) (a c : ℝ) :
      Continuous (fun w : Path2 => intervalInf
        (fun t => if b then (w t).2 else (w t).1) a c) := by
    unfold intervalInf
    apply isCompact_Icc.continuous_sInf
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hpair (b : Bool) (x y : ℤ) : MeasurableSet {w : Path2 |
      x + 1 < y → SideCond ε (fun t => if b then (w t).2 else (w t).1) x y →
      max (intervalInf (fun t => if b then (w t).2 else (w t).1)
        (ε * ((x : ℝ) - 1)) (ε * x))
        (intervalInf (fun t => if b then (w t).2 else (w t).1)
        (ε * ((y : ℝ) - 1)) (ε * y)) <
        intervalInf (fun t => if b then (w t).2 else (w t).1)
          (ε * x) (ε * ((y : ℝ) - 1))} := by
    by_cases hxy : x + 1 < y
    · simp only [hxy, true_implies]
      have hle := measurableSet_le
        ((hm b (ε * ((x : ℝ) - 1)) (ε * x)).max
          (hm b (ε * ((y : ℝ) - 1)) (ε * y))).measurable
        (hm b (ε * x) (ε * ((y : ℝ) - 1))).measurable
      have hlt := measurableSet_lt
        ((hm b (ε * ((x : ℝ) - 1)) (ε * x)).max
          (hm b (ε * ((y : ℝ) - 1)) (ε * y))).measurable
        (hm b (ε * x) (ε * ((y : ℝ) - 1))).measurable
      convert hle.compl.union hlt using 1
      ext w
      simp only [SideCond, mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    · simp [hxy]
  simpa only [SideStrict, ofPred_forall] using
    MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun x =>
      MeasurableSet.iInter (fun y => hpair b x y)))

/-- A shifted strict-side event is Borel in the path and physical phase. -/
theorem measurableSet_shifted_sideStrict (ε : ℝ) :
    MeasurableSet {p : Path2 × ℝ | SideStrict ε
      ⟨fun t => p.1 (t + p.2), p.1.continuous.comp (by fun_prop)⟩} := by
  have h := (measurableSet_sideStrict ε).preimage
    (LatticeProb.continuous_shiftedMeshPath.comp
      (continuous_fst.prodMk ((continuous_const : Continuous (fun _ : Path2 × ℝ => (1 : ℝ))).prodMk continuous_snd))).measurable
  simpa [Function.comp_def, LatticeProb.shiftedMeshPath] using h

/-- Under a.e. Peanosphere existence, strict shifted sides hold jointly for
Brownian paths and any absolutely continuous s-finite phase law. -/
theorem ae_prod_shifted_sideStrict_of_correlatedBM
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hP : ∀ᵐ w ∂μ, ∃ η : ℝ → ℂ, Peanosphere w η) :
    ∀ᵐ p ∂μ.prod Q, SideStrict ε
      ⟨fun t => p.1 (t + p.2), p.1.continuous.comp (by fun_prop)⟩ := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_shifted_sideStrict ε)).2
  filter_upwards [ae_sideStrict_time_translate_of_correlatedBM hμ hε, hP] with w hw ⟨η, hη⟩
  exact hQ.ae_le (hw η hη)

end MatedCRTHarmonic.RouteM
