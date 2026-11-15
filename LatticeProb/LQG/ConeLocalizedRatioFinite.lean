import LatticeProb.LQG.ConeActualJointScaling
import LatticeProb.LQG.ConeJointPowerWindowLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Theorem44

/-! # Finiteness of the localized diameter-to-area ratio -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

/-- The localized diameter-to-area ratio has the same law at every positive
area-time scale for the coupled cone curve. -/
theorem measure_cone_locDA_gt_scale
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    {b : ℝ} (hb : 0 < b) (a : ℝ≥0∞) :
    P {ω | a < GMS4b.locDA b (η ω) 0} =
      P {ω | a < GMS4b.locDA 1 (η ω) 0} := by
  let E : Set C(ℝ, ℂ) := {c | a < GMS4b.locDA 1 c 0}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (GMS4b.measurable_locDA 1 0)
  have h := cone_actual_joint_scaling D hstd hγ hb (univ ×ˢ E)
    (MeasurableSet.univ.prod hE)
  have heq : {ω | (CellScaling.coneRescaleField γ
        (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
        (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
      CellScaling.coneRescaleCurve
        (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω)) ∈
        univ ×ˢ E} = {ω | a < GMS4b.locDA b (η ω) 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and, E]
    have hcurve : CellScaling.coneRescaleCurve
        (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω) =
        GMS4b.curveRescale
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω) := by
      ext t
      rfl
    rw [hcurve, GMS4b.locDA_curveRescale
      (show 0 < CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b from
        Real.exp_pos _) hb]
  rw [heq] at h
  simpa only [mem_ofPred_eq, mem_prod, mem_univ, true_and, E] using h

/-- The unit-scale localized diameter-to-area ratio is finite almost surely. -/
theorem ae_cone_locDA_lt_top
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {p q ρ r e s a ell : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) {M : ℕ} (hM : 0 < M)
    (he : 0 < e) (heupper : e < p ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) (ha : 0 < a) (hell : 0 < ell) :
    ∀ᵐ ω ∂P, GMS4b.locDA 1 (η ω) 0 < ⊤ := by
  have hlim := tendsto_measure_cone_localized_diameter_of_joint D hstd hγ μ hμ F hFm hF
    hp hq hqρ hρ1 hr hM he heupper hs hsγ ha hell
  have hzero : P {ω | GMS4b.locDA 1 (η ω) 0 = ⊤} = 0 := by
    apply le_antisymm ?_ (zero_le)
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := hδ
    have hb : 0 < δ ^ (2 + γ ^ 2 / 2 + p) / 4 := by positivity
    rw [measure_cone_locDA_gt_scale D hstd hγ hb] 
    apply measure_mono
    intro ω hω
    change GMS4b.locDA 1 (η ω) 0 = ⊤ at hω
    change ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
      GMS4b.locDA 1 (η ω) 0
    rw [hω]
    exact ENNReal.ofReal_lt_top
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with ω hω
  exact lt_top_iff_ne_top.mpr hω

end LatticeProb.LQG
