import LatticeProb.LQG.ConeCouplingExitSelection
import LatticeProb.Topology.FirstExitTraceTimeChange

/-! # First-exit trace areas under a coupling time change -/

set_option autoImplicit false

open MeasureTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- On a single coupling event, good scales for the Lebesgue-time curve give
first-exit area bounds for the area-time curve on any covered scale interval. -/
theorem ae_coupling_first_exit_trace_area_of_selected_scales
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ (K : Finset ℤ) (L R : ℝ),
      (∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log R → k ∈ K) →
      (∀ k ∈ K, F (ηL ω) ∉ firstExitBallFailure id ε k) →
      ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log R →
        ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
          min (volume (η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (Real.exp k)}) 0))
            (volume (η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (Real.exp k)}))) := by
  filter_upwards [D.areaParam] with ω harea
  obtain ⟨⟨φ, hφ0, hη⟩, _⟩ := harea
  intro K L R hcover hgood k hkL hkR
  have htrace := first_exit_trace_area_comp_orderIso id (F (ηL ω)) (ηL ω)
    (hF (ηL ω)) φ hφ0 hε k (hgood k (hcover k hkL hkR))
  have heq : (η ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ φ := funext hη
  simpa only [heq] using htrace

/-- The padded cone scales cover the logarithmic interval between the two
cone scales, so good selected scales supply the trace bounds on that interval. -/
theorem ae_coupling_first_exit_trace_area_of_cone_scales
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {ε : ℝ} (hε : 0 < ε) (b₁ b₂ : ℝ) :
    ∀ᵐ ω ∂P,
      (∀ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
        F (ηL ω) ∉ firstExitBallFailure id ε k) →
      ∀ k : ℤ,
        Real.log (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₁) - 1 <
          (k : ℝ) →
        (k : ℝ) ≤ Real.log (CellScaling.coneScale γ γ
          (fun s => B s ω) (fun s => B' s ω) b₂) →
        ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
          min (volume (η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (Real.exp k)}) 0))
            (volume (η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (Real.exp k)}))) := by
  filter_upwards [ae_coupling_first_exit_trace_area_of_selected_scales D F hF hε] with ω hω
  apply hω (conePaddedScales γ γ B B' b₁ b₂ ω)
    (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₁)
    (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₂)
  intro k hkL hkR
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.ceil_le.mpr (le_of_lt hkL)
  · exact Int.le_floor.mpr (le_trans hkR (le_add_of_nonneg_right zero_le_one))

end LatticeProb
