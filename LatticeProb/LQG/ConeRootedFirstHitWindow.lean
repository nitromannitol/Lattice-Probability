import LatticeProb.LQG.ConeFirstHitPowerWindow
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain

/-! # First-hit diameter estimates for a rooted coupling curve -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

/-- A first-hit estimate and a time-reversal law for the rooted coupling curve imply
    the localized power-window diameter limit. -/
theorem tendsto_measure_cone_localized_diameter_of_rooted_firstHit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    (g : Ω → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (hrev : ∀ ω t, g ω t = (F ∘ ηL) ω (-t))
    (hlaw : IdentDistrib g (F ∘ ηL) P P)
    {a₀ a₁ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 < a₁)
    (hbound : ∀ ρ : ℝ, 0 < ρ → ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ ∃ w, ball w (δ * ρ) ⊆
        (ηL ω) '' Icc (MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 ≤ t ∧
            ηL ω t ∉ ball 0 ρ})} ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ / δ)))
    (n : ℕ) (hn : 0 < n) {q ρ r e s a ell : ℝ} (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) {M : ℕ} (hM : 0 < M)
    (he : 0 < e) (heupper : e < (n : ℝ) ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) (ha : 0 < a) (hell : 0 < ell) :
    Tendsto (fun δ : ℝ =>
      P {ω | ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA (δ ^ (2 + γ ^ 2 / 2 + (n : ℝ)) / 4) (η ω) 0})
      (𝓝[>] 0) (𝓝 0) := by
  have hpath : ∀ᵐ ω ∂P, Continuous (ηL ω) ∧
      Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) ∧ (0 : ℂ) ∈ range (ηL ω) ∧
      ∀ t, (F ∘ ηL) ω t = Complex.orthonormalBasisOneI.repr
        (ηL ω (MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 + t) - 0) := by
    filter_upwards [D.spaceFilling,
      MatedCRTHarmonic.CellScaling.JointScalingO.ae_firstHit_zero_of_coupling D] with ω hspace hroot
    have hroot' : MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 = 0 := hroot
    refine ⟨(ηL ω).continuous, hspace.2.1, Set.mem_range.mpr (hspace.1 0), fun t => ?_⟩
    rw [Function.comp_apply, hF, hroot', zero_add, sub_zero]
  exact tendsto_measure_cone_localized_diameter_of_firstHit P D hstd hγ μ hμ F hFm hF
    (fun ω => ⇑(ηL ω)) 0 g (F ∘ ηL) (fun ω => ⇑(ηL ω)) 0 hrev hlaw
    ha₀ ha₁ ha₀ ha₁ hpath hbound hpath hbound n hn hq hqρ hρ1 hr hM he heupper
    hs hsγ ha hell

end LatticeProb.LQG
