/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm11Wire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS

local notation "SQ" => C(closedUnitSquare × closedUnitSquare, ℝ)

lemma measurable_sqMetric_path {Ω : Type} [MeasurableSpace Ω] {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) (ξ a : ℝ) :
    Measurable fun ω => sqMetricC ξ a (fun x => Y x ω) := by
  have h : Measurable (sqFun ξ a ∘ pathC Y hYc) :=
    (measurable_sqFun ξ a).comp (measurable_pathC hYc hYm)
  have e : (sqFun ξ a ∘ pathC Y hYc) = fun ω => sqMetricC ξ a (fun x => Y x ω) :=
    funext fun ω => rfl
  rwa [e] at h

/-- **DDDF Theorem 1 (1)** from (5.54) (for `λ_δ > 0`, via (6.98)) and the uniform Hölder bounds
(UpperHolder), (LowerHolder) of Prop 28 for the family `δ ∈ (0,1)` (l. 1398, 1450, 1648). -/
theorem dddfThm1_1_of_holder
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧
      ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ S6UpperHolderD (xiGamma γ) W P β ∧
        S6LowerHolderD (xiGamma γ) W P α) :
    Blueprint.DDDFThm1_1 := by
  intro γ hγ hγ2 Ω _ P W hW
  obtain ⟨h554, α, β, hα, hβ, hUp, hLow⟩ := h γ hγ hγ2 P W hW
  have hP := hW.isProbabilityMeasure
  have h698 := s6_eq6_98_of_554 hγ hγ2 hW h554
  have hcont : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω, Continuous fun x => phiVer W P δ 1 x ω :=
    fun δ hδ => (isPhiVersion_phiVer hW hδ.1 hδ.2.le).cont
  have hmeasφ : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ x, Measurable (phiVer W P δ 1 x) :=
    fun δ hδ => (isPhiVersion_phiVer hW hδ.1 hδ.2.le).meas
  intro X
  have hXm : ∀ δ ∈ Ioo (0 : ℝ) 1, Measurable (X δ) := fun δ hδ =>
    measurable_sqMetric_path (hcont δ hδ) (hmeasφ δ hδ) _ _
  have hXapp : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω p, X δ ω p = (lambdaDelta (xiGamma γ) W P δ)⁻¹ *
      lenMetricOn (xiGamma γ) (fun x => phiVer W P δ 1 x ω) closedUnitSquare p.1 p.2 :=
    fun δ hδ ω p => sqMetricC_apply' (hcont δ hδ ω) p
  have hUp' : ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : closedUnitSquare, C * ‖(x : ℂ) - y‖ ^ β < X δ ω (x, y)} ≤
        ENNReal.ofReal ζ := fun ζ hζ => (hUp ζ hζ).imp fun C hC δ hδ => by
    refine le_trans (measure_mono ?_) (hC δ hδ)
    rintro ω ⟨x, y, hxy⟩
    exact ⟨x, y, by rwa [hXapp δ hδ ω] at hxy⟩
  have hLow' : ∀ ζ : ℝ, 0 < ζ → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : closedUnitSquare, X δ ω (x, y) < c * ‖(x : ℂ) - y‖ ^ α} ≤
        ENNReal.ofReal ζ := fun ζ hζ => (hLow ζ hζ).imp fun c hc => ⟨hc.1, fun δ hδ => by
    refine le_trans (measure_mono ?_) (hc.2 δ hδ)
    rintro ω ⟨x, y, hxy⟩
    exact ⟨x, y, by rwa [hXapp δ hδ ω] at hxy⟩⟩
  refine ⟨fun δ hδ ω => cont_sqLen (hcont δ hδ ω) _,
    tight_of_upper X hXm (fun δ hδ ω => pmet_sq (lambdaDelta_pos_of_698 hW h698 hδ).le
      (hcont δ hδ ω)) hβ hUp', fun δn ν μ hν _ hlim =>
    biHolder_of_bounds X hXm hα hβ hUp' hLow' δn ν μ hν hlim⟩

end S6Thm
end DDDF
end LQGMetric
