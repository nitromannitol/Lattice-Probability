/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Law at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import Mathlib.MeasureTheory.Function.FactorsThrough




 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

 
def sampleC {Ω : Type*} (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω)
    (ω : Ω) : C(ℂ, ℝ) :=
  ⟨fun x => Y x ω, hYc ω⟩

@[simp] theorem sampleC_apply {Ω : Type*} (Y : ℂ → Ω → ℝ)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) (x : ℂ) :
    sampleC Y hYc ω x = Y x ω := rfl

 
theorem exists_pi_factor {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] {g : C(ℂ, ℝ) → β} (hg : Measurable g) :
    ∃ h : (ℂ → ℝ) → β, Measurable h ∧ ∀ f : C(ℂ, ℝ), g f = h f := by
  have hg' : Measurable[MeasurableSpace.comap (fun f : C(ℂ, ℝ) => (f : ℂ → ℝ))
      MeasurableSpace.pi] g := by
    rw [← LQGMetric.DDDF.measurableSpace_continuousMap_eq_comap]
    exact hg
  obtain ⟨h, hm, hh⟩ := hg'.exists_eq_measurable_comp
  exact ⟨h, hm, fun f => congrFun hh f⟩

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]

 
theorem measurable_sampleC_comp {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] {g : C(ℂ, ℝ) → β} (hg : Measurable g) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => g (sampleC Y hYc ω) := by
  obtain ⟨h, hm, hh⟩ := exists_pi_factor hg
  have e : (fun ω => g (sampleC Y hYc ω)) = fun ω => h (fun x => Y x ω) := by
    funext ω; rw [hh]; rfl
  rw [e]
  exact hm.comp (measurable_pi_iff.mpr hYm)

 
theorem lintegral_sampleC_eq {g : C(ℂ, ℝ) → ℝ≥0∞} (hg : Measurable g)
    {P : Measure Ω} {P₂ : Measure Ω₂} {Y : ℂ → Ω → ℝ} {Y₂ : ℂ → Ω₂ → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hY₂c : ∀ ω, Continuous fun x => Y₂ x ω) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hlaw : P.map (fun ω x => Y x ω) = P₂.map (fun ω x => Y₂ x ω)) :
    ∫⁻ ω, g (sampleC Y hYc ω) ∂P = ∫⁻ ω, g (sampleC Y₂ hY₂c ω) ∂P₂ := by
  obtain ⟨h, hm, hh⟩ := exists_pi_factor hg
  have e1 : (fun ω => g (sampleC Y hYc ω)) = fun ω => h (fun x => Y x ω) := by
    funext ω; rw [hh]; rfl
  have e2 : (fun ω => g (sampleC Y₂ hY₂c ω)) = fun ω => h (fun x => Y₂ x ω) := by
    funext ω; rw [hh]; rfl
  rw [e1, e2, ← lintegral_map hm (measurable_pi_iff.mpr hYm),
    ← lintegral_map hm (measurable_pi_iff.mpr hY₂m), hlaw]

 
theorem indepFun_sampleC {β γ : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    [Nonempty β] [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {g₁ : C(ℂ, ℝ) → β} {g₂ : C(ℂ, ℝ) → γ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    {P : Measure Ω} {Y₁ Y₂ : ℂ → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous fun x => Y₁ x ω) (hc₂ : ∀ ω, Continuous fun x => Y₂ x ω)
    (hind : IndepFun (fun ω x => Y₁ x ω) (fun ω x => Y₂ x ω) P) :
    IndepFun (fun ω => g₁ (sampleC Y₁ hc₁ ω)) (fun ω => g₂ (sampleC Y₂ hc₂ ω)) P := by
  obtain ⟨h₁, hm₁, hh₁⟩ := exists_pi_factor hg₁
  obtain ⟨h₂, hm₂, hh₂⟩ := exists_pi_factor hg₂
  have e1 : (fun ω => g₁ (sampleC Y₁ hc₁ ω)) = h₁ ∘ fun ω x => Y₁ x ω := by
    funext ω; rw [hh₁]; rfl
  have e2 : (fun ω => g₂ (sampleC Y₂ hc₂ ω)) = h₂ ∘ fun ω x => Y₂ x ω := by
    funext ω; rw [hh₂]; rfl
  rw [e1, e2]
  exact hind.comp hm₁ hm₂

 

def polyCostC (ξ : ℝ) (f : C(ℂ, ℝ)) : ℝ≥0∞ := Exponent.PolygonalCost.polyAnnularCost ξ f

theorem measurable_polyCostC (ξ : ℝ) : Measurable (polyCostC ξ) := by
  have h := Exponent.PolygonalCost.measurable_polyAnnularCost (Ω := C(ℂ, ℝ))
    (Y := fun x (f : C(ℂ, ℝ)) => f x) (fun f => f.continuous)
    (fun x => ContinuousMap.measurable_eval x) ξ
  exact h

 
theorem lintegral_polyAnnularCost_eq_of_law (ξ : ℝ) {P : Measure Ω} {P₂ : Measure Ω₂}
    {Y : ℂ → Ω → ℝ} {Y₂ : ℂ → Ω₂ → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hY₂c : ∀ ω, Continuous fun x => Y₂ x ω) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hlaw : P.map (fun ω x => Y x ω) = P₂.map (fun ω x => Y₂ x ω)) :
    ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) ∂P =
      ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y₂ x ω) ∂P₂ :=
  lintegral_sampleC_eq (measurable_polyCostC ξ) hYc hYm hY₂c hY₂m hlaw

 
end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
