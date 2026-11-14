/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianGaussianReference at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteStopping
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# One Gaussian reference for all positive-time spatial Brownian laws

Finite independent Gaussian coordinates identify the actual spatial marginal.
Positive Gaussian densities give absolute continuity relative to the time-one
marginal, uniformly as a qualitative statement over every spatial translation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

private lemma finitePi_absolutelyContinuous : ∀ (n : ℕ)
    (μ ν : Fin n → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
    (∀ i, IsProbabilityMeasure (ν i)) → (∀ i, μ i ≪ ν i) →
    Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
  | zero =>
    intro μ ν hμ hν h
    exact ((Measure.pi_of_empty μ).trans (Measure.pi_of_empty ν).symm).absolutelyContinuous
  | succ n ih =>
    intro μ ν hμ hν h
    let := hμ
    let := hν
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    have htail := ih (fun j ↦ μ ((0 : Fin (n + 1)).succAbove j))
      (fun j ↦ ν ((0 : Fin (n + 1)).succAbove j))
      (fun j ↦ hμ _) (fun j ↦ hν _) (fun j ↦ h _)
    have hprod := (h 0).prod htail
    have hmapμ := (measurePreserving_piFinSuccAbove μ 0).symm.map_eq
    have hmapν := (measurePreserving_piFinSuccAbove ν 0).symm.map_eq
    rw [← hmapμ, ← hmapν]
    exact hprod.map e.symm.measurable

/-- The actual Euclidean marginal is the assembled product of its independent
one-dimensional Gaussian marginals. -/
lemma standardBrownianLaw_map_translated_eval {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (z : Euc d) (t : ℝ≥0) :
    μ.map (fun ω : BrownianPath d ↦ z + ω t) =
      (Measure.pi (fun i : Fin d ↦ gaussianReal (z i) t)).map
        (WithLp.toLp 2 : (Fin d → ℝ) → Euc d) := by
  let : IsProbabilityMeasure μ := hμ.1
  let f : Fin d → BrownianPath d → ℝ := fun i ω ↦ z i + ω t i
  have hm (i : Fin d) : Measurable (f i) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ z i + ω t i)).measurable
  have hind : iIndepFun f μ := hμ.2.2.comp
    (fun i (b : ℝ≥0 → ℝ) ↦ z i + b t) (by intro i; fun_prop)
  have hcoord (i : Fin d) : μ.map (f i) = gaussianReal (z i) t := by
    change μ.map ((fun x : ℝ ↦ z i + x) ∘ (fun ω : BrownianPath d ↦ ω t i)) = _
    rw [← Measure.map_map (by fun_prop)
      (by exact (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω t i)).measurable),
      ((hμ.2.1 i).hasLaw_eval t).map_eq,
      gaussianReal_map_const_add, zero_add]
  have hpi := hind.map_fun_eq_pi_map (fun i ↦ (hm i).aemeasurable)
  simp_rw [hcoord] at hpi
  rw [← hpi, Measure.map_map (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable
    (Measurable.of_eval hm)]
  congr 1

/-- Every positive-time translated spatial Brownian law is absolutely
continuous with respect to the actual time-one spatial Brownian law. -/
theorem standardBrownianLaw_translated_eval_absolutelyContinuous {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (z : Euc d) {t : ℝ≥0} (ht : 0 < t) :
    μ.map (fun ω : BrownianPath d ↦ z + ω t) ≪
      μ.map (fun ω : BrownianPath d ↦ ω 1) := by
  have h := finitePi_absolutelyContinuous d
    (fun i ↦ gaussianReal (z i) t) (fun _ ↦ gaussianReal 0 1)
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun i ↦ (gaussianReal_absolutelyContinuous (z i) ht.ne').trans
      (gaussianReal_absolutelyContinuous' 0 (by norm_num)))
  have hm := h.map (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable
  rw [standardBrownianLaw_map_translated_eval hμ z t]
  have href := standardBrownianLaw_map_translated_eval hμ (0 : Euc d) 1
  simp only [PiLp.zero_apply, zero_add] at href
  rw [← href] at hm
  exact hm

end BouRabeeGwynne
