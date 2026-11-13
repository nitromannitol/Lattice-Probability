/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.TupleCM at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Cameron–Martin shifts on a finite product of probability spaces

For [18] Lemma A.3 with an `N`-tuple of independent fields : the
Radon–Nikodym derivative of the shifted `N`-tuple of zero-boundary parts is the product of the `N` one-field
derivatives (the change of measure `M_δ` of Lemma A.5, is a product over the `N` coordinates).
Abstractly: if `(ν_k).map (· + T_k) = ρ_k ν_k` for each `k`, then
`(Π ν_k).map (· + T) = (∏_k ρ_k(z_k)) Π ν_k`, and the moments of `∏_k ρ_k(z_k)` are the products of the moments.

* `GMSAppA.lintegral_pi_prod` — `∫ ∏_k f_k(z_k) d(Π ν_k) = ∏_k ∫ f_k dν_k`.
* `GMSAppA.map_add_eq_withDensity_of_lintegral` — the law identity from the integral identity.
* `GMSAppA.pi_withDensity_eq` — `Π (ρ_k ν_k) = (∏_k ρ_k(z_k)) Π ν_k`.
* `GMSAppA.lintegral_pi_shift` — `∫ Ψ(z + T) d(Π ν_k) = ∫ Ψ(z) ∏_k ρ_k(z_k) d(Π ν_k)`.
* `GMSAppA.lintegral_pi_prod_rpow` — `∫ (∏_k ρ_k(z_k))^s d(Π ν_k) = ∏_k ∫ ρ_k^s dν_k` for `ρ_k > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {ι : Type*} [Fintype ι] {𝓩 : Type*} [MeasurableSpace 𝓩] {ν : ι → Measure 𝓩}
  [∀ k, IsProbabilityMeasure (ν k)]

/-- `∫ ∏_k f_k(z_k) d(Π ν_k) = ∏_k ∫ f_k dν_k`. -/
theorem lintegral_pi_prod {f : ι → 𝓩 → ℝ≥0∞} (hf : ∀ k, Measurable (f k)) :
    ∫⁻ z, ∏ k, f k (z k) ∂Measure.pi ν = ∏ k, ∫⁻ x, f k x ∂ν k := by
  have hind : iIndepFun (fun k (z : ι → 𝓩) => f k (z k)) (Measure.pi ν) :=
    iIndepFun_pi (μ := ν) (X := fun k => f k) fun k => (hf k).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    fun k => (hf k).comp (measurable_pi_apply k)]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact (measurePreserving_eval ν k).lintegral_comp (hf k)

/-- The law identity `ν.map (· + T) = ρ ν` from the integral identity `∫ Ψ(z + T) dν = ∫ Ψ ρ dν`. -/
theorem map_add_eq_withDensity_of_lintegral [Add 𝓩] {μ : Measure 𝓩} {T : 𝓩}
    (hadd : Measurable fun z : 𝓩 => z + T) {ρ : 𝓩 → ℝ≥0∞}
    (hcm : ∀ Ψ : 𝓩 → ℝ≥0∞, Measurable Ψ → ∫⁻ z, Ψ (z + T) ∂μ = ∫⁻ z, Ψ z * ρ z ∂μ) :
    μ.map (fun z => z + T) = μ.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hadd hs, withDensity_apply _ hs]
  have h1 := hcm (s.indicator 1) (measurable_one.indicator hs)
  have e1 : (fun z => s.indicator (1 : 𝓩 → ℝ≥0∞) (z + T)) =
      ((fun z => z + T) ⁻¹' s).indicator 1 := by
    funext z; rfl
  have e2 : (fun z => s.indicator (1 : 𝓩 → ℝ≥0∞) z * ρ z) = s.indicator ρ := by
    funext z; by_cases hz : z ∈ s <;> simp [hz]
  rw [e1, e2, lintegral_indicator_one (hadd hs), lintegral_indicator hs] at h1
  exact h1

/-- `Π (ρ_k ν_k) = (∏_k ρ_k(z_k)) Π ν_k`. -/
theorem pi_withDensity_eq {ρ : ι → 𝓩 → ℝ} (hρ : ∀ k, Measurable (ρ k)) :
    Measure.pi (fun k => (ν k).withDensity fun x => ENNReal.ofReal (ρ k x)) =
      (Measure.pi ν).withDensity fun z => ∏ k, ENNReal.ofReal (ρ k (z k)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hD : Measurable fun z : ι → 𝓩 => ∏ k, ENNReal.ofReal (ρ k (z k)) :=
    Finset.measurable_prod _ fun k _ => ((hρ k).comp (measurable_pi_apply k)).ennreal_ofReal
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (univ.pi s).indicator (fun z : ι → 𝓩 => ∏ k, ENNReal.ofReal (ρ k (z k))) =
      fun z => ∏ k, (s k).indicator (fun x => ENNReal.ofReal (ρ k x)) (z k) := by
    funext z
    by_cases hz : z ∈ univ.pi s
    · rw [indicator_of_mem hz]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [indicator_of_mem (hz k (mem_univ k))]
    · rw [indicator_of_notMem hz]
      simp only [mem_pi, mem_univ, true_implies, not_forall] at hz
      obtain ⟨k, hk⟩ := hz
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk _)).symm
  rw [e, lintegral_pi_prod fun k => ((hρ k).ennreal_ofReal).indicator (hs k)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [withDensity_apply _ (hs k), lintegral_indicator (hs k)]

/-- **Cameron–Martin on a finite product**: if `∫ Ψ(z + T_k) dν_k = ∫ Ψ ρ_k dν_k` for each `k`, then
`∫ Ψ(z + T) d(Π ν_k) = ∫ Ψ(z) ∏_k ρ_k(z_k) d(Π ν_k)`. -/
theorem lintegral_pi_shift [Add 𝓩] {T : ι → 𝓩} (hadd : ∀ k, Measurable fun z : 𝓩 => z + T k)
    {ρ : ι → 𝓩 → ℝ} (hρ : ∀ k, Measurable (ρ k))
    (hcm : ∀ k, ∀ Ψ : 𝓩 → ℝ≥0∞, Measurable Ψ →
      ∫⁻ z, Ψ (z + T k) ∂ν k = ∫⁻ z, Ψ z * ENNReal.ofReal (ρ k z) ∂ν k)
    {Ψ : (ι → 𝓩) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ z, Ψ (z + T) ∂Measure.pi ν = ∫⁻ z, Ψ z * ∏ k, ENNReal.ofReal (ρ k (z k)) ∂Measure.pi ν := by
  have haddT : Measurable fun z : ι → 𝓩 => z + T :=
    measurable_pi_iff.2 fun k => (hadd k).comp (measurable_pi_apply k)
  have hD : Measurable fun z : ι → 𝓩 => ∏ k, ENNReal.ofReal (ρ k (z k)) :=
    Finset.measurable_prod _ fun k _ => ((hρ k).comp (measurable_pi_apply k)).ennreal_ofReal
  have hmap : (Measure.pi ν).map (fun z => z + T) =
      (Measure.pi ν).withDensity fun z => ∏ k, ENNReal.ofReal (ρ k (z k)) := by
    rw [← pi_withDensity_eq hρ]
    have e : (fun z : ι → 𝓩 => z + T) = fun z k => (fun x => x + T k) (z k) := rfl
    rw [e, Measure.pi_map_pi fun k => (hadd k).aemeasurable]
    congr 1
    funext k
    exact map_add_eq_withDensity_of_lintegral (hadd k) (hcm k)
  rw [← lintegral_map hΨ haddT, hmap, lintegral_withDensity_eq_lintegral_mul _ hD hΨ]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- **Moments of a product density**: `∫ (∏_k ρ_k(z_k))^s d(Π ν_k) = ∏_k ∫ ρ_k^s dν_k` for `ρ_k > 0`. -/
theorem lintegral_pi_prod_rpow {ρ : ι → 𝓩 → ℝ} (hρ : ∀ k, Measurable (ρ k)) (hρ0 : ∀ k x, 0 < ρ k x)
    (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (∏ k, ρ k (z k)) ^ s ∂Measure.pi ν =
      ∏ k, ∫⁻ x, ENNReal.ofReal (ρ k x) ^ s ∂ν k := by
  have e : ∀ z : ι → 𝓩, ENNReal.ofReal (∏ k, ρ k (z k)) ^ s =
      ∏ k, ENNReal.ofReal (ρ k (z k)) ^ s := by
    intro z
    rw [ENNReal.ofReal_rpow_of_pos (Finset.prod_pos fun k _ => hρ0 k (z k)),
      ← Real.finsetProd_rpow _ _ (fun k _ => (hρ0 k (z k)).le),
      ENNReal.ofReal_prod_of_nonneg fun k _ => Real.rpow_nonneg (hρ0 k (z k)).le _]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_rpow_of_pos (hρ0 k (z k))]
  simp_rw [e]
  exact lintegral_pi_prod fun k => (hρ k).ennreal_ofReal.pow_const s

end MatedCRTHarmonic.GMSAppA
