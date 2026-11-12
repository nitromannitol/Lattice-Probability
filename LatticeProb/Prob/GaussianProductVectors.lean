import Mathlib

/-!
# Gaussian vectors on product spaces

Independent Gaussian random vectors, defined on the factors of a product probability space, are
jointly Gaussian.

* `LatticeProb.hasGaussianLaw_comp_fst`, `hasGaussianLaw_comp_snd`: a Gaussian variable composed with
  a coordinate projection of a product probability space is Gaussian.
* `LatticeProb.hasGaussianLaw_prod_map`: if `V₁` is Gaussian on `(Ω₁, μ)` and `V₂` on `(Ω₂, ν)`, then
  `(x₁, x₂) ↦ (V₁ x₁, V₂ x₂)` is Gaussian on `μ.prod ν`.
* `LatticeProb.hasGaussianLaw_pi_comp`: if `V` is Gaussian on `(Ω, P)`, then `w ↦ (s ↦ V (w s))` is Gaussian
  on the finite power `Measure.pi (fun _ => P)`.
* `LatticeProb.hasGaussianLaw_vector_of_isGaussianProcess`: a finite family of values of a Gaussian
  process is a Gaussian vector (for an arbitrary, not necessarily injective, finite indexing).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

section Product

variable {Ω₁ Ω₂ E F : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {μ : Measure Ω₁} {ν : Measure Ω₂}

/-- A Gaussian variable of the first factor is Gaussian on a product probability space. -/
theorem hasGaussianLaw_comp_fst [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] [IsProbabilityMeasure ν] {V : Ω₁ → E} (h : HasGaussianLaw V μ) :
    HasGaussianLaw (fun x : Ω₁ × Ω₂ => V x.1) (μ.prod ν) where
  aemeasurable := h.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  isGaussian_map := by
    have hV : AEMeasurable V (Measure.map Prod.fst (μ.prod ν)) := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]; exact h.aemeasurable
    have e : (μ.prod ν).map (fun x : Ω₁ × Ω₂ => V x.1) = μ.map V := by
      have := AEMeasurable.map_map_of_aemeasurable hV measurable_fst.aemeasurable
      rw [Measure.map_fst_prod, measure_univ, one_smul] at this
      exact this.symm
    rw [e]; exact h.isGaussian_map

/-- A Gaussian variable of the second factor is Gaussian on a product probability space. -/
theorem hasGaussianLaw_comp_snd [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]
    [MeasurableSpace F] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {V : Ω₂ → F}
    (h : HasGaussianLaw V ν) :
    HasGaussianLaw (fun x : Ω₁ × Ω₂ => V x.2) (μ.prod ν) where
  aemeasurable := h.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  isGaussian_map := by
    have hV : AEMeasurable V (Measure.map Prod.snd (μ.prod ν)) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]; exact h.aemeasurable
    have e : (μ.prod ν).map (fun x : Ω₁ × Ω₂ => V x.2) = ν.map V := by
      have := AEMeasurable.map_map_of_aemeasurable hV measurable_snd.aemeasurable
      rw [Measure.map_snd_prod, measure_univ, one_smul] at this
      exact this.symm
    rw [e]; exact h.isGaussian_map

/-- **Independent Gaussian vectors on the two factors of a product are jointly Gaussian.** -/
theorem hasGaussianLaw_prod_map [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [CompleteSpace F] [SecondCountableTopology F] {V₁ : Ω₁ → E} {V₂ : Ω₂ → F}
    (h₁ : HasGaussianLaw V₁ μ) (h₂ : HasGaussianLaw V₂ ν) :
    HasGaussianLaw (fun x : Ω₁ × Ω₂ => (V₁ x.1, V₂ x.2)) (μ.prod ν) :=
  IndepFun.hasGaussianLaw (hasGaussianLaw_comp_fst h₁) (hasGaussianLaw_comp_snd h₂)
    (indepFun_prod₀ h₁.aemeasurable h₂.aemeasurable)

/-- **Independent copies.** If `V` is Gaussian on `(Ω, P)`, the vector of `V` evaluated at the `κ`
coordinates of the finite power `Measure.pi (fun _ => P)` is a Gaussian vector. -/
theorem hasGaussianLaw_pi_comp {κ : Type*} [Fintype κ] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] {V : Ω → E}
    (h : HasGaussianLaw V P) :
    HasGaussianLaw (fun (w : κ → Ω) (s : κ) => V (w s)) (Measure.pi fun _ : κ => P) := by
  refine iIndepFun.hasGaussianLaw (X := fun (s : κ) (w : κ → Ω) => V (w s)) (fun s => ?_)
    (iIndepFun_pi (X := fun _ => V) (fun _ => h.aemeasurable))
  have hmp := measurePreserving_eval (fun _ : κ => P) s
  refine ⟨h.aemeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving, ?_⟩
  have hV : AEMeasurable V (Measure.map (Function.eval s) (Measure.pi fun _ : κ => P)) := by
    rw [hmp.map_eq]; exact h.aemeasurable
  have e : (Measure.pi fun _ : κ => P).map (fun w : κ → Ω => V (w s)) = P.map V := by
    have := AEMeasurable.map_map_of_aemeasurable hV (measurable_pi_apply s).aemeasurable
    rw [hmp.map_eq] at this
    exact this.symm
  rw [e]; exact h.isGaussian_map

end Product

section Vector

variable {Ω T ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The vector `(X (t i))_i` of a Gaussian process along a finite index type is Gaussian. -/
theorem hasGaussianLaw_vector_of_isGaussianProcess [Fintype ι] {X : T → Ω → ℝ}
    (hX : IsGaussianProcess X P) (t : ι → T) : HasGaussianLaw (fun ω i => X (t i) ω) P := by
  have hY : IsGaussianProcess (fun i : ι => X (t i)) P := hX.comp_right t
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i, Finset.mem_univ i⟩
  exact (hY.hasGaussianLaw Finset.univ).map L

end Vector

end LatticeProb
