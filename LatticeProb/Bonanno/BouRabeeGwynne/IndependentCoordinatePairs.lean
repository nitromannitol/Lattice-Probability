/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.IndependentCoordinatePairs at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.HasLaw

/-!
# Regrouping independent coordinate pairs

This finite-dimensional probability identity is the regrouping step used to
pass from real-coordinate Brownian weak Markov to independence of the complete
Euclidean future and past. Both levels of independence are proved inputs to
this lemma; no stochastic process existence or convergence is postulated.
-/
open MeasureTheory ProbabilityTheory
namespace BouRabeeGwynne

theorem indepFun_vectors_of_independent_coordinate_pairs
    {ι Ω X Y : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ι → Ω → X} {g : ι → Ω → Y}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hpairs : iIndepFun (fun i ω ↦ (f i ω, g i ω)) μ)
    (hwithin : ∀ i, IndepFun (f i) (g i) μ) :
    IndepFun (fun ω i ↦ f i ω) (fun ω i ↦ g i ω) μ := by
  letI (i : ι) : IsProbabilityMeasure (μ.map (f i)) :=
    (Measure.isProbabilityMeasure_map_iff (hf i).aemeasurable).mpr inferInstance
  letI (i : ι) : IsProbabilityMeasure (μ.map (g i)) :=
    (Measure.isProbabilityMeasure_map_iff (hg i).aemeasurable).mpr inferInstance
  have hflaw (i : ι) : HasLaw (f i) (μ.map (f i)) μ := ⟨(hf i).aemeasurable, rfl⟩
  have hglaw (i : ι) : HasLaw (g i) (μ.map (g i)) μ := ⟨(hg i).aemeasurable, rfl⟩
  have hpairlaw (i : ι) : HasLaw (fun ω ↦ (f i ω, g i ω))
      ((μ.map (f i)).prod (μ.map (g i))) μ :=
    (hwithin i).hasLaw_prod (hflaw i) (hglaw i)
  have hflaws : HasLaw (fun ω i ↦ f i ω) (Measure.pi fun i ↦ μ.map (f i)) μ :=
    (hpairs.comp (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst)).hasLaw_pi hflaw
  have hglaws : HasLaw (fun ω i ↦ g i ω) (Measure.pi fun i ↦ μ.map (g i)) μ :=
    (hpairs.comp (fun _ ↦ Prod.snd) (fun _ ↦ measurable_snd)).hasLaw_pi hglaw
  apply (indepFun_iff_hasLaw_prodMk_prod hflaws hglaws).mpr
  exact (measurePreserving_arrowProdEquivProdArrow X Y ι
    (fun i ↦ μ.map (f i)) (fun i ↦ μ.map (g i))).hasLaw.comp
      (hpairs.hasLaw_pi hpairlaw)

end BouRabeeGwynne
