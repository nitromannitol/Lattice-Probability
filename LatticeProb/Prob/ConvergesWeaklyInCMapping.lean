import Mathlib.Topology.Metrizable.ContinuousMap
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import LatticeProb.Prob.ContinuousMappingAECont

/-!
# The continuous mapping theorem with almost sure continuity for weak convergence in `C([0,∞), ℝ²)`

Let `Q` be a probability measure on `Ω` and `Y ε : Ω → C([0,∞), ℝ²)` measurable maps whose laws
converge weakly, as `ε ↓ 0`, to the Brownian law of an anisotropic Brownian target (the mode of
convergence of Theorem 1.16 of Gwynne, Miller and Sheffield, *An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515). If a measurable functional `G` of the path
is continuous at almost every path of the limit law, then the laws of `G (Y ε)` converge weakly to
the image of the limit law under `G` (Billingsley, *Convergence of Probability Measures*,
Theorem 2.7). The typical functional is the exit point of a path from a domain, which is
continuous at almost every Brownian path but not everywhere.

## Main statements

* `LatticeProb.Portmanteau.tendsto_imageLaw_of_convergesWeaklyInC`: the image laws converge in
  the space of probability measures on `C([0,∞), ℝ²)`.
* `LatticeProb.Portmanteau.tendsto_integral_of_convergesWeaklyInC_of_ae_continuousAt`: integrals
  of bounded measurable functionals which are continuous almost surely under the limit converge.
* `LatticeProb.Portmanteau.tendsto_map_of_convergesWeaklyInC_of_ae_continuousAt`: the continuous
  mapping theorem with almost sure continuity.
* `LatticeProb.Portmanteau.limsup_measure_preimage_le_of_convergesWeaklyInC_of_ae_continuousAt`
  and `LatticeProb.Portmanteau.le_liminf_measure_preimage_of_convergesWeaklyInC_of_ae_continuousAt`:
  its closed-set and open-set halves for the events `{G (Y ε) ∈ F}`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LatticeProb.Portmanteau

open ReflectedGMS.GMS ReflectedGMS.StatementIngredients

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of the path `Y ε` under `Q`, as a probability measure on `C([0,∞), ℝ²)`. -/
noncomputable def imageLaw (Q : Measure Ω) [IsProbabilityMeasure Q]
    (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2) (hY : ∀ ε, AEMeasurable (Y ε) Q) (ε : ℝ≥0) :
    ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2) :=
  ⟨Q.map (Y ε), (Measure.isProbabilityMeasure_map_iff (hY ε)).mpr inferInstance⟩

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2}
  {target : AnisotropicBrownianTarget}

@[simp] theorem coe_imageLaw (hY : ∀ ε, AEMeasurable (Y ε) Q) (ε : ℝ≥0) :
    (imageLaw Q Y hY ε : Measure (BouRabeeGwynne.BrownianPath 2)) = Q.map (Y ε) := rfl

/-- **Weak convergence in `C([0,∞), ℝ²)` as convergence of probability measures.** For
measurable paths, the convergence of Theorem 1.16 of Gwynne, Miller and Sheffield is the
convergence of the laws of `Y ε` to the Brownian law of the target in the topology of weak
convergence of probability measures. -/
theorem tendsto_imageLaw_of_convergesWeaklyInC (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) :
    Tendsto (imageLaw Q Y hY) (𝓝[>] 0) (𝓝 target.pathLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hf := h f f.continuous ⟨‖f‖, fun x => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x⟩
  refine Tendsto.congr (fun ε => ?_) hf
  rw [coe_imageLaw, integral_map (hY ε) f.continuous.measurable.aestronglyMeasurable]

/-- **Integrals of almost surely continuous functionals.** If the laws of `Y ε` converge weakly
in `C([0,∞), ℝ²)` to the Brownian law of the target, then `E_Q[g (Y ε)] → E[g (B)]` for every
bounded measurable `g` which is continuous at almost every path of the limit law. -/
theorem tendsto_integral_of_convergesWeaklyInC_of_ae_continuousAt
    (hY : ∀ ε, AEMeasurable (Y ε) Q) (h : ConvergesWeaklyInC Q Y target)
    {g : BouRabeeGwynne.BrownianPath 2 → ℝ} (hg : Measurable g) (hb : ∃ C, ∀ f, |g f| ≤ C)
    (hc : ∀ᵐ f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)), ContinuousAt g f) :
    Tendsto (fun ε => ∫ ω, g (Y ε ω) ∂Q) (𝓝[>] 0)
      (𝓝 (∫ f, g f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
  have key := LatticeProb.tendsto_integral_of_ae_continuousAt
    (tendsto_imageLaw_of_convergesWeaklyInC hY h) hg hb hc
  refine Tendsto.congr (fun ε => ?_) key
  rw [coe_imageLaw, integral_map (hY ε) hg.aestronglyMeasurable]

section Mapping

variable {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

/-- **The continuous mapping theorem with almost sure continuity.** If the laws of `Y ε`
converge weakly in `C([0,∞), ℝ²)` to the Brownian law of the target and the measurable map `G`
is continuous at almost every path of the limit law, then the laws of `G (Y ε)` converge weakly
to the image of the limit law under `G`. -/
theorem tendsto_map_of_convergesWeaklyInC_of_ae_continuousAt
    (hY : ∀ ε, AEMeasurable (Y ε) Q) (h : ConvergesWeaklyInC Q Y target)
    {G : BouRabeeGwynne.BrownianPath 2 → T} (hG : Measurable G)
    (hc : ∀ᵐ f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)), ContinuousAt G f) :
    Tendsto (fun ε => (imageLaw Q Y hY ε).map G) (𝓝[>] 0)
      (𝓝 (target.pathLaw.map G)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have hφm : Measurable fun f => φ (G f) := φ.continuous.measurable.comp hG
  have key := tendsto_integral_of_convergesWeaklyInC_of_ae_continuousAt hY h hφm
    ⟨‖φ‖, fun f => by rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm _⟩
    (hc.mono fun f hf => φ.continuous.continuousAt.comp hf)
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map hG.aemeasurable φ.continuous.measurable.aestronglyMeasurable]
  refine Tendsto.congr (fun ε => ?_) key
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map hG.aemeasurable φ.continuous.measurable.aestronglyMeasurable, coe_imageLaw,
    integral_map (hY ε) hφm.aestronglyMeasurable]

end Mapping

section Portmanteau

variable {T : Type*} [PseudoEMetricSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

omit [PseudoEMetricSpace T] [OpensMeasurableSpace T] in
/-- The image law of `G (Y ε)` evaluated at a measurable set. -/
theorem imageLaw_map_apply (hY : ∀ ε, AEMeasurable (Y ε) Q)
    {G : BouRabeeGwynne.BrownianPath 2 → T} (hG : Measurable G) {F : Set T}
    (hF : MeasurableSet F) (ε : ℝ≥0) :
    ((imageLaw Q Y hY ε).map G : Measure T) F = Q {ω | G (Y ε ω) ∈ F} := by
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hG hF, coe_imageLaw,
    Measure.map_apply_of_aemeasurable (hY ε) (hG hF)]
  rfl

/-- **Closed-set half.** Under the hypotheses of the continuous mapping theorem with almost sure
continuity, `limsup_{ε ↓ 0} Q {G (Y ε) ∈ F} ≤ P(G (B) ∈ F)` for every closed set `F`. -/
theorem limsup_measure_preimage_le_of_convergesWeaklyInC_of_ae_continuousAt
    (hY : ∀ ε, AEMeasurable (Y ε) Q) (h : ConvergesWeaklyInC Q Y target)
    {G : BouRabeeGwynne.BrownianPath 2 → T} (hG : Measurable G)
    (hc : ∀ᵐ f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)), ContinuousAt G f)
    {F : Set T} (hF : IsClosed F) :
    (𝓝[>] (0 : ℝ≥0)).limsup (fun ε => Q {ω | G (Y ε ω) ∈ F}) ≤
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) (G ⁻¹' F) := by
  have key := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_map_of_convergesWeaklyInC_of_ae_continuousAt hY h hG hc) hF
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hG hF.measurableSet] at key
  simpa only [imageLaw_map_apply hY hG hF.measurableSet] using key

/-- **Open-set half.** Under the hypotheses of the continuous mapping theorem with almost sure
continuity, `P(G (B) ∈ U) ≤ liminf_{ε ↓ 0} Q {G (Y ε) ∈ U}` for every open set `U`. -/
theorem le_liminf_measure_preimage_of_convergesWeaklyInC_of_ae_continuousAt
    (hY : ∀ ε, AEMeasurable (Y ε) Q) (h : ConvergesWeaklyInC Q Y target)
    {G : BouRabeeGwynne.BrownianPath 2 → T} (hG : Measurable G)
    (hc : ∀ᵐ f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)), ContinuousAt G f)
    {U : Set T} (hU : IsOpen U) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) (G ⁻¹' U) ≤
      (𝓝[>] (0 : ℝ≥0)).liminf (fun ε => Q {ω | G (Y ε ω) ∈ U}) := by
  have key := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_map_of_convergesWeaklyInC_of_ae_continuousAt hY h hG hc) hU
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hG hU.measurableSet] at key
  simpa only [imageLaw_map_apply hY hG hU.measurableSet] using key

end Portmanteau

end LatticeProb.Portmanteau
