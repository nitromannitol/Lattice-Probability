/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47MeasC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The whole-plane GFF on the completed probability space (D70 packet D70-T, `decisions/DEC-47.md`)

Decision D70 runs GM §4's conditional arguments on a complete probability space; the T4.2
assembly passes from `(Ω, mΩ, P)` to `(NullMeasurableSpace Ω P, P.completion)` (mathlib). This file
supplies the transfer of the field hypothesis:

* `gm_isProbabilityMeasure_completion`;
* `gm_integral_completion`: `∫ g ∂P.completion = ∫ g ∂P` for every real `g` (a.e.-strong
  measurability is the same for `P` and its completion, and both integrals vanish otherwise);
* `gm_map_completion`: laws of a.e.-measurable maps are unchanged;
* `gm_isWholePlaneGFF_completion`.

Conclusions about probabilities come back by `Measure.completion_apply` (definitional).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric.GM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- the identity `NullMeasurableSpace Ω P → Ω` -/
def gm_ofNull (P : Measure Ω) : NullMeasurableSpace Ω P → Ω := id

theorem gm_measurable_ofNull : Measurable (gm_ofNull P) :=
  fun s hs => (hs.nullMeasurableSet : NullMeasurableSet s P)

theorem gm_map_ofNull : P.completion.map (gm_ofNull P) = P := by
  ext s hs
  rw [Measure.map_apply gm_measurable_ofNull hs]
  rfl

instance gm_isProbabilityMeasure_completion [IsProbabilityMeasure P] :
    IsProbabilityMeasure P.completion :=
  ⟨(measure_univ : P univ = 1)⟩

/-- a.e.-measurability for `P` gives a.e.-measurability for the completion -/
theorem gm_aemeasurable_completion {β : Type*} [MeasurableSpace β] {f : Ω → β}
    (hf : AEMeasurable f P) : AEMeasurable (f ∘ gm_ofNull P) P.completion :=
  ⟨hf.mk f ∘ gm_ofNull P, hf.measurable_mk.comp gm_measurable_ofNull, hf.ae_eq_mk⟩

/-- laws of a.e.-measurable maps are unchanged by completion -/
theorem gm_map_completion {β : Type*} [MeasurableSpace β] {f : Ω → β} (hf : AEMeasurable f P) :
    P.completion.map (f ∘ gm_ofNull P) = P.map f := by
  have h1 : P.completion.map (f ∘ gm_ofNull P) = P.completion.map (hf.mk f ∘ gm_ofNull P) :=
    Measure.map_congr hf.ae_eq_mk
  rw [h1, Measure.map_congr hf.ae_eq_mk, ← Measure.map_map hf.measurable_mk gm_measurable_ofNull,
    gm_map_ofNull]

/-- integrals of real functions are unchanged by completion -/
theorem gm_integral_completion (g : Ω → ℝ) :
    ∫ ω, g (gm_ofNull P ω) ∂(P.completion) = ∫ ω, g ω ∂P := by
  by_cases hg : AEStronglyMeasurable g P
  · have h := integral_map (μ := P.completion) gm_measurable_ofNull.aemeasurable
      (f := g) (by rw [gm_map_ofNull]; exact hg)
    rw [gm_map_ofNull] at h
    exact h.symm
  · have hg' : ¬ AEStronglyMeasurable (g ∘ gm_ofNull P) P.completion := by
      intro h
      apply hg
      have hm : Measurable (h.mk _) := h.stronglyMeasurable_mk.measurable
      exact ((NullMeasurable.aemeasurable (μ := P) hm).congr h.ae_eq_mk.symm).aestronglyMeasurable
    exact (integral_non_aestronglyMeasurable hg').trans (integral_non_aestronglyMeasurable hg).symm

/-- covariances are unchanged by completion -/
theorem gm_covariance_completion (X Y : Ω → ℝ) :
    covariance (X ∘ gm_ofNull P) (Y ∘ gm_ofNull P) P.completion = covariance X Y P := by
  unfold covariance
  simp only [Function.comp_apply]
  rw [gm_integral_completion X, gm_integral_completion Y]
  exact gm_integral_completion (fun ω => (X ω - ∫ x, X x ∂P) * (Y ω - ∫ x, Y x ∂P))

/-- **D70-T: the whole-plane GFF on the completed space** -/
theorem gm_isWholePlaneGFF_completion {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    IsWholePlaneGFF (h ∘ gm_ofNull P) P.completion where
  measurable := hh.measurable.comp gm_measurable_ofNull
  gaussian := ⟨fun I => by
    have hI := hh.gaussian.hasGaussianLaw I
    exact ⟨gm_aemeasurable_completion hI.aemeasurable, by
      rw [show (fun ω => I.restrict fun x : TestC0 => (h ∘ gm_ofNull P) ω x.1) =
        (fun ω => I.restrict fun x : TestC0 => h ω x.1) ∘ gm_ofNull P from rfl,
        gm_map_completion hI.aemeasurable]
      exact hI.isGaussian_map⟩⟩
  centered := fun φ => (gm_integral_completion (P := P) (fun ω => h ω φ.1)).trans (hh.centered φ)
  covariance_eq := fun φ ψ =>
    (gm_covariance_completion (P := P) (fun ω => h ω φ.1) (fun ω => h ω ψ.1)).trans
      (hh.covariance_eq φ ψ)

end LQGMetric.GM
