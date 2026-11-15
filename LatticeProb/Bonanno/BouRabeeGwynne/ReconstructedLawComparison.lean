/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ReconstructedLawComparison at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   imports and the coupling lemma reference are adapted to the local library. -/
import LatticeProb.Prob.LevyProkhorovMaps
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! Compare an actual stopped law with its finite reconstruction on the same
original sample. Only the mass of failed reconstruction is lost. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BouRabeeGwynne

theorem levyProkhorov_curveLaws_le_of_ae_good {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f g : Ω → CurveSpace d)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (E : Set Ω) (r : ℝ≥0) (hbad : μ E ≤ (r : ℝ≥0∞))
    (hclose : ∀ᵐ ω ∂μ, ω ∉ E → edist (f ω) (g ω) < (r : ℝ≥0∞)) :
    levyProkhorovEDist (μ.map f) (μ.map g) ≤ r := by
  have hpair : AEMeasurable (fun ω => (f ω, g ω)) μ := hf.prodMk hg
  let σ : Measure (CurveSpace d × CurveSpace d) := μ.map (fun ω => (f ω, g ω))
  have hfst : σ.fst = μ.map f := by
    change (μ.map (fun ω => (f ω, g ω))).map Prod.fst = μ.map f
    rw [measurable_fst.aemeasurable.map_map_of_aemeasurable hpair]
    rfl
  have hsnd : σ.snd = μ.map g := by
    change (μ.map (fun ω => (f ω, g ω))).map Prod.snd = μ.map g
    rw [measurable_snd.aemeasurable.map_map_of_aemeasurable hpair]
    rfl
  apply LatticeProb.levyProkhorovEDist_le_of_coupling _ _ σ hfst hsnd r
  have hm : MeasurableSet {p : CurveSpace d × CurveSpace d |
      (r : ℝ≥0∞) ≤ edist p.1 p.2} :=
    measurableSet_le measurable_const (measurable_fst.edist measurable_snd)
  change (μ.map (fun ω => (f ω, g ω))) _ ≤ _
  rw [Measure.map_apply_of_aemeasurable hpair hm]
  apply (measure_mono_ae ?_).trans hbad
  filter_upwards [hclose] with ω hω
  intro hp
  by_contra hgood
  exact (not_lt_of_ge hp) (hω hgood)

theorem levyProkhorov_curveLaws_le_of_ae_reconstruction {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω) (f g : Ω → CurveSpace d)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (E : Set Ω) (r : ℝ≥0) (hr : 0 < r) (hbad : μ E ≤ (r : ℝ≥0∞))
    (heq : ∀ᵐ ω ∂μ, ω ∉ E → f ω = g ω) :
    levyProkhorovEDist (μ.map f) (μ.map g) ≤ r := by
  apply levyProkhorov_curveLaws_le_of_ae_good μ f g hf hg E r hbad
  filter_upwards [heq] with ω hω
  intro hgood
  rw [hω hgood, edist_self]
  exact_mod_cast hr

end BouRabeeGwynne
