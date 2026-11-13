/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.LocalMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.DataProcessing
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.DiskMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.NormalizationMoment

/-!
# Local Markov decomposition away from both normalization circles

The zero-boundary part on a disk disjoint from the unit circle is independent
of the exterior field. If a second normalization circle is also disjoint, its
circle-average difference from the unit circle is exterior-measurable. Thus
the harmonic part and the random normalization constant may be mixed jointly
while using one common independent zero-boundary GFF law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open LQGMetric LQGMetric.GM LQGMetric.Blueprint LQGMetric.CircleAvg

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

private abbrev outsideSigma (V : Opens ℂ) (h : Ω → DistC) : MeasurableSpace Ω :=
  fieldSigmaClosed h (V : Set ℂ)ᶜ

/-- A Markov decomposition on the local disk, with a measurable harmonic part
and a zero-boundary part independent of all exterior data. -/
structure LocalMarkov (V : Opens ℂ) (P : Measure Ω) (h : Ω → DistC) where
  G : Ω → DistC
  Z : Ω → DistC
  G_meas : Measurable[outsideSigma V h] G
  dec : ∀ᵐ ω ∂P, h ω = G ω + Z ω
  harmonic : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
    InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
    ∀ φ : TestOn V, restrictTo V (G ω) φ = ∫ x, g x * φ x
  zeroBoundary : IsZeroBoundaryGFF V (fun ω => restrictTo V (Z ω)) P
  indep : Indep (MeasurableSpace.comap Z inferInstance) (outsideSigma V h) P

/-- The pinned GFF Markov theorem supplies a decomposition on any open local
disk disjoint from the unit normalization circle. -/
theorem exists_localMarkov (hh : IsNormalizedWPGFF h P) (V : Opens ℂ)
    (hV : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1)) :
    Nonempty (LocalMarkov V P h) := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨H, Z, hdec, hharm, ⟨G, hGm, hG⟩, -, hzb, -, hindep⟩ :=
    LQGMetric.DFGPS.markov_normAt LQGMetric.MarkovFinal.lmLem2_1
      P h hh.1 (by norm_num) 0 hh.2 V hV
  refine ⟨⟨G, Z, hGm, ?_, ?_, hzb, hindep⟩⟩
  · filter_upwards [hG] with ω hω
    rw [hdec ω, hω]
  · filter_upwards [hharm, hG] with ω ⟨g, hg, hgrep⟩ hω
    exact ⟨g, hg, by rw [← hω]; exact hgrep⟩

/-- The second circle average, hence the normalization difference, is
measurable from the exterior whenever its circle misses the local disk. -/
theorem measurable_normalization_increment_outside (V : Opens ℂ) (R : ℝ) (z₀ : ℂ)
    (hRpos : 0 < R)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere z₀ R)) :
    Measurable[outsideSigma V h] (cInc h R z₀ 1 0) := by
  have hR : ∀ x ∈ sphere z₀ R, x ∈ (V : Set ℂ)ᶜ := by
    intro x hx hxin
    exact (Set.disjoint_left.mp hVR hxin hx)
  have h1 : ∀ x ∈ sphere (0 : ℂ) 1, x ∈ (V : Set ℂ)ᶜ := by
    intro x hx hxin
    exact (Set.disjoint_left.mp hV₁ hxin hx)
  have hRa : sphere z₀ |R| ⊆ (V : Set ℂ)ᶜ := by
    intro x hx
    exact hR x (by simpa only [abs_of_pos hRpos] using hx)
  have h1a : sphere (0 : ℂ) |(1 : ℝ)| ⊆ (V : Set ℂ)ᶜ := by
    intro x hx
    exact h1 x (by simpa using hx)
  exact (measurable_circleAvg_fieldSigmaClosed h R z₀ hRa).sub
    (measurable_circleAvg_fieldSigmaClosed h 1 0 h1a)

/-- The harmonic part and the random normalization constant are jointly
independent of the zero-boundary GFF on the local disk. -/
theorem LocalMarkov.indep_exterior_pair {V : Opens ℂ} (M : LocalMarkov V P h) (R : ℝ) (z₀ : ℂ)
    (hRpos : 0 < R)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere z₀ R)) :
    IndepFun (fun ω => (M.G ω, cInc h R z₀ 1 0 ω)) M.Z P := by
  have hm : Measurable[outsideSigma V h]
      (fun ω => (M.G ω, cInc h R z₀ 1 0 ω)) :=
    M.G_meas.prodMk (measurable_normalization_increment_outside V R z₀ hRpos hV₁ hVR)
  exact (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_left M.indep.symm hm.comap_le)

/-- The actual joint law used for mixing: the exterior harmonic field together
with the Gaussian normalization constant is independent of the restricted
zero-boundary GFF. -/
theorem LocalMarkov.joint_exterior_zeroBoundary {V : Opens ℂ}
    (M : LocalMarkov V P h) (hh : IsNormalizedWPGFF h P)
    (R : ℝ) (z₀ : ℂ) (hRpos : 0 < R)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere z₀ R)) :
    P.map (fun ω => ((M.G ω, cInc h R z₀ 1 0 ω), restrictTo V (M.Z ω))) =
      (P.map fun ω => (M.G ω, cInc h R z₀ 1 0 ω)).prod
        (P.map fun ω => restrictTo V (M.Z ω)) := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have houtside : outsideSigma V h ≤ ‹MeasurableSpace Ω› :=
    GM.Bilip.fieldSigmaClosed_le hh.1.measurable _
  have hG : Measurable M.G := M.G_meas.mono houtside le_rfl
  have hc : Measurable (cInc h R z₀ 1 0) := measurable_cInc hh.1 R z₀ 1 0
  have hA : Measurable (fun ω => (M.G ω, cInc h R z₀ 1 0 ω)) := hG.prodMk hc
  have hZ : Measurable (fun ω => restrictTo V (M.Z ω)) := M.zeroBoundary.measurable
  have hi : IndepFun (fun ω => (M.G ω, cInc h R z₀ 1 0 ω))
      (fun ω => restrictTo V (M.Z ω)) P :=
    (M.indep_exterior_pair R z₀ hRpos hV₁ hVR).comp measurable_id
      (measurable_restrictTo V)
  exact (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hZ.aemeasurable).1 hi

end MatedCRTHarmonic.GMSCM
