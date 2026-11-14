/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CanonicalH at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import Mathlib.Probability.Distributions.Gaussian.Real




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC IsWholePlaneGFF addConst)
open SupercriticalLQGUniqueness

def standardGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardGaussian := inferInstanceAs
  (IsProbabilityMeasure (gaussianReal 0 1))

theorem gff_prod_fst {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    IsWholePlaneGFF (fun p : Ω × ℝ => h p.1) (P.prod ν) := by
  have hY : Measurable (fun p : Ω × ℝ => h p.1) := hh.measurable.comp measurable_fst
  have hlaw : (P.prod ν).map (fun p : Ω × ℝ => h p.1) = P.map h := by
    calc
      (P.prod ν).map (fun p : Ω × ℝ => h p.1) =
          ((P.prod ν).map Prod.fst).map h :=
        (Measure.map_map hh.measurable measurable_fst).symm
      _ = P.map h := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq hY hh hlaw

def gaussianShift {Ω : Type} (h : Ω → DistC) : Ω × ℝ → DistC :=
  fun p => addConst (h p.1) p.2

theorem gff_gaussianShift {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    IsWholePlaneGFF (gaussianShift h) (P.prod standardGaussian) := by
  exact (gff_prod_fst P standardGaussian h hh).addConst measurable_snd

 
theorem canonical_gaussianShift_isGFFPlusCont {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    LQGMetric.IsGFFPlusCont (id : DistC → DistC)
      ((P.prod standardGaussian).map (gaussianShift h)) := by
  exact LQGMetric.GM.Tight.isGFFPlusCont_of_wp
    (LQGMetric.GM.isWholePlaneGFF_id_map (gff_gaussianShift P h hh))

 
end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
