import LatticeProb.Probability.WeakLQGMetricExponent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P6Closing
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointIface
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.QPosClosure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RProved

/-!
# The exponent of a weak LQG metric is `Q(ξ)`, unconditionally

Let `ξ > 0`. Every weak LQG metric with parameter `ξ` and exponent `Q`
(Ding-Dubédat-Dunlap-Falconet; `SupercriticalLQGUniqueness.IsWeakLQGMetric`) has
`Q = Q(ξ) = distExp 2 ξ`, the LFPP distance exponent.

`LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight` derives this from two inputs:
Pfeffer's comparison of scales (*Weak Liouville quantum gravity metrics with matter central charge
c ∈ (-∞, 25)*, Theorem 1.9) and the point-to-point tightness of supercritical LFPP (Ding-Gwynne,
Section 4). Both follow from the Ding-Gwynne percolation estimate and exponent relation, together
with the positivity of the exponent and the existence of the LFPP normalizers
(`iface_plThm19_of_dg20`, `dg20Section4_point_tight_of_inputs`). The percolation estimate and the
exponent relation are themselves proved for every `ξ > 0` (`laneA4_dg20PercEstimate_proved`,
`laneA4_dg20ExponentRelation_proved`).

## Main results

* `LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20`: the identification `Q = Q(ξ)`
  from the Ding-Gwynne percolation estimate and exponent relation.
* `LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric`: the identification `Q = Q(ξ)` without
  hypotheses.
-/

namespace LQGMetric.HeatCircle

/-- **The exponent of a weak LQG metric from the Ding-Gwynne estimates.** Assume the
percolation estimate and the exponent relation of Ding-Gwynne for supercritical LFPP. Then every
weak LQG metric with parameter `ξ > 0` and exponent `Q` has `Q = Q(ξ) = distExp 2 ξ`. -/
theorem distExp_eq_of_isWeakLQGMetric_of_dg20
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation) :
    ∀ ξ Q D, SupercriticalLQGUniqueness.IsWeakLQGMetric ξ Q D →
      HigherDimLQGMetric.distExp 2 ξ = Q :=
  distExp_eq_of_isWeakLQGMetric_of_pointTight
    (SupercriticalLQGUniqueness.B2.Polylog.iface_plThm19_of_dg20 hPerc hExp
      SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved
      (SupercriticalLQGUniqueness.B2.Polylog.lfppNormalizerExists_of_existsUnique
        fun ξ ε => SupercriticalLQGUniqueness.existsUnique_isLFPPNormalizer ξ ε))
    (SupercriticalLQGUniqueness.B2.DG20Pt.dg20Section4_point_tight_of_inputs hPerc hExp
      SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved)

/-- **The exponent of a weak LQG metric is `Q(ξ)`.** Every weak LQG metric with parameter
`ξ > 0` and exponent `Q` has `Q = Q(ξ) = distExp 2 ξ`. -/
theorem distExp_eq_of_isWeakLQGMetric :
    ∀ ξ Q D, SupercriticalLQGUniqueness.IsWeakLQGMetric ξ Q D →
      HigherDimLQGMetric.distExp 2 ξ = Q :=
  distExp_eq_of_isWeakLQGMetric_of_dg20
    SupercriticalLQGUniqueness.B2.DG20Conc.laneA4_dg20PercEstimate_proved
    SupercriticalLQGUniqueness.B2.DG20Conc.laneA4_dg20ExponentRelation_proved

end LQGMetric.HeatCircle
