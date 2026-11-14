/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.PfeToDG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.NormalizerTransfer

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Polylog

 




theorem isWeakLQGMetric_of_pfe_of_normalizer_comparable
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hPfe : IsPfeWeakMetric ξ D c)
    (hcomp : ∃ C : ℝ, 0 < C ∧ ∀ r : Ioi (0 : ℝ),
      C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) ≤ c r ∧
      (c r : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q)) :
    IsWeakLQGMetric ξ Q D := by
  obtain ⟨C, hC, hcomp⟩ := hcomp
  rcases hPfe with ⟨hMeas, hLength, hLocal, hWeyl, hTrans, hRatio, hTight⟩
  refine ⟨hMeas, hLength, hLocal, hWeyl, hTrans, ?_⟩
  intro Ω _ P _ h hGFF a ha A
  let p : Ioi (0 : ℝ) → ℝ := fun r => (r : ℝ) ^ ((ξ : ℝ) * Q)
  have hp (r : Ioi (0 : ℝ)) : 0 < p r := Real.rpow_pos_of_pos r.property _
  have hc (r : Ioi (0 : ℝ)) : 0 < (c r : ℝ) := (c r).property
  have hcp (r : Ioi (0 : ℝ)) : C⁻¹ * p r ≤ (c r : ℝ) ∧
      (c r : ℝ) ≤ C * p r := hcomp r
  have hpow (r : Ioi (0 : ℝ)) :
      (r : ℝ) ^ (-((ξ : ℝ) * Q)) = (p r)⁻¹ :=
    Real.rpow_neg r.property.le _
  have hT := hTight P h hGFF a ha A
  constructor
  · have hNew := tight_of_comparable_normalizers P p (fun r => (c r : ℝ))
        (fun r ω => Real.exp (-((ξ : ℝ) * a r ω)))
        (fun r ω => acrossDist (D (h ω)) (A.dilate r r.2))
        hp hc C hC hcp hT.1
    simpa only [hpow] using hNew
  · have hNew := tight_of_comparable_normalizers P p (fun r => (c r : ℝ))
        (fun r ω => Real.exp (-((ξ : ℝ) * a r ω)))
        (fun r ω => aroundDist (D (h ω)) (A.dilate r r.2))
        hp hc C hC hcp hT.2
    simpa only [hpow] using hNew

end SupercriticalLQGUniqueness.B2.Polylog
