import LatticeProb.Topology.IntervalReparamEDist
import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Normalization of interval reparametrization distances -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb.IntervalReparamEDist

/-- Conjugating time changes by order isomorphisms preserves the infimum of
    their supremal costs. -/
theorem intervalEDist_eq_normalized {d : ℕ} (f g : ℝ≥0 → EuclideanSpace ℝ (Fin d))
    {T U : ℝ≥0∞} (a : unitInterval ≃o TimeInterval T)
    (b : unitInterval ≃o TimeInterval U)
    (p q : NormalizedCurve d)
    (hp : ∀ t, p.path t = f (a t).1)
    (hq : ∀ t, q.path t = g (b t).1) :
    intervalEDist f g T U = NormalizedCurve.frechetEDist p q := by
  apply le_antisymm
  · refine le_iInf fun e => ?_
    let φ : TimeInterval T ≃o TimeInterval U := a.symm.trans (e.trans b)
    calc
      intervalEDist f g T U ≤ ⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1) :=
        intervalEDist_le_of_orderIso f g φ
      _ ≤ NormalizedCurve.timeChangeCost p q e := by
        refine iSup_le fun t => ?_
        have h := le_iSup (fun s : unitInterval => edist (p.path s) (q.path (e s))) (a.symm t)
        simpa only [hp, hq, φ, OrderIso.trans_apply, OrderIso.apply_symm_apply,
          NormalizedCurve.timeChangeCost] using h
  · refine le_iInf fun φ => ?_
    let e : NormalizedCurve.TimeChange := a.trans (φ.trans b.symm)
    calc
      NormalizedCurve.frechetEDist p q ≤ NormalizedCurve.timeChangeCost p q e := iInf_le _ e
      _ ≤ ⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1) := by
        refine iSup_le fun t => ?_
        have h := le_iSup (fun s : TimeInterval T => edist (f s.1) (g (φ s).1)) (a t)
        simpa only [NormalizedCurve.timeChangeCost, hp, hq, e, OrderIso.trans_apply,
          OrderIso.apply_symm_apply] using h

end LatticeProb.IntervalReparamEDist
