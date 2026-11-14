/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BoundaryStoppingComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.CurvePauses

/-! Deterministic comparison of stopped ambient curves. The stopping parameters
may differ, and the discrete parameter may be zero. The Brownian boundary-time
oscillation estimate is supplied separately when this lemma is applied. -/

open Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

/-- Hold the path at its position at time `a` after that time. -/
noncomputable def stoppedUnitCurve {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) (a : unitInterval) :
    C(unitInterval, EuclideanSpace ℝ (Fin d)) :=
  ⟨fun t => f (min t a), f.continuous.comp (continuous_id.min continuous_const)⟩

/-- If the two stopping times lie in one interval of small oscillation for the
second curve, stopping adds at most that oscillation to the ambient error. -/
theorem stoppedUnitCurve_dist_timeChange_le {d : ℕ}
    (f g : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (e : NormalizedCurve.TimeChange) (a b l u : unitInterval) {ε η : ℝ}
    (hclose : ∀ t, dist (f t) (g (e t)) ≤ ε)
    (ha : e a ∈ Icc l u) (hb : b ∈ Icc l u)
    (hosc : ∀ s ∈ Icc l u, ∀ t ∈ Icc l u, dist (g s) (g t) ≤ η)
    (t : unitInterval) :
    dist (stoppedUnitCurve f a t) (stoppedUnitCurve g b (e t)) ≤ ε + η := by
  have hη : 0 ≤ η := (dist_nonneg : 0 ≤ dist (g (e a)) (g (e a))).trans
    (hosc (e a) ha (e a) ha)
  have hmin (s : unitInterval) : dist (g (min s (e a))) (g (min s b)) ≤ η := by
    by_cases hs : s ≤ l
    · simpa only [min_eq_left (hs.trans ha.1), min_eq_left (hs.trans hb.1), dist_self]
        using hη
    · have hls : l ≤ s := (lt_of_not_ge hs).le
      exact hosc _ ⟨le_min hls ha.1, (min_le_right _ _).trans ha.2⟩
        _ ⟨le_min hls hb.1, (min_le_right _ _).trans hb.2⟩
  have hmatch := hclose (min t a)
  have hemin : e (min t a) = min (e t) (e a) := OrderIso.map_inf e t a
  rw [hemin] at hmatch
  exact (dist_triangle _ (g (min (e t) (e a))) _).trans
    (add_le_add hmatch (hmin (e t)))

/-- The comparison uses an actual increasing time homeomorphism in the paper's
Fréchet quotient, and includes constant zero-duration stopped paths. -/
theorem curveSpace_edist_stoppedUnitCurve_le {d : ℕ}
    (f g : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (e : NormalizedCurve.TimeChange) (a b l u : unitInterval) {ε η : ℝ}
    (hclose : ∀ t, dist (f t) (g (e t)) ≤ ε)
    (ha : e a ∈ Icc l u) (hb : b ∈ Icc l u)
    (hosc : ∀ s ∈ Icc l u, ∀ t ∈ Icc l u, dist (g s) (g t) ≤ η) :
    edist (CurveSpace.project (stoppedUnitCurve f a))
      (CurveSpace.project (stoppedUnitCurve g b)) ≤ ENNReal.ofReal (ε + η) := by
  apply (iInf_le _ e).trans
  apply iSup_le
  intro t
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (stoppedUnitCurve_dist_timeChange_le f g e a b l u hclose ha hb hosc t)

end BouRabeeGwynne
