/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.SkeletonCurveComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.CurveSpace
import LatticeProb.Bonanno.BouRabeeGwynne.TimePartition

/-!
# Actual Fréchet comparison from finite coupled skeletons

The matching time homeomorphism is constructed from the two finite partitions.
The spatial estimate uses the two within-segment oscillation bounds and the
error between corresponding skeleton vertices. Constant normalized curves,
including duration-zero stopped paths, obey the same comparison.
-/

open scoped unitInterval ENNReal

namespace BouRabeeGwynne
namespace TimePartition

variable {n d : ℕ} (P Q : TimePartition n) (f g : NormalizedCurve d)

/-- Matching corresponding finite time intervals gives a pointwise spatial bound. -/
theorem dist_timeChange_le_of_segment_bounds {α β γ : ℝ}
    (hf : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      P.left i ≤ t ∧ t ≤ P.right i → dist (f.path t) (f.path (P.left i)) ≤ α)
    (hvertices : ∀ i : Fin (n + 1),
      dist (f.path (P.left i)) (g.path (Q.left i)) ≤ β)
    (hg : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      Q.left i ≤ t ∧ t ≤ Q.right i → dist (g.path t) (g.path (Q.left i)) ≤ γ)
    (t : unitInterval) :
    dist (f.path t) (g.path (P.timeChange Q t)) ≤ α + β + γ := by
  let i := P.interval t
  have ht := P.interval_spec t
  have he := P.timeChange_mem_interval Q i ht
  calc
    dist (f.path t) (g.path (P.timeChange Q t)) ≤
        dist (f.path t) (f.path (P.left i)) +
          dist (f.path (P.left i)) (g.path (P.timeChange Q t)) := dist_triangle _ _ _
    _ ≤ dist (f.path t) (f.path (P.left i)) +
        (dist (f.path (P.left i)) (g.path (Q.left i)) +
          dist (g.path (Q.left i)) (g.path (P.timeChange Q t))) :=
      add_le_add_right (dist_triangle _ _ _) _
    _ ≤ α + (β + γ) := add_le_add (hf i t ht)
      (add_le_add (hvertices i) (by simpa only [dist_comm] using hg i _ he))
    _ = α + β + γ := by ring

/-- The actual infimum-over-homeomorphisms Fréchet distance is controlled by
finite skeleton errors and within-segment oscillations. -/
theorem frechetEDist_le_of_segment_bounds {α β γ : ℝ}
    (hf : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      P.left i ≤ t ∧ t ≤ P.right i → dist (f.path t) (f.path (P.left i)) ≤ α)
    (hvertices : ∀ i : Fin (n + 1),
      dist (f.path (P.left i)) (g.path (Q.left i)) ≤ β)
    (hg : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      Q.left i ≤ t ∧ t ≤ Q.right i → dist (g.path t) (g.path (Q.left i)) ≤ γ) :
    NormalizedCurve.frechetEDist f g ≤ ENNReal.ofReal (α + β + γ) := by
  apply (iInf_le _ (P.timeChange Q)).trans
  apply iSup_le
  intro t
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (P.dist_timeChange_le_of_segment_bounds Q f g hf hvertices hg t)

/-- The same bound holds in the genuine metric quotient used by Theorem A. -/
theorem curveSpace_edist_le_of_segment_bounds {α β γ : ℝ}
    (hf : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      P.left i ≤ t ∧ t ≤ P.right i → dist (f.path t) (f.path (P.left i)) ≤ α)
    (hvertices : ∀ i : Fin (n + 1),
      dist (f.path (P.left i)) (g.path (Q.left i)) ≤ β)
    (hg : ∀ i : Fin (n + 1), ∀ t : unitInterval,
      Q.left i ≤ t ∧ t ≤ Q.right i → dist (g.path t) (g.path (Q.left i)) ≤ γ) :
    edist (CurveSpace.mk f) (CurveSpace.mk g) ≤ ENNReal.ofReal (α + β + γ) :=
  P.frechetEDist_le_of_segment_bounds Q f g hf hvertices hg

end TimePartition

/-- Zero-duration stopped paths are constant representatives, whose actual
Fréchet distance is exactly the distance between their positions. -/
theorem frechetEDist_const_const {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    NormalizedCurve.frechetEDist (NormalizedCurve.const x) (NormalizedCurve.const y) =
      edist x y := by
  apply le_antisymm
  · have h := NormalizedCurve.frechetEDist_le_edist_path
      (NormalizedCurve.const x) (NormalizedCurve.const y)
    simpa only [NormalizedCurve.const, ContinuousMap.edist_eq_iSup,
      ContinuousMap.const_apply, iSup_const] using h
  · exact NormalizedCurve.endpoint_edist_le (NormalizedCurve.const x) (NormalizedCurve.const y)

end BouRabeeGwynne
