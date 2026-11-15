/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TilingStoppedLawComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ActualStoppedLawComparison
import LatticeProb.Bonanno.BouRabeeGwynne.WalkEdgeSupport

/-! Specialize the actual stopped-law comparison to the genuine ambient
tiling walk. Every step bound and excursion range bound follows from the
tiling geometry and the fixed-ball selectors. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal NNReal

namespace BouRabeeGwynne.OrthogonalTiling

set_option linter.unusedVariables false in
theorem levyProkhorov_actual_tiling_stopped_laws_le {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (T : OrthogonalTiling d) (hd : 1 ≤ d) {W : Set (Euc d)}
    (hW : Bornology.IsBounded W)
    [Fintype (T.closedVertices W)] [MeasurableSpace (T.closedVertices W)]
    [MeasurableSingletonClass (T.closedVertices W)]
    (centers : J → Euc d) {r : ℝ} (hr : 0 < r)
    (hBW : ∀ j, ball (centers j) r ⊆ W) (hmesh : T.mesh ≠ ∞)
    (hA : ∀ v ∈ T.finiteInterior W,
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (hB : ∀ j v, v ∈ {v : T.closedVertices W | T.pos v ∈ ball (centers j) r} →
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (haccess : (T.finiteNetwork (T.closedVertices W)).BoundaryAccessible (T.finiteInterior W))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (hselect : ∀ i x j, select i x = some j →
      ball x (r / 2) ⊆ ball (centers j) r)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (initial : J) (v : T.closedVertices W) (z : Euc d)
    (hv : T.pos v ∈ ball (centers initial) r) (hz : z ∈ ball (centers initial) r)
    (n : ℕ) (P : TimePartition n) {U : Set (Euc d)} (hU : IsOpen U)
    {a ε δ η : ℝ} (hε : 0 < ε) (hbuffer : ε + 2 * T.mesh.toReal < δ)
    (hnone : ∀ i x, select i x = none → x ∉ thickening δ U)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (T.pos v) z ≤ a)
    (hpoint : (2 * r + 2 * T.mesh.toReal) + a + 2 * r ≤ ε)
    {b c o : ℝ≥0∞}
    (hfailure : (T.finiteNetwork (T.closedVertices W)).walkBrownianJointLaw
      (fun w => T.pos w) (T.pos_injective.comp Subtype.val_injective)
      (fun j => {w | T.pos w ∈ ball (centers j) r}) hB
      (fun j => ball (centers j) r) (fun _ => isOpen_ball) μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair
        (fun w : T.closedVertices W => T.pos w) (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion (fun j => ball (centers j) r) z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion (fun j => ball (centers j) r) z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (ε + η) < (rMiddle : ℝ≥0∞)) :
    levyProkhorovEDist
      (((T.finiteNetwork (T.closedVertices W)).trajectoryLaw (T.finiteInterior W) hA v).map
        (stoppedPolygonalCurve (fun w : T.closedVertices W => T.pos w)
          {w | T.pos w ∈ U}))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  have hinside : ∀ i x j, select i x = some j → x ∈ ball (centers j) r := by
    intro i x j hj
    exact hselect i x j hj (mem_ball_self (half_pos hr))
  have hsteps := T.trajectoryLaw_ae_step_dist_le_two_mesh (T.closedVertices W)
    (T.finiteInterior W) hA v hmesh
  have hwrange := T.trajectoryLaw_selectedBallSkeleton_ae_oscillation centers hr hBW hmesh
    hA hB haccess select hs hinside initial v hv
  have hbrange := standardBrownianLaw_skeleton_ae_oscillation hd hμ centers hr select hs
    hinside initial z hz
  exact (T.finiteNetwork (T.closedVertices W)).levyProkhorov_actual_stopped_laws_le hd
    (fun w => T.pos w) (T.pos_injective.comp Subtype.val_injective)
    (fun j => {w | T.pos w ∈ ball (centers j) r}) hB
    (fun j => ball (centers j) r) (fun _ => isOpen_ball) (fun _ => isBounded_ball)
    μ hμ select hs m E hE hdE (fun j _ hw => hBW j hw) hA haccess initial v z n P
    hU hε (by positivity) hbuffer hnone hdiam hnear hpoint hsteps hwrange hbrange
    hfailure htail hosc rWalk rMiddle rBrownian hrWalk hrBrownian
    hwalkBudget hbrownianBudget hmiddleBudget hsmall

end BouRabeeGwynne.OrthogonalTiling
