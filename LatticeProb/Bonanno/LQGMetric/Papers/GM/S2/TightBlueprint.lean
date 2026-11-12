/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightBlueprint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightD
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.Moments.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.Algebra.Order.Field.GeomSum
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GM S2.4a–c in the Blueprint form (D56)

The Blueprint Props `Blueprint.GMS2_4a`, `GMS2_4b`, `GMS2_4c` (GM U:449–452, decision D14 =
DEC-A D-A3; constants before `(Ω, P, h)`, decision D56) follow from the proved
`GM.Tight.gm_S2_4a`, `gm_S2_4a_sep`, `gm_S2_4b`, `gm_S2_4c` (own proofs, D-A3) by rewriting the
events: `rK + z = scaleSet r z K`, `‖(ru + z) − (rv + z)‖ = r‖u − v‖`,
`𝔠_r e^{ξh_r(z)} = scaleFac`, and `setDist`/`internalDiam` as an infimum/supremum over pairs.
For `GMS2_4c`, an empty `U` (allowed by `IsPreconnected`) forces `K = ∅`, and the internal
diameter of the empty set is `0`.

`GMS2_4e` follows from `gm_S2_4e` (which assumes `DFGPSScaling` and `LMLem3_1a`, D14) by
compactness: on `B̄_r(z) × B̄_r(z)` the continuous `D_h` attains a maximum `< M`, while
`D_h(x, y) > M` for `x ∈ B_r(z)`, `y ∈ ∂B_{Rr}(z)`.

`GMS2_4d` follows from `gm_S2_4d` (the distance around the annulus, `ContMetric.aroundDist`, is at
most `A·D_h(x, y)` for all `x, y` on the two boundary circles): then `aroundDist ≤ A·D_h(∂B_{αr},
∂B_r) < (2A + 2)·D_h(∂B_{αr}, ∂B_r)` (the set distance is positive and finite), so some
disconnecting path in the annulus has length `≤ (2A + 2)·D_h(∂B_{αr}, ∂B_r)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric
namespace GM
namespace Tight

lemma norm_affine_sub {r : ℝ} (hr : 0 < r) (z u v : ℂ) :
    ‖((r : ℂ) * u + z) - ((r : ℂ) * v + z)‖ = r * ‖u - v‖ := by
  rw [show ((r : ℂ) * u + z) - ((r : ℂ) * v + z) = (r : ℂ) * (u - v) by ring, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- **GM.S2.4a** in the Blueprint form (D56), from `gm_S2_4a` and `gm_S2_4a_sep`. -/
theorem blueprint_GMS2_4a : GMS2_4a := by
  intro γ hγ hγ2 D c hD
  refine ⟨fun U K hU hUb hK hKU p hp => ?_, fun K hK b hb p hp => ?_⟩
  · have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
    have hfc : IsCompact (frontier U) :=
      hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have hdisj : Disjoint K (frontier U) :=
      (Set.disjoint_iff_inter_eq_empty.2 hU.inter_frontier_eq).mono_left hKU
    obtain ⟨s, hs, H⟩ := gm_S2_4a hD hK hfc hdisj hε
    refine ⟨s, hs, fun P _ h hh z r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr z).le⟩
    simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
    intro hall
    apply hω
    rw [setDist, MetricGeometry.le_setEDist]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine (ENNReal.ofReal_le_ofReal (le_of_lt ?_)).trans_eq (edist_dist _ _).symm
    have h1 := hall u hu v hv
    simp only [scaleFac, mul_assoc] at h1 ⊢
    exact h1
  · have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨s, hs, H⟩ := gm_S2_4a_sep hD hK hb hε
    refine ⟨s, hs, fun P _ h hh z r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr z).le⟩
    simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
    intro hall
    apply hω
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    rw [norm_affine_sub hr, mul_comm b r] at huv
    have := hall u hu v hv (le_of_mul_le_mul_left huv hr)
    simp only [scaleFac, ← mul_assoc]
    exact this.le

/-- **GM.S2.4b** in the Blueprint form (D56), from `gm_S2_4b`. -/
theorem blueprint_GMS2_4b : GMS2_4b := by
  intro γ hγ hγ2 D c hD K hK s hs p hp
  have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨b, hb, H⟩ := gm_S2_4b hD hK hs hε
  refine ⟨b, hb, fun P _ h hh z r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr z).le⟩
  simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
  intro hall
  apply hω
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
  rw [norm_affine_sub hr, mul_comm b r] at huv
  have := hall u hu v hv (le_of_mul_le_mul_left huv hr)
  simp only [scaleFac, ← mul_assoc]
  exact this.le

/-- **GM.S2.4c** in the Blueprint form (D56), from `gm_S2_4c` (`U = ∅` handled separately). -/
theorem blueprint_GMS2_4c : GMS2_4c := by
  intro γ hγ hγ2 D c hD U K hU hUb hUc hK hKU p hp
  by_cases hne : U.Nonempty
  · have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨S, hS, H⟩ := gm_S2_4c hD hU ⟨hne, hUc⟩ hUb hK hKU hε
    refine ⟨S, hS, fun P _ h hh z r hr =>
      (measure_mono fun ω hω => ?_).trans (H P h hh r hr z).le⟩
    simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
    intro hall
    apply hω
    refine iSup₂_le fun _ hu' => iSup₂_le fun _ hv' => ?_
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨v, hv, rfl⟩ := hv'
    simpa only [scaleFac, scaleSet, mul_assoc] using hall u hu v hv
  · have hK0 : K = ∅ := subset_eq_empty hKU (not_nonempty_iff_eq_empty.1 hne)
    refine ⟨1, one_pos, fun P _ h hh z r hr => ?_⟩
    have : {ω | internalDiam (D (h ω)) (scaleSet r z K) (scaleSet r z U) ≤
        ENNReal.ofReal (1 * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ = ∅ := by
      ext ω
      simp [internalDiam, scaleSet, hK0]
    rw [this, measure_empty]
    exact bot_le

/-- deterministic step of `blueprint_GMS2_4e_of`: a separating level `M` on `B̄_{2r}(z)` gives
`sup_{u,v ∈ B_r(z)} D(u,v) < D(B_r(z), ∂B_{Rr}(z))` -/
lemma iSup_lt_setDist_of_level (d : ContMetric) {z : ℂ} {r R M : ℝ} (hr : 0 < r)
    (hM1 : ∀ u ∈ closedBall z (2 * r), ∀ v ∈ closedBall z (2 * r), d.1 (u, v) < M)
    (hM2 : ∀ x ∈ closedBall z (2 * r), ∀ y ∈ sphere z (R * r), M < d.1 (x, y)) :
    (⨆ u ∈ ball z r, ⨆ v ∈ ball z r, ENNReal.ofReal (d.1 (u, v))) <
      setDist d (ball z r) (sphere z (R * r)) := by
  have hK : IsCompact (closedBall z r ×ˢ closedBall z r) :=
    (isCompact_closedBall z r).prod (isCompact_closedBall z r)
  have hKne : (closedBall z r ×ˢ closedBall z r).Nonempty :=
    ⟨(z, z), mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hKne d.1.continuous.continuousOn
  have hsub : closedBall z r ⊆ closedBall z (2 * r) := closedBall_subset_closedBall (by linarith)
  have hm1 : d.1 q < M := hM1 q.1 (hsub hq.1) q.2 (hsub hq.2)
  have hm0 : 0 ≤ d.1 q := dist_nonneg (x := d.pt q.1) (y := d.pt q.2)
  calc (⨆ u ∈ ball z r, ⨆ v ∈ ball z r, ENNReal.ofReal (d.1 (u, v)))
      ≤ ENNReal.ofReal (d.1 q) :=
        iSup₂_le fun u hu => iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal
          (hmax (show (u, v) ∈ closedBall z r ×ˢ closedBall z r from
            ⟨ball_subset_closedBall hu, ball_subset_closedBall hv⟩))
    _ < ENNReal.ofReal M := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hm1
    _ ≤ setDist d (ball z r) (sphere z (R * r)) := by
        rw [setDist, MetricGeometry.le_setEDist]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        refine (ENNReal.ofReal_le_ofReal ?_).trans_eq (edist_dist _ _).symm
        exact (hM2 x (hsub (ball_subset_closedBall hx)) y hy).le

/-- **GM.S2.4e** in the Blueprint form (D56), from `gm_S2_4e` (which assumes DFGPS Theorem 1.5
`DFGPSScaling` and LM Lemma 3.1 `LMLem3_1a`). -/
theorem blueprint_GMS2_4e_of (hT15 : DFGPSScaling) (hL31 : LMLem3_1a) : GMS2_4e := by
  intro γ hγ hγ2 D c hD β hβ0 hβ1
  obtain ⟨R, hR, H⟩ := gm_S2_4e hT15 hL31 hγ hγ2 hD (β := ENNReal.ofReal β)
    (ENNReal.ofReal_pos.2 hβ0)
  refine ⟨R, hR, fun P _ h hh z r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr z).le⟩
  simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
  rintro ⟨M, hM1, hM2⟩
  exact hω (iSup_lt_setDist_of_level (D (h ω)) hr hM1 hM2)

end Tight
end GM
end LQGMetric
