/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightWind at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FieldLawlerSubSepWind
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

/-!
# GM S2.4d, topological part: loops near a circle disconnect an annulus (task P2-TIGHT)

Decision D-A3 (`decisions/DEC-A.md` (c), S2.4d): "The loop then has winding number 1 about 0, so
it disconnects the two boundaries: a connecting path avoiding it would keep the winding
constant." Here, `disconnects_of_near_circle`: a closed loop `Γ` with
`‖Γ t − (z + ρ e^{2πit})‖ < min(ρ − a, b − ρ)` for all `t` disconnects `∂B_a(z)` from `∂B_b(z)`.

Proof with the winding index of QuantumZipper (`QuantumZipper.FieldLawler.flSepIdx`, built on the
continuous-logarithm degree `QuantumZipper.CA.Topo.loopDeg`; Burckel, *Classical Analysis in the
Complex Plane*, Def. 4.2, Cor. 4.3; Ahlfors, *Complex Analysis*, Ch. 4 §2.1, p. 116): the index
is locally constant off `Γ` (`flSepIdx_eventuallyEq`), so constant along a path avoiding `Γ`;
by the dog-on-a-leash lemma (`loopDeg_eq_of_norm_sub_lt`) it is `1` at points of `∂B_a(z)`
(compare with the circle, `loopDeg_circle`) and `0` at points of `∂B_b(z)` (compare with a
constant, `loopDeg_const`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex

namespace LQGMetric
namespace GM
namespace Tight

open QuantumZipper.CA.Topo QuantumZipper.FieldLawler

lemma circleLoop_closed (ρ : ℝ) : circleLoop ρ 0 = circleLoop ρ 1 := by
  simp only [circleLoop, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero,
    mul_one]
  exact (periodic_circleMap 0 ρ).eq.symm

lemma norm_circleLoop {ρ : ℝ} (hρ : 0 ≤ ρ) (t : unitInterval) : ‖circleLoop ρ t‖ = ρ := by
  simp [circleLoop, norm_circleMap_zero, abs_of_nonneg hρ]

/-- A loop uniformly close to the circle `∂B_ρ(z)` disconnects `∂B_a(z)` from `∂B_b(z)`. -/
theorem disconnects_of_near_circle {Γ : C(unitInterval, ℂ)} (hΓc : Γ 0 = Γ 1) {z : ℂ}
    {a ρ b : ℝ} (ha : 0 ≤ a) (haρ : a < ρ) (hρb : ρ < b)
    (hΓ : ∀ t, ‖Γ t - (z + circleLoop ρ t)‖ < min (ρ - a) (b - ρ)) :
    Disconnects (range Γ) (sphere z a) (sphere z b) := by
  intro x y γ hx hy
  by_contra hne
  have hoff : ∀ s t, Γ t ≠ γ s := fun s t h => hne ⟨γ s, ⟨s, rfl⟩, ⟨t, h⟩⟩
  have hρ0 : ρ ≠ 0 := by linarith
  have hcirc := norm_circleLoop (ha.trans haρ.le)
  have hcl := circleLoop_closed ρ
  have hx' : ‖x - z‖ = a := by rw [← dist_eq_norm]; exact mem_sphere.1 hx
  have hy' : ‖y - z‖ = b := by rw [← dist_eq_norm]; exact mem_sphere.1 hy
  have hsc : ∀ w : ℂ, flSepShift Γ w 0 = flSepShift Γ w 1 := fun w => by
    simp [flSepShift, hΓc]
  -- index `1` about `x`
  have h1 : flSepIdx Γ x = 1 := by
    have hne0 : ∀ t, flSepShift Γ x t ≠ 0 := fun t h =>
      hoff 0 t (by rw [γ.source]; exact sub_eq_zero.1 h)
    rw [flSepIdx_eq Γ hne0]
    let δ : C(unitInterval, ℂ) := ⟨fun t => circleLoop ρ t + (z - x), by fun_prop⟩
    have hδn : ∀ t, ρ - a ≤ ‖δ t‖ := fun t => by
      calc ρ - a = ‖circleLoop ρ t‖ - ‖x - z‖ := by rw [hcirc, hx']
        _ ≤ ‖circleLoop ρ t - (x - z)‖ := norm_sub_norm_le _ _
        _ = ‖δ t‖ := by
          congr 1
          show circleLoop ρ t - (x - z) = circleLoop ρ t + (z - x)
          ring
    have hδ : ∀ t, δ t ≠ 0 := fun t h => by
      have := hδn t
      rw [h, norm_zero] at this
      linarith
    have hδc : δ 0 = δ 1 := by
      show circleLoop ρ 0 + (z - x) = circleLoop ρ 1 + (z - x)
      rw [hcl]
    rw [loopDeg_eq_of_norm_sub_lt _ δ hne0 hδ (hsc x) hδc (fun t => ?_),
      loopDeg_eq_of_norm_sub_lt δ (circleLoop ρ) hδ (circleLoop_ne_zero hρ0) hδc hcl
        (fun t => ?_)]
    · exact loopDeg_circle hρ0
    · have e : δ t - circleLoop ρ t = z - x := by
        show circleLoop ρ t + (z - x) - circleLoop ρ t = z - x
        ring
      rw [e, norm_sub_rev, hx', hcirc]
      exact haρ
    · have e : flSepShift Γ x t - δ t = Γ t - (z + circleLoop ρ t) := by
        show Γ t - x - (circleLoop ρ t + (z - x)) = _
        ring
      rw [e]
      exact (hΓ t).trans_le ((min_le_left _ _).trans (hδn t))
  -- index `0` about `y`
  have h0 : flSepIdx Γ y = 0 := by
    have hne0 : ∀ t, flSepShift Γ y t ≠ 0 := fun t h =>
      hoff 1 t (by rw [γ.target]; exact sub_eq_zero.1 h)
    rw [flSepIdx_eq Γ hne0]
    have hzy : z - y ≠ 0 := fun h => by
      rw [← norm_eq_zero, norm_sub_rev, hy'] at h
      linarith
    rw [loopDeg_eq_of_norm_sub_lt _ (ContinuousMap.const unitInterval (z - y)) hne0
      (fun _ => hzy) (hsc y) rfl (fun t => ?_), loopDeg_const _ hzy]
    have e : flSepShift Γ y t - ContinuousMap.const unitInterval (z - y) t =
        (Γ t - (z + circleLoop ρ t)) + circleLoop ρ t := by
      show Γ t - y - (z - y) = _
      ring
    rw [e, ContinuousMap.const_apply, norm_sub_rev, hy']
    calc ‖Γ t - (z + circleLoop ρ t) + circleLoop ρ t‖
        ≤ ‖Γ t - (z + circleLoop ρ t)‖ + ‖circleLoop ρ t‖ := norm_add_le _ _
      _ < (b - ρ) + ρ := by
          rw [hcirc]
          exact add_lt_add_of_lt_of_le ((hΓ t).trans_le (min_le_right _ _)) le_rfl
      _ = b := by ring
  -- constancy along `γ`
  have hlc : IsLocallyConstant fun s => flSepIdx Γ (γ s) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    exact (γ.continuous.tendsto s).eventually
      (flSepIdx_eventuallyEq Γ hΓc (fun t => hoff s t))
  have := hlc.apply_eq_of_preconnectedSpace 0 1
  simp only [γ.source, γ.target, h1, h0] at this
  exact one_ne_zero this

end Tight
end GM
end LQGMetric
