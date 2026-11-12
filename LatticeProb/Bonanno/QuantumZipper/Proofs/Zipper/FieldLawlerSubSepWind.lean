/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.FieldLawlerSubSepWind at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-TOPSEP helper: a connected set on which a loop has nonzero index is bounded

Task FL-TOPSEP (helper of FL-THM, D75). The separation input `FLTopSepStmt`
(`FieldLawlerSubTopMain.lean`) says that a point `x` of `D = ℍ \ K_t` inside `B(0, ε)` lies in a
bounded component of `D \ A` for a maximal arc `A` of `D ∩ C_ε`. Every route to it (in `D`, or on
the `ℍ` side through `Z_t`) ends with the standard index argument: if a closed loop `Γ` avoids a
connected set `S` and has nonzero index about some point of `S`, then `S` is bounded, because the
index is locally constant off `Γ` and vanishes far away: Ahlfors, *Complex Analysis*, 3rd ed.,
McGraw-Hill 1979, Ch. 4, §2.1, properties (i)–(ii) of the index `n(γ, a)`, p. 116 ("constant in
each of the regions determined by γ, and zero in the unbounded region"); followed here with the
continuous-logarithm degree `loopDeg` of `TopoDegree.lean`).

`flSep_isBounded_of_loopDeg`: the index statement.
-/

noncomputable section

open Set Metric Complex

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.CA.Topo

/-- The loop `t ↦ Γ t - z`. -/
def flSepShift (Γ : C(unitInterval, ℂ)) (z : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Γ t - z, by fun_prop⟩

open Classical in
/-- The index of `Γ` about `z` (`0` when `z` lies on `Γ`). -/
def flSepIdx (Γ : C(unitInterval, ℂ)) (z : ℂ) : ℤ :=
  if h : ∀ t, flSepShift Γ z t ≠ 0 then loopDeg (flSepShift Γ z) h else 0

theorem flSepIdx_eq (Γ : C(unitInterval, ℂ)) {z : ℂ} (h : ∀ t, flSepShift Γ z t ≠ 0) :
    flSepIdx Γ z = loopDeg (flSepShift Γ z) h := by
  unfold flSepIdx
  exact dif_pos h

/-- The index is locally constant off the loop. -/
theorem flSepIdx_eventuallyEq (Γ : C(unitInterval, ℂ)) (hΓc : Γ 0 = Γ 1) {z : ℂ}
    (hz : ∀ t, Γ t ≠ z) : ∀ᶠ w in nhds z, flSepIdx Γ w = flSepIdx Γ z := by
  -- distance from `z` to the loop
  have hcont : Continuous fun t : unitInterval => ‖Γ t - z‖ := by fun_prop
  obtain ⟨t₀, -, ht₀⟩ := (isCompact_univ (X := unitInterval)).exists_isMinOn univ_nonempty
    hcont.continuousOn
  set δ := ‖Γ t₀ - z‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 (hz t₀))
  have hmin : ∀ t, δ ≤ ‖Γ t - z‖ := fun t => ht₀ (mem_univ t)
  have hne : ∀ t, flSepShift Γ z t ≠ 0 := fun t => sub_ne_zero.2 (hz t)
  filter_upwards [Metric.ball_mem_nhds z hδpos] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hnew : ∀ t, flSepShift Γ w t ≠ 0 := by
    intro t h
    have h' : Γ t - w = 0 := h
    have := hmin t
    have h2 : Γ t - z = w - z := by linear_combination h'
    rw [h2] at this
    linarith
  rw [flSepIdx_eq Γ hnew, flSepIdx_eq Γ hne]
  refine loopDeg_eq_of_norm_sub_lt _ _ hnew hne
    (by simp [flSepShift, hΓc]) (by simp [flSepShift, hΓc]) fun t => ?_
  show ‖(Γ t - w) - (Γ t - z)‖ < ‖Γ t - z‖
  have : (Γ t - w) - (Γ t - z) = -(w - z) := by ring
  rw [this, norm_neg]
  exact lt_of_lt_of_le hw (hmin t)

end FieldLawler
end QuantumZipper
