/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorCenterDegree at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorReparam
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_ratio_degree_eq_center_degree
    {σ : ℝ → ℂ} (hσ : ContinuousOn σ (Icc (0 : ℝ) 1))
    (hclosed : σ 0 = σ 1)
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hσann : ∀ u ∈ Icc (0 : ℝ) 1,
      r < dist (σ u) c ∧ dist (σ u) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    {G : C(unitInterval, ℂ)} (hG : ∀ u, G u ≠ 0)
    (hGdef : ∀ u, G u = (σ u - c) / (σ u - v)) :
    QuantumZipper.CA.Topo.loopDeg G hG =
      QuantumZipper.CA.Topo.loopDeg
        (⟨fun u : unitInterval => σ u - c, by
          have hc : Continuous (fun u : unitInterval => σ u) :=
            hσ.comp_continuous continuous_subtype_val (fun u => u.2)
          exact hc.sub continuous_const⟩ : C(unitInterval, ℂ))
        (fun u => sub_ne_zero.mpr (by
          intro heq
          have h := (hσann u u.2).1
          rw [heq, dist_self] at h
          linarith)) := by
  let C : C(unitInterval, ℂ) := ⟨fun u => σ u - c, by
    have hc : Continuous (fun u : unitInterval => σ u) :=
      hσ.comp_continuous continuous_subtype_val (fun u => u.2)
    exact hc.sub continuous_const⟩
  let B : C(unitInterval, ℂ) := ⟨fun u => σ u - v, by
    have hc : Continuous (fun u : unitInterval => σ u) :=
      hσ.comp_continuous continuous_subtype_val (fun u => u.2)
    exact hc.sub continuous_const⟩
  have hC : ∀ u, C u ≠ 0 := by
    intro u heq
    have h := (hσann u u.2).1
    have : σ u = c := sub_eq_zero.mp heq
    rw [this, dist_self] at h
    linarith
  have hB : ∀ u, B u ≠ 0 := by
    intro u heq
    have h := (hσann u u.2).2
    have : σ u = v := sub_eq_zero.mp heq
    rw [this] at h
    linarith
  have hcst : c - v ≠ 0 := by
    intro heq
    have : c = v := sub_eq_zero.mp heq
    rw [← this, dist_self] at hv
    have h := (hσann 0 (by simp)).1
    linarith
  have hBc : B 0 = B 1 := by simpa [B] using congrArg (fun z : ℂ => z - v) hclosed
  have hCc : C 0 = C 1 := by simpa [C] using congrArg (fun z : ℂ => z - c) hclosed
  have hGc : G 0 = G 1 := by
    rw [hGdef, hGdef]
    simpa using congrArg (fun z : ℂ => (z - c) / (z - v)) hclosed
  have hBdeg : QuantumZipper.CA.Topo.loopDeg B hB = 0 := by
    have hclose : ∀ u : unitInterval,
        ‖B u - (ContinuousMap.const unitInterval (c - v)) u‖ <
          ‖(ContinuousMap.const unitInterval (c - v)) u‖ := by
      intro u
      simpa [B, dist_eq_norm, sub_sub_sub_cancel_right] using
        (hσann u u.2).2.trans_le (by simpa [dist_eq_norm, norm_sub_rev] using hv)
    have heq := QuantumZipper.CA.Topo.loopDeg_eq_of_norm_sub_lt B
      (ContinuousMap.const unitInterval (c - v)) hB (fun _ => hcst)
      hBc rfl hclose
    simpa only [QuantumZipper.CA.Topo.loopDeg_const] using heq
  have hmul := QuantumZipper.CA.Topo.loopDeg_mul G B hG hB hGc hBc
  have hprod : G * B = C := by
    ext u
    simp only [ContinuousMap.mul_apply]
    rw [hGdef]
    dsimp [B, C]
    exact div_mul_cancel₀ _ (hB u)
  have hres : QuantumZipper.CA.Topo.loopDeg C hC =
      QuantumZipper.CA.Topo.loopDeg G hG := by
    simpa only [hprod, hBdeg, add_zero] using hmul
  simpa only [C] using hres.symm

end SupercriticalLQGUniqueness.B2.DG20Conc
