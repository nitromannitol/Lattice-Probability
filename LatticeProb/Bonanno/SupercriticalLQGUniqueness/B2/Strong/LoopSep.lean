/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.LoopSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 










set_option autoImplicit false

noncomputable section

open Set Metric Complex QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.Strong

 

theorem loop_meets_path (L : C(unitInterval, ℂ)) (hc : L 0 = L 1) (hne : ∀ t, L t ≠ 0)
    (hdeg : loopDeg L hne ≠ 0) {a b : ℂ} (ha : ∀ t, ‖a‖ < ‖L t‖) (hb : ∀ t, ‖L t‖ < ‖b‖)
    (γ : Path a b) : (range γ ∩ range L).Nonempty := by
  by_contra hemp
  have hH : ∀ p : unitInterval × unitInterval, L p.1 - γ p.2 ≠ 0 := by
    intro p hp
    exact hemp ⟨γ p.2, ⟨p.2, rfl⟩, ⟨p.1, (sub_eq_zero.mp hp)⟩⟩
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => L p.1 - γ p.2, by fun_prop⟩
  have hH' : ∀ p, H p ≠ 0 := hH
  have hcH : ∀ s, H (0, s) = H (1, s) := fun s => by simp [H, hc]
  have key := loopDeg_homotopy H hH' hcH
  have h0 : loopDeg (slice H 0) (fun _ => hH' _) = loopDeg L hne := by
    apply loopDeg_eq_of_norm_sub_lt (slice H 0) L (fun _ => hH' _) hne
      (by simp [slice, H, hc]) hc
    intro t
    simp only [slice, H, ContinuousMap.coe_mk, Path.source]
    rw [show L t - a - L t = -a by ring, norm_neg]
    exact ha t
  have hb0 : (-b) ≠ 0 := by
    intro h
    have := hb 0
    rw [neg_eq_zero.mp h, norm_zero] at this
    exact (not_lt.mpr (norm_nonneg _)) this
  have h1 : loopDeg (slice H 1) (fun _ => hH' _) =
      loopDeg (ContinuousMap.const unitInterval (-b)) (fun _ => hb0) := by
    apply loopDeg_eq_of_norm_sub_lt (slice H 1) (ContinuousMap.const unitInterval (-b))
      (fun _ => hH' _) (fun _ => hb0) (by simp [slice, H, hc]) rfl
    intro t
    simp only [slice, H, ContinuousMap.coe_mk, Path.target, ContinuousMap.const_apply]
    rw [show L t - b - -b = L t by ring, norm_neg]
    exact hb t
  rw [h0, h1, loopDeg_const] at key
  exact hdeg key

theorem mem_Icc_mul {T : ℝ} (hT : 0 ≤ T) (u : unitInterval) : T * (u : ℝ) ∈ Icc 0 T :=
  ⟨mul_nonneg hT u.2.1, by nlinarith [u.2.1, u.2.2]⟩

 
theorem disconnects_of_lift {P Λ : ℝ → ℂ} {c : ℂ} {T r R : ℝ} (hT : 0 ≤ T)
    (hP : ContinuousOn P (Icc 0 T)) (hΛ : ContinuousOn Λ (Icc 0 T))
    (hexp : ∀ t ∈ Icc 0 T, P t = c + Complex.exp (Λ t))
    (hend : Λ T = Λ 0 + 2 * Real.pi * I)
    (hin : ∀ t ∈ Icc 0 T, r < ‖P t - c‖) (hout : ∀ t ∈ Icc 0 T, ‖P t - c‖ < R) :
    LQGMetric.Disconnects (P '' Icc 0 T) (sphere c r) (sphere c R) := by
  have hcont : Continuous (fun u : unitInterval => T * (u : ℝ)) := by fun_prop
  let L : C(unitInterval, ℂ) :=
    ⟨fun u => P (T * u) - c, (hP.comp_continuous hcont (mem_Icc_mul hT)).sub continuous_const⟩
  have hLΛ : ∀ u : unitInterval, Complex.exp (Λ (T * u)) = L u := fun u => by
    simp only [L, ContinuousMap.coe_mk]
    rw [hexp _ (mem_Icc_mul hT u)]
    ring
  have hne : ∀ u : unitInterval, L u ≠ 0 := fun u => by
    rw [← hLΛ]; exact Complex.exp_ne_zero _
  have h0 : (T * ((0 : unitInterval) : ℝ)) = 0 := by simp
  have h1 : (T * ((1 : unitInterval) : ℝ)) = T := by simp
  have hc : L 0 = L 1 := by
    rw [← hLΛ, ← hLΛ, h0, h1, hend, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hdeg : loopDeg L hne = 1 := by
    apply loopDeg_unique L hne hc (L := fun u => Λ (T * u))
      (hΛ.comp_continuous hcont (mem_Icc_mul hT)) hLΛ
    rw [h0, h1, hend]
    push_cast
    ring
  intro x y γ hx hy
  let γ' : Path (x - c) (y - c) := γ.map (continuous_sub_right c)
  have hx' : ‖x - c‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.1 hx
  have hy' : ‖y - c‖ = R := by rw [← dist_eq_norm]; exact mem_sphere.1 hy
  obtain ⟨z, ⟨s, hs⟩, ⟨u, hu⟩⟩ := loop_meets_path L hc hne (by rw [hdeg]; norm_num)
    (fun u => by rw [hx']; exact hin _ (mem_Icc_mul hT u))
    (fun u => by rw [hy']; exact hout _ (mem_Icc_mul hT u)) γ'
  refine ⟨γ s, ⟨s, rfl⟩, T * u, mem_Icc_mul hT u, ?_⟩
  have e1 : γ' s = γ s - c := rfl
  have e2 : L u = P (T * u) - c := rfl
  have := hu.trans hs.symm
  rw [e1, e2] at this
  linear_combination this

end SupercriticalLQGUniqueness.B2.Strong
