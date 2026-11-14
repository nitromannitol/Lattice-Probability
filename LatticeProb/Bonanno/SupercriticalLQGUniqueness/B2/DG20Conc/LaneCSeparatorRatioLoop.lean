/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorRatioLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorLoopSeed
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_normalized_separator_ratio_loop
    (D : ContMetric)
    {ρ : ℝ → ℂ} (hρ : ContinuousOn ρ (Icc (0 : ℝ) 1))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ t ∈ Icc (0 : ℝ) 1,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc (0 : ℝ) 1)
      (sphere c r) (sphere c (2 * r))) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      ρ s = ρ t ∧
      let σ := SupercriticalLQGUniqueness.B2.Strong.seg ρ s t
      D.len σ 0 1 ≤ D.len ρ 0 1 ∧
      ∃ (G : C(unitInterval, ℂ)) (hG : ∀ u, G u ≠ 0),
        (∀ u, G u = (σ u - c) / (σ u - v)) ∧
        QuantumZipper.CA.Topo.loopDeg G hG ≠ 0 := by
  obtain ⟨L, hL, hExp, s, hs, t, ht, heq, hne⟩ :=
    laneC_normalized_separator_lifted_return hρ hr hρann hv hsep
  let σ := SupercriticalLQGUniqueness.B2.Strong.seg ρ s t
  have hσ : ContinuousOn σ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hs ht
  have hσann : ∀ u ∈ Icc (0 : ℝ) 1,
      r < dist (σ u) c ∧ dist (σ u) c < 2 * r := by
    intro u hu
    exact hρann _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht hu)
  have hσv : ∀ u ∈ Icc (0 : ℝ) 1, σ u ≠ v := by
    intro u hu hEq
    have h := (hσann u hu).2
    rw [hEq] at h
    linarith
  have hσc : ∀ u ∈ Icc (0 : ℝ) 1, σ u ≠ c := by
    intro u hu hEq
    have h := (hσann u hu).1
    rw [hEq, dist_self] at h
    linarith
  let G : C(unitInterval, ℂ) := ⟨fun u => (σ u - c) / (σ u - v), by
    have hc : Continuous (fun u : unitInterval => σ u) :=
      hσ.comp_continuous continuous_subtype_val (fun u => u.2)
    exact (hc.sub continuous_const).div (hc.sub continuous_const)
      (fun u => sub_ne_zero.mpr (hσv u u.2))⟩
  have hG : ∀ u, G u ≠ 0 := by
    intro u
    exact div_ne_zero (sub_ne_zero.mpr (hσc u u.2))
      (sub_ne_zero.mpr (hσv u u.2))
  have hclosed : G 0 = G 1 := by
    change (σ 0 - c) / (σ 0 - v) = (σ 1 - c) / (σ 1 - v)
    simpa [σ, SupercriticalLQGUniqueness.B2.Strong.seg] using
      congrArg (fun z : ℂ => (z - c) / (z - v)) heq
  let M : unitInterval → ℂ := fun u => L (s + (u : ℝ) * (t - s))
  have hM : Continuous M := by
    have hp : Continuous (fun u : unitInterval => s + (u : ℝ) * (t - s)) := by
      fun_prop
    exact hL.comp_continuous hp (fun u =>
      SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht u.2)
  have hMexp : ∀ u : unitInterval, Complex.exp (M u) = G u := by
    intro u
    exact hExp _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht u.2)
  have hdeg := QuantumZipper.CA.Topo.loopDeg_eq_of_lift G hG hclosed hM hMexp
  have hdegne : QuantumZipper.CA.Topo.loopDeg G hG ≠ 0 := by
    intro hz
    rw [hz] at hdeg
    have hM0 : M 0 = L s := by simp [M]
    have hM1 : M 1 = L t := by simp [M]
    rw [hM0, hM1] at hdeg
    simp at hdeg
    exact hne (sub_eq_zero.mp hdeg).symm
  refine ⟨s, hs, t, ht, heq, ?_, G, hG, (fun _ => rfl), hdegne⟩
  exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
    (D.pt ∘ ρ) hs ht

end SupercriticalLQGUniqueness.B2.DG20Conc
