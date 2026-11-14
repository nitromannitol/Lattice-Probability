/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeAround at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeSquareLoop
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushCircuit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_four_prime_wide_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {top bot left right : ℝ → ℂ}
    (htop : AdmPath (laneCPrimeWideRect 0).toSet
      (laneCPrimeWideRect 0).side₁ (laneCPrimeWideRect 0).side₂ top)
    (hbot : AdmPath (laneCPrimeWideRect 1).toSet
      (laneCPrimeWideRect 1).side₁ (laneCPrimeWideRect 1).side₂ bot)
    (hleft : AdmPath (laneCPrimeWideRect 2).toSet
      (laneCPrimeWideRect 2).side₁ (laneCPrimeWideRect 2).side₂ left)
    (hright : AdmPath (laneCPrimeWideRect 3).toSet
      (laneCPrimeWideRect 3).side₁ (laneCPrimeWideRect 3).side₂ right) :
    (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
      laneCPrimeInner laneCPrimeOuter ≤
      lfppLen ξ f top + lfppLen ξ f bot +
        lfppLen ξ f left + lfppLen ξ f right := by
  obtain ⟨γ, hp, hc, hm, hball, hdeg, hlen⟩ :=
    laneC_four_prime_wide_open_loop (ξ := ξ) (f := f)
      htop hbot hleft hright
  let L : C(unitInterval, ℂ) :=
    ⟨fun u => γ u,
      hp.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2)⟩
  have hsep : Disconnects (γ '' Icc (0 : ℝ) 1)
      laneCPrimeInner laneCPrimeOuter := by
    have hsep' := laneC_prime_open_loop_disconnects L hc
      (fun u => hm u.2) (fun u => hball u u.2) (by
        change loopDeg
          ⟨fun u : unitInterval => γ u - laneCPrimeCenter,
            (hp.continuousOn.comp_continuous continuous_subtype_val
              (fun u => u.2)).sub continuous_const⟩ _ ≠ 0
        rw [hdeg]
        norm_num)
    have hrange : range L = γ '' Icc (0 : ℝ) 1 := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u, u.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    exact hrange ▸ hsep'
  have hsub : γ '' Icc (0 : ℝ) 1 ⊆ laneCPrimeAround := by
    rintro z ⟨t, ht, rfl⟩
    exact hm ht
  calc
    (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
        laneCPrimeInner laneCPrimeOuter ≤
        (lfppContMetric ξ f hf).len γ 0 1 := by
      unfold ContMetric.aroundDist
      exact iInf_le_of_le (0 : ℝ) (iInf_le_of_le (1 : ℝ)
        (iInf_le_of_le γ (iInf_le_of_le zero_le_one
          (iInf_le_of_le hp.continuousOn
            (iInf_le_of_le hsub (iInf_le_of_le hsep le_rfl))))))
    _ ≤ lfppLen ξ f γ := by
      simpa only [lfppLen_eq] using len_le_lfppLen hf hp le_rfl le_rfl
    _ ≤ _ := hlen

end SupercriticalLQGUniqueness.B2.DG20Conc
