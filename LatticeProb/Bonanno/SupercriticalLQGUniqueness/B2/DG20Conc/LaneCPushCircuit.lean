/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushCircuit at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareLoop
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPathDegree
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushLength
import LatticeProb.Bonanno.LQGMetric.LFPP.Length

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

theorem laneC_push_closed_loop_separates
    {γ : ℝ → ℂ} (hp : IsPiecewiseC1Path γ (γ 0) (γ 1))
    (hc : γ 0 = γ 1)
    (hm : MapsTo γ (Icc (0 : ℝ) 1) laneCDoublePrimeCross)
    (hdeg : loopDeg
      ⟨fun u : unitInterval => γ u - laneCSquareCenter,
        (hp.continuousOn.comp_continuous continuous_subtype_val
          (fun u => u.2)).sub continuous_const⟩
      (by
        intro u hz
        have hn := laneC_closed_ring_norm_ge (hm u.2)
        rw [show γ u - laneCSquareCenter = 0 from hz, norm_zero] at hn
        norm_num at hn) = 1)
    {d : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1 / 1000) :
    Disconnects ((laneCInwardPush d ∘ γ) '' Icc (0 : ℝ) 1)
      laneCDoublePrimeInner laneCDoublePrimeOuter := by
  let ρ := laneCInwardPush d ∘ γ
  have hρp : IsPiecewiseC1Path ρ (ρ 0) (ρ 1) := by
    simpa [ρ, Function.comp] using laneC_inwardPush_piecewise d hp
  have hρc : ρ 0 = ρ 1 := by simp [ρ, hc]
  have hρm : MapsTo ρ (Icc (0 : ℝ) 1) laneCDoublePrimeAround :=
    laneC_inwardPush_path_open hd hdsmall hm
  let L : C(unitInterval, ℂ) :=
    ⟨fun u => ρ u,
      hρp.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2)⟩
  let P : C(unitInterval, ℂ) :=
    ⟨fun u => γ u,
      hp.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2)⟩
  have hP : ∀ u, P u ∈ laneCDoublePrimeCross := fun u => hm u.2
  have hPclosed : P 0 = P 1 := hc
  have hLopen : ∀ u, L u ∈ laneCDoublePrimeAround := fun u => hρm u.2
  have hLclosed : L 0 = L 1 := hρc
  have hpush := laneC_inwardPush_loopDeg_eq hd hdsmall P hP hPclosed
  have hLdeg : loopDeg
      ⟨fun u => L u - laneCSquareCenter, L.continuous.sub continuous_const⟩
      (by
        intro u hz
        have hcenter : laneCSquareCenter ∈ laneCInnerCluster := by
          norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]
        exact (hLopen u).2 ((sub_eq_zero.mp hz) ▸ hcenter)) = 1 := by
    convert hpush.trans hdeg using 1
    congr 1
  have hsep := laneC_open_loop_disconnects L hLclosed hLopen (by
    rw [hLdeg]
    norm_num)
  have hrange : range L = ρ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  exact hrange ▸ hsep

theorem laneC_push_closed_loop_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f)
    {γ : ℝ → ℂ} (hp : IsPiecewiseC1Path γ (γ 0) (γ 1))
    (hc : γ 0 = γ 1)
    (hm : MapsTo γ (Icc (0 : ℝ) 1) laneCDoublePrimeCross)
    (hdeg : loopDeg
      ⟨fun u : unitInterval => γ u - laneCSquareCenter,
        (hp.continuousOn.comp_continuous continuous_subtype_val
          (fun u => u.2)).sub continuous_const⟩
      (by
        intro u hz
        have hn := laneC_closed_ring_norm_ge (hm u.2)
        rw [show γ u - laneCSquareCenter = 0 from hz, norm_zero] at hn
        norm_num at hn) = 1) :
    (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter ≤ lfppLen ξ f γ := by
  let A := (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
    laneCDoublePrimeInner laneCDoublePrimeOuter
  have hle : ∀ n, A ≤ lfppLen ξ f
      (laneCInwardPush (laneCPushSequence n) ∘ γ) := by
    intro n
    have hd := laneC_push_sequence_pos n
    have hds := laneC_push_sequence_le n
    let ρ := laneCInwardPush (laneCPushSequence n) ∘ γ
    have hρp : IsPiecewiseC1Path ρ (ρ 0) (ρ 1) := by
      simpa [ρ, Function.comp] using laneC_inwardPush_piecewise _ hp
    have hρm : MapsTo ρ (Icc (0 : ℝ) 1) laneCDoublePrimeAround :=
      laneC_inwardPush_path_open hd hds hm
    have hsub : ρ '' Icc (0 : ℝ) 1 ⊆ laneCDoublePrimeAround := by
      rintro z ⟨t, ht, rfl⟩
      exact hρm ht
    have hsep := laneC_push_closed_loop_separates hp hc hm hdeg hd hds
    calc
      A ≤ (lfppContMetric ξ f hf).len ρ 0 1 := by
        unfold A ContMetric.aroundDist
        exact iInf_le_of_le (0 : ℝ) (iInf_le_of_le (1 : ℝ)
          (iInf_le_of_le ρ (iInf_le_of_le zero_le_one
            (iInf_le_of_le hρp.continuousOn
              (iInf_le_of_le hsub (iInf_le_of_le hsep le_rfl))))))
      _ ≤ lfppLen ξ f ρ := by
        simpa only [lfppLen_eq] using len_le_lfppLen hf hρp le_rfl le_rfl
  exact ge_of_tendsto (laneC_inwardPush_lfppLen_tendsto hf hp hm)
    (Eventually.of_forall hle)

end SupercriticalLQGUniqueness.B2.DG20Conc
