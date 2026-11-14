/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwelveNear at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwelveRects

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_twelve_paths_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (p : Fin 12 → ℝ → ℂ)
    (hp : ∀ j : Fin 12,
      AdmPath (laneCDoublePrimeTwelveRect j).toSet
        (laneCDoublePrimeTwelveRect j).side₁
        (laneCDoublePrimeTwelveRect j).side₂ (p j)) :
    (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter ≤
      (lfppLen ξ f (p 0) + lfppLen ξ f (p 8) + lfppLen ξ f (p 1)) +
      (lfppLen ξ f (p 2) + lfppLen ξ f (p 9) + lfppLen ξ f (p 3)) +
      (lfppLen ξ f (p 4) + lfppLen ξ f (p 10) + lfppLen ξ f (p 5)) +
      (lfppLen ξ f (p 6) + lfppLen ξ f (p 11) + lfppLen ξ f (p 7)) := by
  let γ : Fin 8 → ℝ → ℂ := fun j => p ⟨j.val, by omega⟩
  have hγ : ∀ j : Fin 8,
      AdmPath (laneCDoublePrimeLongRect j).toSet
        (laneCDoublePrimeLongRect j).side₁
        (laneCDoublePrimeLongRect j).side₂ (γ j) := by
    intro j
    simpa [γ, laneCDoublePrimeTwelveRect] using hp ⟨j.val, by omega⟩
  have htop : AdmPath laneCTopConnector.toSet
      laneCTopConnector.side₁ laneCTopConnector.side₂ (p 8) := by
    simpa [laneCDoublePrimeTwelveRect] using hp 8
  have hbot : AdmPath laneCBottomConnector.toSet
      laneCBottomConnector.side₁ laneCBottomConnector.side₂ (p 9) := by
    simpa [laneCDoublePrimeTwelveRect] using hp 9
  have hleft : AdmPath laneCLeftConnector.toSet
      laneCLeftConnector.side₁ laneCLeftConnector.side₂ (p 10) := by
    simpa [laneCDoublePrimeTwelveRect] using hp 10
  have hright : AdmPath laneCRightConnector.toSet
      laneCRightConnector.side₁ laneCRightConnector.side₂ (p 11) := by
    simpa [laneCDoublePrimeTwelveRect] using hp 11
  simpa [γ] using
    laneC_twelve_long_aroundDist_le hf γ (p 8) (p 9) (p 10) (p 11)
      hγ htop hbot hleft hright

theorem laneC_twelve_near_threshold {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hcost : ∀ j : Fin 12,
      (rectLen ξ f (laneCDoublePrimeTwelveRect j)).toReal ≤ b) :
    (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter ≤ ENNReal.ofReal (12 * b) := by
  let A := (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
    laneCDoublePrimeInner laneCDoublePrimeOuter
  have hε : ∀ ε : ℝ, 0 < ε → A ≤ ENNReal.ofReal (12 * (b + ε)) := by
    intro ε hε
    obtain ⟨p, hp⟩ := laneC_twelve_rect_near_paths (ξ := ξ) hf hε
    have hlen (j : Fin 12) :
        lfppLen ξ f (p j) ≤ ENNReal.ofReal (b + ε) := by
      have h1 := (hp j).2
      have hfin := laneC_twelve_rect_len_ne_top (ξ := ξ) hf j
      rw [← ENNReal.ofReal_toReal hfin] at h1
      calc
        _ ≤ ENNReal.ofReal (rectLen ξ f (laneCDoublePrimeTwelveRect j)).toReal +
            ENNReal.ofReal ε := h1
        _ ≤ ENNReal.ofReal b + ENNReal.ofReal ε :=
          add_le_add (ENNReal.ofReal_le_ofReal (hcost j)) le_rfl
        _ = ENNReal.ofReal (b + ε) := (ENNReal.ofReal_add hb hε.le).symm
    have hbase := laneC_twelve_paths_aroundDist_le (ξ := ξ) hf p (fun j => (hp j).1)
    calc
      A ≤ (lfppLen ξ f (p 0) + lfppLen ξ f (p 8) + lfppLen ξ f (p 1)) +
          (lfppLen ξ f (p 2) + lfppLen ξ f (p 9) + lfppLen ξ f (p 3)) +
          (lfppLen ξ f (p 4) + lfppLen ξ f (p 10) + lfppLen ξ f (p 5)) +
          (lfppLen ξ f (p 6) + lfppLen ξ f (p 11) + lfppLen ξ f (p 7)) := hbase
      _ ≤ (ENNReal.ofReal (b + ε) + ENNReal.ofReal (b + ε) +
          ENNReal.ofReal (b + ε)) +
          (ENNReal.ofReal (b + ε) + ENNReal.ofReal (b + ε) +
          ENNReal.ofReal (b + ε)) +
          (ENNReal.ofReal (b + ε) + ENNReal.ofReal (b + ε) +
          ENNReal.ofReal (b + ε)) +
          (ENNReal.ofReal (b + ε) + ENNReal.ofReal (b + ε) +
          ENNReal.ofReal (b + ε)) := by
        gcongr <;> exact hlen _
      _ = ENNReal.ofReal (12 * (b + ε)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
        norm_num
        ring
  have hseq : Tendsto (fun n : ℕ => ENNReal.ofReal
      (12 * (b + (n + 1 : ℝ)⁻¹))) atTop
      (nhds (ENNReal.ofReal (12 * b))) := by
    have hreal : Tendsto (fun n : ℕ => 12 * (b + (n + 1 : ℝ)⁻¹))
        atTop (nhds (12 * b)) := by
      have hsmall : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
        simpa [Nat.cast_add, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hc : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12) := tendsto_const_nhds
      have hb' : Tendsto (fun _ : ℕ => b) atTop (nhds b) := tendsto_const_nhds
      simpa only [add_zero] using hc.mul (hb'.add hsmall)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact ge_of_tendsto hseq (Eventually.of_forall fun n =>
    hε _ (by positivity))

theorem laneC_twelve_rect_long_imp {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {N b : ℝ} (hN : 12 ≤ N)
    (hlarge : ENNReal.ofReal (N * b) <
      (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
        laneCDoublePrimeInner laneCDoublePrimeOuter) :
    ∃ j : Fin 12, b < (rectLen ξ f (laneCDoublePrimeTwelveRect j)).toReal := by
  by_contra hbad
  push Not at hbad
  by_cases hb : 0 ≤ b
  · have hA := laneC_twelve_near_threshold hf hb hbad
    have hmul : 12 * b ≤ N * b := mul_le_mul_of_nonneg_right hN hb
    exact (not_lt_of_ge (hA.trans (ENNReal.ofReal_le_ofReal hmul))) hlarge
  · have hneg : b < 0 := lt_of_not_ge hb
    have h0 : 0 ≤ (rectLen ξ f (laneCDoublePrimeTwelveRect 0)).toReal :=
      ENNReal.toReal_nonneg
    exact (not_lt_of_ge (hbad 0)) (hneg.trans_le h0)

end SupercriticalLQGUniqueness.B2.DG20Conc
