/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeNear at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwelveNear

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF Filter

theorem laneC_prime_long_nonneg (side : Fin 4) (i : Fin 5) :
    0 ≤ (laneCPrimeLongRect side i).w ∧
      0 ≤ (laneCPrimeLongRect side i).h := by
  fin_cases side <;> norm_num [laneCPrimeLongRect]

theorem laneC_prime_join_nonneg (side : Fin 4) (i : Fin 4) :
    0 ≤ (laneCPrimeJoinRect side i).w ∧
      0 ≤ (laneCPrimeJoinRect side i).h := by
  fin_cases side <;> norm_num [laneCPrimeJoinRect]

theorem laneC_prime_long_len_ne_top {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (side : Fin 4) (i : Fin 5) :
    rectLen ξ f (laneCPrimeLongRect side i) ≠ ⊤ :=
  rectLen_ne_top _ (laneC_prime_long_nonneg side i).1
    (laneC_prime_long_nonneg side i).2 hf

theorem laneC_prime_join_len_ne_top {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (side : Fin 4) (i : Fin 4) :
    rectLen ξ f (laneCPrimeJoinRect side i) ≠ ⊤ :=
  rectLen_ne_top _ (laneC_prime_join_nonneg side i).1
    (laneC_prime_join_nonneg side i).2 hf

theorem laneC_prime_near_paths {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : Fin 4 → Fin 5 → ℝ → ℂ)
      (d : Fin 4 → Fin 4 → ℝ → ℂ),
      (∀ side i,
        AdmPath (laneCPrimeLongRect side i).toSet
          (laneCPrimeLongRect side i).side₁
          (laneCPrimeLongRect side i).side₂ (p side i) ∧
        lfppLen ξ f (p side i) ≤
          rectLen ξ f (laneCPrimeLongRect side i) + ENNReal.ofReal ε) ∧
      (∀ side i,
        AdmPath (laneCPrimeJoinRect side i).toSet
          (laneCPrimeJoinRect side i).side₁
          (laneCPrimeJoinRect side i).side₂ (d side i) ∧
        lfppLen ξ f (d side i) ≤
          rectLen ξ f (laneCPrimeJoinRect side i) + ENNReal.ofReal ε) := by
  have hp : ∀ side i, ∃ p : ℝ → ℂ,
      AdmPath (laneCPrimeLongRect side i).toSet
        (laneCPrimeLongRect side i).side₁
        (laneCPrimeLongRect side i).side₂ p ∧
      lfppLen ξ f p ≤
        rectLen ξ f (laneCPrimeLongRect side i) + ENNReal.ofReal ε := by
    intro side i
    exact S6D.exists_near (laneC_prime_long_len_ne_top hf side i) hε
  have hd : ∀ side i, ∃ d : ℝ → ℂ,
      AdmPath (laneCPrimeJoinRect side i).toSet
        (laneCPrimeJoinRect side i).side₁
        (laneCPrimeJoinRect side i).side₂ d ∧
      lfppLen ξ f d ≤
        rectLen ξ f (laneCPrimeJoinRect side i) + ENNReal.ofReal ε := by
    intro side i
    exact S6D.exists_near (laneC_prime_join_len_ne_top hf side i) hε
  choose p hp' using hp
  choose d hd' using hd
  exact ⟨p,d,hp',hd'⟩

theorem laneC_prime_near_threshold {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hpl : ∀ side i, (rectLen ξ f (laneCPrimeLongRect side i)).toReal ≤ b)
    (hdl : ∀ side i, (rectLen ξ f (laneCPrimeJoinRect side i)).toReal ≤ b) :
    (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
      laneCPrimeInner laneCPrimeOuter ≤ ENNReal.ofReal (36 * b) := by
  let A := (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
    laneCPrimeInner laneCPrimeOuter
  have hε : ∀ ε : ℝ, 0 < ε → A ≤ ENNReal.ofReal (36 * (b + ε)) := by
    intro ε hε
    obtain ⟨p,d,hp,hd⟩ := laneC_prime_near_paths (ξ := ξ) (f := f) hf hε
    have hpLen (side : Fin 4) (i : Fin 5) :
        lfppLen ξ f (p side i) ≤ ENNReal.ofReal (b + ε) := by
      have h1 := (hp side i).2
      have hfin := laneC_prime_long_len_ne_top (ξ := ξ) (f := f) hf side i
      rw [← ENNReal.ofReal_toReal hfin] at h1
      calc
        _ ≤ ENNReal.ofReal (rectLen ξ f (laneCPrimeLongRect side i)).toReal +
            ENNReal.ofReal ε := h1
        _ ≤ ENNReal.ofReal b + ENNReal.ofReal ε :=
          add_le_add (ENNReal.ofReal_le_ofReal (hpl side i)) le_rfl
        _ = ENNReal.ofReal (b + ε) := (ENNReal.ofReal_add hb hε.le).symm
    have hdLen (side : Fin 4) (i : Fin 4) :
        lfppLen ξ f (d side i) ≤ ENNReal.ofReal (b + ε) := by
      have h1 := (hd side i).2
      have hfin := laneC_prime_join_len_ne_top (ξ := ξ) (f := f) hf side i
      rw [← ENNReal.ofReal_toReal hfin] at h1
      calc
        _ ≤ ENNReal.ofReal (rectLen ξ f (laneCPrimeJoinRect side i)).toReal +
            ENNReal.ofReal ε := h1
        _ ≤ ENNReal.ofReal b + ENNReal.ofReal ε :=
          add_le_add (ENNReal.ofReal_le_ofReal (hdl side i)) le_rfl
        _ = ENNReal.ofReal (b + ε) := (ENNReal.ofReal_add hb hε.le).symm
    have hbase := laneC_prime_paths_aroundDist_le hf p d
      (fun side i => (hp side i).1) (fun side i => (hd side i).1)
      hpLen hdLen
    calc
      A ≤ 36 * ENNReal.ofReal (b + ε) := hbase
      _ = ENNReal.ofReal (36 * (b + ε)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36)]
        norm_num
  have hseq : Tendsto (fun n : ℕ => ENNReal.ofReal
      (36 * (b + (n + 1 : ℝ)⁻¹))) atTop
      (nhds (ENNReal.ofReal (36 * b))) := by
    have hreal : Tendsto (fun n : ℕ => 36 * (b + (n + 1 : ℝ)⁻¹))
        atTop (nhds (36 * b)) := by
      have hsmall : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
        simpa [Nat.cast_add, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hc : Tendsto (fun _ : ℕ => (36 : ℝ)) atTop (nhds 36) := tendsto_const_nhds
      have hb' : Tendsto (fun _ : ℕ => b) atTop (nhds b) := tendsto_const_nhds
      simpa only [add_zero] using hc.mul (hb'.add hsmall)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact ge_of_tendsto hseq (Eventually.of_forall fun n =>
    hε _ (by positivity))

end SupercriticalLQGUniqueness.B2.DG20Conc
