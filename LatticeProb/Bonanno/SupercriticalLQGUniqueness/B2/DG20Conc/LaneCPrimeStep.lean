/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeStep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeMeet
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBridgeGeneric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

private theorem laneC_prime_prefix_source (side : Fin 4) (i : Fin 4) :
    (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).side₁ =
      (laneCPrimePrefixRect side i.succ).side₁ := by
  fin_cases side <;> simp [laneCPrimePrefixRect, MarkedRect.side₁]

private theorem laneC_prime_next_target (side : Fin 4) (i : Fin 4) :
    (laneCPrimeLongRect side i.succ).side₂ =
      (laneCPrimePrefixRect side i.succ).side₂ := by
  fin_cases side <;> simp [laneCPrimeLongRect, laneCPrimePrefixRect,
    MarkedRect.side₂, Fin.val_succ, laneCPrimeFin4AsFin5] <;> ring

theorem laneC_prime_step {ξ : ℝ} {f : ℂ → ℝ}
    (side : Fin 4) (i : Fin 4)
    {p q δ : ℝ → ℂ}
    (hp : AdmPath (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).toSet
      (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).side₁
      (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).side₂ p)
    (hq : AdmPath (laneCPrimeLongRect side i.succ).toSet
      (laneCPrimeLongRect side i.succ).side₁
      (laneCPrimeLongRect side i.succ).side₂ q)
    (hδ : AdmPath (laneCPrimeJoinRect side i).toSet
      (laneCPrimeJoinRect side i).side₁
      (laneCPrimeJoinRect side i).side₂ δ) :
    ∃ r : ℝ → ℂ,
      AdmPath (laneCPrimePrefixRect side i.succ).toSet
        (laneCPrimePrefixRect side i.succ).side₁
        (laneCPrimePrefixRect side i.succ).side₂ r ∧
      lfppLen ξ f r ≤ lfppLen ξ f p + lfppLen ξ f δ + lfppLen ξ f q := by
  obtain ⟨a,b,ha,hab,hb,hd⟩ := laneC_prime_join_clip side i hδ
  let d := subPath δ a b
  obtain ⟨zp,hzp,wp,hwp,hpp,hpU0⟩ := hp
  obtain ⟨zq,hzq,wq,hwq,hqp,hqU0⟩ := hq
  obtain ⟨zd,hzd,wd,hwd,hdp,hdU0⟩ := hd
  have hpU : MapsTo p (Icc (0 : ℝ) 1)
      (laneCPrimePrefixRect side i.succ).toSet :=
    fun t ht => laneC_prime_prefix_subset_next side i (hpU0 t ht)
  have hqU : MapsTo q (Icc (0 : ℝ) 1)
      (laneCPrimePrefixRect side i.succ).toSet :=
    fun t ht => laneC_prime_long_next_subset side i (hqU0 t ht)
  have hdU : MapsTo d (Icc (0 : ℝ) 1)
      (laneCPrimePrefixRect side i.succ).toSet :=
    fun t ht => laneC_prime_join_mid_subset_next side i (hdU0 t ht)
  have hE : p 0 ∈ (laneCPrimePrefixRect side i.succ).side₁ := by
    rw [← laneC_prime_prefix_source side i]
    simpa [hpp.source] using hzp
  have hF : q 1 ∈ (laneCPrimePrefixRect side i.succ).side₂ := by
    rw [← laneC_prime_next_target side i]
    simpa [hqp.target] using hwq
  obtain ⟨r,hr,hlen⟩ := laneC_bridge_two_paths
    (by simpa [hpp.source, hpp.target] using hpp)
    (by simpa [hqp.source, hqp.target] using hqp)
    (by simpa [d, hdp.source, hdp.target] using hdp)
    hpU hqU hdU hE hF
    (laneC_prime_prefix_meets_join side i ⟨zp,hzp,wp,hwp,hpp,hpU0⟩
      ⟨zd,hzd,wd,hwd,hdp,hdU0⟩)
    (laneC_prime_next_meets_join side i ⟨zq,hzq,wq,hwq,hqp,hqU0⟩
      ⟨zd,hzd,wd,hwd,hdp,hdU0⟩)
  refine ⟨r,hr,hlen.trans ?_⟩
  exact add_le_add_left (add_le_add_right
    (laneC_subpath_len_le ha hab hb) (lfppLen ξ f p)) (lfppLen ξ f q)

end SupercriticalLQGUniqueness.B2.DG20Conc
