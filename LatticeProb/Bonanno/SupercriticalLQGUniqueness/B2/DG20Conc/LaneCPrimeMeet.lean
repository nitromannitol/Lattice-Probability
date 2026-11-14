/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeMeet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeJoinClip

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneC_prime_prefix_meets_join (side : Fin 4) (i : Fin 4)
    {p d : ℝ → ℂ}
    (hp : AdmPath (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).toSet
      (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).side₁
      (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).side₂ p)
    (hd : AdmPath (laneCPrimeJoinMidRect side i).toSet
      (laneCPrimeJoinMidRect side i).side₁
      (laneCPrimeJoinMidRect side i).side₂ d) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, p s = d t := by
  fin_cases side
  · (apply hv_meet (H := laneCPrimePrefixRect 0 (laneCPrimeFin4AsFin5 i))
        (V := laneCPrimeJoinMidRect 0 i) <;>
        first | assumption | (norm_num [laneCPrimeFin4AsFin5, laneCPrimePrefixRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
  · (apply hv_meet (H := laneCPrimePrefixRect 1 (laneCPrimeFin4AsFin5 i))
        (V := laneCPrimeJoinMidRect 1 i) <;>
        first | assumption | (norm_num [laneCPrimeFin4AsFin5, laneCPrimePrefixRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
  · have h : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        d s = p t := by
      (apply hv_meet (H := laneCPrimeJoinMidRect 2 i)
          (V := laneCPrimePrefixRect 2 (laneCPrimeFin4AsFin5 i)) <;>
          first | assumption | (norm_num [laneCPrimeFin4AsFin5, laneCPrimePrefixRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
    obtain ⟨s, hs, t, ht, heq⟩ := h
    exact ⟨t, ht, s, hs, heq.symm⟩
  · have h : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        d s = p t := by
      (apply hv_meet (H := laneCPrimeJoinMidRect 3 i)
          (V := laneCPrimePrefixRect 3 (laneCPrimeFin4AsFin5 i)) <;>
          first | assumption | (norm_num [laneCPrimeFin4AsFin5, laneCPrimePrefixRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
    obtain ⟨s, hs, t, ht, heq⟩ := h
    exact ⟨t, ht, s, hs, heq.symm⟩

theorem laneC_prime_next_meets_join (side : Fin 4) (i : Fin 4)
    {q d : ℝ → ℂ}
    (hq : AdmPath (laneCPrimeLongRect side i.succ).toSet
      (laneCPrimeLongRect side i.succ).side₁
      (laneCPrimeLongRect side i.succ).side₂ q)
    (hd : AdmPath (laneCPrimeJoinMidRect side i).toSet
      (laneCPrimeJoinMidRect side i).side₁
      (laneCPrimeJoinMidRect side i).side₂ d) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, q s = d t := by
  fin_cases side
  · (apply hv_meet (H := laneCPrimeLongRect 0 i.succ)
        (V := laneCPrimeJoinMidRect 0 i) <;>
        first | assumption | (norm_num [laneCPrimeLongRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
  · (apply hv_meet (H := laneCPrimeLongRect 1 i.succ)
        (V := laneCPrimeJoinMidRect 1 i) <;>
        first | assumption | (norm_num [laneCPrimeLongRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
  · have h : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        d s = q t := by
      (apply hv_meet (H := laneCPrimeJoinMidRect 2 i)
          (V := laneCPrimeLongRect 2 i.succ) <;>
          first | assumption | (norm_num [laneCPrimeLongRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
    obtain ⟨s, hs, t, ht, heq⟩ := h
    exact ⟨t, ht, s, hs, heq.symm⟩
  · have h : ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        d s = q t := by
      (apply hv_meet (H := laneCPrimeJoinMidRect 3 i)
          (V := laneCPrimeLongRect 3 i.succ) <;>
          first | assumption | (norm_num [laneCPrimeLongRect, laneCPrimeJoinMidRect] <;> (first | positivity | linarith)))
    obtain ⟨s, hs, t, ht, heq⟩ := h
    exact ⟨t, ht, s, hs, heq.symm⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
