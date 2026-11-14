/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeLongImp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeNear

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_prime_long_imp {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {N b : ℝ} (hN : 36 ≤ N)
    (hlarge : ENNReal.ofReal (N * b) <
      (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
        laneCPrimeInner laneCPrimeOuter) :
    (∃ side : Fin 4, ∃ i : Fin 5,
      b < (rectLen ξ f (laneCPrimeLongRect side i)).toReal) ∨
    (∃ side : Fin 4, ∃ i : Fin 4,
      b < (rectLen ξ f (laneCPrimeJoinRect side i)).toReal) := by
  by_contra hbad
  push Not at hbad
  obtain ⟨hpl,hdl⟩ := hbad
  by_cases hb : 0 ≤ b
  · have hA := laneC_prime_near_threshold hf hb hpl hdl
    have hmul : 36 * b ≤ N * b := mul_le_mul_of_nonneg_right hN hb
    exact (not_lt_of_ge (hA.trans (ENNReal.ofReal_le_ofReal hmul))) hlarge
  · have hneg : b < 0 := lt_of_not_ge hb
    have h0 : 0 ≤ (rectLen ξ f (laneCPrimeLongRect 0 0)).toReal :=
      ENNReal.toReal_nonneg
    exact (not_lt_of_ge (hpl 0 0)) (hneg.trans_le h0)

end SupercriticalLQGUniqueness.B2.DG20Conc
