/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_sublinear_power_le
    {a C ζ : ℝ} (ha : a < 1) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → C * (K : ℝ) ^ a ≤ ζ * K := by
  have hlim : Tendsto (fun K : ℕ => C * (K : ℝ) ^ (a - 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(1 - a))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - a)).comp
        tendsto_natCast_atTop_atTop
    simpa only [show -(1 - a) = a - 1 by ring, mul_zero] using
      tendsto_const_nhds.mul hpow
  have hsmall : ∀ᶠ K : ℕ in atTop, C * (K : ℝ) ^ (a - 1) < ζ :=
    hlim.eventually (Iio_mem_nhds hζ)
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.1
    (hsmall.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨hsmallK, hK1⟩ := hK₀ K hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  rw [Real.rpow_sub_one hKpos.ne'] at hsmallK
  have hdiv : C * (K : ℝ) ^ a / K < ζ := by
    simpa only [mul_div_assoc] using hsmallK
  have hlt : C * (K : ℝ) ^ a < ζ * K :=
    (div_lt_iff₀ hKpos).mp hdiv
  exact hlt.le

end SupercriticalLQGUniqueness.B2.DG20Conc
