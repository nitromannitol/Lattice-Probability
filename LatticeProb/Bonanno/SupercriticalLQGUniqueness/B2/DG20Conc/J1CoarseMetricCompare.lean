/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseMetricCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseAroundCompare
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.LFPP

theorem j1_coarse_cross_around_compare
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (U E F : Set ℂ) (v : ℂ) (M : ℝ)
    (hosc : ∀ z ∈ U, |g z - g v| ≤ M) :
    crossLenIn ξ f U E F ≤
      ENNReal.ofReal (Real.exp (-ξ * g v + |ξ| * M)) *
        crossLenIn ξ (fun z => g z + f z) U E F ∧
    crossLenIn ξ (fun z => g z + f z) U E F ≤
      ENNReal.ofReal (Real.exp (ξ * g v + |ξ| * M)) *
        crossLenIn ξ f U E F ∧
    (lfppContMetric ξ f hf).aroundDist U E F ≤
      ENNReal.ofReal (Real.exp (-ξ * g v + |ξ| * M)) *
        (lfppContMetric ξ (fun z => g z + f z) (hg.add hf)).aroundDist U E F ∧
    (lfppContMetric ξ (fun z => g z + f z) (hg.add hf)).aroundDist U E F ≤
      ENNReal.ofReal (Real.exp (ξ * g v + |ξ| * M)) *
        (lfppContMetric ξ f hf).aroundDist U E F := by
  have hξosc (z : ℂ) (hz : z ∈ U) :
      ξ * (g z - g v) ≤ |ξ| * M ∧
      ξ * (g v - g z) ≤ |ξ| * M := by
    have hh := mul_le_mul_of_nonneg_left (hosc z hz) (abs_nonneg ξ)
    have hleft : ξ * (g z - g v) ≤ |ξ * (g z - g v)| :=
      le_abs_self _
    have hright : ξ * (g v - g z) ≤ |ξ * (g v - g z)| :=
      le_abs_self _
    constructor
    · calc
        _ ≤ |ξ * (g z - g v)| := hleft
        _ = |ξ| * |g z - g v| := abs_mul _ _
        _ ≤ _ := hh
    · calc
        _ ≤ |ξ * (g v - g z)| := hright
        _ = |ξ| * |g z - g v| := by rw [abs_mul, abs_sub_comm]
        _ ≤ _ := hh
  have hlow (z : ℂ) (hz : z ∈ U) :
      ξ * f z ≤ ξ * (g z + f z) +
        (-ξ * g v + |ξ| * M) := by
    nlinarith [(hξosc z hz).2]
  have hupp (z : ℂ) (hz : z ∈ U) :
      ξ * (g z + f z) ≤ ξ * f z +
        (ξ * g v + |ξ| * M) := by
    nlinarith [(hξosc z hz).1]
  exact ⟨T20D.crossLenIn_le_of_le_add hlow,
    T20D.crossLenIn_le_of_le_add hupp,
    j1_aroundDist_le_of_field_bound ξ hf (hg.add hf) U E F hlow,
    j1_aroundDist_le_of_field_bound ξ (hg.add hf) hf U E F hupp⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
