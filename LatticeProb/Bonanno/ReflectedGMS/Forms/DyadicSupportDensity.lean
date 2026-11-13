/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicSupportDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicRightLimits
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal
open ReflectedWalk.Theorem16

namespace ReflectedGMS

/-- Every nonempty interval below a positive horizon contains a point of the
finite-horizon dyadic support. -/
theorem exists_dyadicSupport_between (T : ℝ≥0) (hT : 0 < T)
    {a b : ℝ≥0} (hab : a < b) (hbT : b ≤ T) :
    ∃ x ∈ dyadicSupport T, a < x ∧ x < b := by
  let a' := a / T
  let b' := b / T
  let c := (a' + b') / 2
  have ha'b' : a' < b' := by
    exact (div_lt_div_iff_of_pos_right hT).2 hab
  have hac : a' < c := left_lt_add_div_two.2 ha'b'
  have hcb : c < b' := add_div_two_lt_right.2 ha'b'
  have hε : 0 < b' - c := tsub_pos_iff_lt.2 hcb
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    (by norm_num : (2⁻¹ : ℝ≥0) < 1)
  let q := dyadicCeil n c
  have hcq : c ≤ q := le_dyadicCeil n c
  have hqb' : q < b' := by
    calc
      q < c + (2 ^ n)⁻¹ := dyadicCeil_lt n c
      _ = c + (2⁻¹ : ℝ≥0) ^ n := by rw [← inv_pow]
      _ < c + (b' - c) := by simpa [add_comm] using add_lt_add_left hn c
      _ = b' := add_tsub_cancel_of_le hcb.le
  obtain ⟨k, hkq⟩ := dyadicCeil_mem n c
  let x := T * q
  have hx_time : x = dyadicTime T n k := by
    dsimp [x]
    change T * dyadicCeil n c = dyadicTime T n k
    rw [← hkq]
    simp only [dyadicTime]
    ring
  have hax : a < x := by
    dsimp [x]
    have hx : a' * T < q * T := mul_lt_mul_of_pos_right (hac.trans_le hcq) hT
    simpa [a', div_mul_cancel₀ a hT.ne', mul_comm] using hx
  have hxb : x < b := by
    dsimp [x]
    have hx : q * T < b' * T := mul_lt_mul_of_pos_right hqb' hT
    simpa [b', div_mul_cancel₀ b hT.ne', mul_comm] using hx
  have hk : k < 2 ^ n := by
    apply (dyadicTime_strictMono T hT n).lt_iff_lt.mp
    rw [← hx_time]
    simpa [dyadicTime] using hxb.trans_le hbT
  exact ⟨x, ⟨n, k, hk, hx_time⟩, hax, hxb⟩

/-- Dyadic times strictly to the right accumulate at every point before a
positive horizon. -/
theorem dyadicSupport_nhdsWithin_Ioi_neBot (T : ℝ≥0) (hT : 0 < T)
    {t : ℝ≥0} (htT : t < T) :
    NeBot (nhdsWithin t (dyadicSupport T ∩ Ioi t)) := by
  rw [nhdsWithin_neBot]
  intro U hU
  obtain ⟨r, htr, hrU⟩ := exists_Ico_subset_of_mem_nhds hU ⟨T, htT⟩
  have htmin : t < min r T := lt_min htr htT
  obtain ⟨x, hxS, htx, hxupper⟩ :=
    exists_dyadicSupport_between T hT htmin (min_le_right _ _)
  exact ⟨x, hrU ⟨htx.le, hxupper.trans_le (min_le_left _ _)⟩, hxS, htx⟩

/-- Dyadic times strictly to the left accumulate at every positive point not
past a positive horizon. -/
theorem dyadicSupport_nhdsWithin_Iio_neBot (T : ℝ≥0) (hT : 0 < T)
    {t : ℝ≥0} (ht0 : 0 < t) (htT : t ≤ T) :
    NeBot (nhdsWithin t (dyadicSupport T ∩ Iio t)) := by
  rw [nhdsWithin_neBot]
  intro U hU
  obtain ⟨l, hlt, hlU⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, ht0⟩
  obtain ⟨x, hxS, hlx, hxt⟩ := exists_dyadicSupport_between T hT hlt htT
  exact ⟨x, hlU ⟨hlx, hxt.le⟩, hxS, hxt⟩

end ReflectedGMS
