/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.GlobalDyadicSupport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicRightLimits
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov

/-! Compatibility of the existing global dyadic meshes with the finite
power-of-two horizons used by the crossing estimates. -/

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal
open ReflectedWalk.Theorem16

namespace ReflectedGMS

/-- The union of the existing dyadic meshes. -/
def globalDyadicSupport : Set ℝ≥0 := ⋃ n : ℕ, dyadicMesh n

theorem mem_globalDyadicSupport_iff (s : ℝ≥0) :
    s ∈ globalDyadicSupport ↔ ∃ n k : ℕ, s = dyadicTime 1 n k := by
  simp only [globalDyadicSupport, mem_iUnion, dyadicMesh, mem_range,
    dyadicTime, mul_one, eq_comm]

/-- A power-of-two horizon gives exactly the global mesh below that horizon. -/
theorem dyadicSupport_pow_two (N : ℕ) :
    dyadicSupport (2 ^ N) = globalDyadicSupport ∩ Iio (2 ^ N) := by
  ext s
  constructor
  · rintro ⟨n, k, hk, rfl⟩
    constructor
    · apply (mem_globalDyadicSupport_iff _).2
      refine ⟨n, k * 2 ^ N, ?_⟩
      simp only [dyadicTime, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one]
    · have hlt := dyadicTime_strictMono (2 ^ N) (by positivity) n hk
      simpa [dyadicTime] using hlt
  · rintro ⟨hs, hlt⟩
    obtain ⟨n, k, rfl⟩ := (mem_globalDyadicSupport_iff s).1 hs
    have htime : dyadicTime (2 ^ N) (n + N) k = dyadicTime 1 n k := by
      simp only [dyadicTime, pow_add, mul_one]
      field_simp
    refine ⟨n + N, k, ?_, htime.symm⟩
    apply (dyadicTime_strictMono (2 ^ N) (by positivity) (n + N)).lt_iff_lt.mp
    rw [htime]
    simpa [dyadicTime] using hlt

/-- Near a point below the horizon, arbitrary restrictions of the global
support and the finite support have identical neighborhood filters. -/
theorem nhdsWithin_globalDyadicSupport_eq {t : ℝ≥0} (N : ℕ)
    (ht : t < 2 ^ N) (A : Set ℝ≥0) :
    𝓝[globalDyadicSupport ∩ A] t = 𝓝[dyadicSupport (2 ^ N) ∩ A] t := by
  rw [dyadicSupport_pow_two, inter_right_comm]
  exact (nhdsWithin_inter_of_mem'
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht))).symm

theorem exists_pow_two_horizon (t : ℝ≥0) : ∃ N : ℕ, t < 2 ^ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  refine ⟨N, hN.trans_le ?_⟩
  exact_mod_cast (show N < 2 ^ N from Nat.lt_two_pow_self).le

end ReflectedGMS
