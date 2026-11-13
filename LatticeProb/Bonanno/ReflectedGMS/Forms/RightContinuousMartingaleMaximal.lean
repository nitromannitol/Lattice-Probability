/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.RightContinuousMartingaleMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CountableMartingaleMaximal
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity
import Mathlib.Topology.Order.Cadlag

/-! The countable Doob bound controls every time of an almost surely
right-continuous martingale, using the existing globally dense dyadic support. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS

theorem martingale_sq_rightContinuous_maximal_ineq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P)
    (hRC : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ M t ω))
    (T ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t ≤ T, (ε : ℝ) < (M t ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
  let S := insert T (globalDyadicSupport ∩ Iic T)
  have hSc : S.Countable :=
    (globalDyadicSupport_countable.mono inter_subset_left).insert T
  obtain ⟨τ, hτ⟩ := hSc.exists_eq_range (by exact ⟨T, mem_insert T _⟩)
  have hτT (n : ℕ) : τ n ≤ T := by
    have hn : τ n ∈ S := by rw [hτ]; exact mem_range_self n
    rcases hn with hn | hn
    · exact hn.le
    · exact hn.2
  have hmax := martingale_sq_countable_maximal_ineq hM h2 τ T hτT ε
  refine le_trans ?_ hmax
  apply mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  apply measure_mono_ae
  filter_upwards [hRC] with ω hω
  rintro ⟨t, ht, hε⟩
  suffices ∃ r ∈ S, (ε : ℝ) ≤ (M r ω) ^ 2 by
    obtain ⟨r, hr, hεr⟩ := this
    rw [hτ] at hr
    obtain ⟨n, rfl⟩ := hr
    exact ⟨n, hεr⟩
  rcases eq_or_lt_of_le ht with hteq | ht
  · exact ⟨T, mem_insert T _, by simpa only [hteq] using hε.le⟩
  · letI := globalDyadicSupport_nhdsWithin_Ioi_neBot t
    have hlim : Tendsto (fun r ↦ (M r ω) ^ 2)
        (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 ((M t ω) ^ 2)) :=
      ((hω t).mono inter_subset_right).pow 2
    have hlev : ∀ᶠ r in 𝓝[globalDyadicSupport ∩ Ioi t] t,
        (ε : ℝ) < (M r ω) ^ 2 := hlim (Ioi_mem_nhds hε)
    have htime : ∀ᶠ r in 𝓝[globalDyadicSupport ∩ Ioi t] t, r < T :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
    have hsupp : ∀ᶠ r in 𝓝[globalDyadicSupport ∩ Ioi t] t,
        r ∈ globalDyadicSupport ∩ Ioi t := self_mem_nhdsWithin
    obtain ⟨r, hrS, hrε, hrT⟩ := (hsupp.and (hlev.and htime)).exists
    exact ⟨r, Or.inr ⟨hrS.1, hrT.le⟩, hrε.le⟩

end ReflectedGMS
