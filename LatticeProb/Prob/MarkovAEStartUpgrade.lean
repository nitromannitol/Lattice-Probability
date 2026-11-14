import Mathlib
import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# From almost every starting point to every starting point

Let `K : E → Prob C(ℝ≥0, E)` be a continuous family of path laws with the Markov property at every
positive time, and let `ν` be a reference measure on `E` such that, for each `z` and `t > 0`, the law
of `x t` under `K z` is absolutely continuous with respect to `ν` (for Brownian motion in the plane
and `ν` Lebesgue measure this is the Gaussian density of the time-`t` marginal).

Two additive functionals `A`, `B` (families of measurable functions of the path, a.s. continuous in
the time, vanishing at time `0`, and a.s. additive in the sense `A (t + s) = A t + A s ∘ (shift by t)`
under every `K z`) which agree `K y`-almost surely for `ν`-almost every starting point `y` agree
`K z`-almost surely for every starting point `z`.

* `LatticeProb.measure_pathShift_preimage_real_eq_integral`: the Markov property in set form, for a
  fixed time, `K z {x | x (t + ·) ∈ S} = ∫ K (x t) S d(K z)(x)`.
* `LatticeProb.ae_pathShift_mem_of_ae_start`: if `K y`-almost every path lies in `S` for `ν`-almost
  every `y`, then `K z`-almost every shifted path `x (t + ·)` lies in `S`, for every `z`.
* `LatticeProb.ae_forall_eq_of_ae_start_of_additive`: the upgrade of the equality of two additive
  functionals from `ν`-almost every starting point to every starting point.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **The Markov property at a fixed time in set form.**  The probability that the shifted path
`x (t + ·)` lies in a measurable set `S` is the integral of the probability `K (x t) S`. -/
theorem measure_pathShift_preimage_real_eq_integral {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) {z : E} {t : ℝ≥0} (h : MarkovAt K z t) {S : Set C(ℝ≥0, E)}
    (hS : MeasurableSet S) :
    (K z : Measure C(ℝ≥0, E)).real {x | pathShift x t ∈ S} =
      ∫ x, (K (x t) : Measure C(ℝ≥0, E)).real S ∂(K z : Measure C(ℝ≥0, E)) := by
  have hg : Measurable fun p : C(ℝ≥0, E) × C(ℝ≥0, E) => S.indicator (fun _ => (1 : ℝ)) p.2 :=
    (measurable_const.indicator hS).comp measurable_snd
  have hC : ∀ p : C(ℝ≥0, E) × C(ℝ≥0, E), ‖S.indicator (fun _ => (1 : ℝ)) p.2‖ ≤ 1 := by
    intro p
    by_cases hp : p.2 ∈ S <;> simp [hp]
  have hmain := h.integral_eq_of_measurable hK hg hC
  have hsh : Measurable fun x : C(ℝ≥0, E) => pathShift x t :=
    (continuous_pathShift_uncurry.comp (continuous_id.prodMk continuous_const)).measurable
  have hpre : MeasurableSet {x : C(ℝ≥0, E) | pathShift x t ∈ S} := hsh hS
  have hL : ∫ x, S.indicator (fun _ => (1 : ℝ)) (pathShift x t) ∂(K z : Measure C(ℝ≥0, E)) =
      (K z : Measure C(ℝ≥0, E)).real {x | pathShift x t ∈ S} := by
    have : (fun x : C(ℝ≥0, E) => S.indicator (fun _ => (1 : ℝ)) (pathShift x t)) =
        {x : C(ℝ≥0, E) | pathShift x t ∈ S}.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : pathShift x t ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : C(ℝ≥0, E) | pathShift x t ∈ S} from hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show x ∉ {x : C(ℝ≥0, E) | pathShift x t ∈ S} from hx)]
    rw [this, integral_indicator_const _ hpre, smul_eq_mul, mul_one]
  have hR : ∀ x : C(ℝ≥0, E), ∫ w, S.indicator (fun _ => (1 : ℝ)) w
      ∂(K (x t) : Measure C(ℝ≥0, E)) = (K (x t) : Measure C(ℝ≥0, E)).real S := fun x => by
    rw [integral_indicator_const _ hS, smul_eq_mul, mul_one]
  rw [← hL]
  simpa [hR] using hmain

/-- **Almost every starting point controls every starting point after a positive time.**  If, for
`ν`-almost every `y`, `K y`-almost every path lies in the measurable set `S`, and the time-`t`
marginal of `K z` is absolutely continuous with respect to `ν`, then `K z`-almost every shifted path
`x (t + ·)` lies in `S`. -/
theorem ae_pathShift_mem_of_ae_start {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {ν : Measure E} {z : E} {t : ℝ≥0} (h : MarkovAt K z t)
    (hac : (K z : Measure C(ℝ≥0, E)).map (fun x => x t) ≪ ν) {S : Set C(ℝ≥0, E)}
    (hS : MeasurableSet S)
    (hν : ∀ᵐ y ∂ν, ∀ᵐ x ∂(K y : Measure C(ℝ≥0, E)), x ∈ S) :
    ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), pathShift x t ∈ S := by
  have hnull : ∀ᵐ y ∂ν, (K y : Measure C(ℝ≥0, E)).real Sᶜ = 0 := by
    filter_upwards [hν] with y hy
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hy)
  have hmeas : AEMeasurable (fun x : C(ℝ≥0, E) => x t) (K z : Measure C(ℝ≥0, E)) :=
    (continuous_eval_const t).aemeasurable
  have h1 : ∀ᵐ y ∂(K z : Measure C(ℝ≥0, E)).map (fun x => x t),
      (K y : Measure C(ℝ≥0, E)).real Sᶜ = 0 := hac.ae_le hnull
  have h2 : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), (K (x t) : Measure C(ℝ≥0, E)).real Sᶜ = 0 :=
    ae_of_ae_map hmeas h1
  have h3 := measure_pathShift_preimage_real_eq_integral hK h hS.compl
  rw [integral_eq_zero_of_ae h2, measureReal_eq_zero_iff (measure_ne_top _ _)] at h3
  exact ae_iff.2 h3

/-- **Upgrade from almost every starting point to every starting point for additive functionals.**
Let `K` be a continuous family of path laws with the Markov property at every positive time, whose
time-`t` marginals (`t > 0`) are absolutely continuous with respect to `ν`.  Let `A`, `B` be families of
measurable functions of the path, almost surely continuous in time, vanishing at time `0` and almost
surely additive under every `K z`.  If `A t x = B t x` for all `t`, for `K y`-almost every `x`, for
`ν`-almost every `y`, then the same holds for every `y`. -/
theorem ae_forall_eq_of_ae_start_of_additive {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) {ν : Measure E}
    (hM : ∀ z t, 0 < t → MarkovAt K z t)
    (hac : ∀ z t, 0 < t → (K z : Measure C(ℝ≥0, E)).map (fun x => x t) ≪ ν)
    {A B : ℝ≥0 → C(ℝ≥0, E) → ℝ≥0} (hA : ∀ t, Measurable (A t)) (hB : ∀ t, Measurable (B t))
    (hAc : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), Continuous (fun t => A t x) ∧ A 0 x = 0)
    (hBc : ∀ z, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), Continuous (fun t => B t x) ∧ B 0 x = 0)
    (hAadd : ∀ z s t, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      A (t + s) x = A t x + A s (pathShift x t))
    (hBadd : ∀ z s t, ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      B (t + s) x = B t x + B s (pathShift x t))
    (hae : ∀ᵐ y ∂ν, ∀ᵐ x ∂(K y : Measure C(ℝ≥0, E)), ∀ t, A t x = B t x) (z : E) :
    ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ∀ t, A t x = B t x := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp [hε]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsh : ∀ (n : ℕ) (t : ℝ≥0), ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)),
      A t (pathShift x (ε n)) = B t (pathShift x (ε n)) := fun n t =>
    ae_pathShift_mem_of_ae_start hK (hM z (ε n) (hεpos n)) (hac z (ε n) (hεpos n))
      (S := {x | A t x = B t x}) (measurableSet_eq_fun (hA t) (hB t))
      (hae.mono fun y hy => hy.mono fun x hx => hx t)
  have hcount : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ∀ n : ℕ, ∀ t ∈ D,
      A (ε n + (t - ε n)) x = A (ε n) x + A (t - ε n) (pathShift x (ε n)) ∧
      B (ε n + (t - ε n)) x = B (ε n) x + B (t - ε n) (pathShift x (ε n)) ∧
      A (t - ε n) (pathShift x (ε n)) = B (t - ε n) (pathShift x (ε n)) := by
    rw [ae_all_iff]
    intro n
    rw [ae_ball_iff hDc]
    intro t _
    filter_upwards [hAadd z (t - ε n) (ε n), hBadd z (t - ε n) (ε n), hsh n (t - ε n)] with
      x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hcount, hAc z, hBc z] with x hx hA' hB'
  have hD : ∀ t ∈ D, A t x = B t x := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0; rw [hA'.2, hB'.2]
    · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
      have hev : ∀ᶠ n in atTop, ε n ≤ t :=
        (hεlim.eventually (Iio_mem_nhds htpos)).mono fun n hn => le_of_lt hn
      have key : ∀ᶠ n in atTop, A t x + B (ε n) x = B t x + A (ε n) x := by
        filter_upwards [hev] with n hn
        obtain ⟨e1, e2, e3⟩ := hx n t ht
        rw [add_tsub_cancel_of_le hn] at e1 e2
        rw [e1, e2, e3]
        ring
      have l1 : Tendsto (fun n => A t x + B (ε n) x) atTop (𝓝 (A t x + B 0 x)) :=
        tendsto_const_nhds.add ((hB'.1.tendsto 0).comp hεlim)
      have l2 : Tendsto (fun n => B t x + A (ε n) x) atTop (𝓝 (B t x + A 0 x)) :=
        tendsto_const_nhds.add ((hA'.1.tendsto 0).comp hεlim)
      have := tendsto_nhds_unique (l1.congr' key) l2
      simpa [hA'.2, hB'.2] using this
  intro t
  exact congrFun (hA'.1.ext_on hDd hB'.1 hD) t

end LatticeProb
