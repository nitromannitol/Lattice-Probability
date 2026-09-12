/-
The exit time of Brownian motion on `ℝ ^ d` from a ball.

`LatticeProb/Prob/BrownianMax.lean` proves the Gaussian maximal estimate for a
real Brownian motion whose values are measurable.  Here it is transported to a
Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)`, presented as in
`LatticeProb/Gauss/BrownianCont.lean` by its three properties: it starts at `x`,
each coordinate centred and scaled by `√d` is a real Brownian motion, and the
coordinates are independent.  Only the first two are used: a union bound over
the coordinates needs no independence.

Two steps.  A process with only almost surely continuous paths and no
measurability is replaced by a measurable version which agrees with it at every
time almost surely; this is where `exists_isBrownianReal_modification` and the
indistinguishability of two continuous modifications are used.  Then a vector of
norm larger than `A` has a coordinate with `A < √d |v i|`, which is exactly the
value of the rescaled coordinate process, so the `d` one-dimensional estimates
add up.

The conclusion is the Gaussian bound `C exp (- c A ^ 2 / T)` on the probability
that the motion leaves the ball of radius `A` about its starting point before
time `T`, with `C = 4 d + 4` and `c = 1 / 32` depending only on the dimension.
-/
import Mathlib
import LatticeProb.Prob.BrownianMax
import LatticeProb.Gauss.BrownianCont

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The one-dimensional estimate without a measurability hypothesis -/

/-- A Brownian motion has a measurable version which agrees with it at every time,
almost surely. -/
theorem exists_measurable_indistinguishable (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ IsBrownianReal C P ∧
      ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω := by
  have hB'm : ∀ t, Measurable ((hB.aemeasurable t).mk (B t)) :=
    fun t => (hB.aemeasurable t).measurable_mk
  have hB'eq : ∀ t, B t =ᵐ[P] (hB.aemeasurable t).mk (B t) :=
    fun t => (hB.aemeasurable t).ae_eq_mk
  have hB'pre : IsPreBrownianReal (fun t => (hB.aemeasurable t).mk (B t)) P :=
    hB.toIsPreBrownianReal.congr hB'eq
  obtain ⟨C, hCm, hmod, hC⟩ := exists_isBrownianReal_modification hB'pre hB'm
  refine ⟨C, hCm, hC, ?_⟩
  have hBC : ∀ t, B t =ᵐ[P] C t := fun t => (hB'eq t).trans (hmod t)
  exact ae_forall_eq_of_modification hBC hB.cont hC.cont

/-- **The Gaussian maximal estimate for a real Brownian motion.**  The chance that the path
ever moves by `a` from its starting value before time `T` is at most
`4 exp (- a ^ 2 / (32 T))`.  No measurability is assumed: the estimate is proved for a
measurable version and transported back. -/
theorem measure_exists_abs_sub_ge_le' [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω - B 0 ω|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (32 * (T : ℝ))))) := by
  obtain ⟨C, hCm, hC, hind⟩ := exists_measurable_indistinguishable hB
  have hsub : {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω - B 0 ω|}
      ≤ᵐ[P] {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |C s ω - C 0 ω|} := by
    filter_upwards [hind] with ω hω hmem
    obtain ⟨s, hs, hsa⟩ := hmem
    refine ⟨s, hs, ?_⟩
    rw [← hω s, ← hω 0]
    exact hsa
  exact le_trans (measure_mono_ae hsub) (measure_exists_abs_sub_ge_le hC hCm T ha)


/-! ### Brownian motion on `ℝ ^ d` -/

/-- A vector of `EuclideanSpace ℝ (Fin d)` all of whose coordinates are at most `c` in
absolute value has norm at most `√d * c`. -/
theorem norm_le_sqrt_mul_of_forall_abs_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, |x i| ≤ c) : ‖x‖ ≤ Real.sqrt d * c := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (d : ℝ) * c ^ 2 := by
    have hi : ∀ i : Fin d, ‖x i‖ ^ 2 ≤ c ^ 2 := by
      intro i
      have h1 : ‖x i‖ ≤ c := by
        rw [Real.norm_eq_abs]
        exact h i
      nlinarith [abs_nonneg (x i), norm_nonneg (x i)]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
      _ = (d : ℝ) * c ^ 2 := by simp [Finset.sum_const]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * c := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

/-- A vector of norm larger than `A` has a coordinate with `A < √d |v i|`, which is the size
of the corresponding coordinate of a Brownian motion with generator `Δ / (2 d)`. -/
theorem exists_coord_lt_sqrt_mul_abs {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) {A : ℝ}
    (hA : 0 < A) (h : A < ‖v‖) : ∃ i, A < Real.sqrt d * |v i| := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hv : v = 0 := Subsingleton.elim v 0
    rw [hv, norm_zero] at h
    linarith
  · have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hle : ∀ i, |v i| ≤ A / Real.sqrt d := by
      intro i
      rw [le_div_iff₀ hsq, mul_comm]
      exact hcon i
    have hnorm := norm_le_sqrt_mul_of_forall_abs_le v (by positivity) hle
    rw [mul_div_cancel₀ A (ne_of_gt hsq)] at hnorm
    linarith

/-- **Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)` started at `x`**: it starts at
`x`, each coordinate centred and scaled by `√d` is a real Brownian motion, and the
coordinate processes are independent.  These are the three properties produced by
`LatticeProb.exists_isBrownian`. -/
structure IsBrownianSpace {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) : Prop where
  /-- The process starts at `x`. -/
  start : ∀ᵐ ω ∂P, B 0 ω = x
  /-- Each coordinate, centred and scaled by `√d`, is a real Brownian motion. -/
  coord : ∀ i : Fin d, IsBrownianReal (fun t ω => Real.sqrt d * (B t ω i - x i)) P
  /-- The coordinate processes are independent. -/
  indep : iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => B t ω i) P

/-- **The paths of a Brownian motion on `ℝ ^ d` are almost surely continuous.**  Each
coordinate is, and continuity into `EuclideanSpace` is continuity of the coordinates. -/
theorem IsBrownianSpace.cont {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P) :
    ∀ᵐ ω ∂P, Continuous fun t => B t ω := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · filter_upwards with ω
    rw [continuous_induced_rng]
    exact continuous_pi (fun i => i.elim0)
  · have hsq : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hall : ∀ᵐ ω ∂P, ∀ i : Fin d, Continuous fun t => Real.sqrt d * (B t ω i - x i) := by
      rw [ae_all_iff]
      exact fun i => (hB.coord i).cont
    filter_upwards [hall] with ω hω
    rw [continuous_induced_rng]
    refine continuous_pi (fun i => ?_)
    have h1 : Continuous fun t => Real.sqrt d * (B t ω i - x i) := hω i
    have h2 : (fun t => (B t ω) i)
        = fun t => (Real.sqrt d)⁻¹ * (Real.sqrt d * (B t ω i - x i)) + x i := by
      funext t
      field_simp
      ring
    show Continuous fun t => (B t ω) i
    rw [h2]
    exact (h1.const_mul _).add continuous_const

/-- A Brownian motion is defined on a probability space: the independence of the coordinate
processes already forces the total mass to be one. -/
theorem IsBrownianSpace.isProbabilityMeasure {d : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P) :
    IsProbabilityMeasure P :=
  hB.indep.isProbabilityMeasure

/-- **A Brownian motion on `ℝ ^ d` started at `x` exists**, so the hypothesis of the exit
estimate is not vacuous.  This is `LatticeProb.exists_isBrownian` read as the predicate. -/
theorem exists_isBrownianSpace (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), @IsBrownianSpace Ω mΩ d x B P := by
  obtain ⟨Ω, mΩ, P, B, h1, h2, h3⟩ := exists_isBrownian d x
  exact ⟨Ω, mΩ, P, B, ⟨h1, h2, h3⟩⟩

/-- **The Brownian exit-time tail.**  For Brownian motion on `ℝ ^ d` with generator
`Δ / (2 d)` started at `u`, the probability that it leaves the Euclidean ball of radius `A`
about `u` before time `T` is at most `C exp (- c A ^ 2 / T)`, with `C` and `c` depending only
on the dimension.  The proof takes `C = 4 d + 4` and `c = 1 / 32`: a vector of norm larger
than `A` has a coordinate with `A < √d |v i|`, and each of the `d` rescaled coordinates is a
real Brownian motion, to which the one-dimensional maximal estimate applies.  The radius `A`
is an arbitrary positive number: nothing in the proof uses `A ≥ 1`. -/
theorem brownian_exit_tail_pos (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          IsBrownianSpace d u B P → ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T →
            P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}
              ≤ ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T))) := by
  refine ⟨4 * d + 4, 1 / 32, by positivity, by norm_num, ?_⟩
  intro u Ω _ P hP B hB A hA T hT
  have hA0 : (0 : ℝ) < A := hA
  have hTTc : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
  have hexp : -(1 / 32 * A ^ 2 / T) = -(A ^ 2 / (32 * T)) := by ring
  rw [hexp]
  have hsub : {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}
      ≤ᵐ[P] ⋃ i : Fin d, {ω | ∃ s : ℝ≥0, s ≤ T.toNNReal ∧
        A ≤ |Real.sqrt d * (B s ω i - u i) - Real.sqrt d * (B 0 ω i - u i)|} := by
    filter_upwards [hB.start] with ω hstart hmem
    obtain ⟨s, hs, hsa⟩ := hmem
    obtain ⟨i, hi⟩ := exists_coord_lt_sqrt_mul_abs (B s ω - u) hA0 hsa
    refine Set.mem_iUnion.2 ⟨i, s, (Real.le_toNNReal_iff_coe_le hT.le).2 hs.le, ?_⟩
    have h0 : Real.sqrt d * (B 0 ω i - u i) = 0 := by
      rw [hstart]
      simp
    rw [h0, sub_zero, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hcoord : (B s ω - u) i = B s ω i - u i := by simp
    rw [hcoord] at hi
    exact hi.le
  refine le_trans (measure_mono_ae hsub) ?_
  have hterm : ∀ i : Fin d, P {ω | ∃ s : ℝ≥0, s ≤ T.toNNReal ∧
      A ≤ |Real.sqrt d * (B s ω i - u i) - Real.sqrt d * (B 0 ω i - u i)|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(A ^ 2 / (32 * T)))) := by
    intro i
    have h := measure_exists_abs_sub_ge_le' (hB.coord i) T.toNNReal hA0
    rwa [hTTc] at h
  calc P (⋃ i : Fin d, {ω | ∃ s : ℝ≥0, s ≤ T.toNNReal ∧
          A ≤ |Real.sqrt d * (B s ω i - u i) - Real.sqrt d * (B 0 ω i - u i)|})
      ≤ ∑' i : Fin d, P {ω | ∃ s : ℝ≥0, s ≤ T.toNNReal ∧
          A ≤ |Real.sqrt d * (B s ω i - u i) - Real.sqrt d * (B 0 ω i - u i)|} :=
        measure_iUnion_le _
    _ = ∑ i : Fin d, P {ω | ∃ s : ℝ≥0, s ≤ T.toNNReal ∧
          A ≤ |Real.sqrt d * (B s ω i - u i) - Real.sqrt d * (B 0 ω i - u i)|} :=
        tsum_fintype _
    _ ≤ ∑ _i : Fin d, 4 * ENNReal.ofReal (Real.exp (-(A ^ 2 / (32 * T)))) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (d : ℝ≥0∞) * (4 * ENNReal.ofReal (Real.exp (-(A ^ 2 / (32 * T))))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((4 * (d : ℝ) + 4) * Real.exp (-(A ^ 2 / (32 * T)))) := by
        rw [ENNReal.ofReal_mul (by positivity), ← mul_assoc]
        refine mul_le_mul_left ?_ _
        have h1 : (d : ℝ≥0∞) * 4 = ENNReal.ofReal (4 * (d : ℝ)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp [ENNReal.ofReal_natCast, mul_comm]
        rw [h1]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The Brownian exit-time tail**, in the form with `1 ≤ A`.  This is
`LatticeProb.brownian_exit_tail_pos` restricted to radii at least one. -/
theorem brownian_exit_tail (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          IsBrownianSpace d u B P → ∀ A : ℝ, 1 ≤ A → ∀ T : ℝ, 0 < T →
            P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A < ‖B s ω - u‖}
              ≤ ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T))) := by
  obtain ⟨C, c, hC, hc, h⟩ := brownian_exit_tail_pos d
  refine ⟨C, c, hC, hc, ?_⟩
  intro u Ω _ P hP B hB A hA T hT
  exact h u Ω P hP B hB A (lt_of_lt_of_le one_pos hA) T hT

/-! ### The closed ball -/

/-- A bound which holds at every smaller positive radius holds at the radius itself, because
the Gaussian bound is continuous in the radius. -/
theorem le_ofReal_exp_of_forall_lt {C c T A : ℝ} (hA : 0 < A) {x : ℝ≥0∞}
    (h : ∀ A' : ℝ, 0 < A' → A' < A →
      x ≤ ENNReal.ofReal (C * Real.exp (-(c * A' ^ 2 / T)))) :
    x ≤ ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T))) := by
  have hc : Continuous fun A' : ℝ => ENNReal.ofReal (C * Real.exp (-(c * A' ^ 2 / T))) :=
    ENNReal.continuous_ofReal.comp (by continuity)
  have hlim : Filter.Tendsto (fun A' : ℝ => ENNReal.ofReal (C * Real.exp (-(c * A' ^ 2 / T))))
      (nhdsWithin A (Set.Iio A)) (nhds (ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T))))) :=
    (hc.tendsto A).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  have hpos : ∀ᶠ A' in nhdsWithin A (Set.Iio A), 0 < A' :=
    (eventually_gt_nhds hA).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with A' h1 h2
  exact h A' h1 h2

/-- **The Brownian exit-time tail for the CLOSED ball.**  The probability that the motion
reaches distance `A` from its starting point before time `T` obeys the same bound, with the same
constants, because the open-ball bound holds at every smaller radius and the bound is continuous
in the radius. -/
theorem brownian_exit_tail_closed (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          IsBrownianSpace d u B P → ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T →
            P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
              ≤ ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T))) := by
  obtain ⟨C, c, hC, hc, h⟩ := brownian_exit_tail_pos d
  refine ⟨C, c, hC, hc, ?_⟩
  intro u Ω _ P hP B hB A hA T hT
  refine le_ofReal_exp_of_forall_lt hA ?_
  intro A' hA' hA'A
  refine le_trans (measure_mono ?_) (h u Ω P hP B hB A' hA' T hT)
  rintro ω ⟨s, hs, hsA⟩
  exact ⟨s, hs, lt_of_lt_of_le hA'A hsA⟩

end LatticeProb

end
