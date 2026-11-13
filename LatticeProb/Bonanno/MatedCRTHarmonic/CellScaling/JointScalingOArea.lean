/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.JointScalingOArea at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample

/-!
#  a measurable area functional of curve segments

To transport the
joint law of `(h, η)` we need the area parametrization `η = Par(μ_h, η_L)` of the space-filling
curve as a **measurable** function of the pair (field, Lebesgue-parametrized curve). Its basic
ingredient is the area of a curve segment `c([min 0 q, max 0 q])` as a measurable function of the
field `f` and the curve `c`.

`CellScaling.lqgArea γ f` is a `Classical.choose` (junk `0` without a vague limit), so we use instead
the measurable functional

  `areaSeg γ f c q = ⨅ₙ limsup_k ofReal (∫ bumpₙ d(lqgAreaApprox γ f k))`,

where `bumpₙ(z) = max 0 (1 − (n + 1) d(z, c([min 0 q, max 0 q])))` are continuous, compactly
supported and decrease to the indicator of the (compact) segment. It is jointly measurable in
`(f, c)` (`measurable_areaSeg`: the approximations have the explicit density
`2^{-kγ²/2} e^{γ f_{2^{-k}}(z)}`, jointly measurable by LQGMetric's `measurable_circleAvg`), and it
equals `m(c([min 0 q, max 0 q]))` whenever `m` is a vague limit of the approximations
(`areaSeg_eq`; monotone convergence for the decreasing bumps). SLE-free and deterministic.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

open LQGMetric

/-! ### Distance to a curve segment -/

/-- The distance from `z` to the curve segment `c([min 0 q, max 0 q])`. -/
def segDist (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) : ℝ :=
  sInf ((fun s => ‖z - c s‖) '' uIcc 0 q)

theorem continuous_segDist (q : ℝ) :
    Continuous fun p : C(ℝ, ℂ) × ℂ => segDist p.1 q p.2 := by
  have hev : Continuous fun x : (C(ℝ, ℂ) × ℂ) × ℝ => x.1.1 x.2 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hf : Continuous fun x : (C(ℝ, ℂ) × ℂ) × ℝ => ‖x.1.2 - x.1.1 x.2‖ :=
    ((continuous_snd.comp continuous_fst).sub hev).norm
  exact isCompact_uIcc.continuous_sInf (f := fun (p : C(ℝ, ℂ) × ℂ) (s : ℝ) => ‖p.2 - p.1 s‖) hf

theorem segDist_nonneg (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) : 0 ≤ segDist c q z := by
  apply Real.sInf_nonneg
  rintro _ ⟨s, -, rfl⟩
  exact norm_nonneg _

/-- The infimum defining `segDist` is attained. -/
theorem exists_segDist_eq (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) :
    ∃ s ∈ uIcc 0 q, ‖z - c s‖ = segDist c q z := by
  have hK : IsCompact ((fun s => ‖z - c s‖) '' uIcc 0 q) :=
    isCompact_uIcc.image (continuous_const.sub c.continuous).norm
  have hne : ((fun s => ‖z - c s‖) '' uIcc 0 q).Nonempty := nonempty_uIcc.image _
  exact hK.sInf_mem hne

theorem segDist_le (c : C(ℝ, ℂ)) {q s : ℝ} (hs : s ∈ uIcc 0 q) (z : ℂ) :
    segDist c q z ≤ ‖z - c s‖ := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨u, -, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨s, hs, rfl⟩

theorem segDist_eq_zero_iff (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) :
    segDist c q z = 0 ↔ z ∈ c '' uIcc 0 q := by
  constructor
  · intro h
    obtain ⟨s, hs, hs'⟩ := exists_segDist_eq c q z
    rw [h, norm_eq_zero, sub_eq_zero] at hs'
    exact ⟨s, hs, hs'.symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine le_antisymm ?_ (segDist_nonneg c q _)
    simpa using segDist_le c hs (c s)

theorem isCompact_seg (c : C(ℝ, ℂ)) (q : ℝ) : IsCompact (c '' uIcc 0 q) :=
  isCompact_uIcc.image c.continuous

/-! ### The bumps -/

/-- The continuous bump `max 0 (1 − (n + 1) d(z, c([min 0 q, max 0 q])))`. -/
def segBump (c : C(ℝ, ℂ)) (q : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  max 0 (1 - ((n : ℝ) + 1) * segDist c q z)

theorem continuous_segBump_uncurry (q : ℝ) (n : ℕ) :
    Continuous fun p : C(ℝ, ℂ) × ℂ => segBump p.1 q n p.2 :=
  continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_segDist q)))

theorem continuous_segBump (c : C(ℝ, ℂ)) (q : ℝ) (n : ℕ) : Continuous fun z => segBump c q n z := by
  have h := (continuous_segBump_uncurry q n).comp (Continuous.prodMk_right (X := C(ℝ, ℂ)) (Y := ℂ) c)
  exact h

theorem segBump_nonneg (c : C(ℝ, ℂ)) (q : ℝ) (n : ℕ) (z : ℂ) : 0 ≤ segBump c q n z :=
  le_max_left _ _

theorem segBump_antitone (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) :
    Antitone fun n : ℕ => segBump c q n z := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  have hd := segDist_nonneg c q z
  unfold segBump
  have h : 1 - ((n : ℝ) + 1) * segDist c q z ≤ 1 - ((m : ℝ) + 1) * segDist c q z := by nlinarith
  exact max_le_max le_rfl h

theorem segBump_eq_one_of_mem {c : C(ℝ, ℂ)} {q : ℝ} {z : ℂ} (hz : z ∈ c '' uIcc 0 q) (n : ℕ) :
    segBump c q n z = 1 := by
  rw [segBump, (segDist_eq_zero_iff c q z).2 hz, mul_zero, sub_zero]
  exact max_eq_right zero_le_one

theorem hasCompactSupport_segBump (c : C(ℝ, ℂ)) (q : ℝ) (n : ℕ) :
    HasCompactSupport (segBump c q n) := by
  obtain ⟨M, hM⟩ := (isCompact_seg c q).isBounded.exists_norm_le
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (M + 1)) fun z hz => ?_
  have h1 : M + 1 < ‖z‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  have hd : 1 ≤ segDist c q z := by
    obtain ⟨s, hs, hs'⟩ := exists_segDist_eq c q z
    rw [← hs']
    have h2 := hM (c s) ⟨s, hs, rfl⟩
    calc (1 : ℝ) ≤ ‖z‖ - ‖c s‖ := by linarith
      _ ≤ ‖z - c s‖ := norm_sub_norm_le z (c s)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [segBump]
  apply max_eq_left
  nlinarith

/-- The bumps decrease to the indicator of the segment. -/
theorem iInf_ofReal_segBump (c : C(ℝ, ℂ)) (q : ℝ) (z : ℂ) :
    ⨅ n : ℕ, ENNReal.ofReal (segBump c q n z) = (c '' uIcc 0 q).indicator 1 z := by
  by_cases hz : z ∈ c '' uIcc 0 q
  · rw [indicator_of_mem hz]
    simp [segBump_eq_one_of_mem hz]
  · rw [indicator_of_notMem hz]
    have hd : 0 < segDist c q z := lt_of_le_of_ne (segDist_nonneg c q z)
      (fun h => hz ((segDist_eq_zero_iff c q z).1 h.symm))
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / segDist c q z)
    rw [div_lt_iff₀ hd] at hn
    refine le_antisymm (iInf_le_of_le n ?_) (by positivity)
    have hb : segBump c q n z = 0 := by
      rw [segBump]
      apply max_eq_left
      nlinarith
    simp [hb]

/-! ### The approximations: explicit density and measurability -/

/-- The density `2^{-kγ²/2} e^{γ f_{2^{-k}}(z)}` of `lqgAreaApprox γ f k` is jointly measurable. -/
theorem measurable_approxDens (γ : ℝ) (k : ℕ) :
    Measurable fun p : DistC × ℂ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg p.1 (dyadicScale k) p.2) := by
  have h1 : Measurable fun p : DistC × ℂ => circleAvg p.1 (dyadicScale k) p.2 :=
    measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, dyadicScale k, p.2))
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have h2 := (Real.measurable_exp.comp (h1.const_mul γ)).const_mul (dyadicScale k ^ (γ ^ 2 / 2))
  exact h2

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

theorem integral_lqgAreaApprox (γ : ℝ) (k : ℕ) (u : DistC) (g : ℂ → ℝ) :
    ∫ z, g z ∂lqgAreaApprox γ u k =
      ∫ z, (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg u (dyadicScale k) z)) * g z := by
  have hd : Measurable fun z : ℂ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg u (dyadicScale k) z) :=
    (measurable_approxDens γ k).comp (f := fun z : ℂ => (u, z))
      (measurable_const.prodMk measurable_id)
  have h0 : ∀ z : ℂ, 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg u (dyadicScale k) z) :=
    fun z => mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  rw [lqgAreaApprox]
  exact QuantumZipper.GoodSample.integral_withDensity_ofReal hd h0 g

/-- The bump integrals against the approximations are jointly measurable in (field, curve). -/
theorem measurable_integral_segBump (γ : ℝ) (k : ℕ) (q : ℝ) (n : ℕ) :
    Measurable fun p : DistC × C(ℝ, ℂ) => ∫ z, segBump p.2 q n z ∂lqgAreaApprox γ p.1 k := by
  have e : (fun p : DistC × C(ℝ, ℂ) => ∫ z, segBump p.2 q n z ∂lqgAreaApprox γ p.1 k) =
      fun p => ∫ z, (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg p.1 (dyadicScale k) z)) *
        segBump p.2 q n z := by
    funext p
    exact integral_lqgAreaApprox γ k p.1 _
  rw [e]
  have h1 : Measurable fun x : (DistC × C(ℝ, ℂ)) × ℂ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg x.1.1 (dyadicScale k) x.2) :=
    (measurable_approxDens γ k).comp (f := fun x : (DistC × C(ℝ, ℂ)) × ℂ => (x.1.1, x.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun x : (DistC × C(ℝ, ℂ)) × ℂ => segBump x.1.2 q n x.2 :=
    (continuous_segBump_uncurry q n).measurable.comp
      (f := fun x : (DistC × C(ℝ, ℂ)) × ℂ => (x.1.2, x.2))
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact (h1.mul h2).stronglyMeasurable.integral_prod_right'.measurable

/-! ### The segment area functional -/

/-- **The measurable area functional of a curve segment**: `μ_f(c([min 0 q, max 0 q]))` whenever
the area approximations of `f` converge vaguely (`areaSeg_eq`). -/
def areaSeg (γ : ℝ) (f : DistC) (c : C(ℝ, ℂ)) (q : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, limsup (fun k => ENNReal.ofReal (∫ z, segBump c q n z ∂lqgAreaApprox γ f k)) atTop

theorem measurable_areaSeg (γ q : ℝ) :
    Measurable fun p : DistC × C(ℝ, ℂ) => areaSeg γ p.1 p.2 q :=
  Measurable.iInf fun n => Measurable.limsup fun k =>
    ENNReal.measurable_ofReal.comp (measurable_integral_segBump γ k q n)

/-- **Identification**: for a vague limit `m` of the area approximations of `f`, the functional
computes the `m`-mass of every curve segment. -/
theorem areaSeg_eq (γ : ℝ) {f : DistC} {m : Measure ℂ} (hv : IsVagueLimitC (lqgAreaApprox γ f) m)
    (c : C(ℝ, ℂ)) (q : ℝ) : areaSeg γ f c q = m (c '' uIcc 0 q) := by
  have : IsFiniteMeasureOnCompacts m := ⟨fun K hK => hv.1 K hK⟩
  have hint : ∀ n : ℕ, Integrable (segBump c q n) m := fun n =>
    (continuous_segBump c q n).integrable_of_hasCompactSupport (hasCompactSupport_segBump c q n)
  have hn : ∀ n : ℕ, limsup (fun k => ENNReal.ofReal (∫ z, segBump c q n z ∂lqgAreaApprox γ f k))
      atTop = ∫⁻ z, ENNReal.ofReal (segBump c q n z) ∂m := by
    intro n
    have hconv := hv.2 _ (continuous_segBump c q n) (hasCompactSupport_segBump c q n)
    have hconv' : Tendsto (fun k => ENNReal.ofReal (∫ z, segBump c q n z ∂lqgAreaApprox γ f k))
        atTop (𝓝 (ENNReal.ofReal (∫ z, segBump c q n z ∂m))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hconv
    rw [hconv'.limsup_eq]
    exact ofReal_integral_eq_lintegral_ofReal (hint n)
      (ae_of_all _ fun z => segBump_nonneg c q n z)
  simp only [areaSeg, hn]
  rw [← lintegral_iInf (f := fun n z => ENNReal.ofReal (segBump c q n z))
    (fun n => ENNReal.measurable_ofReal.comp (continuous_segBump c q n).measurable)
    (fun a b hab z => ENNReal.ofReal_le_ofReal (segBump_antitone c q z hab))
    (hint 0).lintegral_lt_top.ne]
  simp_rw [iInf_ofReal_segBump]
  exact lintegral_indicator_one (isCompact_seg c q).isClosed.measurableSet

end JointScalingO

end MatedCRTHarmonic.CellScaling
