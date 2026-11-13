/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.HoldingDivergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide
import LatticeProb.Bonanno.ReflectedWalk.TimeChange
import LatticeProb.Bonanno.ReflectedWalk.Recurrence
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Divergence of the embedded holding times of an arbitrary reflected walk (Gwynne–Sung, p. 26)

Step 2 of the uniqueness proof of Theorem 1.6 (arXiv:2506.18827, Section 3.4) needs the clock of
the embedded chain (3.31) to run to `∞`: the covering lemma
`Theorem16.TimeChange.exists_mem_Ico` — "every `t ≥ 0` lies in `[tⁿ_j, tⁿ_{j+1})`" — rests on
the paper's sentence "a.s. `lim_k ∑_{j ≤ k} Tⁿ_j = ∞`".  This file proves that sentence for an
**arbitrary** process `𝓧` satisfying the properties (i)–(vi) of Theorem 1.6
(`IsReflectedWalk`), at **every** level `n` of an exhaustion:

  `∀ n, ∀ᵐ ω ∂𝓧.P z, ∑' j, TimeChange.stepHolding 𝓧.X (E.Gsub n) j ω = ⊤`

(`Theorem16.ae_tsum_stepHolding_eq_top`; `TimeChange.stepHolding` is *definitionally*
`UniquenessGeneralSide.holdingTime`, so this is literally `∑_j Tⁿ_j = ∞`), together with the
equivalent statement about the times themselves, `tⁿ_j → ∞`
(`Theorem16.ae_tendsto_stepAt_atTop`).

## The argument

The distributional input is the headline of Step 1,
`Theorem16.map_embeddedPairOf_exhaustion`:

  `(𝓧.P z).map (embeddedPairOf 𝓧.X (E.Gsub n) v₀) = E.chainLaw hG n z ⊗ₘ holdingKernel w`,

i.e. the embedded chain `Yⁿ = (X̃_{tⁿ_j})_j` is the Markov chain of (3.2)–(3.3) started at `z`
and, *conditionally on it*, the holding times are independent with
`Tⁿ_j ~ Exponential(w(Yⁿ_j))` (`holdingKernel_apply`).  Since the property
`∑_j ofReal (T_j) = ∞` is a measurable property of the second coordinate of the pair,
`Measure.ae_compProd_of_ae_ae` reduces the claim to: for `E.chainLaw hG n z`-a.e. embedded path
`y`, the product measure `⨂_j Exponential(w(y_j))` gives full mass to the divergent sequences.

The obstacle is that the rates `w(y_j)` are path dependent and need not be bounded, so
`P(T_j > 1) = e^{-w(y_j)}` is not bounded below along the whole sequence.  This is resolved
exactly as in `RateFunction.lean` for the constructed side, by **property (v)** in the form of
Remark 3.1: the chain `Yⁿ` is recurrent, so almost surely it visits a fixed vertex
`z' ∈ VGₙ` at arbitrarily large times (`ConductanceGraph.Exhaustion.chainLaw_ae_exists_gt_eq`).
Along the infinite set `K = {k : y_k = z'}` the rate is the *constant* `w(z')`, the events
`{T_k > 1}`, `k ∈ K`, are independent with the constant probability `e^{-w(z')} > 0`, so
`∑_k P(T_k > 1) = ∞` and the second Borel–Cantelli lemma
(`ProbabilityTheory.measure_limsup_eq_one`, unconditional, no filtration needed) gives that
infinitely many of them occur; the sub-sum over those indices is then already `∞`.  This is
`infinitePi_expMeasure_ae_tsum_eq_top`, the exact analogue of
`RateFunction.expFamily_ae_tsum_div_eq_top` for the *kernel* side, where the i.i.d. rescaling by
a fixed `Exponential(1)` family is replaced by an infinite product of exponentials with varying
rates.

Finally the a.s. statement on the law of the pair is pulled back to `𝓧.P z`
(`MeasureTheory.ae_of_ae_map`, using the a.e.-measurability
`Theorem16.aemeasurable_embeddedPairOf` of the pair), and the real-valued holding sequence
`holdingSeqOf = fun j => (holdingTime …).toReal` is converted back to the `[0,∞]`-valued
`holdingTime` using `Theorem16.holdingTime_ne_top` on the almost sure event
`Theorem16.ae_forall_definedAt` that every `tⁿ_j` is finite.

## Conventions

`hR` (property (ii) at `∞`, `Theorem16.RightContinuousAtInfty`) is carried as an explicit
hypothesis, as in `Theorem16.ae_forall_definedAt` and
`Theorem16.map_embeddedPairOf_exhaustion`, rather than projected out of `IsReflectedWalk`; the
only projection used is `(h z).2.2.1`, property (ii) proper.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology NNReal

universe u

namespace ReflectedWalk

/-! ### The tail of the exponential law, and the coordinates of an infinite product -/

/-- `P(Exponential(c) > 1) = e^{-c} ≠ 0`: the one-sided bound that feeds the second
Borel–Cantelli lemma.  (`RateFunction.expMeasure_one_Ioi_one_ne_zero` is the case `c = 1`.) -/
lemma expMeasure_Ioi_one_ne_zero {c : ℝ} (hc : 0 < c) :
    ProbabilityTheory.expMeasure c (Set.Ioi (1 : ℝ)) ≠ 0 := by
  have : IsProbabilityMeasure (ProbabilityTheory.expMeasure c) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hc
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hc]
  simp only [zero_le_one, ite_true, mul_one]
  refine (tsub_pos_iff_lt.mpr ?_).ne'
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith [Real.exp_pos (-c)])

/-- The coordinates of an infinite product of probability measures are independent.  (The
special case of `RateFunction.iIndepFun_eval_expFamily` for an arbitrary, not necessarily
constant, family of factors.) -/
lemma iIndepFun_eval_infinitePi {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    iIndepFun (fun (i : ι) (x : ∀ j, X j) => x i) (Measure.infinitePi μ) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun i => measurable_pi_apply i]
  simp only [Measure.infinitePi_map_eval]
  exact Measure.map_id

/-! ### Divergence of a sum of independent exponentials with infinitely many equal rates

This is the probabilistic core of Lemma 3.5, Step 0 (p. 21, "`∑_j T_{[(n,j)]}` stochastically
dominates a countable sum of `exponential(w(x))` random variables, hence is a.s. infinite"), in
the form needed on the *uniqueness* side: the holding times are not given as a rescaled i.i.d.
family but only through their conditional law, an infinite product of exponentials whose rates
vary along the path. -/

/-- **Divergence of a countable sum of independent exponentials.**  If the rates `r` are positive
and take the *same* value `c > 0` along an infinite set `K ⊆ ℕ` of indices, then almost surely
`∑_j T_j = ∞` for `T` distributed as `⨂_j Exponential(r j)`.

Proof: the events `{T_k > 1}`, `k ∈ K`, are independent
(`iIndepFun_eval_infinitePi`) with the constant probability `e^{-c} > 0`
(`expMeasure_Ioi_one_ne_zero`), so their probabilities sum to `∞` and the second Borel–Cantelli
lemma (`ProbabilityTheory.measure_limsup_eq_one`) says that almost surely infinitely many of
them occur; the sub-sum of the series over those indices is then at least `∑ 1 = ∞`. -/
theorem infinitePi_expMeasure_ae_tsum_eq_top {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) {K : Set ℕ}
    (hK : K.Infinite) {c : ℝ} (hc : 0 < c) (hrc : ∀ k ∈ K, r k = c) :
    ∀ᵐ t ∂(Measure.infinitePi fun j => ProbabilityTheory.expMeasure (r j)),
      ∑' j, ENNReal.ofReal (t j) = ⊤ := by
  classical
  have hprob : ∀ j, IsProbabilityMeasure (ProbabilityTheory.expMeasure (r j)) :=
    fun j => ProbabilityTheory.isProbabilityMeasure_expMeasure (hr j)
  set ν : Measure (ℕ → ℝ) := Measure.infinitePi fun j => ProbabilityTheory.expMeasure (r j)
    with hν
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- the events `{T_k > 1}` for `k ∈ K`
  let T : ℕ → Set ℝ := fun k => {x | k ∈ K ∧ 1 < x}
  have hTm : ∀ k, MeasurableSet (T k) := fun k => by
    have hTk : T k = {_x : ℝ | k ∈ K} ∩ Set.Ioi 1 := by
      ext x
      simp [T]
    rw [hTk]
    exact (MeasurableSet.const _).inter measurableSet_Ioi
  let s : ℕ → Set (ℕ → ℝ) := fun k => (fun t : ℕ → ℝ => t k) ⁻¹' T k
  have hsm : ∀ k, MeasurableSet (s k) := fun k => measurable_pi_apply k (hTm k)
  have heval : ∀ (k : ℕ) (A : Set ℝ), MeasurableSet A →
      ν ((fun t : ℕ → ℝ => t k) ⁻¹' A) = ProbabilityTheory.expMeasure (r k) A := by
    intro k A hA
    rw [hν, ← Measure.map_apply (measurable_pi_apply k) hA, Measure.infinitePi_map_eval]
  have hind : iIndepSet s ν := by
    rw [iIndepSet_iff_meas_biInter hsm, hν]
    intro S
    exact (iIndepFun_eval_infinitePi fun j => ProbabilityTheory.expMeasure (r j))
      |>.measure_inter_preimage_eq_mul S fun k _ => hTm k
  -- their probabilities sum to `∞`
  have hsum : ∑' k, ν (s k) = ⊤ := by
    have := hK.to_subtype
    apply top_le_iff.mp
    calc (⊤ : ℝ≥0∞)
        = ∑' k, K.indicator (fun _ => ProbabilityTheory.expMeasure c (Set.Ioi (1 : ℝ))) k := by
          rw [← tsum_subtype]
          exact (ENNReal.tsum_const_eq_top_of_ne_zero (expMeasure_Ioi_one_ne_zero hc)).symm
      _ ≤ ∑' k, ν (s k) := ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ K
    · rw [Set.indicator_of_mem hk]
      have hTk : T k = Set.Ioi 1 := by
        ext x
        simp [T, hk]
      show ProbabilityTheory.expMeasure c (Set.Ioi (1 : ℝ)) ≤
        ν ((fun t : ℕ → ℝ => t k) ⁻¹' T k)
      rw [heval k _ (hTm k), hTk, hrc k hk]
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  -- so infinitely many of them occur, almost surely
  have h1 := measure_limsup_eq_one hsm hind hsum
  have h2 : ∀ᵐ t ∂ν, t ∈ limsup s atTop := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_limsup_atTop hsm)).mpr h1
  filter_upwards [h2] with t ht
  rw [mem_limsup_iff_frequently_mem] at ht
  have hinf : {k | t ∈ s k}.Infinite := Nat.frequently_atTop_iff_infinite.mp ht
  have := hinf.to_subtype
  apply top_le_iff.mp
  calc (⊤ : ℝ≥0∞) = ∑' k, {k | t ∈ s k}.indicator (fun _ => (1 : ℝ≥0∞)) k := by
        rw [← tsum_subtype]
        exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' k, ENNReal.ofReal (t k) := ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : t ∈ s k
  · rw [Set.indicator_of_mem (show k ∈ {k | t ∈ s k} from hk)]
    obtain ⟨-, h1t⟩ : k ∈ K ∧ 1 < t k := hk
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal h1t.le
  · rw [Set.indicator_of_notMem (show k ∉ {k | t ∈ s k} from hk)]
    exact zero_le

/-! ### The conditional law of the holding times, given a recurrent embedded path -/

section Kernel

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- **The holding times along a recurrent path diverge.**  Conditionally on the embedded chain
`y`, the holding times are independent with `T_j ~ Exponential(w(y_j))`
(`holdingKernel_apply`); if `y` returns to a vertex `z'` at arbitrarily large times — which
Remark 3.1 guarantees almost surely — then infinitely many of the rates equal `w(z')` and
`infinitePi_expMeasure_ae_tsum_eq_top` applies. -/
theorem holdingKernel_ae_tsum_ofReal_eq_top {w : V → ℝ} (hw : ∀ x, 0 < w x) {y : ℕ → V} {z' : V}
    (hrec : ∀ N, ∃ k, N < k ∧ y k = z') :
    ∀ᵐ t ∂(holdingKernel w y), ∑' j, ENNReal.ofReal (t j) = ⊤ := by
  rw [holdingKernel_apply hw y]
  refine infinitePi_expMeasure_ae_tsum_eq_top (fun j => hw (y j)) (K := {k | y k = z'})
    (Set.infinite_of_forall_exists_gt fun N => ?_) (hw z') fun k hk => congrArg w hk
  obtain ⟨k, hk, hy⟩ := hrec N
  exact ⟨k, hy, hk⟩

end Kernel

/-! ### The divergence of the embedded holding times of an arbitrary reflected walk -/

namespace Theorem16

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {𝓧 : ProcessFamily V}

/-- **The level-`n` holding times of (3.31) diverge** (Gwynne–Sung, p. 26: "a.s.
`lim_k ∑_{j ≤ k} Tⁿ_j = ∞`"), for an **arbitrary** process satisfying the properties (i)–(vi) of
Theorem 1.6, at every level of an exhaustion and from every starting point.

This is the hypothesis `h_tsum_holdingTime_eq_top` of
`Theorem16.TimeChange.approximatedAtFixedTimes_processN` and of
`Theorem16.TimeChange.rewindBound_processN`; `TimeChange.stepHolding` is *definitionally*
`holdingTime`, the `Tⁿ_j` of (3.31). -/
theorem ae_tsum_stepHolding_eq_top (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) (E : G.Exhaustion) (z : V) :
    ∀ n, ∀ᵐ ω ∂𝓧.P z, ∑' j, TimeChange.stepHolding 𝓧.X (E.Gsub n) j ω = ⊤ := by
  intro n
  obtain ⟨z', hz'⟩ := E.nonempty n
  -- the pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)` is a random element of `VG^ℕ × ℝ^ℕ`
  have hdef : ∀ k : ℕ, ∀ᵐ ω ∂𝓧.P z, ∃ x : V,
      stoppedValue 𝓧.X (stepTime 𝓧.X (E.Gsub n) k) ω = some x := by
    intro k
    filter_upwards [ae_forall_definedAt h hG z hR (E.nonempty n)] with ω hω
    exact ((mem_definedAt_iff (E.Gsub n) k ω).1 (hω k)).2
  have hpairm : AEMeasurable (embeddedPairOf 𝓧.X (E.Gsub n) z) (𝓧.P z) :=
    aemeasurable_embeddedPairOf 𝓧.measurable_X (h z).2.2.1 (hR z) (E.Gsub n) z hdef
  -- divergence under the law of the pair: `Measure.ae_compProd_of_ae_ae` and recurrence
  have hmeas : MeasurableSet
      {p : (ℕ → V) × (ℕ → ℝ) | ∑' j, ENNReal.ofReal (p.2 j) = ⊤} :=
    (Measurable.tsum fun j =>
      ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).comp measurable_snd))
      (measurableSet_singleton ⊤)
  have h1 : ∀ᵐ p ∂(E.chainLaw hG n z ⊗ₘ holdingKernel w),
      ∑' j, ENNReal.ofReal (p.2 j) = ⊤ := by
    refine Measure.ae_compProd_of_ae_ae hmeas ?_
    filter_upwards [E.chainLaw_ae_exists_gt_eq hG n hz' z] with y hy
    exact holdingKernel_ae_tsum_ofReal_eq_top hw hy
  rw [← map_embeddedPairOf_exhaustion h hG hw hR E n z z] at h1
  have h2 : ∀ᵐ ω ∂𝓧.P z, ∑' j, ENNReal.ofReal (holdingSeqOf 𝓧.X (E.Gsub n) ω j) = ⊤ :=
    ae_of_ae_map hpairm h1
  -- back from `ℝ` to `[0,∞]`: every `Tⁿ_j` is finite because every `tⁿ_j` is
  filter_upwards [h2, ae_forall_definedAt h hG z hR (E.nonempty n)] with ω hω hdefω
  have hne : ∀ j, holdingTime 𝓧.X (E.Gsub n) j ω ≠ ⊤ := fun j =>
    holdingTime_ne_top ((mem_definedAt_iff (E.Gsub n) (j + 1) ω).1 (hdefω (j + 1))).1
  calc ∑' j, TimeChange.stepHolding 𝓧.X (E.Gsub n) j ω
      = ∑' j, ENNReal.ofReal (holdingSeqOf 𝓧.X (E.Gsub n) ω j) :=
        tsum_congr fun j => (ENNReal.ofReal_toReal (hne j)).symm
    _ = ⊤ := hω

/-- **The embedded times of (3.31) run to infinity**, `tⁿ_j → ∞` almost surely: the form in
which the paper uses the divergence of the holding times (p. 26, the covering lemma
`TimeChange.exists_mem_Ico`).  The times are monotone (`TimeChange.stepAt_mono`) and unbounded
(`TimeChange.exists_lt_stepAt`). -/
theorem ae_tendsto_stepAt_atTop (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) (E : G.Exhaustion) (z : V) :
    ∀ n, ∀ᵐ ω ∂𝓧.P z,
      Tendsto (fun j => TimeChange.stepAt 𝓧.X (E.Gsub n) j ω) atTop atTop := by
  intro n
  filter_upwards [ae_tsum_stepHolding_eq_top h hG hw hR E z n,
    ae_forall_definedAt h hG z hR (E.nonempty n)] with ω hdiv hdefω
  have hfin : TimeChange.StepTimesFinite 𝓧.X (E.Gsub n) ω := fun j =>
    ((mem_definedAt_iff (E.Gsub n) j ω).1 (hdefω j)).1
  refine tendsto_atTop_atTop_of_monotone (fun j k hjk => TimeChange.stepAt_mono hfin hjk) ?_
  intro t
  obtain ⟨k, hk⟩ := TimeChange.exists_lt_stepAt hfin hdiv t
  exact ⟨k, hk.le⟩

end Theorem16

end ReflectedWalk

