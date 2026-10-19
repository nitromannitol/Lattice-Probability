/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianHarmonicExit.lean, BouRabeeGwynne/HarmonicNearClosureBrownianExit.lean.
-/

import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianStoppedLimit

/-!
# Harmonic exit identities on path space

For a standard Brownian law, the expectation of a function `f` at the exit position of the shifted
path `t ↦ z + ω t` from an open set `U` equals `f z`, provided `f` is harmonic on `U`.
The identity
is first proved for compactly supported `f`: the exit time is truncated, the bounded stopped
identity gives mean zero for each truncation, and dominated convergence passes to the limit, using
that the exit time is almost surely finite and that the path starts at the origin almost surely.
The position form for `HarmonicNearClosure` then follows from a compactly supported extension that
agrees with the function on a neighbourhood of the closure of `U`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- For a standard Brownian law, the path starts at the origin almost surely. -/
lemma standardBrownianLaw_eval_zero_ae {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ᵐ ω ∂μ, ω 0 = 0 := by
  have h : ∀ᵐ ω ∂μ, ∀ i : Fin d, ω 0 i = 0 :=
    ae_all_iff.mpr (fun i ↦ (hμ.2.1 i).eval_zero_ae_eq_zero)
  filter_upwards [h] with ω hω
  ext i
  exact hω i

/-- For a standard Brownian law in dimension at least one, the expectation of a compactly
supported function `f`, harmonic on a bounded open set `U`, at the exit position of the shifted
path from `U` started at `z` equals `f z`. -/
theorem standardBrownianLaw_integral_exit_harmonic_compactSupport {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (hh : IsHarmonicOn f U) (z : Euc d) :
    (∫ ω, f (z + ω (continuousExitTime U z ω).toNNReal) ∂μ) = f z := by
  letI : IsProbabilityMeasure μ := hμ.1
  let τ : BrownianPath d → ℝ≥0∞ := continuousExitTime U z
  have hτ : IsStoppingTime (brownianNaturalFiltration d) τ :=
    isStoppingTime_continuousExitTime hU z
  let σ : ℕ → BrownianPath d → ℝ≥0 := fun n ω ↦
    (min (τ ω) (n : ℝ≥0∞)).toNNReal
  have hσeq (n : ℕ) :
      (fun ω ↦ (σ n ω : ℝ≥0∞)) = fun ω ↦ min (τ ω) (n : ℝ≥0∞) := by
    funext ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hσstop (n : ℕ) : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ (σ n ω : ℝ≥0∞)) := by
    rw [hσeq]
    exact hτ.min_const (n : ℝ≥0)
  have hσbound (n : ℕ) (ω : BrownianPath d) : σ n ω ≤ (n : ℝ≥0) := by
    rw [← ENNReal.coe_le_coe, congrFun (hσeq n) ω]
    exact min_le_right _ _
  have hstay (n : ℕ) (ω : BrownianPath d) (t : ℝ≥0) (ht : t < σ n ω) : z + ω t ∈ U := by
    apply mem_of_lt_continuousExitTime
    have hle : (σ n ω : ℝ≥0∞) ≤ τ ω := by
      rw [congrFun (hσeq n) ω]
      exact min_le_left _ _
    exact (ENNReal.coe_lt_coe.mpr ht).trans_le hle
  have hmean (n : ℕ) : (∫ ω, f (z + ω (σ n ω)) - f (z + ω 0) ∂μ) = 0 :=
    standardBrownianLaw_bounded_stopped_harmonic_difference hμ hf hsupp hh
      (hσstop n) (n : ℝ≥0) (hσbound n) z (hstay n)
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hmzero : Measurable (fun ω : BrownianPath d ↦ f (z + ω 0)) :=
    hf.continuous.measurable.comp
      (measurable_const.add (continuous_eval_const (0 : ℝ≥0)).measurable)
  have hmseq (n : ℕ) : Measurable (fun ω : BrownianPath d ↦ f (z + ω (σ n ω))) :=
    hf.continuous.measurable.comp (measurable_const.add
      (measurable_brownian_random_evaluation (measurable_nnreal_brownian_stopping (hσstop n))))
  have hdom (n : ℕ) : ∀ᵐ ω ∂μ, ‖f (z + ω (σ n ω)) - f (z + ω 0)‖ ≤ 2 * M := by
    filter_upwards [] with ω
    exact (norm_sub_le _ _).trans (by linarith [hM (z + ω (σ n ω)), hM (z + ω 0)])
  have hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞ := standardBrownianLaw_ae_finiteExit hd hμ hUb z
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f (z + ω (σ n ω)) - f (z + ω 0)) atTop
      (𝓝 (f (z + ω (τ ω).toNNReal) - f (z + ω 0))) := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ ω).toNNReal : ℝ)
    have heq : (fun n ↦ f (z + ω (σ n ω)) - f (z + ω 0)) =ᶠ[atTop]
        fun _ : ℕ ↦ f (z + ω (τ ω).toNNReal) - f (z + ω 0) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : τ ω ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hω]
        have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hreal : ((τ ω).toNNReal : ℝ) ≤ ((n : ℝ≥0) : ℝ) := by
          simpa only [NNReal.coe_natCast] using hN.le.trans hNn
        exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hreal)
      simp only [σ, min_eq_left hle]
    exact tendsto_const_nhds.congr' heq.symm
  have hint := tendsto_integral_of_dominated_convergence (fun _ : BrownianPath d ↦ 2 * M)
    (fun n ↦ ((hmseq n).sub hmzero).aestronglyMeasurable) (integrable_const _) hdom hlim
  have hdiff : (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ) = 0 :=
    tendsto_nhds_unique hint (by simpa only [Pi.sub_apply, hmean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))
  have hmexit : Measurable (fun ω : BrownianPath d ↦ f (z + ω (τ ω).toNNReal)) :=
    hf.continuous.measurable.comp (measurable_const.add
      (measurable_brownian_random_evaluation
        (ENNReal.measurable_toNNReal.comp (measurable_continuousExitTime hU z))))
  have hiexit : Integrable (fun ω : BrownianPath d ↦ f (z + ω (τ ω).toNNReal)) μ :=
    (integrable_const M).mono' hmexit.aestronglyMeasurable (Eventually.of_forall (fun ω ↦ hM _))
  have hizero : Integrable (fun ω : BrownianPath d ↦ f (z + ω 0)) μ :=
    (integrable_const M).mono' hmzero.aestronglyMeasurable (Eventually.of_forall (fun ω ↦ hM _))
  have hbase : (∫ ω, f (z + ω 0) ∂μ) = f z := by
    have heq : (fun ω : BrownianPath d ↦ f (z + ω 0)) =ᵐ[μ] fun _ ↦ f z :=
      (standardBrownianLaw_eval_zero_ae hμ).mono (fun ω hω ↦ by
        change f (z + ω 0) = f z
        rw [hω, add_zero])
    rw [integral_congr_ae heq]
    simp
  have heq := integral_sub hiexit hizero
  change (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ) =
    (∫ ω, f (z + ω (τ ω).toNNReal) ∂μ) - (∫ ω, f (z + ω 0) ∂μ) at heq
  rw [hdiff, hbase] at heq
  exact sub_eq_zero.mp heq.symm

/-- For a standard Brownian law in dimension at least one, the expectation of a function `h`,
harmonic on an open neighbourhood of the closure of a bounded open set `U`, at the exit position
of the shifted path from `U` started at a point `z ∈ U` equals `h z`. -/
theorem standardBrownianLaw_integral_exit_harmonicNearClosure {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {h : Euc d → ℝ} (hh : HarmonicNearClosure h U) {z : Euc d} (hz : z ∈ U) :
    ∫ ω, h (z + ω (continuousExitTime U z ω).toNNReal) ∂μ = h z := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨W, hW, hUW, hhW⟩ := hh
  obtain ⟨g, V, _, hUV, _, hg, hgc, _, heq, hgharm⟩ :=
    hhW.exists_compactSupport_eq_near_compact hUb.isCompact_closure hW hUW
  have hUsub : U ⊆ V := subset_closure.trans hUV
  have hgharmU : IsHarmonicOn g U :=
    ⟨hg.contDiffOn, fun x hx => hgharm.laplacian_eq_zero (hUsub hx)⟩
  have hae : ∀ᵐ ω ∂μ, z + ω (continuousExitTime U z ω).toNNReal ∈ frontier U := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
      standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω h0 hfin
    refine continuousExitTime_mem_frontier hU ?_ hfin
    rw [h0, add_zero]
    exact hz
  have hcongr :
      (fun ω : BrownianPath d ↦ h (z + ω (continuousExitTime U z ω).toNNReal)) =ᵐ[μ]
        fun ω ↦ g (z + ω (continuousExitTime U z ω).toNNReal) := by
    filter_upwards [hae] with ω hω
    exact (heq (hUV (frontier_subset_closure hω))).symm
  rw [integral_congr_ae hcongr, ← heq (hUsub hz)]
  exact standardBrownianLaw_integral_exit_harmonic_compactSupport hd hμ hU hUb hg hgc hgharmU z

namespace BrownianPathHarmonicExitExample

/-- The constant function `1` is harmonic near the closure of the open unit ball of `Euc 2`. -/
theorem const_harmonicNearClosure_ball :
    HarmonicNearClosure (fun _ : Euc 2 => (1 : ℝ)) (Metric.ball 0 1) :=
  harmonicNearClosure_iff.mpr (InnerProductSpace.harmonicOnNhd_const _)

/-- The second Fréchet derivative of the coordinate function `y ↦ y 0` vanishes, since the
coordinate function is a continuous linear map. -/
theorem coord_iteratedFDeriv_two (x : Euc 2) :
    iteratedFDeriv ℝ 2 (fun y : Euc 2 => y 0) x = 0 := by
  let l : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  have hl : (fun y : Euc 2 => y 0) = ⇑l := rfl
  have hfd : (fun y : Euc 2 => fderiv ℝ (⇑l) y) = fun _ => l := by
    funext y
    exact l.fderiv
  have h1 : iteratedFDeriv ℝ 1 (fun _ : Euc 2 => l) = 0 := iteratedFDeriv_succ_const 0 l
  rw [hl]
  show iteratedFDeriv ℝ (1 + 1) (⇑l) x = 0
  rw [iteratedFDeriv_succ_eq_comp_right, hfd, h1]
  simp only [Function.comp_apply, Pi.zero_apply]
  exact LinearIsometryEquiv.map_zero _

/-- The coordinate function `y ↦ y 0` is harmonic on all of `Euc 2`. -/
theorem coord_isHarmonicOn_univ : IsHarmonicOn (fun y : Euc 2 => y 0) Set.univ := by
  refine ⟨?_, fun x _ => ?_⟩
  · exact (EuclideanSpace.proj (0 : Fin 2) : Euc 2 →L[ℝ] ℝ).contDiff.contDiffOn
  · simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      coord_iteratedFDeriv_two]

/-- The coordinate function `y ↦ y 0` is harmonic near the closure of the open unit ball of
`Euc 2`. -/
theorem coord_harmonicNearClosure_ball :
    HarmonicNearClosure (fun y : Euc 2 => y 0) (Metric.ball 0 1) :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, coord_isHarmonicOn_univ⟩

/-- For a standard Brownian law on `Euc 2`-valued paths, the position form holds for the
coordinate function `y ↦ y 0` on the open unit ball, at every starting point `z` in the ball. -/
theorem coord_integral_exit_ball {μ : Measure (BrownianPath 2)} (hμ : IsStandardBrownianLaw μ)
    {z : Euc 2} (hz : z ∈ Metric.ball (0 : Euc 2) 1) :
    ∫ ω, (z + ω (continuousExitTime (Metric.ball 0 1) z ω).toNNReal) 0 ∂μ = z 0 :=
  standardBrownianLaw_integral_exit_harmonicNearClosure (by norm_num) hμ Metric.isOpen_ball
    Metric.isBounded_ball coord_harmonicNearClosure_ball hz

/-- For a standard Brownian law on `Euc 2`-valued paths, the position form holds for the
constant function `1` on the open unit ball, at every starting point `z` in the ball. -/
theorem const_integral_exit_ball {μ : Measure (BrownianPath 2)} (hμ : IsStandardBrownianLaw μ)
    {z : Euc 2} (hz : z ∈ Metric.ball (0 : Euc 2) 1) :
    ∫ ω, (fun _ : Euc 2 => (1 : ℝ))
      (z + ω (continuousExitTime (Metric.ball 0 1) z ω).toNNReal) ∂μ =
      (fun _ : Euc 2 => (1 : ℝ)) z :=
  standardBrownianLaw_integral_exit_harmonicNearClosure (by norm_num) hμ Metric.isOpen_ball
    Metric.isBounded_ball const_harmonicNearClosure_ball hz

end BrownianPathHarmonicExitExample

end LatticeProb
