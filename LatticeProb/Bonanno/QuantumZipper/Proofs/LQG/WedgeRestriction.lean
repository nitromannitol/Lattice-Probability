/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeRestriction at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeToolkit

/-!
# Restriction identity for the wedge (blueprint `SECTION5_BLUEPRINT.md`, node B4(b))

Inside the closed unit half-disc (radii `≤ 1`, i.e. log-scales `t = −log|z| ≥ 0`) the wedge
field `wedgeField (lateralPart X') A Q` of an `IsWedgeProcess α Q` process `A` independent of a
free field `X'` has the same coordinate law as `ofFun (α (−log|·|)) + X` with `X` a free field
normalized by `radAvgReg X 1`. Coordinates: the folded circles of `coordsFull` and the raw test
pairings, restricted to circles and test functions carried by `closedBall 0 1`.

Route. On `t ≥ 0` the wedge radial part is `√2 b_t + (α − Q) t`, so the field reads
`lateral + α(−log|z|) + √2 b_{−log|z|}`; the normalized free field reads
`lateral(X) + α(−log|z|) + √2 β_{−log|z|}` with `β = (√2)⁻¹ radialProc X` a Brownian motion
independent of `lateral(X)` (`WedgeToolkit` (a1), (a2)). Both are the same measurable function
`Ψ` of (lateral coordinates, Brownian path); the path integrals are read through dyadic
Riemann sums (`Jmod`), which agree a.s. with the path integrals (`ae_tendsto_Jn`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace WedgeRes

open WedgeTK CircleFubini

/-! ## 1. Dyadic Riemann sums of paths -/

/-- Rounding down to the grid `4^{-n} ℕ`. -/
def flr (n : ℕ) (s : ℝ≥0) : ℝ≥0 := Real.toNNReal ((⌊(4 : ℝ) ^ n * s⌋₊ : ℝ) / 4 ^ n)

theorem flr_le (n : ℕ) (s : ℝ≥0) : (flr n s : ℝ) ≤ s := by
  unfold flr
  rw [Real.coe_toNNReal _ (by positivity), div_le_iff₀ (by positivity), mul_comm]
  exact Nat.floor_le (by positivity)

theorem sub_flr_le (n : ℕ) (s : ℝ≥0) : (s : ℝ) - flr n s ≤ 1 / 4 ^ n := by
  unfold flr
  rw [Real.coe_toNNReal _ (by positivity)]
  have h := Nat.lt_floor_add_one ((4 : ℝ) ^ n * s)
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h4]
  linarith

theorem measurable_flr (n : ℕ) : Measurable (flr n) := by
  unfold flr
  exact ((((measurable_from_top : Measurable (Nat.cast : ℕ → ℝ)).comp
    (Measurable.nat_floor (measurable_const.mul measurable_coe_nnreal_real))).div_const _)).real_toNNReal

theorem countable_range_flr (n : ℕ) : (Set.range (flr n)).Countable := by
  have hsub : Set.range (flr n) ⊆ Set.range (fun k : ℕ => Real.toNNReal ((k : ℝ) / 4 ^ n)) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨⌊(4 : ℝ) ^ n * s⌋₊, rfl⟩
  exact (Set.countable_range _).mono hsub

/-- Riemann sum at level `n` of a path against a measure on times. -/
def Jn (lam : Measure ℝ≥0) (n : ℕ) (w : ℝ≥0 → ℝ) : ℝ := ∫ s, w (flr n s) ∂lam

/-- The path integral read through dyadic Riemann sums (junk if they do not converge). -/
def Jmod (lam : Measure ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ := limUnder atTop fun n => Jn lam n w

theorem measurable_eval_flr (n : ℕ) :
    Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (flr n p.2)) := by
  have : Countable (Set.range (flr n)) := (countable_range_flr n).to_subtype
  intro T hT
  have key : (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (flr n p.2)) ⁻¹' T
      = ⋃ d : Set.range (flr n),
          {w : ℝ≥0 → ℝ | w (d : ℝ≥0) ∈ T} ×ˢ (flr n ⁻¹' ({(d : ℝ≥0)} : Set ℝ≥0)) := by
    ext ⟨w, s⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hmem
      exact ⟨⟨flr n s, Set.mem_range_self s⟩, hmem, rfl⟩
    · rintro ⟨d, hmem, hdz⟩
      rwa [hdz]
  rw [key]
  refine MeasurableSet.iUnion fun d => MeasurableSet.prod ?_ ?_
  · exact measurable_pi_apply (d : ℝ≥0) hT
  · exact measurable_flr n (measurableSet_singleton _)

theorem measurable_Jmod (lam : Measure ℝ≥0) [SFinite lam] : Measurable (Jmod lam) := by
  unfold Jmod Jn
  exact (StronglyMeasurable.limUnder fun n =>
    (StronglyMeasurable.integral_prod_right' (ν := lam)
      (measurable_eval_flr n).stronglyMeasurable)).measurable

/-! ## 2. Riemann sums of a pre-Brownian path converge almost surely -/

theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
    integral_id_gaussianReal] at h
  simpa using h

theorem abs_le_amgm (x : ℝ) {c : ℝ} (hc : 0 < c) : |x| ≤ (c + x ^ 2 / c) / 2 := by
  have h : 0 ≤ (|x| - c) ^ 2 := sq_nonneg _
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx, le_div_iff₀ two_pos, add_div' _ _ _ hc.ne', le_div_iff₀ hc]
  nlinarith

section PreBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → ℝ}

theorem memLp_preBrownian (hW : IsPreBrownianReal W P) (s : ℝ≥0) : MemLp (W s) 2 P :=
  (hW.isGaussianProcess.hasGaussianLaw_eval s).memLp_two

theorem integral_abs_sub_le (hW : IsPreBrownianReal W P) (s u : ℝ≥0) {c : ℝ} (hc : 0 < c) :
    ∫ ω, |W s ω - W u ω| ∂P ≤ (c + (nndist (s : ℝ) (u : ℝ) : ℝ) / c) / 2 := by
  have h2 : MemLp (fun ω => W s ω - W u ω) 2 P :=
    (memLp_preBrownian hW s).sub (memLp_preBrownian hW u)
  have hsq : ∫ ω, (W s ω - W u ω) ^ 2 ∂P = nndist (s : ℝ) (u : ℝ) := by
    have h := (hW.hasLaw_sub s u).integral_comp (f := fun x : ℝ => x ^ 2)
      (continuous_pow 2).aestronglyMeasurable
    simp only [Function.comp_def, Pi.sub_apply] at h
    rw [h, integral_sq_gaussianReal]; rfl
  calc ∫ ω, |W s ω - W u ω| ∂P ≤ ∫ ω, (c + (W s ω - W u ω) ^ 2 / c) / 2 ∂P :=
        integral_mono (h2.integrable one_le_two).abs
          (((integrable_const c).add (h2.integrable_sq.div_const c)).div_const 2)
          fun ω => abs_le_amgm _ hc
    _ = _ := by
        rw [integral_div, integral_add (integrable_const _) (h2.integrable_sq.div_const _),
          integral_div, hsq, integral_const, probReal_univ, one_smul]

theorem integral_abs_le (hW : IsPreBrownianReal W P) (s : ℝ≥0) :
    ∫ ω, |W s ω| ∂P ≤ (1 + (s : ℝ)) / 2 := by
  have h2 := memLp_preBrownian hW s
  have hsq : ∫ ω, (W s ω) ^ 2 ∂P = s := by
    have h := (hW.hasLaw_eval s).integral_comp (f := fun x : ℝ => x ^ 2)
      (continuous_pow 2).aestronglyMeasurable
    simp only [Function.comp_def] at h
    rw [h, integral_sq_gaussianReal]
  calc ∫ ω, |W s ω| ∂P ≤ ∫ ω, (1 + (W s ω) ^ 2 / 1) / 2 ∂P :=
        integral_mono (h2.integrable one_le_two).abs
          (((integrable_const 1).add (h2.integrable_sq.div_const 1)).div_const 2)
          fun ω => abs_le_amgm _ one_pos
    _ = _ := by
        rw [integral_div, integral_add (integrable_const _) (h2.integrable_sq.div_const _),
          integral_div, hsq, integral_const, probReal_univ, one_smul, div_one]

theorem nndist_flr_le (n : ℕ) (s : ℝ≥0) :
    (nndist ((flr n s : ℝ≥0) : ℝ) (s : ℝ) : ℝ) ≤ 1 / 4 ^ n := by
  rw [coe_nndist, dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (flr_le n s))]
  exact sub_flr_le n s

/-- **Riemann sums of a pre-Brownian path converge almost surely**, for a finite measure on
times with a first moment. -/
theorem ae_tendsto_Jn (hWm : Measurable (Function.uncurry W)) (hW : IsPreBrownianReal W P)
    {lam : Measure ℝ≥0} [IsFiniteMeasure lam] (hlam : Integrable (fun s : ℝ≥0 => (s : ℝ)) lam) :
    ∀ᵐ ω ∂P, Integrable (fun s => W s ω) lam ∧
      Tendsto (fun n => Jn lam n (fun s => W s ω)) atTop (𝓝 (∫ s, W s ω ∂lam)) := by
  have hWs : ∀ s, Measurable (W s) := fun s => hWm.of_uncurry_left
  -- joint measurability
  have hm0 : Measurable (fun p : Ω × ℝ≥0 => ENNReal.ofReal |W p.2 p.1|) :=
    (continuous_abs.measurable.comp (hWm.comp measurable_swap)).ennreal_ofReal
  have hmn : ∀ n : ℕ, Measurable (fun p : Ω × ℝ≥0 =>
      ENNReal.ofReal |W (flr n p.2) p.1 - W p.2 p.1|) := fun n =>
    (continuous_abs.measurable.comp
      ((hWm.comp ((measurable_flr n).comp measurable_snd |>.prodMk measurable_fst)).sub
      (hWm.comp measurable_swap))).ennreal_ofReal
  -- first moments
  have hL1 : ∫⁻ ω, ∫⁻ s, ENNReal.ofReal |W s ω| ∂lam ∂P ≠ ⊤ := by
    rw [lintegral_lintegral_swap hm0.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ s, ENNReal.ofReal ((1 + (s : ℝ)) / 2) ∂lam) ?_ ?_
    · rw [show (∫⁻ s, ENNReal.ofReal ((1 + (s : ℝ)) / 2) ∂lam) =
          ENNReal.ofReal (∫ s, (1 + (s : ℝ)) / 2 ∂lam) from
        (ofReal_integral_eq_lintegral_ofReal
          ((((integrable_const (1 : ℝ)).add hlam).div_const 2 :
            Integrable (fun s : ℝ≥0 => (1 + (s : ℝ)) / 2) lam))
          (ae_of_all _ fun s : ℝ≥0 => div_nonneg (add_nonneg zero_le_one s.2)
            zero_le_two)).symm]
      exact ENNReal.ofReal_ne_top
    · refine lintegral_mono fun s => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((memLp_preBrownian hW s).integrable one_le_two).abs (ae_of_all _ fun _ => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (integral_abs_le hW s)
  have hL2 : ∫⁻ ω, ∑' n, ∫⁻ s, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂lam ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => ((hmn n).lintegral_prod_right').aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * lam univ) ?_ ?_
    · rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
      simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.tsum_geometric]
      refine ENNReal.inv_ne_top.2 (tsub_pos_of_lt ?_).ne'
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [lintegral_lintegral_swap (hmn n).aemeasurable]
      calc ∫⁻ s, ∫⁻ ω, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂P ∂lam
          ≤ ∫⁻ _, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∂lam := by
            refine lintegral_mono fun s => ?_
            rw [show (∫⁻ ω, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂P) =
                ENNReal.ofReal (∫ ω, |W (flr n s) ω - W s ω| ∂P) from
              (ofReal_integral_eq_lintegral_ofReal
              ((((memLp_preBrownian hW (flr n s)).sub (memLp_preBrownian hW s)).integrable
                one_le_two).abs : Integrable (fun ω => |W (flr n s) ω - W s ω|) P)
              (ae_of_all _ fun _ => abs_nonneg _)).symm]
            refine ENNReal.ofReal_le_ofReal ((integral_abs_sub_le hW _ s
              (by positivity : (0 : ℝ) < (1 / 2) ^ n)).trans ?_)
            have h1 := nndist_flr_le n s
            have h4 : (1 : ℝ) / 4 ^ n / (1 / 2) ^ n = (1 / 2) ^ n := by
              have e : (1 : ℝ) / 4 ^ n = (1 / 2) ^ n * (1 / 2) ^ n := by
                rw [← mul_pow, show (1 : ℝ) / 2 * (1 / 2) = 1 / 4 by norm_num, one_div_pow]
              rw [e, mul_div_assoc, div_self (by positivity), mul_one]
            have h5 : (nndist ((flr n s : ℝ≥0) : ℝ) (s : ℝ) : ℝ) / (1 / 2) ^ n ≤
                (1 / 2) ^ n := by
              exact (div_le_div_of_nonneg_right h1 (by positivity)).trans h4.le
            linarith
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * lam univ := lintegral_const _
  have hae1 := ae_lt_top' (hm0.lintegral_prod_right').aemeasurable hL1
  have hae2 := ae_lt_top' (AEMeasurable.tsum fun n =>
    ((hmn n).lintegral_prod_right').aemeasurable) hL2
  filter_upwards [hae1, hae2] with ω h1 h2
  have hWω : Measurable fun s => W s ω := hWm.comp (measurable_id.prodMk measurable_const)
  have hint : Integrable (fun s => W s ω) lam := by
    refine ⟨hWω.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact h1
  have hDm : ∀ n : ℕ, Measurable fun s => W (flr n s) ω - W s ω := fun n =>
    (hWω.comp (measurable_flr n)).sub hWω
  have hDfin : ∀ n : ℕ, ∫⁻ s, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂lam ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top h2.ne (ENNReal.le_tsum (f := fun n =>
      ∫⁻ s, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂lam) n)
  have hDint : ∀ n : ℕ, Integrable (fun s => W (flr n s) ω - W s ω) lam := fun n => by
    refine ⟨(hDm n).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_top_iff_ne_top.2 (hDfin n)
  refine ⟨hint, ?_⟩
  have hlim : Tendsto (fun n => ∫⁻ s, ENNReal.ofReal |W (flr n s) ω - W s ω| ∂lam) atTop
      (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top h2.ne
  have hlim' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  rw [ENNReal.toReal_zero] at hlim'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim'
  have e : Jn lam n (fun s => W s ω) - ∫ s, W s ω ∂lam =
      ∫ s, (W (flr n s) ω - W s ω) ∂lam := by
    unfold Jn
    rw [integral_sub ((hDint n).add hint |>.congr (ae_of_all _ fun s => by simp)) hint]
  rw [e, Function.comp_apply, ← ofReal_integral_eq_lintegral_ofReal (hDint n).abs
    (ae_of_all _ fun _ => abs_nonneg _), ENNReal.toReal_ofReal (integral_nonneg fun _ =>
      abs_nonneg _)]
  exact norm_integral_le_integral_norm _

end PreBrownian

/-! ## 3. A measurable continuous version of a Brownian motion -/

section Version

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem exists_good_version {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, Measurable (Function.uncurry B') ∧
      (∀ ω, Continuous fun s => B' s ω) ∧ (∀ᵐ ω ∂P, ∀ s, B' s ω = B s ω) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set mk : ℝ≥0 → Ω → ℝ := fun s => (hB.aemeasurable s).mk (B s) with hmk
  have hS : ∀ᵐ ω ∂P, Continuous (fun s => B s ω) ∧ ∀ d ∈ D, B d ω = mk d ω := by
    filter_upwards [hB.cont, (eventually_countable_ball hDc).2 fun d _ =>
      (hB.aemeasurable d).ae_eq_mk] with ω h1 h2 using ⟨h1, h2⟩
  set N := {ω | ¬ (Continuous (fun s => B s ω) ∧ ∀ d ∈ D, B d ω = mk d ω)} with hN_def
  have hN : P N = 0 := ae_iff.1 hS
  set Ω₁ := (toMeasurable P N)ᶜ with hΩ₁_def
  have hΩ₁m : MeasurableSet Ω₁ := (measurableSet_toMeasurable P N).compl
  have hΩ₁ : ∀ ω ∈ Ω₁, Continuous (fun s => B s ω) ∧ ∀ d ∈ D, B d ω = mk d ω :=
    fun ω hω => by
      by_contra h; exact hω (subset_toMeasurable P N h)
  have hΩ₁ae : ∀ᵐ ω ∂P, ω ∈ Ω₁ := by
    rw [ae_iff]
    have : {a | ¬ a ∈ Ω₁} = toMeasurable P N := by ext; simp [Ω₁]
    rw [this, measure_toMeasurable, hN]
  set B' : ℝ≥0 → Ω → ℝ := fun s ω => Ω₁.indicator (fun ω => B s ω) ω with hB'
  have hc : ∀ ω, Continuous fun s => B' s ω := fun ω => by
    by_cases hω : ω ∈ Ω₁
    · simp only [hB', Set.indicator_of_mem hω]; exact (hΩ₁ ω hω).1
    · simp only [hB', hω, not_false_eq_true, Set.indicator_of_notMem]; exact continuous_const
  have hm : ∀ s, Measurable (B' s) := fun s => by
    have hs : s ∈ closure D := by rw [hDd.closure_eq]; exact Set.mem_univ s
    obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 hs
    refine measurable_of_tendsto_metrizable (f := fun n ω => Ω₁.indicator (mk (u n)) ω)
      (fun n => (hB.aemeasurable (u n)).measurable_mk.indicator hΩ₁m) ?_
    rw [tendsto_pi_nhds]; intro ω
    by_cases hω : ω ∈ Ω₁
    · simp only [hB', Set.indicator_of_mem hω]
      have : ∀ n, mk (u n) ω = B (u n) ω := fun n => ((hΩ₁ ω hω).2 (u n) (huD n)).symm
      simp_rw [this]
      exact ((hΩ₁ ω hω).1.tendsto s).comp hu
    · simp only [hB', hω, not_false_eq_true, Set.indicator_of_notMem]
      exact tendsto_const_nhds
  refine ⟨B', measurable_uncurry_of_continuous_of_measurable hc hm, hc, ?_⟩
  filter_upwards [hΩ₁ae] with ω hω s
  simp only [hB', Set.indicator_of_mem hω]

end Version

/-! ## 4. Cross-space law identities -/

section CrossLaw

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Two centered Gaussian vectors with the same covariances have the same law. -/
theorem map_eq_of_gaussian_vec {ι : Type*} [Fintype ι] {U : ι → Ω → ℝ} {V : ι → Ω' → ℝ}
    (hU : HasGaussianLaw (fun ω i => U i ω) P) (hV : HasGaussianLaw (fun ω i => V i ω) P')
    (hUm : ∀ i, Measurable (U i)) (hVm : ∀ i, Measurable (V i))
    (hU2 : ∀ i, MemLp (U i) 2 P) (hV2 : ∀ i, MemLp (V i) 2 P')
    (hU0 : ∀ i, ∫ ω, U i ω ∂P = 0) (hV0 : ∀ i, ∫ ω, V i ω ∂P' = 0)
    (hcov : ∀ i j, cov[U i, U j; P] = cov[V i, V j; P']) :
    P.map (fun ω i => U i ω) = P'.map (fun ω i => V i ω) := by
  classical
  haveI := hU.isGaussian_map
  haveI := hV.isGaussian_map
  have hmU : Measurable fun ω i => U i ω := measurable_pi_iff.2 hUm
  have hmV : Measurable fun ω i => V i ω := measurable_pi_iff.2 hVm
  have hL0 : ∀ (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ),
      L x = ∑ i, (L fun k => if i = k then 1 else 0) * x i := by
    intro L x
    rw [show L x = L.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]
    rw [mul_comm]; rfl
  have hL : ∀ (Z : ι → Ω → ℝ) (L : StrongDual ℝ (ι → ℝ)),
      (L ∘ fun ω i => Z i ω) = fun ω => ∑ i, (L fun k => if i = k then 1 else 0) * Z i ω :=
    fun Z L => funext fun ω => hL0 L _
  have hL' : ∀ (Z : ι → Ω' → ℝ) (L : StrongDual ℝ (ι → ℝ)),
      (L ∘ fun ω i => Z i ω) = fun ω => ∑ i, (L fun k => if i = k then 1 else 0) * Z i ω :=
    fun Z L => funext fun ω => hL0 L _
  refine IsGaussian.ext_covarianceBilinDual ?_ ?_
  · rw [integral_map hmU.aemeasurable aestronglyMeasurable_id,
      integral_map hmV.aemeasurable aestronglyMeasurable_id]
    funext i
    show (∫ ω, (fun i => U i ω) ∂P) i = (∫ ω, (fun i => V i ω) ∂P') i
    rw [eval_integral (fun i => (hU2 i).integrable one_le_two),
      eval_integral (fun i => (hV2 i).integrable one_le_two), hU0, hV0]
  · ext L₁ L₂
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covariance_map L₁.continuous.aestronglyMeasurable L₂.continuous.aestronglyMeasurable
        hmU.aemeasurable,
      covariance_map L₁.continuous.aestronglyMeasurable L₂.continuous.aestronglyMeasurable
        hmV.aemeasurable, hL U L₁, hL U L₂, hL' V L₁, hL' V L₂,
      covariance_fun_sum_fun_sum (fun i => (hU2 i).const_mul _) (fun j => (hU2 j).const_mul _),
      covariance_fun_sum_fun_sum (fun i => (hV2 i).const_mul _) (fun j => (hV2 j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_right, hcov]

/-- Laws of the Gaussian families of two free fields along the same pairs agree. -/
theorem map_gaussFam_eq₂ {X : Ω → FieldSample} {X' : Ω' → FieldSample}
    (hX : IsFreeGFFModConstH X P) (hX' : IsFreeGFFModConstH X' P') {I : Type*}
    (p : I → BPair) :
    P.map (fun ω i => gaussFam X p i ω) = P'.map (fun ω i => gaussFam X' p i ω) := by
  have h1 := isProjectiveLimit_map (P := P) (X := gaussFam X p) (measurable_gaussFam_pi hX p).aemeasurable
  have h2 := isProjectiveLimit_map (P := P') (X := gaussFam X' p)
    (measurable_gaussFam_pi hX' p).aemeasurable
  have e : (fun J : Finset I => P'.map fun ω => J.restrict fun i => gaussFam X' p i ω) =
      fun J => P.map fun ω => J.restrict fun i => gaussFam X p i ω := by
    funext J
    exact (map_eq_of_gaussian_vec (U := fun i : J => gaussFam X p i)
      (V := fun i : J => gaussFam X' p i)
      ((isGaussianProcess_gaussFam hX p).hasGaussianLaw J)
      ((isGaussianProcess_gaussFam hX' p).hasGaussianLaw J)
      (fun i => measurable_gaussFam hX p i) (fun i => measurable_gaussFam hX' p i)
      (fun i => memLp_gaussFam hX p i) (fun i => memLp_gaussFam hX' p i)
      (fun i => integral_gaussFam hX p i) (fun i => integral_gaussFam hX' p i)
      (fun i j => by rw [cov_gaussFam hX p i j, cov_gaussFam hX' p i j])).symm
  rw [e] at h2
  exact h1.unique h2

/-- Two pre-Brownian motions with measurable paths have the same path law. -/
theorem map_path_eq {W : ℝ≥0 → Ω → ℝ} {W' : ℝ≥0 → Ω' → ℝ} (hW : IsPreBrownianReal W P)
    (hW' : IsPreBrownianReal W' P') (hm : Measurable fun ω s => W s ω)
    (hm' : Measurable fun ω s => W' s ω) :
    P.map (fun ω s => W s ω) = P'.map (fun ω s => W' s ω) := by
  have h1 := isProjectiveLimit_map (P := P) (X := W) hm.aemeasurable
  have h2 := isProjectiveLimit_map (P := P') (X := W') hm'.aemeasurable
  have e1 : (fun I : Finset ℝ≥0 => P.map fun ω => I.restrict fun s => W s ω) =
      BrownianReal.projectiveFamily := funext fun I => (hW.hasLaw I).map_eq
  have e2 : (fun I : Finset ℝ≥0 => P'.map fun ω => I.restrict fun s => W' s ω) =
      BrownianReal.projectiveFamily := funext fun I => (hW'.hasLaw I).map_eq
  rw [e1] at h1
  rw [e2] at h2
  exact h1.unique h2

end CrossLaw

/-! ## 5. Coordinates in the closed unit half-disc -/

/-- The log-scale `(−log‖z‖)⁺` of a point. -/
def tau (z : ℂ) : ℝ≥0 := (-Real.log ‖z‖).toNNReal

theorem measurable_tau : Measurable tau :=
  (Real.measurable_log.comp measurable_norm).neg.real_toNNReal

theorem tau_coe {z : ℂ} (hz : ‖z‖ ≤ 1) : (tau z : ℝ) = -Real.log ‖z‖ :=
  Real.coe_toNNReal _ (neg_nonneg.2 (Real.log_nonpos (norm_nonneg z) hz))

theorem exp_neg_tau {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) : Real.exp (-(tau z : ℝ)) = ‖z‖ := by
  rw [tau_coe hz, neg_neg, Real.exp_log (norm_pos_iff.2 hz0)]

/-- Circles of `coordsFull` carried by the closed unit disc. -/
def BallCirc : Type := {n : ℕ // fcN n (closedBall (0 : ℂ) 1)ᶜ = 0}

/-- Test functions supported in the closed unit disc. -/
def BallTest : Type := {ρ : TestFun H // tsupport ρ.1 ⊆ closedBall (0 : ℂ) 1}

/-- Index set of the half-disc coordinates. -/
abbrev BallIdx : Type := BallCirc ⊕ BallTest

/-- Admissible measures carried by the closed unit disc. -/
def IsBallMeas (μ : Measure ℂ) : Prop := IsAdmissibleH μ ∧ μ (closedBall (0 : ℂ) 1)ᶜ = 0

theorem IsBallMeas.ae_mem {μ : Measure ℂ} (h : IsBallMeas μ) : ∀ᵐ z ∂μ, ‖z‖ ≤ 1 :=
  (ae_iff.2 h.2).mono fun z hz => by simpa using hz

theorem integrable_log_norm_adm {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    Integrable (fun z => Real.log ‖z‖) μ := by
  obtain ⟨hfin, ⟨K, hK, hKH, hμK⟩, C, hC, hbd⟩ := hμ
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hμR : μ (ballH (max R₀ 1))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun z hz =>
      ⟨closedBall_subset_closedBall (le_max_left _ _) (hR₀ hz), hKH hz⟩) hμK
  exact integrable_log_norm (le_max_right _ _) hμR hC (by simpa using hbd 0)

instance isProbabilityMeasure_fcN (n : ℕ) : IsProbabilityMeasure (fcN n) := by
  unfold fcN; infer_instance

/-- The constant part `α ∫ −log‖z‖ dμ`. -/
def Kc (α : ℝ) (μ : Measure ℂ) : ℝ := α * ∫ z, -Real.log ‖z‖ ∂μ

/-- The Brownian part `∫ w(τ z) dμ(z)`, read through dyadic Riemann sums. -/
def Jc (μ : Measure ℂ) (w : ℝ≥0 → ℝ) : ℝ := Jmod (μ.map tau) w

/-- The map (lateral coordinates, Brownian path) ↦ half-disc coordinates. -/
def Psi (α : ℝ) (p : (BallIdx → ℝ) × (ℝ≥0 → ℝ)) : BallIdx → ℝ :=
  Sum.elim (fun n => p.1 (.inl n) + Kc α (fcN n.1) + √2 * Jc (fcN n.1) p.2)
    (fun ρ => p.1 (.inr ρ) +
      (Kc α (CharFun.tdens ρ.1.1) - Kc α (CharFun.tdens fun z => -ρ.1.1 z)) +
      √2 * (Jc (CharFun.tdens ρ.1.1) p.2 - Jc (CharFun.tdens fun z => -ρ.1.1 z) p.2))

theorem measurable_Psi (α : ℝ) : Measurable (Psi α) := by
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with n | ρ
  · exact (((measurable_pi_apply _).comp measurable_fst).add_const _).add
      (((measurable_Jmod _).comp measurable_snd).const_mul _)
  · exact (((measurable_pi_apply _).comp measurable_fst).add_const _).add
      ((((measurable_Jmod _).comp measurable_snd).sub
        ((measurable_Jmod _).comp measurable_snd)).const_mul _)

/-! ## 6. Per-measure identities -/

section PerMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end PerMeasure

section PerMeasureZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

end PerMeasureZ

/-! ## 7. The restriction identity -/

section Main

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

end Main

end WedgeRes
end QuantumZipper
