/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeToolkit at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GaussianToolkit
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Regularization
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.LQG.Wedge
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant

/-!
# Wedge toolkit (blueprint `SECTION5_BLUEPRINT.md`, node B4 (a) and (d))

For a free-boundary GFF modulo constants `X`:

* (a1) the radial process `A_t = radAvgReg X e^{-t} − radAvgReg X 1` (`radialProc`) has a.s.
  continuous paths and is a centered Gaussian process with
  `Cov(A_s, A_t) = 2 min(s⁺,t⁺) + 2 min(s⁻,t⁻)`; equivalently `A_t = √2 B_t` (`t ≥ 0`) and
  `A_{-t} = √2 B'_t` for two independent standard Brownian motions (`radialBMpos`,
  `radialBMneg`).
* (a2) `indepFun_radialProc_lateralPart`: the path `A` is independent of the full coordinates
  (`coordsFull` jointly with the test pairings) of `lateralPart X`.
* (a3) `fieldLawFull_lateralPart_rescale`: `fieldLawFull H` of `lateralPart (rescale X Q a)`
  equals that of `lateralPart X`, for all `a > 0`.
* (d) `fieldLawFull_lateralPart_reflect`: the same for `RegClosure.reflectH` (`z ↦ −z̄`).

Route: every lateral coordinate is a.s. a pair difference `X(μ) − X(radSmear μ)` of the free
field (radial stochastic Fubini `ae_integral_radial`, regularization `ae_tendsto_integral_G`);
laws of such Gaussian families depend only on `kernelCov2` (`map_gaussFam_eq`), which is
invariant under `z ↦ a z` and `z ↦ −z̄` for balanced pairs, and the lateral/radial
cross-covariances vanish (`kernelCov2_lat_rad`).

Main tool: `exists_isRegVersion`, a jointly measurable regular witness `G` of `X` (every-circle
regularity, `RegularSample`) whose values agree a.s. with the raw folded-circle coordinates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace WedgeTK

open RegSample KolmD GaussTK CircleFubini

/-! ## 1. A jointly measurable regular version -/

section Modification

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A continuous modification of a measurable process on `ℝ⁴` can be chosen measurable in
`ω` at every parameter. -/
theorem exists_measurable_modification4 {Y V : (Fin 4 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun q => Y q ω) (hV : ∀ q, Measurable (V q))
    (hYV : ∀ q, (fun ω => Y q ω) =ᵐ[P] V q) :
    ∃ Y' : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y' q ω) ∧
      (∀ q, Measurable (Y' q)) ∧ (∀ᵐ ω ∂P, ∀ q, Y' q ω = Y q ω) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Fin 4 → ℝ)
  have hall : ∀ᵐ ω ∂P, ∀ s ∈ S, Y s ω = V s ω :=
    (eventually_countable_ball hSc).2 fun s _ => hYV s
  set N := {ω | ¬ ∀ s ∈ S, Y s ω = V s ω} with hN_def
  have hN : P N = 0 := ae_iff.1 hall
  set Ω₁ := (toMeasurable P N)ᶜ with hΩ₁_def
  have hΩ₁m : MeasurableSet Ω₁ := (measurableSet_toMeasurable P N).compl
  have hΩ₁ : ∀ ω ∈ Ω₁, ∀ s ∈ S, Y s ω = V s ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable P N h)
  have hΩ₁ae : ∀ᵐ ω ∂P, ω ∈ Ω₁ := by
    rw [ae_iff]
    have : {a | ¬ a ∈ Ω₁} = toMeasurable P N := by ext; simp [Ω₁]
    rw [this, measure_toMeasurable, hN]
  refine ⟨fun q ω => Ω₁.indicator (fun ω => Y q ω) ω, fun ω => ?_, fun q => ?_, ?_⟩
  · by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]; exact hYc ω
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]; exact continuous_const
  · have hq : q ∈ closure S := by rw [hSd.closure_eq]; exact Set.mem_univ q
    obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hq
    refine measurable_of_tendsto_metrizable (f := fun n ω => Ω₁.indicator (V (u n)) ω)
      (fun n => (hV (u n)).indicator hΩ₁m) ?_
    rw [tendsto_pi_nhds]; intro ω
    by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]
      have : ∀ n, V (u n) ω = Y (u n) ω := fun n => (hΩ₁ ω hω (u n) (huS n)).symm
      simp_rw [this]
      exact ((hYc ω).tendsto q).comp hu
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]
      exact tendsto_const_nhds
  · filter_upwards [hΩ₁ae] with ω hω q
    simp only [Set.indicator_of_mem hω]

end Modification

section RegVersion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- `G` is a regular version of the field `X`: continuous witnesses, measurable in `ω`,
almost surely regular witnesses of `X ω`, and a.s. equal to the raw circle coordinates at each
fixed circle. -/
structure IsRegVersion (X : Ω → FieldSample) (P : Measure Ω) (G : Ω → ℂ × ℝ → ℝ) : Prop where
  cont : ∀ ω, ContinuousOn (G ω) (Hbar ×ˢ Ioi 0)
  meas : ∀ q, Measurable fun ω => G ω q
  reg : ∀ᵐ ω ∂P, IsRegularWith (X ω) (G ω)
  raw : ∀ w ∈ Hbar, ∀ r : ℝ, 0 < r →
    (fun ω => G ω (w, r)) =ᵐ[P] fun ω => X ω (foldedCircle w r)

/-- **Regular version** of a free field (strengthening of `ae_isRegularSample`). -/
theorem exists_isRegVersion [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    ∃ G : Ω → ℂ × ℝ → ℝ, IsRegVersion X P G := by
  classical
  set V : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => X ω (nuQ q) with hV
  have hVm : ∀ q, AEMeasurable (V q) P := fun q => (hX.measurable_coord _).aemeasurable
  obtain ⟨W₀, hW₀c, hW₀V, hW₀lim⟩ := exists_continuous_modification_D (d := 4) le_rfl hVm
    fun R => ⟨_, mul_nonneg (pow_nonneg (by positivity) 8) (gaussianAbsMoment_nonneg 16),
      momentBound_nuQ hX R⟩
  obtain ⟨W, hWc, hWm, hWW₀⟩ := exists_measurable_modification4 hW₀c
    (fun q => hX.measurable_coord (nuQ q)) hW₀V
  have hWV : ∀ q, (fun ω => W q ω) =ᵐ[P] V q := fun q => by
    filter_upwards [hWW₀, hW₀V q] with ω h1 h2
    rw [h1 q]; exact h2
  have hWlim : ∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => V (rndD n q) ω) atTop (𝓝 (W q ω)) := by
    filter_upwards [hWW₀, hW₀lim] with ω h1 h2 q
    rw [h1 q]; exact h2 q
  -- the sets of parameters
  set S : Set (ℂ × ℝ) := Hbar ×ˢ Ioi 0 with hS
  set S3 : Set ((ℂ × ℝ) × ℝ) := S ×ˢ Ioi 0 with hS3
  have hpr3 : ∀ p ∈ S3, (0 : ℝ) < p.1.2 := fun p hp => hp.1.2
  have hWpr : ∀ ω, ContinuousOn (fun p : (ℂ × ℝ) × ℝ => W (pr p.1.1 p.1.2 p.2) ω)
      {p | 0 < p.1.2} := fun ω => (hWc ω).comp_continuousOn continuousOn_pr
  have hFc : ∀ ω, ContinuousOn (fun q : ℂ × ℝ => W (pr q.1 q.2 0) ω) S := fun ω =>
    (hWpr ω).comp (continuous_id.prodMk continuous_const).continuousOn fun q hq => hq.2
  -- the smoothed witness agrees with `W` almost surely at each point
  have hpt : ∀ p ∈ S3, ∀ᵐ ω ∂P, ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      W (pr p.1.1 p.1.2 p.2) ω := by
    rintro ⟨⟨w, r⟩, ρ⟩ ⟨⟨hw, hr⟩, hρ⟩
    simp only [mem_Ioi] at hr hρ
    show ∀ᵐ ω ∂P, ∫ u, W (pr u ρ 0) ω ∂foldedCircle w r = W (pr w r ρ) ω
    have hYc : ∀ ω, ContinuousOn (fun u => W (pr u ρ 0) ω - W (pr w ρ 0) ω) Hbar := fun ω =>
      (((hWc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
    have hY : ∀ u ∈ Hbar, (fun ω => W (pr u ρ 0) ω - W (pr w ρ 0) ω) =ᵐ[P]
        fun ω => X ω (foldedCircle u ρ) - X ω (foldedCircle w ρ) := by
      intro u hu
      filter_upwards [hWV (pr u ρ 0), hWV (pr w ρ 0)] with ω h1 h2
      simp only [h1, h2, hV, nuQ_pr_zero hu hρ, nuQ_pr_zero hw hρ]
    have hF := integral_fcAvg_ae_eq_bind_real hX hρ hw hYc hY (foldedCircle w r)
      (isCompact_ballH (‖w‖ + r)) inter_subset_right (foldedCircle_support hr.le le_rfl)
    filter_upwards [hF, hWV (pr w ρ 0), hWV (pr w r ρ)] with ω h1 h2 h3
    have hint : Integrable (fun u => W (pr u ρ 0) ω) (foldedCircle w r) :=
      RegClosure.integrable_fc ((hWc ω).comp (continuous_pr_fst ρ 0)).continuousOn w hr.le
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ,
      one_smul, measure_univ, one_smul] at h1
    simp only [hV] at h2 h3
    rw [nuQ_pr_zero hw hρ] at h2
    rw [h3, nuQ_pr hw hr hρ.le]
    linarith
  -- a countable dense set of parameters
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S3
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      W (pr p.1.1 p.1.2 p.2) ω :=
    (eventually_countable_ball hDc).2 fun p hp => hpt p (hDS hp)
  refine ⟨fun ω q => W (pr q.1 q.2 0) ω, hFc, fun q => hWm _, ?_, ?_⟩
  · filter_upwards [hWlim, hall] with ω hlim hD
    -- the smoothed witness equals `W` everywhere on `S3`
    have hG : ContinuousOn (fun p : (ℂ × ℝ) × ℝ =>
        ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2) S3 := by
      have hH : ContinuousOn (fun q : ((ℂ × ℝ) × ℝ) × ℂ => W (pr q.2 q.1.2 0) ω)
          (S3 ×ˢ Hbar) := by
        have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => ((q.2, q.1.2), (0 : ℝ)) := by
          fun_prop
        exact (hWpr ω).comp hm.continuousOn fun q hq => (show (0 : ℝ) < q.1.2 from hq.1.2)
      exact RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ)
        (H := fun p u => W (pr u p.2 0) ω) (c := fun p => p.1.1) (r := fun p => p.1.2) hH
        (continuous_fst.comp continuous_fst).continuousOn
        (continuous_snd.comp continuous_fst).continuousOn
    have hEq : EqOn (fun p : (ℂ × ℝ) × ℝ => ∫ u, W (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2)
        (fun p => W (pr p.1.1 p.1.2 p.2) ω) S3 :=
      eqOn_of_dense hDS hSD hG ((hWpr ω).mono fun p hp => hpr3 p hp) fun p hp => hD p hp
    refine ⟨hFc ω, fun k z hz => ?_, ?_⟩
    · -- clause (i)
      have h := hlim (pr z (radius k) 0)
      simp only [rndD_pr, hV] at h
      have e : ∀ n, nuQ (pr (dyadicRoundC n z) (radius k) 0) =
          foldedCircle (dyadicRoundC n z) (radius k) := fun n =>
        nuQ_pr_zero (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k)
      simp only [e] at h
      exact h
    · -- clause (ii)
      have hΦ : ContinuousOn (fun p : (ℂ × ℝ) × ℝ => W (pr p.1.1 p.1.2 p.2) ω)
          (S ×ˢ Ici 0) := (hWpr ω).mono fun p hp => hp.1.2
      refine RegClosure.tluo_of_dist_le (tluo_of_continuousOn hΦ) ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
      have := hEq (show (q, ρ) ∈ S3 from ⟨hq, hρ⟩)
      simp only at this
      simp only [this, le_refl]
  · intro w hw r hr
    filter_upwards [hWV (pr w r 0)] with ω h
    simp only [h, hV, nuQ_pr_zero hw hr]

end RegVersion

/-! ## 2. Semicircle averages about `0` on regular samples -/

/-- The dyadic radii `(m+1)/2^n` read by `radAvgReg`. -/
def dyRad (n m : ℕ) : ℝ := ((m : ℝ) + 1) / 2 ^ n

theorem dyRad_pos (n m : ℕ) : 0 < dyRad n m := by unfold dyRad; positivity

theorem tendsto_one_div_two_pow : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  refine (tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2))).congr fun n => ?_
  simp [one_div]

/-- `radAvgReg` along a regular witness that also represents the raw values at the dyadic
radii about `0`. -/
theorem radAvgReg_eq_of_regular {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hraw : ∀ n m : ℕ, x (foldedCircle 0 (dyRad n m)) = F (0, dyRad n m)) {r : ℝ}
    (hr : 0 < r) : radAvgReg x r = F (0, r) := by
  have hs : ∀ n : ℕ, dyadicRound n r + radius n = dyRad n (⌊(2 : ℝ) ^ n * r⌋.toNat) := by
    intro n
    rw [CoordsFull.radAvg_radius_eq_div, dyRad]
    have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
    have : ((⌊(2 : ℝ) ^ n * r⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * r⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; push_cast; ring
  have hlim : Tendsto (fun n : ℕ => dyadicRound n r + radius n) atTop (𝓝 r) := by
    have h1 : Tendsto (fun n : ℕ => dyadicRound n r) atTop (𝓝 r) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n r)
        tendsto_one_div_two_pow
    have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
      tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
    simpa using h1.add h2
  have hmem : ∀ n : ℕ, ((0 : ℂ), dyadicRound n r + radius n) ∈ Hbar ×ˢ Ioi (0 : ℝ) := fun n =>
    ⟨zero_mem_Hbar, by rw [hs n]; exact dyRad_pos _ _⟩
  have ht : Tendsto (fun n : ℕ => ((0 : ℂ), dyadicRound n r + radius n)) atTop
      (𝓝[Hbar ×ˢ Ioi 0] ((0 : ℂ), r)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hlim, Eventually.of_forall hmem⟩
  have hc := (hF.1 ((0 : ℂ), r) ⟨zero_mem_Hbar, hr⟩).tendsto.comp ht
  unfold radAvgReg
  have e : (fun n : ℕ => x (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun n => F ((0 : ℂ), dyadicRound n r + radius n) := by
    funext n; rw [hs n]; exact hraw n _
  rw [e]; exact hc.limUnder_eq

/-- Good samples: regular with witness `F`, which also gives the raw dyadic semicircle
values about `0`. -/
def GoodRad (x : FieldSample) (F : ℂ × ℝ → ℝ) : Prop :=
  IsRegularWith x F ∧ ∀ n m : ℕ, x (foldedCircle 0 (dyRad n m)) = F (0, dyRad n m)

theorem GoodRad.radAvgReg_eq {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : GoodRad x F) {r : ℝ}
    (hr : 0 < r) : radAvgReg x r = F (0, r) :=
  radAvgReg_eq_of_regular h.1 h.2 hr

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
  {G : Ω → ℂ × ℝ → ℝ}

theorem IsRegVersion.ae_good (hG : IsRegVersion X P G) : ∀ᵐ ω ∂P, GoodRad (X ω) (G ω) := by
  have h2 : ∀ᵐ ω ∂P, ∀ n m : ℕ, X ω (foldedCircle 0 (dyRad n m)) = G ω (0, dyRad n m) := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro m
    filter_upwards [hG.raw 0 zero_mem_Hbar _ (dyRad_pos n m)] with ω h
    exact h.symm
  filter_upwards [hG.reg, h2] with ω h1 h2' using ⟨h1, h2'⟩

theorem measurable_radAvgReg (hX : IsFreeGFFModConstH X P) (r : ℝ) :
    Measurable fun ω => radAvgReg (X ω) r := by
  unfold radAvgReg
  exact (StronglyMeasurable.limUnder fun n => (hX.measurable_coord _).stronglyMeasurable).measurable

end Good

/-! ## 3. The radial process -/

/-- The radial process `A_t = h_{e^{-t}}(0) − h_1(0)` of a random field. -/
def radialProc {Ω : Type*} (X : Ω → FieldSample) (t : ℝ) (ω : Ω) : ℝ :=
  radAvgReg (X ω) (Real.exp (-t)) - radAvgReg (X ω) 1

/-- `(√2)⁻¹ A_t`, `t ≥ 0`. -/
def radialBMpos {Ω : Type*} (X : Ω → FieldSample) : ℝ≥0 → Ω → ℝ :=
  fun s ω => (√2)⁻¹ * radialProc X s ω

/-- `(√2)⁻¹ A_{-t}`, `t ≥ 0`. -/
def radialBMneg {Ω : Type*} (X : Ω → FieldSample) : ℝ≥0 → Ω → ℝ :=
  fun s ω => (√2)⁻¹ * radialProc X (-(s : ℝ)) ω

/-- The good index of the radial increment `fc(0, e^{-t}) − fc(0, 1)`. -/
def radIdx (t : ℝ) : {p : FcIdx // p.Good} :=
  ⟨((0 : ℂ), Real.exp (-t), (0 : ℂ), 1), zero_mem_Hbar, Real.exp_pos _, zero_mem_Hbar, one_pos⟩

theorem kernelCov_fc0 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    kernelCov neumannH (foldedCircle 0 a) (foldedCircle 0 b) = -2 * Real.log (max a b) := by
  have := kernelCov_fc_real_sameCenter (s := 0) ha hb
  simpa using this

theorem max_exp_neg_one (s : ℝ) : max (Real.exp (-s)) 1 = Real.exp (max (-s) 0) := by
  rcases le_total (-s) 0 with h | h
  · rw [max_eq_right h, Real.exp_zero, max_eq_right (by simpa using Real.exp_le_exp.2 h)]
  · rw [max_eq_left h, max_eq_left (by simpa using Real.exp_le_exp.2 h)]

theorem radial_cov_algebra (s t : ℝ) :
    -2 * max (-s) (-t) + 2 * max (-s) 0 + 2 * max (-t) 0 =
      2 * min (max s 0) (max t 0) + 2 * min (max (-s) 0) (max (-t) 0) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem fcPairCov_radIdx (s t : ℝ) :
    fcPairCov (radIdx s).1 (radIdx t).1 =
      2 * min (max s 0) (max t 0) + 2 * min (max (-s) 0) (max (-t) 0) := by
  simp only [radIdx, fcPairCov, kernelCov2]
  rw [kernelCov_fc0 (Real.exp_pos _) (Real.exp_pos _), kernelCov_fc0 (Real.exp_pos _) one_pos,
    kernelCov_fc0 one_pos (Real.exp_pos _), kernelCov_fc0 one_pos one_pos, max_self,
    Real.log_one, max_exp_neg_one, max_comm 1, max_exp_neg_one,
    ← Real.exp_monotone.map_max, Real.log_exp, Real.log_exp, Real.log_exp,
    ← radial_cov_algebra]
  ring

theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f f' g g' : Ω → ℝ}
    (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') : cov[f, g; P] = cov[f', g'; P] := by
  unfold covariance
  rw [integral_congr_ae hf, integral_congr_ae hg]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with ω h1 h2
  rw [h1, h2]

section Radial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
  {G : Ω → ℂ × ℝ → ℝ}

theorem radialProc_ae_eq (hG : IsRegVersion X P G) (t : ℝ) :
    radialProc X t =ᵐ[P] fcPairVal X (radIdx t).1 := by
  filter_upwards [hG.ae_good, hG.raw 0 zero_mem_Hbar _ (Real.exp_pos (-t)),
    hG.raw 0 zero_mem_Hbar 1 one_pos] with ω hg h1 h2
  simp only [radialProc, fcPairVal, radIdx]
  rw [hg.radAvgReg_eq (Real.exp_pos _), hg.radAvgReg_eq one_pos, h1, h2]

theorem measurable_radialProc (hX : IsFreeGFFModConstH X P) (t : ℝ) :
    Measurable (radialProc X t) :=
  (measurable_radAvgReg hX _).sub (measurable_radAvgReg hX _)

/-- (a1) The radial process has almost surely continuous paths on `ℝ`. -/
theorem ae_continuous_radialProc [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, Continuous fun t => radialProc X t ω := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  filter_upwards [hG.ae_good] with ω hg
  have e : (fun t => radialProc X t ω) =
      fun t => G ω ((0 : ℂ), Real.exp (-t)) - G ω (0, 1) := by
    funext t; simp only [radialProc]
    rw [hg.radAvgReg_eq (Real.exp_pos _), hg.radAvgReg_eq one_pos]
  rw [e]
  refine Continuous.sub ?_ continuous_const
  exact (hG.cont ω).comp_continuous
    (continuous_const.prodMk (Real.continuous_exp.comp continuous_neg))
    fun t => ⟨zero_mem_Hbar, Real.exp_pos _⟩

/-- (a1) The radial process is a Gaussian process. -/
theorem isGaussianProcess_radialProc [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    IsGaussianProcess (radialProc X) P := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  refine ((isGaussianProcess_fcPair hX).comp_right radIdx).congr fun t => ?_
  exact (radialProc_ae_eq hG t).symm

/-- (a1) The radial process is centered. -/
theorem integral_radialProc [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (t : ℝ) :
    ∫ ω, radialProc X t ω ∂P = 0 := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  rw [integral_congr_ae (radialProc_ae_eq hG t)]
  exact integral_fcPairVal hX (radIdx t).2

/-- (a1) Covariance of the radial process: two independent Brownian motions of
diffusivity `2` on `t ≥ 0` and on `t ≤ 0`. -/
theorem covariance_radialProc [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (s t : ℝ) :
    cov[radialProc X s, radialProc X t; P] =
      2 * min (max s 0) (max t 0) + 2 * min (max (-s) 0) (max (-t) 0) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  rw [covariance_congr_ae (radialProc_ae_eq hG s) (radialProc_ae_eq hG t),
    covariance_fcPairVal hX (radIdx s).2 (radIdx t).2, fcPairCov_radIdx]

theorem inv_sqrt_two_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]

theorem cov_scaled_radial [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (s t : ℝ) :
    cov[fun ω => (√2)⁻¹ * radialProc X s ω, fun ω => (√2)⁻¹ * radialProc X t ω; P] =
      min (max s 0) (max t 0) + min (max (-s) 0) (max (-t) 0) := by
  rw [covariance_const_mul_left, covariance_const_mul_right, covariance_radialProc hX,
    ← mul_assoc, inv_sqrt_two_mul_self]
  ring

theorem integral_scaled_radial [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (t : ℝ) :
    ∫ ω, (√2)⁻¹ * radialProc X t ω ∂P = 0 := by
  rw [integral_const_mul, integral_radialProc hX, mul_zero]

/-- (a1) `(√2)⁻¹ A_t`, `t ≥ 0`, is a standard Brownian motion. -/
theorem isBrownianReal_radialBMpos [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    IsBrownianReal (radialBMpos X) P where
  toIsPreBrownianReal := by
    refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
    · have h := ((isGaussianProcess_radialProc hX).comp_right
        (fun s : ℝ≥0 => (s : ℝ))).smul (fun _ => (√2)⁻¹)
      exact h
    · intro t; exact integral_scaled_radial hX t
    · intro s t hst
      have hs : (0 : ℝ) ≤ s := s.2
      have ht : (0 : ℝ) ≤ t := t.2
      have hst' : (s : ℝ) ≤ t := hst
      show cov[fun ω => (√2)⁻¹ * radialProc X s ω, fun ω => (√2)⁻¹ * radialProc X t ω; P] = s
      rw [cov_scaled_radial hX, max_eq_left hs, max_eq_left ht,
        max_eq_right (neg_nonpos.2 hs), max_eq_right (neg_nonpos.2 ht), min_eq_left hst',
        min_self, add_zero]
  cont := by
    filter_upwards [ae_continuous_radialProc hX] with ω h
    exact continuous_const.mul (h.comp NNReal.continuous_coe)

/-- (a1) `(√2)⁻¹ A_{-t}`, `t ≥ 0`, is a standard Brownian motion. -/
theorem isBrownianReal_radialBMneg [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    IsBrownianReal (radialBMneg X) P where
  toIsPreBrownianReal := by
    refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
    · have h := ((isGaussianProcess_radialProc hX).comp_right
        (fun s : ℝ≥0 => -(s : ℝ))).smul (fun _ => (√2)⁻¹)
      exact h
    · intro t; exact integral_scaled_radial hX _
    · intro s t hst
      have hs : (0 : ℝ) ≤ s := s.2
      have ht : (0 : ℝ) ≤ t := t.2
      have hst' : (s : ℝ) ≤ t := hst
      show cov[fun ω => (√2)⁻¹ * radialProc X (-(s : ℝ)) ω,
        fun ω => (√2)⁻¹ * radialProc X (-(t : ℝ)) ω; P] = s
      rw [cov_scaled_radial hX, neg_neg, neg_neg, max_eq_left hs, max_eq_left ht,
        max_eq_right (neg_nonpos.2 hs), max_eq_right (neg_nonpos.2 ht), min_eq_left hst',
        min_self, zero_add]
  cont := by
    filter_upwards [ae_continuous_radialProc hX] with ω h
    exact continuous_const.mul (h.comp (NNReal.continuous_coe.neg))

/-- (a1) The two halves of the radial process are independent. -/
theorem indepFun_radialBM [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) :
    IndepFun (pathOf (radialBMpos X)) (pathOf (radialBMneg X)) P := by
  have hG : IsGaussianProcess (Sum.elim (radialBMpos X) (radialBMneg X)) P := by
    have h := ((isGaussianProcess_radialProc hX).comp_right
      (Sum.elim (fun s : ℝ≥0 => (s : ℝ)) (fun s : ℝ≥0 => -(s : ℝ)))).smul (fun _ => (√2)⁻¹)
    refine h.congr fun i => ?_
    cases i <;> exact ae_of_all _ fun ω => rfl
  refine hG.indepFun_of_covariance_eq_zero
    (fun s => (measurable_const.mul (measurable_radialProc hX _)).aemeasurable)
    (fun t => (measurable_const.mul (measurable_radialProc hX _)).aemeasurable)
    fun s t => ?_
  have hs : (0 : ℝ) ≤ s := s.2
  have ht : (0 : ℝ) ≤ t := t.2
  show cov[fun ω => (√2)⁻¹ * radialProc X s ω,
    fun ω => (√2)⁻¹ * radialProc X (-(t : ℝ)) ω; P] = 0
  rw [cov_scaled_radial hX, neg_neg, max_eq_left hs, max_eq_right (neg_nonpos.2 ht),
    max_eq_right (neg_nonpos.2 hs), max_eq_left ht, min_eq_right hs, min_eq_left ht]
  ring

omit [MeasurableSpace Ω] in
/-- The radial process is `√2` times the two Brownian motions. -/
theorem radialProc_eq_pos (t : ℝ≥0) (ω : Ω) : radialProc X t ω = √2 * radialBMpos X t ω := by
  simp only [radialBMpos, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 two_pos), one_mul]

omit [MeasurableSpace Ω] in
theorem radialProc_eq_neg (t : ℝ≥0) (ω : Ω) :
    radialProc X (-(t : ℝ)) ω = √2 * radialBMneg X t ω := by
  simp only [radialBMneg, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 two_pos), one_mul]

end Radial

/-! ## 4. Measure identities for folded circles -/

theorem fc_foldH_eq (v : ℂ) (s : ℝ) : foldedCircle (foldH v) s = foldedCircle v s :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
    RegClosure.integral_fc_foldH f.continuous.continuousOn v s

theorem measurable_mul_left' (b : ℝ) : Measurable fun u : ℂ => (b : ℂ) * u :=
  measurable_const.mul measurable_id

theorem measurable_neg_conj : Measurable fun u : ℂ => -conj u :=
  Complex.continuous_conj.neg.measurable

theorem fc_map_mul (c : ℂ) (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (foldedCircle c s).map (fun u => (b : ℂ) * u) = foldedCircle ((b : ℂ) * c) (b * s) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (measurable_mul_left' b).aemeasurable f.continuous.aestronglyMeasurable]
  exact RegClosure.integral_fc_comp_mul (g := fun u => f u) f.continuous.continuousOn c s hb

theorem fc_map_neg_conj (c : ℂ) (s : ℝ) :
    (foldedCircle c s).map (fun u => -conj u) = foldedCircle (-conj c) s := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map measurable_neg_conj.aemeasurable f.continuous.aestronglyMeasurable]
  exact RegClosure.integral_fc_comp_neg_conj (g := fun u => f u) f.continuous.continuousOn c s

theorem measurable_fc_radius (c : ℂ) : Measurable (fun r : ℝ => foldedCircle c r) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hcont : Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    unfold circleMap; fun_prop
  have hg : Measurable (fun p : ℝ × ℝ => foldH (circleMap c p.1 p.2)) :=
    measurable_foldH.comp hcont.measurable
  have h := (measurable_measure_prodMk_left (ν := volume.restrict (Set.Ico 0 (2 * π))) (hg hs))
  convert h.const_mul ((ENNReal.ofReal (2 * π))⁻¹) using 1
  funext r
  rw [foldedCircle, Measure.map_apply measurable_foldH hs, circleUnif, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap c r) (measurable_foldH hs), smul_eq_mul]
  rfl

theorem fc_ae_norm {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂foldedCircle 0 r, ‖x‖ = r := by
  rw [foldedCircle, ae_map_iff measurable_foldH.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  filter_upwards [KernelId.ae_norm_sub_center 0 hr] with x hx
  rw [norm_foldH']; simpa using hx

/-! ## 5. Radial smearing -/

/-- The radial kernel `z ↦ foldedCircle 0 ‖z‖` (semicircle about `0` through `z`). -/
def radKernel : ProbabilityTheory.Kernel ℂ ℂ where
  toFun z := foldedCircle 0 ‖z‖
  measurable' := (measurable_fc_radius 0).comp measurable_norm

instance : IsMarkovKernel radKernel :=
  ⟨fun z => by show IsProbabilityMeasure (foldedCircle 0 ‖z‖); infer_instance⟩

/-- The radial smearing `∫ foldedCircle 0 ‖z‖ dμ(z)` of `μ`: pairing with it reads
`∫ h_{‖z‖}(0) dμ(z)`. -/
def radSmear (μ : Measure ℂ) : Measure ℂ := μ.bind fun z => foldedCircle 0 ‖z‖

theorem radSmear_apply (μ : Measure ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    radSmear μ A = ∫⁻ z, foldedCircle 0 ‖z‖ A ∂μ :=
  Measure.bind_apply hA radKernel.measurable.aemeasurable

theorem radSmear_univ (μ : Measure ℂ) : radSmear μ univ = μ univ := by
  rw [radSmear_apply μ MeasurableSet.univ]; simp

instance isFiniteMeasure_radSmear (μ : Measure ℂ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (radSmear μ) :=
  ⟨by rw [radSmear_univ]; exact measure_lt_top _ _⟩

theorem integral_radSmear (μ : Measure ℂ) [IsFiniteMeasure μ] {F : ℂ → ℝ}
    (hF : Integrable F (radSmear μ)) :
    Integrable (fun z => ∫ x, F x ∂foldedCircle 0 ‖z‖) μ ∧
      ∫ x, F x ∂(radSmear μ) = ∫ z, ∫ x, F x ∂foldedCircle 0 ‖z‖ ∂μ := by
  change Integrable F (radKernel ∘ₘ μ) at hF
  change Integrable (fun z => ∫ x, F x ∂radKernel z) μ ∧
    ∫ x, F x ∂(radKernel ∘ₘ μ) = ∫ z, ∫ x, F x ∂radKernel z ∂μ
  rw [Measure.comp_eq_comp_const_apply] at hF ⊢
  refine ⟨?_, ?_⟩
  · simpa using hF.integral_comp
  · rw [ProbabilityTheory.Kernel.integral_comp hF]; simp

theorem radSmear_support {μ : Measure ℂ} {R : ℝ} (hμ : μ (ballH R)ᶜ = 0) :
    radSmear μ (ballH R)ᶜ = 0 := by
  rw [radSmear_apply μ (measurableSet_ballH R).compl]
  have hae : ∀ᵐ z ∂μ, z ∈ ballH R := mem_ae_iff.mpr hμ
  have : ∀ᵐ z ∂μ, foldedCircle 0 ‖z‖ (ballH R)ᶜ = 0 := hae.mono fun z hz =>
    foldedCircle_support (norm_nonneg z) (by
      have := hz.1; rw [mem_closedBall, dist_zero_right] at this; simpa using this)
  rw [lintegral_congr_ae this, lintegral_zero]

theorem potConst_le {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    potConst r ≤ (Real.log 2 + 2 * Real.posLog R) + max 0 (-Real.log r) := by
  unfold potConst
  have h1 : Real.posLog r ≤ Real.posLog R := Real.posLog_le_posLog (by linarith) hrR
  have h2 : -Real.log r ≤ max 0 (-Real.log r) := le_max_right _ _
  linarith

/-- Admissible measures supported in `ballH R`, with a finite log-potential at `0`. -/
theorem radSmear_pot {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hμ : μ (ballH R)ᶜ = 0) (h0 : μ {0} = 0) {C : ℝ≥0∞}
    (hC : ∫⁻ x, ENNReal.ofReal (-Real.log ‖x‖) ∂μ ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂radSmear μ ≤
      2 * (ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R) * μ univ + C) := by
  have hk : Measurable (fun z : ℂ => foldedCircle 0 ‖z‖) :=
    (measurable_fc_radius 0).comp measurable_norm
  rw [radSmear, Measure.lintegral_bind hk.aemeasurable (measurable_logPot y).aemeasurable]
  have hae : ∀ᵐ z ∂μ, z ∈ ballH R ∧ z ≠ 0 := by
    filter_upwards [mem_ae_iff.mpr hμ, (measure_eq_zero_iff_ae_notMem.1 h0)] with z h1 h2
    exact ⟨h1, h2⟩
  calc ∫⁻ z, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle 0 ‖z‖ ∂μ
      ≤ ∫⁻ z, 2 * (ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R) +
          ENNReal.ofReal (-Real.log ‖z‖)) ∂μ := by
        refine lintegral_mono_ae (hae.mono fun z hz => ?_)
        have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz.2
        have hzR : ‖z‖ ≤ R := by
          have := hz.1.1; rwa [mem_closedBall, dist_zero_right] at this
        have key : ENNReal.ofReal (potConst ‖z‖) ≤
            ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R) + ENNReal.ofReal (-Real.log ‖z‖) := by
          refine (ENNReal.ofReal_le_ofReal (potConst_le hz0 hzR)).trans ?_
          refine (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ?_)
          rw [CircleFubini.ofReal_max_zero]
        exact (foldedCircle_pot_le hz0 0 y).trans (mul_le_mul_of_nonneg_left key zero_le)
    _ = 2 * (ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R) * μ univ +
          ∫⁻ z, ENNReal.ofReal (-Real.log ‖z‖) ∂μ) := by
        rw [lintegral_const_mul (f := fun z : ℂ => ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R)
            + ENNReal.ofReal (-Real.log ‖z‖)) _ (measurable_const.add
          (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp measurable_norm).neg)),
          lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := by gcongr

theorem isAdmissibleH_radSmear {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleH (radSmear μ) := by
  have h0 := noAtoms_of_isAdmissibleH hμ 0
  obtain ⟨hfin, ⟨K, hK, hKH, hμK⟩, C, hC, hbd⟩ := hμ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hμR : μ (ballH R)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun z hz => ⟨hR hz, hKH hz⟩) hμK
  have hC0 : ∫⁻ x, ENNReal.ofReal (-Real.log ‖x‖) ∂μ ≤ C := by simpa using hbd 0
  refine admissible_of_bounds (radSmear_support hμR) ?_ (radSmear_pot hμR h0 hC0)
  exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _), hC.ne⟩)

/-- Linearity of `kernelCov neumannH` in the first measure under radial smearing. -/
theorem kernelCov_radSmear (μ : Measure ℂ) [IsFiniteMeasure μ] {R : ℝ}
    (hS : radSmear μ (ballH R)ᶜ = 0)
    {μ' : Measure ℂ} [IsFiniteMeasure μ'] (hμ' : μ' (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ' ≤ C) :
    Integrable (fun z => kernelCov neumannH (foldedCircle 0 ‖z‖) μ') μ ∧
      ∫ z, kernelCov neumannH (foldedCircle 0 ‖z‖) μ' ∂μ
        = kernelCov neumannH (radSmear μ) μ' := by
  have hint := integrable_neumannH hS hμ' hCt hC
  have hF : Integrable (fun x => ∫ y, neumannH x y ∂μ') (radSmear μ) :=
    hint.integral_prod_left
  obtain ⟨h1, h2⟩ := integral_radSmear μ hF
  exact ⟨h1, h2.symm⟩

/-- Pairing with a semicircle about `0` on the right. -/
theorem kernelCov_fc0_right (ν : Measure ℂ) {a : ℝ} (ha : 0 < a) :
    kernelCov neumannH ν (foldedCircle 0 a) = ∫ x, -2 * Real.log (max a ‖x‖) ∂ν := by
  unfold kernelCov
  congr 1; funext x
  rw [KernelId.integral_neumannH_foldedCircle_right' 0 x ha]
  simp only [KernelId.fcPot, zero_sub, norm_neg, Complex.norm_conj]
  ring

/-! ## 6. Measurability of lateral coordinates -/

theorem measurable_dyadicRound' (n : ℕ) : Measurable (dyadicRound n) := by
  unfold dyadicRound
  exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
    (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))

theorem countable_range_radRound (n : ℕ) :
    (Set.range fun r : ℝ => dyadicRound n r + radius n).Countable := by
  have hsub : (Set.range fun r : ℝ => dyadicRound n r + radius n) ⊆
      Set.range (fun m : ℤ => (m : ℝ) / (2 : ℝ) ^ n + radius n) := by
    rintro _ ⟨r, rfl⟩
    exact ⟨⌊(2 : ℝ) ^ n * r⌋, rfl⟩
  exact (Set.countable_range _).mono hsub

theorem measurable_eval_radRound (n : ℕ) :
    Measurable (fun p : FieldSample × ℝ =>
      p.1 (foldedCircle 0 (dyadicRound n p.2 + radius n))) := by
  set g : ℝ → ℝ := fun r => dyadicRound n r + radius n with hg
  have hgm : Measurable g := (measurable_dyadicRound' n).add_const _
  have : Countable (Set.range g) := (countable_range_radRound n).to_subtype
  intro T hT
  have key : (fun p : FieldSample × ℝ => p.1 (foldedCircle 0 (g p.2))) ⁻¹' T
      = ⋃ d : Set.range g,
          {x : FieldSample | x (foldedCircle 0 (d : ℝ)) ∈ T} ×ˢ (g ⁻¹' ({(d : ℝ)} : Set ℝ)) := by
    ext ⟨x, r⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hmem
      exact ⟨⟨g r, Set.mem_range_self r⟩, hmem, rfl⟩
    · rintro ⟨d, hmem, hdz⟩
      rwa [hdz]
  show MeasurableSet ((fun p : FieldSample × ℝ => p.1 (foldedCircle 0 (g p.2))) ⁻¹' T)
  rw [key]
  refine MeasurableSet.iUnion fun d => MeasurableSet.prod ?_ ?_
  · exact measurable_pi_apply (foldedCircle 0 (d : ℝ)) hT
  · exact hgm (measurableSet_singleton _)

theorem measurable_radAvgReg₂ : Measurable (fun p : FieldSample × ℝ => radAvgReg p.1 p.2) := by
  unfold radAvgReg
  exact (StronglyMeasurable.limUnder fun n =>
    (measurable_eval_radRound n).stronglyMeasurable).measurable

theorem measurable_lateralPart_apply (μ : Measure ℂ) [SFinite μ] :
    Measurable fun x : FieldSample => lateralPart x μ := by
  unfold lateralPart
  refine (measurable_evalReg μ).sub ?_
  exact (StronglyMeasurable.integral_prod_right' (ν := μ)
    (measurable_radAvgReg₂.comp (measurable_fst.prodMk
      (measurable_norm.comp measurable_snd))).stronglyMeasurable).measurable

/-- The part of a field sample seen by the regularized evaluations: its values at finite
measures. -/
def finPart (x : FieldSample) : FieldSample := {μ : Measure ℂ | IsFiniteMeasure μ}.indicator x

theorem finPart_fc (x : FieldSample) (c : ℂ) (r : ℝ) :
    finPart x (foldedCircle c r) = x (foldedCircle c r) :=
  Set.indicator_of_mem (show IsFiniteMeasure (foldedCircle c r) from inferInstance) x

theorem avgReg_finPart (x : FieldSample) : avgReg (finPart x) = avgReg x := by
  funext k z; unfold avgReg; simp only [finPart_fc]

theorem radAvgReg_finPart (x : FieldSample) : radAvgReg (finPart x) = radAvgReg x := by
  funext r; unfold radAvgReg; simp only [finPart_fc]

theorem evalReg_finPart (x : FieldSample) : evalReg (finPart x) = evalReg x := by
  funext ν; unfold evalReg; rw [avgReg_finPart]

theorem lateralPart_finPart (x : FieldSample) : lateralPart (finPart x) = lateralPart x := by
  funext μ; unfold lateralPart; rw [evalReg_finPart, radAvgReg_finPart]

theorem measurable_finPart {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    (hY : ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => Y ω μ) :
    Measurable fun ω => finPart (Y ω) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases hμ : IsFiniteMeasure μ
  · simp only [finPart, Set.indicator_of_mem (show μ ∈ {μ : Measure ℂ | IsFiniteMeasure μ}
      from hμ)]
    exact hY μ hμ
  · simp only [finPart, Set.indicator_of_notMem (show μ ∉ {μ : Measure ℂ | IsFiniteMeasure μ}
      from hμ)]
    exact measurable_const

theorem measurable_lateral_of {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    (hY : ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => Y ω μ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] : Measurable fun ω => lateralPart (Y ω) μ := by
  have e : (fun ω => lateralPart (Y ω) μ) =
      (fun x => lateralPart x μ) ∘ (fun ω => finPart (Y ω)) := by
    funext ω; simp [lateralPart_finPart]
  rw [e]; exact (measurable_lateralPart_apply μ).comp (measurable_finPart hY)

/-! ## 7. Regularization at a fixed radius and along `c · 2^{-k}` -/

section RegFixed

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

theorem IsRegVersion.continuousOn_slice (hG : IsRegVersion X P G) (ω : Ω) {r : ℝ}
    (hr : 0 < r) : ContinuousOn (fun u => G ω (u, r)) Hbar :=
  (hG.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn fun _ hu => ⟨hu, hr⟩

/-- Stochastic Fubini for the regular version at a fixed radius. -/
theorem ae_integral_G_eq (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) {r : ℝ}
    (hr : 0 < r) (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ν Kᶜ = 0) :
    ∀ᵐ ω ∂P, ∫ u, G ω (u, r) ∂ν = X ω (ν.bind fun w => foldedCircle w r) := by
  have hYc : ∀ ω, ContinuousOn (fun u => G ω (u, r) - G ω (0, r)) Hbar := fun ω =>
    (hG.continuousOn_slice ω hr).sub continuousOn_const
  have hY : ∀ u ∈ Hbar, (fun ω => G ω (u, r) - G ω (0, r)) =ᵐ[P]
      fun ω => X ω (foldedCircle u r) - X ω (foldedCircle 0 r) := by
    intro u hu
    filter_upwards [hG.raw u hu r hr, hG.raw 0 zero_mem_Hbar r hr] with ω h1 h2
    rw [h1, h2]
  have hF := integral_fcAvg_ae_eq_bind_real hX hr zero_mem_Hbar hYc hY ν hK hKH hνK
  set c := foldedCircle (0 : ℂ) r with hc
  set m : ℝ≥0 := (ν Set.univ).toNNReal with hm_def
  have hm : ν Set.univ = (m : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top ν _)).symm
  have hadm : IsAdmissibleH c := isAdmissibleH_foldedCircle zero_mem_Hbar hr
  have hlin := hX.linear c c hadm hadm m 0
  have hsm : ν Set.univ • c = m • c + (0 : ℝ≥0) • c := by
    rw [zero_smul, add_zero, hm]
    exact (ENNReal.smul_def m c).symm
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
  filter_upwards [hF, hlin, hG.raw 0 zero_mem_Hbar r hr] with ω h2 h3 h4
  have hYi : Integrable (fun z => G ω (z, r)) ν := by
    have : IntegrableOn (fun z => G ω (z, r)) K ν :=
      ((hG.continuousOn_slice ω hr).mono hKH).integrableOn_compact hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  have e1 : ∫ z, G ω (z, r) ∂ν =
      ∫ z, (G ω (z, r) - G ω (0, r)) ∂ν + (ν Set.univ).toReal * G ω (0, r) := by
    rw [integral_sub hYi (integrable_const _), integral_const, smul_eq_mul, measureReal_def]
    ring
  rw [e1, h2, hsm, h3, h4, hm]
  simp only [ENNReal.coe_toReal, NNReal.coe_zero, zero_mul, add_zero]
  ring

theorem sq_c_radius (c : ℝ) (n : ℕ) : (c * radius n) ^ 2 = c ^ 2 * (4⁻¹ : ℝ) ^ n := by
  unfold radius
  rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
  norm_num

/-- Almost sure convergence `X ν_{c 2^{-k}} → X ν` for a good measure at positive height. -/
theorem ae_tendsto_smooth_c (hX : IsFreeGFFModConstH X P) {M : ℝ≥0} {R δ : ℝ} (hδ : 0 < δ)
    {ν : Measure ℂ} (hν : SmoothConv.IsGoodSC M R ν) (him : ∀ᵐ w ∂ν, δ < w.im) {c : ℝ}
    (hc : 0 < c) :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (ν.bind fun w => foldedCircle w (c * radius k))) atTop
      (𝓝 (X ω ν)) := by
  have hrad : Tendsto (fun k : ℕ => c * radius k) atTop (𝓝 0) := by
    simpa using (tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).const_mul c
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds (lt_min hδ one_pos)))
  set C : ℝ := 2 * ((M : ℝ) * (2 * π) * (ν Set.univ).toReal) * c ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  set sd : ℕ → Ω → ℝ := fun k ω =>
    X ω (ν.bind fun w => foldedCircle w (c * radius k)) - X ω ν with hsd
  have hmeas : ∀ k, Measurable (sd k) := fun k =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (sd (k + k₀) ω ^ 2) with hf
  have hfm : ∀ k, Measurable (f k) := fun k => ((hmeas (k + k₀)).pow_const 2).ennreal_ofReal
  have hbound : ∀ k, ∫⁻ ω, f k ω ∂P ≤ ENNReal.ofReal C * ENNReal.ofReal 4⁻¹ ^ k := by
    intro k
    have hk := hk₀ (k + k₀) (by omega)
    have hr : 0 < c * radius (k + k₀) := mul_pos hc (radius_pos _)
    have hr1 : c * radius (k + k₀) ≤ 1 := hk.le.trans (min_le_right _ _)
    have i1 : ∀ᵐ w ∂ν, c * radius (k + k₀) ≤ w.im :=
      him.mono fun w hw => (hk.le.trans (min_le_left _ _)).trans hw.le
    have ga := hν.bind_fc hr.le hr1 i1
    have mA : (ν.bind fun w => foldedCircle w (c * radius (k + k₀))) Set.univ = ν Set.univ :=
      SmoothConv.bind_fc_univ ν _
    have hint : Integrable (fun ω => sd (k + k₀) ω ^ 2) P :=
      (SmoothConv.memLp_pair_sc hX ga.isAdmissibleH hν.isAdmissibleH mA).integrable_sq
    have c1 := hX.covariance_eq ((ν.bind fun w => foldedCircle w (c * radius (k + k₀))), ν)
      ((ν.bind fun w => foldedCircle w (c * radius (k + k₀))), ν) ga.isAdmissibleH
      hν.isAdmissibleH mA ga.isAdmissibleH hν.isAdmissibleH mA
    dsimp only at c1
    have hm := hX.centered _ _ ga.isAdmissibleH hν.isAdmissibleH mA
    have key : ∫ ω, sd (k + k₀) ω ^ 2 ∂P = cov[sd (k + k₀), sd (k + k₀); P] := by
      unfold covariance
      simp only [hsd]
      rw [hm]
      simp only [sub_zero, sq]
    have h2 : ∫ ω, sd (k + k₀) ω ^ 2 ∂P ≤ C * (4⁻¹ : ℝ) ^ (k + k₀) := by
      rw [key]
      simp only [hsd]
      rw [c1]
      refine (le_abs_self _).trans
        ((Regularization.abs_energy_single_le hr hr1 hν i1).trans (le_of_eq ?_))
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity),
        sq_c_radius, hCdef]
      ring
    calc ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, sd (k + k₀) ω ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * (4⁻¹ : ℝ) ^ k) := by
          refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = ENNReal.ofReal C * ENNReal.ofReal 4⁻¹ ^ k := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by norm_num)]
  have hsum : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun k => (hfm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    refine (tsub_pos_of_lt ?_).ne'
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  have hae := ae_lt_top' (AEMeasurable.tsum fun k => (hfm k).aemeasurable) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => sd (k + k₀) ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [f, Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun k => sd (k + k₀) ω) atTop (𝓝 0) := by
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h4
    exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h4
  rw [← tendsto_add_atTop_iff_nat k₀]
  have h5 := h3.add_const (X ω ν)
  simp only [sd, sub_add_cancel, zero_add] at h5
  exact h5

/-- The smoothed integrals of the regular version converge to the raw coordinate along
`c · 2^{-k}`. -/
theorem ae_tendsto_integral_G (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    {M : ℝ≥0} {R δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ} (hν : SmoothConv.IsGoodSC M R ν)
    (him : ∀ᵐ w ∂ν, δ < w.im) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ u, G ω (u, c * radius k) ∂ν) atTop (𝓝 (X ω ν)) := by
  have := hν.isFiniteMeasure
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ u, G ω (u, c * radius k) ∂ν =
      X ω (ν.bind fun w => foldedCircle w (c * radius k)) :=
    ae_all_iff.2 fun k => ae_integral_G_eq hX hG (mul_pos hc (radius_pos k)) ν hK
      Set.inter_subset_right hν.2
  filter_upwards [h1, ae_tendsto_smooth_c hX hδ hν him hc] with ω h1 h2
  simp only [h1]
  exact h2

end RegFixed

/-! ## 8. `L²` Fubini with an integrable variance bound, and the radial stochastic Fubini -/

section AbstractFubini'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν] {Z : α → Ω → ℝ}
  {b : α → ℝ}

theorem integrable_sq_prod' (hZ : Measurable (Function.uncurry Z))
    (hmom : ∀ᵐ z ∂ν, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ᵐ z ∂ν, ∫ ω, Z z ω ^ 2 ∂P ≤ b z) (hb : Integrable b ν) :
    Integrable (fun p : α × Ω => Z p.1 p.2 ^ 2) (ν.prod P) := by
  have hm : Measurable (fun p : α × Ω => Z p.1 p.2 ^ 2) := hZ.pow_const 2
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨hmom, ?_⟩
  refine Integrable.mono' hb hm.norm.aestronglyMeasurable.integral_prod_right'
    (hB.mono fun z hz => ?_)
  have h1 : ∀ ω, ‖Z z ω ^ 2‖ = Z z ω ^ 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [h1]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  exact hz

theorem fubini_mul' (hZ : Measurable (Function.uncurry Z))
    (hmom : ∀ᵐ z ∂ν, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ᵐ z ∂ν, ∫ ω, Z z ω ^ 2 ∂P ≤ b z) (hb : Integrable b ν) {g : Ω → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 P) :
    ∫ ω, (∫ z, Z z ω ∂ν) * g ω ∂P = ∫ z, ∫ ω, Z z ω * g ω ∂P ∂ν := by
  have hsq := integrable_sq_prod' hZ hmom hB hb
  have hgsq : Integrable (fun ω => g ω ^ 2) P := hg2.integrable_sq
  have hg2' : Integrable (fun p : α × Ω => g p.2 ^ 2) (ν.prod P) := by
    have hm : Measurable (fun p : α × Ω => g p.2 ^ 2) := (hg.comp measurable_snd).pow_const 2
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    exact ⟨ae_of_all _ fun _ => hgsq, integrable_const (∫ y, ‖g y ^ 2‖ ∂P)⟩
  have hint : Integrable (fun p : α × Ω => Z p.1 p.2 * g p.2) (ν.prod P) := by
    refine Integrable.mono' ((hsq.add hg2').div_const 2)
      ((hZ.mul (hg.comp measurable_snd)).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|Z p.1 p.2| - |g p.2|), sq_abs (Z p.1 p.2), sq_abs (g p.2)]
  calc ∫ ω, (∫ z, Z z ω ∂ν) * g ω ∂P = ∫ ω, ∫ z, Z z ω * g ω ∂ν ∂P := by
        congr 1; funext ω; rw [integral_mul_const]
    _ = ∫ z, ∫ ω, Z z ω * g ω ∂P ∂ν :=
        (integral_integral_swap (f := fun z ω => Z z ω * g ω) hint).symm

theorem memLp_integral' (hZ : Measurable (Function.uncurry Z))
    (hmom : ∀ᵐ z ∂ν, Integrable (fun ω => Z z ω ^ 2) P)
    (hB : ∀ᵐ z ∂ν, ∫ ω, Z z ω ^ 2 ∂P ≤ b z) (hb : Integrable b ν) :
    Measurable (fun ω => ∫ z, Z z ω ∂ν) ∧ MemLp (fun ω => ∫ z, Z z ω ∂ν) 2 P ∧
      ∀ᵐ ω ∂P, Integrable (fun z => Z z ω) ν := by
  have hsq := integrable_sq_prod' hZ hmom hB hb
  have hLm : Measurable (fun ω => ∫ z, Z z ω ∂ν) :=
    (hZ.stronglyMeasurable.integral_prod_left (μ := ν)).measurable
  have h2 : ∀ᵐ ω ∂P, Integrable (fun z => Z z ω ^ 2) ν := hsq.prod_left_ae
  have hZω : ∀ ω, Measurable fun z => Z z ω := fun ω => hZ.of_uncurry_right
  have h1 : ∀ᵐ ω ∂P, Integrable (fun z => Z z ω) ν := h2.mono fun ω hω =>
    ((memLp_two_iff_integrable_sq (hZω ω).aestronglyMeasurable).2 hω).integrable one_le_two
  refine ⟨hLm, ?_, h1⟩
  rw [memLp_two_iff_integrable_sq hLm.aestronglyMeasurable]
  have hbound : Integrable (fun ω => (ν Set.univ).toReal * ∫ z, Z z ω ^ 2 ∂ν) P :=
    hsq.integral_prod_right.const_mul _
  refine Integrable.mono' hbound (hLm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact CircleFubini.sq_integral_le' hω1 hω2

end AbstractFubini'

theorem integrable_log_norm {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ} (hR : 1 ≤ R)
    (hμR : μ (ballH R)ᶜ = 0) {C : ℝ≥0∞} (hC : C < ⊤)
    (hC0 : ∫⁻ x, ENNReal.ofReal (-Real.log ‖x‖) ∂μ ≤ C) :
    Integrable (fun z => Real.log ‖z‖) μ := by
  have hm : Measurable fun z : ℂ => Real.log ‖z‖ := Real.measurable_log.comp measurable_norm
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hae : ∀ᵐ z ∂μ, z ∈ ballH R := mem_ae_iff.mpr hμR
  calc ∫⁻ z, ‖Real.log ‖z‖‖ₑ ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal (-Real.log ‖z‖) + ENNReal.ofReal (Real.log R)) ∂μ := by
        refine lintegral_mono_ae (hae.mono fun z hz => ?_)
        have hzR : ‖z‖ ≤ R := by
          have := hz.1; rwa [mem_closedBall, dist_zero_right] at this
        have hlog : Real.log ‖z‖ ≤ Real.log R := by
          rcases (norm_nonneg z).eq_or_lt with h | h
          · rw [← h, Real.log_zero]; exact Real.log_nonneg hR
          · exact Real.log_le_log h hzR
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (Real.log ‖z‖) with h | h
        · rw [abs_of_nonneg h]; exact le_add_left (ENNReal.ofReal_le_ofReal hlog)
        · rw [abs_of_nonpos h]; exact le_self_add
    _ = ∫⁻ z, ENNReal.ofReal (-Real.log ‖z‖) ∂μ + ENNReal.ofReal (Real.log R) * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hC0.trans_lt hC,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem kernelCov2_radPair {s : ℝ} (hs : 0 < s) :
    kernelCov2 neumannH (foldedCircle 0 s, foldedCircle 0 1)
        (foldedCircle 0 s, foldedCircle 0 1) =
      -2 * Real.log s + 4 * Real.log (max s 1) := by
  simp only [kernelCov2]
  rw [kernelCov_fc0 hs hs, kernelCov_fc0 hs one_pos, kernelCov_fc0 one_pos hs,
    kernelCov_fc0 one_pos one_pos, max_self, max_self, Real.log_one, max_comm 1 s]
  ring

section RadialFubini

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Radial stochastic Fubini.** For an admissible `μ`, almost surely the radial profile of
the regular version is `μ`-integrable and `∫ h_{‖z‖}(0) dμ(z) = X (radSmear μ)`. -/
theorem ae_integral_radial (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∀ᵐ ω ∂P, Integrable (fun z => G ω (0, ‖z‖)) μ ∧
      ∫ z, G ω (0, ‖z‖) ∂μ = X ω (radSmear μ) := by
  have h0 := noAtoms_of_isAdmissibleH hμ 0
  have hrSA := isAdmissibleH_radSmear hμ
  obtain ⟨hfin, ⟨K, hK, hKH, hμK⟩, C, hC, hbd⟩ := hμ
  haveI := hfin
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R := max R₀ 1 with hR_def
  have hR1 : 1 ≤ R := le_max_right _ _
  have hμR : μ (ballH R)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun z hz =>
      ⟨closedBall_subset_closedBall (le_max_left _ _) (hR₀ hz), hKH hz⟩) hμK
  have hC0 : ∫⁻ x, ENNReal.ofReal (-Real.log ‖x‖) ∂μ ≤ C := by simpa using hbd 0
  have hlogI := integrable_log_norm hR1 hμR hC hC0
  -- measures
  set rS := radSmear μ with hrS
  set c1 := foldedCircle (0 : ℂ) 1 with hc1
  set μ₀ := μ Set.univ • c1 with hμ₀
  have : IsFiniteMeasure μ₀ := isFiniteMeasure_smul' _ (measure_ne_top _ _) _
  have hc1A : IsAdmissibleH c1 := isAdmissibleH_foldedCircle zero_mem_Hbar one_pos
  have hc1S : c1 (ballH R)ᶜ = 0 := foldedCircle_support zero_le_one (by simpa using hR1)
  have hrSS : rS (ballH R)ᶜ = 0 := radSmear_support hμR
  have hCrs_ne : 2 * (ENNReal.ofReal (Real.log 2 + 2 * Real.posLog R) * μ univ + C) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _), hC.ne⟩)
  have hrSP := radSmear_pot hμR h0 hC0
  have hC1_ne : 2 * ENNReal.ofReal (potConst 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hc1P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂c1 ≤
      2 * ENNReal.ofReal (potConst 1) := fun y => foldedCircle_pot_le one_pos 0 y
  have h0S : μ₀ (ballH R)ᶜ = 0 := by rw [hμ₀, Measure.smul_apply, hc1S, smul_zero]
  have h0P : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ₀ ≤
      μ Set.univ * (2 * ENNReal.ofReal (potConst 1)) := smul_pot hc1P
  have hμC1 : μ Set.univ * (2 * ENNReal.ofReal (potConst 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) hC1_ne
  have h0A : IsAdmissibleH μ₀ := admissible_of_bounds h0S hμC1 h0P
  have h0U : μ₀ Set.univ = μ Set.univ := by
    rw [hμ₀, Measure.smul_apply, measure_univ (μ := c1), smul_eq_mul, mul_one]
  have hqU : rS Set.univ = μ₀ Set.univ := by rw [hrS, radSmear_univ, h0U]
  -- circles of radius `‖z‖`
  have hfcS : ∀ z ∈ ballH R, foldedCircle 0 ‖z‖ (ballH R)ᶜ = 0 := fun z hz =>
    foldedCircle_support (norm_nonneg z) (by
      have := hz.1; rw [mem_closedBall, dist_zero_right] at this; simpa using this)
  have hfcA : ∀ z : ℂ, z ≠ 0 → IsAdmissibleH (foldedCircle 0 ‖z‖) := fun z hz =>
    isAdmissibleH_foldedCircle zero_mem_Hbar (norm_pos_iff.2 hz)
  have hgood : ∀ᵐ z ∂μ, z ∈ ballH R ∧ z ≠ 0 := by
    filter_upwards [mem_ae_iff.mpr hμR, measure_eq_zero_iff_ae_notMem.1 h0] with z h1 h2
    exact ⟨h1, h2⟩
  -- the random variables
  set At : ℝ → Ω → ℝ := fun t ω => G ω (0, Real.exp (-t)) - G ω (0, 1) with hAt
  have hAtc : ∀ ω, Continuous fun t => At t ω := fun ω =>
    ((hG.cont ω).comp_continuous
      (continuous_const.prodMk (Real.continuous_exp.comp continuous_neg))
      fun t => ⟨zero_mem_Hbar, Real.exp_pos _⟩).sub continuous_const
  have hAtm : ∀ t, Measurable (At t) := fun t => (hG.meas _).sub (hG.meas _)
  have hAtJ : Measurable (Function.uncurry At) :=
    measurable_uncurry_of_continuous_of_measurable hAtc hAtm
  set Z : ℂ → Ω → ℝ := fun z ω => At (-Real.log ‖z‖) ω with hZdef
  have hZm : Measurable (Function.uncurry Z) :=
    hAtJ.comp (((Real.measurable_log.comp measurable_norm).neg.comp measurable_fst).prodMk
      measurable_snd)
  have hZeq : ∀ z : ℂ, z ≠ 0 → ∀ ω, Z z ω = G ω (0, ‖z‖) - G ω (0, 1) := fun z hz ω => by
    simp only [hZdef, hAt, neg_neg, Real.exp_log (norm_pos_iff.2 hz)]
  set W : ℂ → Ω → ℝ := fun z ω => X ω (foldedCircle 0 ‖z‖) - X ω c1 with hWdef
  have hZW : ∀ z : ℂ, z ≠ 0 → Z z =ᵐ[P] W z := fun z hz => by
    filter_upwards [hG.raw 0 zero_mem_Hbar ‖z‖ (norm_pos_iff.2 hz),
      hG.raw 0 zero_mem_Hbar 1 one_pos] with ω h1 h2
    rw [hZeq z hz ω, h1, h2]
  set D : Ω → ℝ := fun ω => X ω rS - X ω μ₀ with hD
  have hDm : Measurable D := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have h11 : ∀ z : ℂ, (foldedCircle 0 ‖z‖) Set.univ = c1 Set.univ := fun z => by simp [hc1]
  have hWL2 : ∀ z : ℂ, z ≠ 0 → MemLp (W z) 2 P := fun z hz =>
    gff_memLp (p := (foldedCircle 0 ‖z‖, c1)) hX (hfcA z hz) hc1A (h11 z)
  have hDL2 : MemLp D 2 P := gff_memLp (p := (rS, μ₀)) hX hrSA h0A hqU
  have hZL2 : ∀ z : ℂ, z ≠ 0 → MemLp (Z z) 2 P := fun z hz =>
    (hWL2 z hz).ae_eq (hZW z hz).symm
  -- second moments
  have hEWW : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 → ∫ ω, W z ω * W z' ω ∂P =
      kernelCov2 neumannH (foldedCircle 0 ‖z‖, c1) (foldedCircle 0 ‖z'‖, c1) :=
    fun z z' hz hz' =>
      gff_integral_mul (p := (foldedCircle 0 ‖z‖, c1)) (q := (foldedCircle 0 ‖z'‖, c1)) hX
        (hfcA z hz) hc1A (h11 z) (hfcA z' hz') hc1A (h11 z')
  have hEWD : ∀ z : ℂ, z ≠ 0 → ∫ ω, W z ω * D ω ∂P =
      kernelCov2 neumannH (foldedCircle 0 ‖z‖, c1) (rS, μ₀) := fun z hz =>
    gff_integral_mul (p := (foldedCircle 0 ‖z‖, c1)) (q := (rS, μ₀)) hX (hfcA z hz) hc1A
      (h11 z) hrSA h0A hqU
  have hEDW : ∀ z : ℂ, z ≠ 0 → ∫ ω, D ω * W z ω ∂P =
      kernelCov2 neumannH (rS, μ₀) (foldedCircle 0 ‖z‖, c1) := fun z hz =>
    gff_integral_mul (p := (rS, μ₀)) (q := (foldedCircle 0 ‖z‖, c1)) hX hrSA h0A hqU
      (hfcA z hz) hc1A (h11 z)
  have hEDD : ∫ ω, D ω * D ω ∂P = kernelCov2 neumannH (rS, μ₀) (rS, μ₀) :=
    gff_integral_mul (p := (rS, μ₀)) (q := (rS, μ₀)) hX hrSA h0A hqU hrSA h0A hqU
  -- the variance bound
  set b : ℂ → ℝ := fun z => 2 * |Real.log ‖z‖| + 4 * Real.log R with hb
  have hbI : Integrable b μ := (hlogI.abs.const_mul 2).add (integrable_const _)
  have hB : ∀ᵐ z ∂μ, ∫ ω, Z z ω ^ 2 ∂P ≤ b z := hgood.mono fun z hz => by
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz.2
    have hzR : ‖z‖ ≤ R := by have := hz.1.1; rwa [mem_closedBall, dist_zero_right] at this
    have e1 : ∫ ω, Z z ω ^ 2 ∂P = ∫ ω, W z ω * W z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZW z hz.2] with ω hω
      rw [hω, sq]
    rw [e1, hEWW z z hz.2 hz.2, kernelCov2_radPair hz0]
    have h1 : Real.log (max ‖z‖ 1) ≤ Real.log R :=
      Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le hzR hR1)
    have h2 : -Real.log ‖z‖ ≤ |Real.log ‖z‖| := neg_le_abs _
    simp only [hb]; linarith
  have hmom : ∀ᵐ z ∂μ, Integrable (fun ω => Z z ω ^ 2) P :=
    hgood.mono fun z hz => (hZL2 z hz.2).integrable_sq
  -- linearity of the covariance under radial smearing
  have hsmul : ∀ μ' : Measure ℂ, kernelCov neumannH μ₀ μ' =
      (μ Set.univ).toReal * kernelCov neumannH c1 μ' := by
    intro μ'; simp only [kernelCov, hμ₀, integral_smul_measure, smul_eq_mul]
  have hlin2 : ∀ (a b' : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b'],
      a (ballH R)ᶜ = 0 → b' (ballH R)ᶜ = 0 → ∀ {Ca Cb : ℝ≥0∞}, Ca ≠ ⊤ → Cb ≠ ⊤ →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ Ca) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b' ≤ Cb) →
      ∫ z, kernelCov2 neumannH (foldedCircle 0 ‖z‖, c1) (a, b') ∂μ
        = kernelCov2 neumannH (rS, μ₀) (a, b') := by
    intro a b' _ _ ha hb' Ca Cb hCa hCb hPa hPb
    obtain ⟨ia, ea⟩ := kernelCov_radSmear μ hrSS ha hCa hPa
    obtain ⟨ib, eb⟩ := kernelCov_radSmear μ hrSS hb' hCb hPb
    simp only [kernelCov2]
    rw [integral_add (f := fun z => kernelCov neumannH (foldedCircle 0 ‖z‖) a
          - kernelCov neumannH (foldedCircle 0 ‖z‖) b' - kernelCov neumannH c1 a)
        (g := fun _ => kernelCov neumannH c1 b')
        ((ia.sub ib).sub (integrable_const _)) (integrable_const _),
      integral_sub (f := fun z => kernelCov neumannH (foldedCircle 0 ‖z‖) a
          - kernelCov neumannH (foldedCircle 0 ‖z‖) b')
        (g := fun _ => kernelCov neumannH c1 a) (ia.sub ib) (integrable_const _),
      integral_sub ia ib, ea, eb,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hsmul, hsmul]
  -- `L = ∫ Z z dμ`
  obtain ⟨hLm, hLL2, hLint⟩ := memLp_integral' hZm hmom hB hbI
  set L : Ω → ℝ := fun ω => ∫ z, Z z ω ∂μ with hL_def
  have hZmz : ∀ z, Measurable (Z z) := fun z => hZm.of_uncurry_left
  have hZD : ∀ z : ℂ, z ≠ 0 → ∫ ω, Z z ω * D ω ∂P
      = kernelCov2 neumannH (foldedCircle 0 ‖z‖, c1) (rS, μ₀) := by
    intro z hz
    rw [← hEWD z hz]
    refine integral_congr_ae ?_
    filter_upwards [hZW z hz] with ω hω
    rw [hω]
  have E1 : ∫ ω, L ω * D ω ∂P = kernelCov2 neumannH (rS, μ₀) (rS, μ₀) := by
    rw [fubini_mul' hZm hmom hB hbI hDm hDL2]
    calc ∫ z, ∫ ω, Z z ω * D ω ∂P ∂μ
        = ∫ z, kernelCov2 neumannH (foldedCircle 0 ‖z‖, c1) (rS, μ₀) ∂μ :=
          integral_congr_ae (hgood.mono fun z hz => hZD z hz.2)
      _ = _ := hlin2 rS μ₀ hrSS h0S hCrs_ne hμC1 hrSP h0P
  have E2 : ∫ ω, L ω * L ω ∂P = ∫ ω, L ω * D ω ∂P := by
    rw [fubini_mul' hZm hmom hB hbI hLm hLL2, fubini_mul' hZm hmom hB hbI hDm hDL2]
    refine integral_congr_ae (hgood.mono fun z hz => ?_)
    show ∫ ω, Z z ω * L ω ∂P = ∫ ω, Z z ω * D ω ∂P
    have i1 : ∫ ω, Z z ω * L ω ∂P = ∫ ω, L ω * Z z ω ∂P := by simp_rw [mul_comm]
    rw [i1, fubini_mul' hZm hmom hB hbI (hZmz z) (hZL2 z hz.2)]
    calc ∫ z', ∫ ω, Z z' ω * Z z ω ∂P ∂μ
        = ∫ z', kernelCov2 neumannH (foldedCircle 0 ‖z'‖, c1)
            (foldedCircle 0 ‖z‖, c1) ∂μ := by
          refine integral_congr_ae (hgood.mono fun z' hz' => ?_)
          show ∫ ω, Z z' ω * Z z ω ∂P =
            kernelCov2 neumannH (foldedCircle 0 ‖z'‖, c1) (foldedCircle 0 ‖z‖, c1)
          rw [← hEWW z' z hz'.2 hz.2]
          refine integral_congr_ae ?_
          filter_upwards [hZW z hz.2, hZW z' hz'.2] with ω hω hω'
          rw [hω, hω']
      _ = kernelCov2 neumannH (rS, μ₀) (foldedCircle 0 ‖z‖, c1) :=
          hlin2 _ _ (hfcS z hz.1) hc1S (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
            hC1_ne (fun y => foldedCircle_pot_le (norm_pos_iff.2 hz.2) 0 y) hc1P
      _ = ∫ ω, Z z ω * D ω ∂P := by
          rw [← hEDW z hz.2]
          refine integral_congr_ae ?_
          filter_upwards [hZW z hz.2] with ω hω
          rw [hω, mul_comm]
  -- conclusion: `E[(L - D)²] = 0`
  have hsq : ∫ ω, (L ω - D ω) ^ 2 ∂P = 0 := by
    have : ∀ ω, (L ω - D ω) ^ 2 = (L ω * L ω - 2 * (L ω * D ω)) + D ω * D ω := fun ω => by
      ring
    simp_rw [this]
    have iLL := integrable_mul_of_memLp_two hLL2 hLL2
    have iLD := integrable_mul_of_memLp_two hLL2 hDL2
    have iDD := integrable_mul_of_memLp_two hDL2 hDL2
    rw [integral_add (f := fun ω => L ω * L ω - 2 * (L ω * D ω)) (g := fun ω => D ω * D ω)
        (iLL.sub (iLD.const_mul 2)) iDD,
      integral_sub (f := fun ω => L ω * L ω) (g := fun ω => 2 * (L ω * D ω)) iLL
        (iLD.const_mul 2),
      integral_const_mul, E2, E1, hEDD]
    ring
  have hint : Integrable (fun ω => (L ω - D ω) ^ 2) P := (hLL2.sub hDL2).integrable_sq
  have hzero := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (L ω - D ω)) hint).1 hsq
  -- linearity of `X` for the constant
  set mm : ℝ≥0 := (μ Set.univ).toNNReal with hmm_def
  have hmm : μ Set.univ = (mm : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top μ _)).symm
  have hlin := hX.linear c1 c1 hc1A hc1A mm 0
  have hsm : μ Set.univ • c1 = mm • c1 + (0 : ℝ≥0) • c1 := by
    rw [zero_smul, add_zero, hmm]
    exact (ENNReal.smul_def mm c1).symm
  filter_upwards [hzero, hLint, hlin, hG.raw 0 zero_mem_Hbar 1 one_pos] with ω hω hωi h3 h4
  have hLD : L ω = D ω := by
    have h2 : (L ω - D ω) ^ 2 = 0 := hω
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
    linarith
  have hGeq : (fun z => G ω (0, ‖z‖)) =ᵐ[μ] fun z => Z z ω + G ω (0, 1) :=
    hgood.mono fun z hz => by
      show G ω (0, ‖z‖) = Z z ω + G ω (0, 1)
      rw [hZeq z hz.2 ω]; ring
  have hGi : Integrable (fun z => G ω (0, ‖z‖)) μ :=
    (hωi.add (integrable_const _)).congr hGeq.symm
  refine ⟨hGi, ?_⟩
  rw [integral_congr_ae hGeq, integral_add hωi (integrable_const _), integral_const,
    smul_eq_mul, measureReal_def]
  have e2 : ∫ z, Z z ω ∂μ = L ω := rfl
  rw [e2, hLD]
  show X ω rS - X ω μ₀ + (μ Set.univ).toReal * G ω (0, 1) = X ω rS
  rw [hμ₀, hsm, h3, h4, hmm]
  simp only [ENNReal.coe_toReal, NNReal.coe_zero, zero_mul, add_zero]
  ring

end RadialFubini

/-! ## 9. Laws of Gaussian families of pair differences -/

/-- Balanced admissible pairs: the index set of the free field modulo constants. -/
abbrev BPair : Type :=
  {p : Measure ℂ × Measure ℂ // IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}

/-- The pair differences `X(p.1) − X(p.2)` along a family of balanced pairs. -/
def gaussFam {Ω : Type*} (X : Ω → FieldSample) {I : Type*} (p : I → BPair) (i : I) (ω : Ω) : ℝ :=
  X ω (p i).1.1 - X ω (p i).1.2

section GaussLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem isGaussianProcess_gaussFam (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) :
    IsGaussianProcess (gaussFam X p) P :=
  hX.gaussian.comp_right p

theorem measurable_gaussFam (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) (i : I) :
    Measurable (gaussFam X p i) :=
  (hX.measurable_coord _).sub (hX.measurable_coord _)

theorem memLp_gaussFam (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) (i : I) :
    MemLp (gaussFam X p i) 2 P :=
  ((isGaussianProcess_gaussFam hX p).hasGaussianLaw_eval i).memLp_two

theorem integral_gaussFam (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) (i : I) :
    ∫ ω, gaussFam X p i ω ∂P = 0 :=
  hX.centered _ _ (p i).2.1 (p i).2.2.1 (p i).2.2.2

theorem cov_gaussFam (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) (i j : I) :
    cov[gaussFam X p i, gaussFam X p j; P] = kernelCov2 neumannH (p i).1 (p j).1 :=
  hX.covariance_eq (p i).1 (p j).1 (p i).2.1 (p i).2.2.1 (p i).2.2.2 (p j).2.1 (p j).2.2.1
    (p j).2.2.2

theorem measurable_gaussFam_pi (hX : IsFreeGFFModConstH X P) {I : Type*} (p : I → BPair) :
    Measurable (fun ω i => gaussFam X p i ω) :=
  measurable_pi_iff.2 fun i => measurable_gaussFam hX p i

/-- Laws of Gaussian families of pair differences depend only on their covariances. -/
theorem map_gaussFam_eq (hX : IsFreeGFFModConstH X P) {I : Type*} (p q : I → BPair)
    (hpq : ∀ i j, kernelCov2 neumannH (p i).1 (p j).1 = kernelCov2 neumannH (q i).1 (q j).1) :
    P.map (fun ω i => gaussFam X p i ω) = P.map (fun ω i => gaussFam X q i ω) := by
  classical
  refine (map_eq_iff_forall_finset_map_restrict_eq (measurable_gaussFam_pi hX p).aemeasurable
    (measurable_gaussFam_pi hX q).aemeasurable).2 fun J => ?_
  have hmJ : ∀ r : I → BPair, Measurable fun ω => J.restrict fun i => gaussFam X r i ω :=
    fun r => measurable_pi_iff.2 fun j => measurable_gaussFam hX r j
  have key : ∀ r : I → BPair, IsGaussian (P.map fun ω => J.restrict fun i => gaussFam X r i ω) :=
    fun r => ((isGaussianProcess_gaussFam hX r).hasGaussianLaw J).isGaussian_map
  have hmean : ∀ r : I → BPair,
      (P.map fun ω => J.restrict fun i => gaussFam X r i ω)[id] = 0 := by
    intro r
    rw [integral_map (hmJ r).aemeasurable aestronglyMeasurable_id]
    funext j
    simp only [id, Pi.zero_apply]
    show (∫ x, (fun j : J => gaussFam X r j x) ∂P) j = 0
    rw [eval_integral (fun j : J => (memLp_gaussFam hX r j).integrable one_le_two)]
    exact integral_gaussFam hX r j
  have hL : ∀ (r : I → BPair) (L : StrongDual ℝ (J → ℝ)),
      (L ∘ fun ω => J.restrict fun i => gaussFam X r i ω) =
        fun ω => ∑ i : J, (L fun k => if i = k then 1 else 0) * gaussFam X r i ω := by
    intro r L; funext ω
    simp only [Function.comp_apply]
    rw [show L (J.restrict fun i => gaussFam X r i ω) =
      L.toLinearMap (J.restrict fun i => gaussFam X r i ω) from rfl,
      LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, Finset.restrict]
    rw [mul_comm]; rfl
  have hcov : ∀ (r : I → BPair) (L₁ L₂ : StrongDual ℝ (J → ℝ)),
      covarianceBilinDual (P.map fun ω => J.restrict fun i => gaussFam X r i ω) L₁ L₂ =
        ∑ i : J, ∑ j : J, (L₁ fun k => if i = k then 1 else 0) *
          (L₂ fun k => if j = k then 1 else 0) * kernelCov2 neumannH (r i).1 (r j).1 := by
    intro r L₁ L₂
    haveI := key r
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covariance_map L₁.continuous.aestronglyMeasurable L₂.continuous.aestronglyMeasurable
        (hmJ r).aemeasurable, hL r L₁, hL r L₂,
      covariance_fun_sum_fun_sum (fun i : J => (memLp_gaussFam hX r i).const_mul _)
        (fun j : J => (memLp_gaussFam hX r j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, cov_gaussFam hX r i j]
    ring
  haveI := key p
  haveI := key q
  refine IsGaussian.ext_covarianceBilinDual ?_ ?_
  · rw [hmean p, hmean q]
  · ext L₁ L₂
    rw [hcov p, hcov q]
    simp only [hpq]

end GaussLaw

/-! ## 10. Invariance of the Neumann covariance under `z ↦ b z` and `z ↦ −z̄` -/

theorem neumannH_neg_conj (x y : ℂ) : neumannH (-conj x) (-conj y) = neumannH x y := by
  unfold neumannH
  have e1 : ‖-conj x - -conj y‖ = ‖x - y‖ := by
    rw [show -conj x - -conj y = -conj (x - y) by rw [map_sub]; ring, norm_neg,
      Complex.norm_conj]
  have e2 : ‖-conj x - conj (-conj y)‖ = ‖x - conj y‖ := by
    rw [map_neg, Complex.conj_conj, show -conj x - -y = y - conj x by ring,
      ← norm_sub_conj_comm x y]
  rw [e1, e2]

theorem kernelCov_map_gen {f : ℂ → ℂ} (hf : Measurable f) (μ ν : Measure ℂ) [SFinite ν] :
    kernelCov neumannH (μ.map f) (ν.map f) = ∫ x, ∫ y, neumannH (f x) (f y) ∂ν ∂μ := by
  unfold kernelCov
  have hΦ : StronglyMeasurable (fun x => ∫ y, neumannH x y ∂(ν.map f)) :=
    StronglyMeasurable.integral_prod_right' (f := fun p : ℂ × ℂ => neumannH p.1 p.2)
      measurable_neumannH.stronglyMeasurable
  rw [integral_map hf.aemeasurable hΦ.aestronglyMeasurable]
  congr 1; funext x
  exact integral_map hf.aemeasurable
    (measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem kernelCov_map_neg_conj (μ ν : Measure ℂ) [SFinite ν] :
    kernelCov neumannH (μ.map fun u => -conj u) (ν.map fun u => -conj u) =
      kernelCov neumannH μ ν := by
  rw [kernelCov_map_gen measurable_neg_conj]
  simp only [neumannH_neg_conj]
  rfl

theorem kernelCov_map_mul {b : ℝ} (hb : 0 < b) {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) :
    kernelCov neumannH (μ.map fun u => (b : ℂ) * u) (ν.map fun u => (b : ℂ) * u) =
      kernelCov neumannH μ ν - 2 * Real.log b * ((μ Set.univ).toReal * (ν Set.univ).toReal) := by
  have := hμ.1
  have := hν.1
  rw [kernelCov_map_gen (measurable_mul_left' b)]
  have hint := integrable_neumannH_prod hμ hν
  have hin : ∀ᵐ x ∂μ, ∫ y, neumannH ((b : ℂ) * x) ((b : ℂ) * y) ∂ν =
      ∫ y, neumannH x y ∂ν - 2 * Real.log b * (ν Set.univ).toReal := by
    filter_upwards [hint.prod_right_ae] with x hx
    have hae : ∀ᵐ y ∂ν, neumannH ((b : ℂ) * x) ((b : ℂ) * y) = neumannH x y - 2 * Real.log b := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hν x),
        measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hν (conj x))] with y h1 h2
      refine neumannH_smul hb (fun h => h1 (by rw [h]; rfl)) (fun h => h2 ?_)
      rw [h, Complex.conj_conj]; rfl
    rw [integral_congr_ae hae, integral_sub hx (integrable_const _), integral_const,
      smul_eq_mul, measureReal_def]
    ring
  rw [integral_congr_ae hin, integral_sub hint.integral_prod_left (integrable_const _),
    integral_const, smul_eq_mul, measureReal_def]
  unfold kernelCov
  ring

theorem kernelCov2_map_mul {b : ℝ} (hb : 0 < b) (p q : BPair) :
    kernelCov2 neumannH (p.1.1.map fun u => (b : ℂ) * u, p.1.2.map fun u => (b : ℂ) * u)
        (q.1.1.map fun u => (b : ℂ) * u, q.1.2.map fun u => (b : ℂ) * u) =
      kernelCov2 neumannH p.1 q.1 := by
  simp only [kernelCov2]
  rw [kernelCov_map_mul hb p.2.1 q.2.1, kernelCov_map_mul hb p.2.1 q.2.2.1,
    kernelCov_map_mul hb p.2.2.1 q.2.1, kernelCov_map_mul hb p.2.2.1 q.2.2.1, p.2.2.2, q.2.2.2]
  ring

theorem kernelCov2_map_neg_conj (p q : BPair) :
    kernelCov2 neumannH (p.1.1.map fun u => -conj u, p.1.2.map fun u => -conj u)
        (q.1.1.map fun u => -conj u, q.1.2.map fun u => -conj u) =
      kernelCov2 neumannH p.1 q.1 := by
  have := q.2.1.1
  have := q.2.2.1.1
  simp only [kernelCov2, kernelCov_map_neg_conj]

/-! ## 11. Radial smearing and admissibility under `z ↦ b z` and `z ↦ −z̄` -/

theorem radSmear_map_mul {b : ℝ} (hb : 0 < b) (μ : Measure ℂ) :
    radSmear (μ.map fun u => (b : ℂ) * u) = (radSmear μ).map fun u => (b : ℂ) * u := by
  ext A hA
  have hk : ∀ B, MeasurableSet B → Measurable fun z : ℂ => foldedCircle 0 ‖z‖ B :=
    fun B hB => (Measure.measurable_coe hB).comp radKernel.measurable
  rw [radSmear_apply _ hA, Measure.map_apply (measurable_mul_left' b) hA,
    radSmear_apply _ (measurable_mul_left' b hA),
    lintegral_map (hk A hA) (measurable_mul_left' b)]
  congr 1; funext z
  have e : foldedCircle 0 ‖(b : ℂ) * z‖ = (foldedCircle 0 ‖z‖).map fun u => (b : ℂ) * u := by
    rw [fc_map_mul 0 _ hb, mul_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
  rw [e, Measure.map_apply (measurable_mul_left' b) hA]

theorem radSmear_map_neg_conj (μ : Measure ℂ) :
    radSmear (μ.map fun u => -conj u) = (radSmear μ).map fun u => -conj u := by
  ext A hA
  have hk : ∀ B, MeasurableSet B → Measurable fun z : ℂ => foldedCircle 0 ‖z‖ B :=
    fun B hB => (Measure.measurable_coe hB).comp radKernel.measurable
  rw [radSmear_apply _ hA, Measure.map_apply measurable_neg_conj hA,
    radSmear_apply _ (measurable_neg_conj hA), lintegral_map (hk A hA) measurable_neg_conj]
  congr 1; funext z
  have e : foldedCircle 0 ‖-conj z‖ = (foldedCircle 0 ‖z‖).map fun u => -conj u := by
    rw [fc_map_neg_conj, map_zero, neg_zero, norm_neg, Complex.norm_conj]
  rw [e, Measure.map_apply measurable_neg_conj hA]

theorem isAdmissibleH_map_mul {b : ℝ} (hb : 0 < b) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleH (μ.map fun u => (b : ℂ) * u) := by
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  refine isAdmissibleH_map hμ hK hμK (measurable_mul_left' b)
    (continuous_const.mul continuous_id).continuousOn ?_ hb fun x _ y _ => ?_
  · rintro _ ⟨z, hz, rfl⟩
    show 0 ≤ ((b : ℂ) * z).im
    simpa using mul_nonneg hb.le (show 0 ≤ z.im from hKH hz)
  · rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]

theorem isAdmissibleH_map_neg_conj {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleH (μ.map fun u => -conj u) := by
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  refine isAdmissibleH_map hμ hK hμK measurable_neg_conj
    Complex.continuous_conj.neg.continuousOn ?_ one_pos fun x _ y _ => ?_
  · rintro _ ⟨z, hz, rfl⟩
    show 0 ≤ (-conj z).im
    simpa using (show 0 ≤ z.im from hKH hz)
  · rw [one_mul, show -conj x - -conj y = -conj (x - y) by rw [map_sub]; ring, norm_neg,
      Complex.norm_conj]

/-! ## 12. Lebesgue measure under `z ↦ b z` and `z ↦ −z̄`; good pushforward densities -/

theorem map_volume_mul {b : ℝ} (hb : 0 < b) :
    (volume : Measure ℂ).map (fun u => (b : ℂ) * u) = ENNReal.ofReal ((b ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (b • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = b ^ 2 := by
    rw [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ))
    (f := b • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) (by rw [hdet]; positivity)
  have e : ⇑(b • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = fun u => (b : ℂ) * u := by
    funext u; simp [Complex.real_smul]
  rw [e, hdet, abs_of_pos (by positivity)] at h
  exact h

theorem map_volume_neg_conj :
    (volume : Measure ℂ).map (fun u => -conj u) = volume := by
  set f : ℂ →ₗ[ℝ] ℂ := (-1 : ℝ) • Complex.conjAe.toLinearEquiv.toLinearMap with hf
  have hdet : LinearMap.det f = -1 := by
    rw [hf, LinearMap.det_smul, Complex.det_conjAe, Complex.finrank_real_complex]; norm_num
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ))
    (f := f) (by rw [hdet]; norm_num)
  have e : ⇑f = fun u => -conj u := by
    funext u; simp [hf]
  rw [e, hdet] at h
  rw [h]; simp

open CharFun in
theorem isGoodSC_map_mul {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) {b : ℝ}
    (hb : 0 < b) : ∃ (M' : ℝ≥0) (R' δ' : ℝ), 0 < δ' ∧
      SmoothConv.IsGoodSC M' R' ((tdens a).map fun u => (b : ℂ) * u) ∧
      ∀ᵐ w ∂((tdens a).map fun u => (b : ℂ) * u), δ' < w.im := by
  obtain ⟨R, hR⟩ := hd.compact.isBounded.subset_closedBall (0 : ℂ)
  have hKae : ∀ᵐ z ∂tdens a, z ∈ K := ae_iff.2 hd.tdens_compl
  refine ⟨M.toNNReal * (b ^ 2)⁻¹.toNNReal, b * R, b * δ, mul_pos hb hd.delta, ⟨?_, ?_⟩, ?_⟩
  · calc (tdens a).map (fun u => (b : ℂ) * u)
        ≤ ((M.toNNReal : ℝ≥0∞) • volume).map (fun u => (b : ℂ) * u) :=
          Measure.map_mono hd.tdens_le (measurable_mul_left' b)
      _ = ((M.toNNReal * (b ^ 2)⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) • volume := by
          rw [Measure.map_smul, map_volume_mul hb, smul_smul, ENNReal.coe_mul]
          all_goals (try rfl)
          all_goals exact (measurable_mul_left' b).aemeasurable
  · rw [Measure.map_apply (measurable_mul_left' b)
      ((isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl)]
    have hsub : (fun u => (b : ℂ) * u) ⁻¹' (Metric.closedBall (0 : ℂ) (b * R) ∩ Hbar)ᶜ ⊆ Kᶜ := by
      intro z hz hzK
      apply hz
      refine ⟨?_, ?_⟩
      · have := hR hzK
        rw [mem_closedBall, dist_zero_right] at this ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
        exact mul_le_mul_of_nonneg_left this hb.le
      · show 0 ≤ ((b : ℂ) * z).im
        simpa using mul_nonneg hb.le (hd.delta.trans (hd.sub hzK)).le
    exact measure_mono_null hsub hd.tdens_compl
  · rw [ae_map_iff (measurable_mul_left' b).aemeasurable
      (measurableSet_lt measurable_const Complex.measurable_im)]
    filter_upwards [hKae] with z hz
    simpa using mul_lt_mul_of_pos_left (hd.sub hz) hb

open CharFun in
theorem isGoodSC_map_neg_conj {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) :
    ∃ (M' : ℝ≥0) (R' δ' : ℝ), 0 < δ' ∧
      SmoothConv.IsGoodSC M' R' ((tdens a).map fun u => -conj u) ∧
      ∀ᵐ w ∂((tdens a).map fun u => -conj u), δ' < w.im := by
  obtain ⟨R, hR⟩ := hd.compact.isBounded.subset_closedBall (0 : ℂ)
  have hKae : ∀ᵐ z ∂tdens a, z ∈ K := ae_iff.2 hd.tdens_compl
  refine ⟨M.toNNReal, R, δ, hd.delta, ⟨?_, ?_⟩, ?_⟩
  · calc (tdens a).map (fun u => -conj u)
        ≤ ((M.toNNReal : ℝ≥0∞) • volume).map (fun u => -conj u) :=
          Measure.map_mono hd.tdens_le measurable_neg_conj
      _ = (M.toNNReal : ℝ≥0∞) • volume := by
          rw [Measure.map_smul, map_volume_neg_conj]
          all_goals exact measurable_neg_conj.aemeasurable
  · rw [Measure.map_apply measurable_neg_conj
      ((isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl)]
    have hsub : (fun u => -conj u) ⁻¹' (Metric.closedBall (0 : ℂ) R ∩ Hbar)ᶜ ⊆ Kᶜ := by
      intro z hz hzK
      apply hz
      refine ⟨?_, ?_⟩
      · have := hR hzK
        rw [mem_closedBall, dist_zero_right] at this ⊢
        rwa [norm_neg, Complex.norm_conj]
      · show 0 ≤ (-conj z).im
        simpa using (hd.delta.trans (hd.sub hzK)).le
    exact measure_mono_null hsub hd.tdens_compl
  · rw [ae_map_iff measurable_neg_conj.aemeasurable
      (measurableSet_lt measurable_const Complex.measurable_im)]
    filter_upwards [hKae] with z hz
    simpa using hd.sub hz

/-! ## 13. Lateral coordinates of good samples -/

theorem GoodRad.lateralPart_eq {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : GoodRad x F)
    {μ : Measure ℂ} (h0 : μ {0} = 0) :
    lateralPart x μ = evalReg x μ - ∫ z, F (0, ‖z‖) ∂μ := by
  unfold lateralPart
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz
  exact h.radAvgReg_eq (norm_pos_iff.2 hz)

theorem GoodRad.rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : GoodRad x F) (Q : ℝ) {b : ℝ}
    (hb : 0 < b) :
    GoodRad (rescale x Q b) (fun q => F ((b : ℂ) * q.1, b * q.2) + Q * Real.log b) := by
  refine ⟨h.1.rescale' Q hb, fun n m => ?_⟩
  rw [RegClosure.rescale_fc_eq h.1 Q hb 0 (dyRad_pos n m)]
  simp [foldH_of_mem' zero_mem_Hbar]

theorem GoodRad.reflect {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : GoodRad x F) :
    GoodRad (RegClosure.reflectH x) (fun q => F (-conj q.1, q.2)) := by
  refine ⟨h.1.reflectH', fun n m => ?_⟩
  rw [RegClosure.reflectH_fc_eq h.1 zero_mem_Hbar (dyRad_pos n m)]

theorem aesm_of_continuousOn_Hbar {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) {ν : Measure ℂ}
    (hν : ∀ᵐ u ∂ν, u ∈ Hbar) : AEStronglyMeasurable g ν := by
  have := hg.aestronglyMeasurable isClosed_Hbar.measurableSet (μ := ν)
  rwa [Measure.restrict_eq_self_of_ae_mem hν] at this

theorem integrable_of_continuousOn_Hbar {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) : Integrable g ν := by
  obtain ⟨K, hK, hKH, hνK⟩ := hν.2.1
  have := hν.1
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
  have : IntegrableOn g K ν := (hg.mono hKH).integrableOn_compact hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this

theorem ae_mem_Hbar_of_admissible {ν : Measure ℂ} (hν : IsAdmissibleH ν) :
    ∀ᵐ u ∂ν, u ∈ Hbar := by
  obtain ⟨K, -, hKH, hνK⟩ := hν.2.1
  exact (ae_iff.2 hνK).mono fun z hz => hKH hz

section Lateral

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

theorem ae_add_X (hX : IsFreeGFFModConstH X P) {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) : ∀ᵐ ω ∂P, X ω (μ + ν) = X ω μ + X ω ν := by
  filter_upwards [hX.linear μ ν hμ hν 1 1] with ω h
  simpa using h

/-! ### The field itself -/

theorem ae_lateral_X (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hE : ∀ᵐ ω ∂P, evalReg (X ω) μ = X ω μ) :
    ∀ᵐ ω ∂P, lateralPart (X ω) μ = X ω μ - X ω (radSmear μ) := by
  filter_upwards [hG.ae_good, hE, ae_integral_radial hX hG hμ] with ω hg h1 h2
  rw [hg.lateralPart_eq (noAtoms_of_isAdmissibleH hμ 0), h1, h2.2]

theorem ae_evalReg_fc (hG : IsRegVersion X P G) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, evalReg (X ω) (foldedCircle d s) = X ω (foldedCircle d s) := by
  filter_upwards [hG.reg, hG.raw (foldH d) (foldH_mem_Hbar' d) s hs] with ω h1 h2
  rw [h1.evalReg_fc d hs, h2, fc_foldH_eq]

theorem ae_evalReg_tdens (hX : IsFreeGFFModConstH X P) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}
    (hd : CharFun.Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (X ω) (CharFun.tdens a) = X ω (CharFun.tdens a) :=
  ae_evalReg_eq_withDensity hX (M := M.toNNReal)
    (fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hd.bound z))) hd.compact hd.delta
    hd.sub hd.dzero

/-! ### The rescaled field -/

theorem ae_lateral_rescale (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) (Q : ℝ)
    {b : ℝ} (hb : 0 < b) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hE : ∀ᵐ ω ∂P, evalReg (rescale (X ω) Q b) μ =
      X ω (μ.map fun u => (b : ℂ) * u) + Q * Real.log b * (μ Set.univ).toReal) :
    ∀ᵐ ω ∂P, lateralPart (rescale (X ω) Q b) μ =
      X ω (μ.map fun u => (b : ℂ) * u) - X ω (radSmear (μ.map fun u => (b : ℂ) * u)) := by
  have hμb := isAdmissibleH_map_mul hb hμ
  have := hμ.1
  filter_upwards [hG.ae_good, hE, ae_integral_radial hX hG hμb] with ω hg h1 h2
  rw [(hg.rescale Q hb).lateralPart_eq (noAtoms_of_isAdmissibleH hμ 0), h1]
  have hint : Integrable (fun z => G ω (0, b * ‖z‖)) μ := by
    have := (integrable_map_measure h2.1.aestronglyMeasurable
      (measurable_mul_left' b).aemeasurable).1 h2.1
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Function.comp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
  have hmap : ∫ z, G ω (0, b * ‖z‖) ∂μ =
      ∫ u, G ω (0, ‖u‖) ∂(μ.map fun u => (b : ℂ) * u) := by
    rw [integral_map (measurable_mul_left' b).aemeasurable h2.1.aestronglyMeasurable]
    congr 1; funext z; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
  simp only [mul_zero]
  rw [integral_add hint (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
    hmap, h2.2]
  ring

theorem ae_evalReg_rescale_fc (hG : IsRegVersion X P G) (Q : ℝ) {b : ℝ} (hb : 0 < b) (d : ℂ)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, evalReg (rescale (X ω) Q b) (foldedCircle d s) =
      X ω ((foldedCircle d s).map fun u => (b : ℂ) * u) +
        Q * Real.log b * ((foldedCircle d s) Set.univ).toReal := by
  filter_upwards [hG.reg, hG.raw ((b : ℂ) * foldH d)
    (RegClosure.mapsTo_mul_pos hb (foldH_mem_Hbar' d)) (b * s) (mul_pos hb hs)] with ω h1 h2
  rw [(h1.rescale' Q hb).evalReg_fc d hs]
  show G ω ((b : ℂ) * foldH d, b * s) + Q * Real.log b = _
  rw [measure_univ, ENNReal.toReal_one, mul_one, h2, ← fc_foldH_eq d s, fc_map_mul _ _ hb]

theorem ae_evalReg_rescale_tdens (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : CharFun.Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (rescale (X ω) Q b) (CharFun.tdens a) =
      X ω ((CharFun.tdens a).map fun u => (b : ℂ) * u) +
        Q * Real.log b * ((CharFun.tdens a) Set.univ).toReal := by
  obtain ⟨M', R', δ', hδ', hgood, him⟩ := isGoodSC_map_mul hd hb
  have hA := hd.admissible
  have := hA.1
  have hKae := ae_mem_Hbar_of_admissible hA
  have hmapH : ∀ᵐ u ∂((CharFun.tdens a).map fun u => (b : ℂ) * u), u ∈ Hbar :=
    ae_mem_Hbar_of_admissible (isAdmissibleH_map_mul hb hA)
  filter_upwards [hG.reg, ae_tendsto_integral_G hX hG hδ' hgood him hb] with ω h1 h2
  have hF := h1.rescale' Q hb
  have e : ∀ k : ℕ, ∫ w, avgReg (rescale (X ω) Q b) k w ∂(CharFun.tdens a) =
      ∫ u, G ω (u, b * radius k) ∂((CharFun.tdens a).map fun u => (b : ℂ) * u) +
        Q * Real.log b * ((CharFun.tdens a) Set.univ).toReal := by
    intro k
    rw [integral_congr_ae (hKae.mono fun w hw => hF.avgReg_eq k hw)]
    have hcont : ContinuousOn (fun w => G ω ((b : ℂ) * w, b * radius k)) Hbar :=
      (hG.cont ω).comp ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
        fun w hw => ⟨RegClosure.mapsTo_mul_pos hb hw, mul_pos hb (radius_pos k)⟩
    have hint : Integrable (fun w => G ω ((b : ℂ) * w, b * radius k)) (CharFun.tdens a) :=
      integrable_of_continuousOn_Hbar hcont hA
    rw [integral_add hint (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
      integral_map (measurable_mul_left' b).aemeasurable
        (aesm_of_continuousOn_Hbar (hG.continuousOn_slice ω (mul_pos hb (radius_pos k))) hmapH)]
    ring
  unfold evalReg
  simp_rw [e]
  exact (h2.add_const _).limUnder_eq

/-! ### The reflected field -/

theorem ae_lateral_reflect (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hE : ∀ᵐ ω ∂P, evalReg (RegClosure.reflectH (X ω)) μ = X ω (μ.map fun u => -conj u)) :
    ∀ᵐ ω ∂P, lateralPart (RegClosure.reflectH (X ω)) μ =
      X ω (μ.map fun u => -conj u) - X ω (radSmear (μ.map fun u => -conj u)) := by
  have hμr := isAdmissibleH_map_neg_conj hμ
  filter_upwards [hG.ae_good, hE, ae_integral_radial hX hG hμr] with ω hg h1 h2
  rw [hg.reflect.lateralPart_eq (noAtoms_of_isAdmissibleH hμ 0), h1]
  have hmap : ∫ z, G ω (-conj 0, ‖z‖) ∂μ = ∫ u, G ω (0, ‖u‖) ∂(μ.map fun u => -conj u) := by
    rw [integral_map measurable_neg_conj.aemeasurable h2.1.aestronglyMeasurable]
    congr 1; funext z; rw [norm_neg, Complex.norm_conj, map_zero, neg_zero]
  rw [hmap, h2.2]

theorem ae_evalReg_reflect_fc (hG : IsRegVersion X P G) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, evalReg (RegClosure.reflectH (X ω)) (foldedCircle d s) =
      X ω ((foldedCircle d s).map fun u => -conj u) := by
  filter_upwards [hG.reg, hG.raw (-conj (foldH d))
    (RegClosure.mapsTo_neg_conj (foldH_mem_Hbar' d)) s hs] with ω h1 h2
  rw [h1.reflectH'.evalReg_fc d hs]
  show G ω (-conj (foldH d), s) = _
  rw [h2, ← fc_foldH_eq d s, fc_map_neg_conj]

theorem ae_evalReg_reflect_tdens (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G)
    {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : CharFun.Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (RegClosure.reflectH (X ω)) (CharFun.tdens a) =
      X ω ((CharFun.tdens a).map fun u => -conj u) := by
  obtain ⟨M', R', δ', hδ', hgood, him⟩ := isGoodSC_map_neg_conj hd
  have hA := hd.admissible
  have := hA.1
  have hKae := ae_mem_Hbar_of_admissible hA
  have hmapH : ∀ᵐ u ∂((CharFun.tdens a).map fun u => -conj u), u ∈ Hbar :=
    ae_mem_Hbar_of_admissible (isAdmissibleH_map_neg_conj hA)
  filter_upwards [hG.reg, ae_tendsto_integral_G hX hG hδ' hgood him one_pos] with ω h1 h2
  have hF := h1.reflectH'
  have e : ∀ k : ℕ, ∫ w, avgReg (RegClosure.reflectH (X ω)) k w ∂(CharFun.tdens a) =
      ∫ u, G ω (u, 1 * radius k) ∂((CharFun.tdens a).map fun u => -conj u) := by
    intro k
    rw [integral_congr_ae (hKae.mono fun w hw => hF.avgReg_eq k hw), one_mul,
      integral_map measurable_neg_conj.aemeasurable
        (aesm_of_continuousOn_Hbar (hG.continuousOn_slice ω (radius_pos k)) hmapH)]
  unfold evalReg
  simp_rw [e]
  exact h2.limUnder_eq

end Lateral

/-! ## 14. Assembly of the coordinate laws -/

/-- Index set of the coordinates read by `fieldLawFull H`: circles, and test functions. -/
abbrev LatIdx : Type := ℕ ⊕ TestFun H

/-- The `n`-th enumerated folded circle of `coordsFull`. -/
def fcN (n : ℕ) : Measure ℂ :=
  foldedCircle (CoordsFull.fullIndex n).1 (CoordsFull.fullIndex n).2

theorem fullIndex_pos (n : ℕ) : 0 < (CoordsFull.fullIndex n).2 := by
  unfold CoordsFull.fullIndex; positivity

theorem fcN_admissible (n : ℕ) : IsAdmissibleH (fcN n) := by
  rw [fcN, ← fc_foldH_eq]
  exact isAdmissibleH_foldedCircle (foldH_mem_Hbar' _) (fullIndex_pos n)

/-- The lateral coordinates of a random field, as a single family. -/
def latCoords {Ω : Type*} (Y : Ω → FieldSample) (ω : Ω) : LatIdx → ℝ :=
  Sum.elim (fun n => lateralPart (Y ω) (fcN n)) (fun ρ => pairRaw (lateralPart (Y ω)) ρ.1)

theorem measurable_latCoords {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    (hY : ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => Y ω μ) :
    Measurable (latCoords Y) := by
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with n | ρ
  · have := (fcN_admissible n).1
    exact measurable_lateral_of hY (fcN n)
  · obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
    haveI : IsFiniteMeasure (volume.withDensity fun z => ENNReal.ofReal (ρ.1 z)) :=
      hd.admissible.1
    haveI : IsFiniteMeasure (volume.withDensity fun z => ENNReal.ofReal (-ρ.1 z)) :=
      hd.neg.admissible.1
    exact (measurable_lateral_of hY _).sub (measurable_lateral_of hY _)

theorem fieldLawFull_eq_map_latCoords {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (hY : Measurable (latCoords Y)) :
    fieldLawFull H (fun ω => lateralPart (Y ω)) P =
      (P.map (latCoords Y)).map (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ) := by
  rw [Measure.map_map (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ).measurable hY]
  rfl

/-- The Gaussian pairs representing the lateral coordinates, after a measure transform `T`. -/
def latPair (T : Measure ℂ → Measure ℂ) (hTA : ∀ μ, IsAdmissibleH μ → IsAdmissibleH (T μ))
    (hTU : ∀ μ, T μ Set.univ = μ Set.univ) : LatIdx → BPair
  | .inl n => ⟨(T (fcN n), radSmear (T (fcN n))), hTA _ (fcN_admissible n),
      isAdmissibleH_radSmear (hTA _ (fcN_admissible n)), (radSmear_univ _).symm⟩
  | .inr ρ =>
    ⟨(T (CharFun.tdens ρ.1) + radSmear (T (CharFun.tdens fun z => -ρ.1 z)),
      T (CharFun.tdens fun z => -ρ.1 z) + radSmear (T (CharFun.tdens ρ.1))),
      by
        obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
        exact isAdmissibleH_add (hTA _ hd.admissible)
          (isAdmissibleH_radSmear (hTA _ hd.neg.admissible)),
      by
        obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
        exact isAdmissibleH_add (hTA _ hd.neg.admissible)
          (isAdmissibleH_radSmear (hTA _ hd.admissible)),
      by simp only [Measure.add_apply, radSmear_univ]; exact add_comm _ _⟩

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- If every lateral coordinate at circles and densities is a.s. `X(Tμ) − X(rad(Tμ))`, the
lateral coordinates are a.s. the Gaussian family `latPair T`. -/
theorem latCoords_ae_eq (hX : IsFreeGFFModConstH X P) {Y : Ω → FieldSample}
    (T : Measure ℂ → Measure ℂ) (hTA : ∀ μ, IsAdmissibleH μ → IsAdmissibleH (T μ))
    (hTU : ∀ μ, T μ Set.univ = μ Set.univ)
    (hfc : ∀ n, ∀ᵐ ω ∂P, lateralPart (Y ω) (fcN n) =
      X ω (T (fcN n)) - X ω (radSmear (T (fcN n))))
    (hdens : ∀ (a : ℂ → ℝ) (K : Set ℂ) (M δ : ℝ), CharFun.Dens a K M δ →
      ∀ᵐ ω ∂P, lateralPart (Y ω) (CharFun.tdens a) =
        X ω (T (CharFun.tdens a)) - X ω (radSmear (T (CharFun.tdens a))))
    (i : LatIdx) :
    (fun ω => latCoords Y ω i) =ᵐ[P] gaussFam X (latPair T hTA hTU) i := by
  rcases i with n | ρ
  · exact hfc n
  · obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
    have hA₁ := hTA _ hd.admissible
    have hA₂ := hTA _ hd.neg.admissible
    filter_upwards [hdens _ _ _ _ hd, hdens _ _ _ _ hd.neg,
      ae_add_X hX hA₁ (isAdmissibleH_radSmear hA₂),
      ae_add_X hX hA₂ (isAdmissibleH_radSmear hA₁)] with ω h1 h2 h3 h4
    show pairRaw (lateralPart (Y ω)) ρ.1 = gaussFam X (latPair T hTA hTU) (.inr ρ) ω
    simp only [gaussFam, latPair]
    rw [CharFun.pairRaw_eq_tdens, h1, h2, h3, h4]
    ring

theorem latPair_map_fst {f : ℂ → ℂ} (hf : Measurable f)
    (hTA : ∀ μ : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH (μ.map f))
    (hTU : ∀ μ : Measure ℂ, (μ.map f) Set.univ = μ Set.univ)
    (hrad : ∀ μ : Measure ℂ, radSmear (μ.map f) = (radSmear μ).map f) (i : LatIdx) :
    (latPair (fun μ => μ.map f) hTA hTU i).1 =
      ((latPair id (fun _ h => h) (fun _ => rfl) i).1.1.map f,
        (latPair id (fun _ h => h) (fun _ => rfl) i).1.2.map f) := by
  rcases i with n | ρ
  · simp only [latPair, id, hrad]
  · simp only [latPair, id, hrad, Measure.map_add _ _ hf]

end Assembly

/-! ## 15. Main results: (a2) independence, (a3) scale invariance, (d) reflection invariance -/

/-- The radial increments `fc(0, e^{-t}) − fc(0, 1)` as balanced pairs. -/
def radPair (t : ℝ) : BPair :=
  ⟨(foldedCircle 0 (Real.exp (-t)), foldedCircle 0 1),
    isAdmissibleH_foldedCircle zero_mem_Hbar (Real.exp_pos _),
    isAdmissibleH_foldedCircle zero_mem_Hbar one_pos, by simp⟩

/-- The untransformed lateral pairs. -/
def latPairId : LatIdx → BPair := latPair id (fun _ h => h) (fun _ => rfl)

theorem map_univ_mul (b : ℝ) (μ : Measure ℂ) :
    (μ.map fun u => (b : ℂ) * u) Set.univ = μ Set.univ := by
  rw [Measure.map_apply (measurable_mul_left' b) MeasurableSet.univ, Set.preimage_univ]

theorem map_univ_neg_conj (μ : Measure ℂ) :
    (μ.map fun u => -conj u) Set.univ = μ Set.univ := by
  rw [Measure.map_apply measurable_neg_conj MeasurableSet.univ, Set.preimage_univ]

/-- The lateral pairs pushed forward by `z ↦ b z`. -/
def latPairMul {b : ℝ} (hb : 0 < b) : LatIdx → BPair :=
  latPair (fun μ => μ.map fun u => (b : ℂ) * u) (fun _ h => isAdmissibleH_map_mul hb h)
    (map_univ_mul b)

/-- The lateral pairs pushed forward by `z ↦ −z̄`. -/
def latPairRef : LatIdx → BPair :=
  latPair (fun μ => μ.map fun u => -conj u) (fun _ h => isAdmissibleH_map_neg_conj h)
    map_univ_neg_conj

theorem kernelCov2_latPairMul {b : ℝ} (hb : 0 < b) (i j : LatIdx) :
    kernelCov2 neumannH (latPairMul hb i).1 (latPairMul hb j).1 =
      kernelCov2 neumannH (latPairId i).1 (latPairId j).1 := by
  rw [latPairMul, latPair_map_fst (measurable_mul_left' b) _ _ (radSmear_map_mul hb) i,
    latPair_map_fst (measurable_mul_left' b) _ _ (radSmear_map_mul hb) j]
  exact kernelCov2_map_mul hb (latPairId i) (latPairId j)

theorem kernelCov2_latPairRef (i j : LatIdx) :
    kernelCov2 neumannH (latPairRef i).1 (latPairRef j).1 =
      kernelCov2 neumannH (latPairId i).1 (latPairId j).1 := by
  rw [latPairRef, latPair_map_fst measurable_neg_conj _ _ radSmear_map_neg_conj i,
    latPair_map_fst measurable_neg_conj _ _ radSmear_map_neg_conj j]
  exact kernelCov2_map_neg_conj (latPairId i) (latPairId j)

theorem continuous_phi {a : ℝ} (ha : 0 < a) :
    Continuous fun x : ℂ => -2 * Real.log (max a ‖x‖) :=
  continuous_const.mul ((continuous_const.max continuous_norm).log
    fun x => (ha.trans_le (le_max_left _ _)).ne')

theorem integral_phi_radSmear {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {a : ℝ} (ha : 0 < a) :
    ∫ x, -2 * Real.log (max a ‖x‖) ∂(radSmear μ) = ∫ x, -2 * Real.log (max a ‖x‖) ∂μ := by
  have := hμ.1
  have hint := integrable_of_continuousOn_Hbar (continuous_phi ha).continuousOn
    (isAdmissibleH_radSmear hμ)
  rw [(integral_radSmear μ hint).2]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hμ 0)] with z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [integral_congr_ae ((fc_ae_norm hz0).mono fun x hx =>
    show -2 * Real.log (max a ‖x‖) = -2 * Real.log (max a ‖z‖) by rw [hx]),
    integral_const, probReal_univ, one_smul]

theorem kernelCov2_lat_rad (i : LatIdx) (t : ℝ) :
    kernelCov2 neumannH (latPairId i).1 (radPair t).1 = 0 := by
  simp only [kernelCov2, radPair]
  rw [kernelCov_fc0_right _ (Real.exp_pos _), kernelCov_fc0_right _ one_pos,
    kernelCov_fc0_right _ (Real.exp_pos _), kernelCov_fc0_right _ one_pos]
  rcases i with n | ρ
  · simp only [latPairId, latPair, id]
    rw [integral_phi_radSmear (fcN_admissible n) (Real.exp_pos _),
      integral_phi_radSmear (fcN_admissible n) one_pos]
    ring
  · obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
    have hA₁ := hd.admissible
    have hA₂ := hd.neg.admissible
    simp only [latPairId, latPair, id]
    have hI : ∀ {c : ℝ}, 0 < c → ∀ {ν : Measure ℂ}, IsAdmissibleH ν →
        Integrable (fun x : ℂ => -2 * Real.log (max c ‖x‖)) ν := fun hc ν hν =>
      integrable_of_continuousOn_Hbar (continuous_phi hc).continuousOn hν
    rw [integral_add_measure (hI (Real.exp_pos _) hA₁)
        (hI (Real.exp_pos _) (isAdmissibleH_radSmear hA₂)),
      integral_add_measure (hI one_pos hA₁) (hI one_pos (isAdmissibleH_radSmear hA₂)),
      integral_add_measure (hI (Real.exp_pos _) hA₂)
        (hI (Real.exp_pos _) (isAdmissibleH_radSmear hA₁)),
      integral_add_measure (hI one_pos hA₂) (hI one_pos (isAdmissibleH_radSmear hA₁)),
      integral_phi_radSmear hA₁ (Real.exp_pos _), integral_phi_radSmear hA₁ one_pos,
      integral_phi_radSmear hA₂ (Real.exp_pos _), integral_phi_radSmear hA₂ one_pos]
    ring

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem measurable_X_pi (hX : IsFreeGFFModConstH X P) : Measurable X :=
  measurable_pi_iff.2 hX.measurable_coord

theorem hY_X (hX : IsFreeGFFModConstH X P) :
    ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => X ω μ :=
  fun μ _ => hX.measurable_coord μ

theorem hY_rescale (hX : IsFreeGFFModConstH X P) (Q b : ℝ) :
    ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => rescale (X ω) Q b μ :=
  fun μ _ => (measurable_coordChange_apply (fun z => (b : ℂ) * z) Q μ).comp (measurable_X_pi hX)

theorem hY_reflect (hX : IsFreeGFFModConstH X P) :
    ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => RegClosure.reflectH (X ω) μ :=
  fun μ _ => (measurable_evalReg (μ.map fun z => -conj z)).comp (measurable_X_pi hX)

theorem latCoords_X_ae (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : IsRegVersion X P G) (i : LatIdx) :
    (fun ω => latCoords X ω i) =ᵐ[P] gaussFam X latPairId i :=
  latCoords_ae_eq hX id _ _
    (fun n => ae_lateral_X hX hG (fcN_admissible n) (ae_evalReg_fc hG _ (fullIndex_pos n)))
    (fun _ _ _ _ hd => ae_lateral_X hX hG hd.admissible (ae_evalReg_tdens hX hd)) i

theorem latCoords_rescale_ae (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : IsRegVersion X P G) (Q : ℝ) {b : ℝ} (hb : 0 < b) (i : LatIdx) :
    (fun ω => latCoords (fun ω => rescale (X ω) Q b) ω i) =ᵐ[P] gaussFam X (latPairMul hb) i :=
  latCoords_ae_eq hX _ _ _
    (fun n => ae_lateral_rescale hX hG Q hb (fcN_admissible n)
      (ae_evalReg_rescale_fc hG Q hb _ (fullIndex_pos n)))
    (fun _ _ _ _ hd => ae_lateral_rescale hX hG Q hb hd.admissible
      (ae_evalReg_rescale_tdens hX hG Q hb hd)) i

theorem latCoords_reflect_ae (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : IsRegVersion X P G) (i : LatIdx) :
    (fun ω => latCoords (fun ω => RegClosure.reflectH (X ω)) ω i) =ᵐ[P]
      gaussFam X latPairRef i :=
  latCoords_ae_eq hX _ _ _
    (fun n => ae_lateral_reflect hX hG (fcN_admissible n)
      (ae_evalReg_reflect_fc hG _ (fullIndex_pos n)))
    (fun _ _ _ _ hd => ae_lateral_reflect hX hG hd.admissible
      (ae_evalReg_reflect_tdens hX hG hd)) i

/-- **(a3) Scale invariance of the lateral part.** For every `a > 0` (and every `Q`), the lateral
part of the rescaled field `h(a ·) + Q log a` has the same full coordinate law
(`fieldLawFull`, STATEMENT_SPEC A16) as the lateral part of `h`. -/
theorem fieldLawFull_lateralPart_rescale (hX : IsFreeGFFModConstH X P) (Q : ℝ) {a : ℝ}
    (ha : 0 < a) :
    fieldLawFull H (fun ω => lateralPart (rescale (X ω) Q a)) P =
      fieldLawFull H (fun ω => lateralPart (X ω)) P := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hm1 := measurable_latCoords (hY_rescale hX Q a)
  have hm2 := measurable_latCoords (hY_X hX)
  rw [fieldLawFull_eq_map_latCoords hm1, fieldLawFull_eq_map_latCoords hm2]
  congr 1
  calc P.map (latCoords fun ω => rescale (X ω) Q a)
      = P.map (fun ω i => gaussFam X (latPairMul ha) i ω) :=
        map_eq_of_forall_ae_eq hm1.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable
          (latCoords_rescale_ae hX hG Q ha)
    _ = P.map (fun ω i => gaussFam X latPairId i ω) :=
        map_gaussFam_eq hX _ _ (kernelCov2_latPairMul ha)
    _ = P.map (latCoords X) :=
        (map_eq_of_forall_ae_eq hm2.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable
          (latCoords_X_ae hX hG)).symm

/-- **(d) Reflection invariance of the lateral part.** The lateral part of the reflected field
`h(−z̄)` has the same full coordinate law as the lateral part of `h`. -/
theorem fieldLawFull_lateralPart_reflect (hX : IsFreeGFFModConstH X P) :
    fieldLawFull H (fun ω => lateralPart (RegClosure.reflectH (X ω))) P =
      fieldLawFull H (fun ω => lateralPart (X ω)) P := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hm1 := measurable_latCoords (hY_reflect hX)
  have hm2 := measurable_latCoords (hY_X hX)
  rw [fieldLawFull_eq_map_latCoords hm1, fieldLawFull_eq_map_latCoords hm2]
  congr 1
  calc P.map (latCoords fun ω => RegClosure.reflectH (X ω))
      = P.map (fun ω i => gaussFam X latPairRef i ω) :=
        map_eq_of_forall_ae_eq hm1.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable
          (latCoords_reflect_ae hX hG)
    _ = P.map (fun ω i => gaussFam X latPairId i ω) :=
        map_gaussFam_eq hX _ _ kernelCov2_latPairRef
    _ = P.map (latCoords X) :=
        (map_eq_of_forall_ae_eq hm2.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable
          (latCoords_X_ae hX hG)).symm

/-- **(a2) Independence of the radial and lateral parts.** The radial process `A` (as a
path) is independent of the full coordinates of `lateralPart X` (circle coordinates jointly
with the test pairings, the coordinates read by `fieldLawFull`). -/
theorem indepFun_radialProc_lateralPart (hX : IsFreeGFFModConstH X P) :
    IndepFun (fun ω t => radialProc X t ω)
      (fun ω => (CoordsFull.coordsFull (lateralPart (X ω)),
        fun ρ : TestFun H => pairRaw (lateralPart (X ω)) ρ.1)) P := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hmh := measurable_latCoords (hY_X hX)
  have hmf : Measurable (fun ω t => radialProc X t ω) :=
    measurable_pi_iff.2 fun t => measurable_radialProc hX t
  suffices h : IndepFun (fun ω t => radialProc X t ω) (latCoords X) P from
    h.comp measurable_id (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ).measurable
  -- the Gaussian versions
  have hGs : IsGaussianProcess (Sum.elim (gaussFam X radPair) (gaussFam X latPairId)) P := by
    refine (hX.gaussian.comp_right (Sum.elim radPair latPairId)).congr fun i => ?_
    cases i <;> exact ae_of_all _ fun ω => rfl
  have hind' : IndepFun (fun ω t => gaussFam X radPair t ω)
      (fun ω i => gaussFam X latPairId i ω) P :=
    hGs.indepFun_of_covariance_eq_zero (fun t => (measurable_gaussFam hX _ t).aemeasurable)
      (fun i => (measurable_gaussFam hX _ i).aemeasurable) fun t i => by
        rw [covariance_comm]
        exact (hX.covariance_eq _ _ (latPairId i).2.1 (latPairId i).2.2.1 (latPairId i).2.2.2
          (radPair t).2.1 (radPair t).2.2.1 (radPair t).2.2.2).trans (kernelCov2_lat_rad i t)
  have hrad : ∀ t, radialProc X t =ᵐ[P] gaussFam X radPair t := fun t => radialProc_ae_eq hG t
  rw [indepFun_iff_map_prod_eq_prod_map_map hmf.aemeasurable hmh.aemeasurable]
  have hf_eq : P.map (fun ω t => radialProc X t ω) = P.map (fun ω t => gaussFam X radPair t ω) :=
    map_eq_of_forall_ae_eq hmf.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable hrad
  have hh_eq : P.map (latCoords X) = P.map (fun ω i => gaussFam X latPairId i ω) :=
    map_eq_of_forall_ae_eq hmh.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable
      (latCoords_X_ae hX hG)
  set E := MeasurableEquiv.sumPiEquivProdPi fun _ : ℝ ⊕ LatIdx => ℝ with hE
  have m1 : Measurable fun ω (j : ℝ ⊕ LatIdx) =>
      Sum.elim (fun t => radialProc X t ω) (latCoords X ω) j := by
    refine measurable_pi_iff.2 fun j => ?_
    rcases j with t | i
    · exact measurable_radialProc hX t
    · exact measurable_pi_iff.1 hmh i
  have m2 : Measurable fun ω (j : ℝ ⊕ LatIdx) =>
      Sum.elim (fun t => gaussFam X radPair t ω) (fun i => gaussFam X latPairId i ω) j := by
    refine measurable_pi_iff.2 fun j => ?_
    rcases j with t | i
    · exact measurable_gaussFam hX _ t
    · exact measurable_gaussFam hX _ i
  have hfh_eq : P.map (fun ω => ((fun t => radialProc X t ω), latCoords X ω)) =
      P.map (fun ω => ((fun t => gaussFam X radPair t ω), fun i => gaussFam X latPairId i ω)) := by
    have k1 : (fun ω => ((fun t => radialProc X t ω), latCoords X ω)) =
        E ∘ fun ω (j : ℝ ⊕ LatIdx) => Sum.elim (fun t => radialProc X t ω) (latCoords X ω) j :=
      rfl
    have k2 : (fun ω => ((fun t => gaussFam X radPair t ω), fun i => gaussFam X latPairId i ω)) =
        E ∘ fun ω (j : ℝ ⊕ LatIdx) =>
          Sum.elim (fun t => gaussFam X radPair t ω) (fun i => gaussFam X latPairId i ω) j :=
      rfl
    rw [k1, k2, ← Measure.map_map E.measurable m1, ← Measure.map_map E.measurable m2]
    congr 1
    refine map_eq_of_forall_ae_eq m1.aemeasurable m2.aemeasurable fun j => ?_
    rcases j with t | i
    · exact hrad t
    · exact latCoords_X_ae hX hG i
  rw [hfh_eq, hf_eq, hh_eq]
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_gaussFam_pi hX _).aemeasurable
    (measurable_gaussFam_pi hX _).aemeasurable).1 hind'

end Main

end WedgeTK
end QuantumZipper
