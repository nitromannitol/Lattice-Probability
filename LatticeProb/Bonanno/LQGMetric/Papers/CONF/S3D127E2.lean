/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127E2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127E1

/-!
# D127 N3, step 2 tools: the killed-Green seminorm and smooth approximation

For a bounded open `U` and the killed-Green form `B` (S3D127B1):

* `killedGreenForm_add_self`, `sqrt_killedGreenForm_add_le`: `√B` is a seminorm (bilinearity,
  symmetry `killedGreenForm_comm` and Cauchy–Schwarz `killedGreenForm_cs`);
* `sq_integral_le_energy_mul`: `(∫ a g)² ≤ E(g) B(a, a)` for signed bounded `a` vanishing off `U`
  and `g ∈ C_c^∞(U)` (given N1; BP Lemma 1.38 for signed densities, as in
  `dualNormSq_le_killedGreen`);
* `tendsto_killedGreenForm_zero`: `B(dₙ, dₙ) → 0` if `dₙ → 0` a.e., uniformly bounded, vanishing
  off `U` (dominated convergence on `ℂ × ℂ`, dominated by `C² 1_U 1_U G_U`);
* `exists_smooth_approx`: every measurable `0 ≤ ρ ≤ C` vanishing off `U` is approximated in `√B`
  by `ρ' ∈ C_c^∞(U)`, `0 ≤ ρ' ≤ C`: cut off to the compact sets `{infDist(·, Uᶜ) ≥ 1/(n+1)}`, then
  mollify (`ContDiffBump.normed`, Lebesgue differentiation
  `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).

The approximation step is the one of the D127 addendum (DECISIONS.md, 2026-10-02 22:15): standard
mollification, own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped Real Laplacian ContDiff

namespace LQGMetric.CONF.ZBM

open KilledHeat QuantumZipper

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-! ## The seminorm `√B` -/

theorem killedGreenForm_add_self (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ} (haC : ∀ z, |a z| ≤ C)
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    killedGreenForm U (fun z => a z + b z) (fun z => a z + b z) =
      killedGreenForm U a a + 2 * killedGreenForm U a b + killedGreenForm U b b := by
  have i1 := integrable_killedGreenForm hU hR hUR ha ha haC hai hai
  have i2 := integrable_killedGreenForm hU hR hUR ha hb hbC hai hbi
  have i3 := integrable_killedGreenForm hU hR hUR hb ha haC hbi hai
  have i4 := integrable_killedGreenForm hU hR hUR hb hb hbC hbi hbi
  have hcomm := killedGreenForm_comm hU hR hUR hb ha hbC haC hbi hai
  have e : killedGreenForm U (fun z => a z + b z) (fun z => a z + b z) =
      killedGreenForm U a a + killedGreenForm U a b +
        (killedGreenForm U b a + killedGreenForm U b b) := by
    unfold killedGreenForm
    have j12 : Integrable (fun q : ℂ × ℂ => a q.1 * a q.2 * killedGreen U q.1 q.2 +
        a q.1 * b q.2 * killedGreen U q.1 q.2) := i1.add i2
    have j34 : Integrable (fun q : ℂ × ℂ => b q.1 * a q.2 * killedGreen U q.1 q.2 +
        b q.1 * b q.2 * killedGreen U q.1 q.2) := i3.add i4
    rw [← integral_add i1 i2, ← integral_add i3 i4, ← integral_add j12 j34]
    exact integral_congr_ae (Eventually.of_forall fun q => by ring)
  rw [e, hcomm]
  ring

theorem sqrt_killedGreenForm_add_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ} (haC : ∀ z, |a z| ≤ C)
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hbi : Integrable b) :
    √(killedGreenForm U (fun z => a z + b z) (fun z => a z + b z)) ≤
      √(killedGreenForm U a a) + √(killedGreenForm U b b) := by
  have pa := killedGreenForm_psd hU hR hUR ha haC hai
  have pb := killedGreenForm_psd hU hR hUR hb hbC hbi
  have hcs := killedGreenForm_cs hU hR hUR ha hb haC hbC hai hbi
  have habs : |killedGreenForm U a b| ≤ √(killedGreenForm U a a) * √(killedGreenForm U b b) := by
    rw [← Real.sqrt_mul pa]
    exact Real.abs_le_sqrt hcs
  rw [killedGreenForm_add_self hU hR hUR ha hb haC hbC hai hbi]
  have hsa := Real.sq_sqrt pa
  have hsb := Real.sq_sqrt pb
  have hle : killedGreenForm U a a + 2 * killedGreenForm U a b + killedGreenForm U b b ≤
      (√(killedGreenForm U a a) + √(killedGreenForm U b b)) ^ 2 := by
    nlinarith [le_abs_self (killedGreenForm U a b)]
  calc _ ≤ √((√(killedGreenForm U a a) + √(killedGreenForm U b b)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

/-- **Cauchy–Schwarz against the energy** (BP Lemma 1.38 for a signed density):
`(∫ a g)² ≤ E(g) B(a, a)` -/
theorem sq_integral_le_energy_mul (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {a : ℂ → ℝ} (ha : Measurable a) {C : ℝ} (haC : ∀ z, |a z| ≤ C) (hai : Integrable a)
    (haU : ∀ z, z ∉ U → a z = 0) {g : ℂ → ℝ} (hg : g ∈ QuantumZipper.zeroSpace U) :
    (∫ y, a y * g y) ^ 2 ≤ QuantumZipper.dirichletEnergyOn U g * killedGreenForm U a a := by
  obtain ⟨am, ⟨C', hC'⟩, ai, -⟩ := negLap_props hg
  have hcs := killedGreenForm_cs hU hR hUR ha am (C := max C C')
    (fun z => (haC z).trans (le_max_left _ _)) (fun z => (hC' z).trans (le_max_right _ _)) hai ai
  rw [killedGreenForm_negLap_right hU hR hUR hN1 ha hai haU hg,
    killedGreenForm_negLap_self hU hR hUR hN1 hg] at hcs
  have h4 : 0 < (2 * π) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ h4
  calc (2 * π) ^ 2 * (∫ y, a y * g y) ^ 2 = (2 * π * ∫ y, a y * g y) ^ 2 := by ring
    _ ≤ _ := hcs
    _ = _ := by ring

/-! ## Dominated convergence for `B` -/

theorem tendsto_killedGreenForm_zero (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {d : ℕ → ℂ → ℝ} (hd : ∀ n, Measurable (d n)) {C : ℝ} (hC : ∀ n z, |d n z| ≤ C)
    (hdU : ∀ n z, z ∉ U → d n z = 0)
    (hlim : ∀ᵐ z, Tendsto (fun n => d n z) atTop (𝓝 0)) :
    Tendsto (fun n => killedGreenForm U (d n) (d n)) atTop (𝓝 0) := by
  classical
  set ind : ℂ → ℝ := U.indicator fun _ => (1 : ℝ) with hind
  have hindm : Measurable ind := measurable_const.indicator hU.measurableSet
  have hind1 : ∀ z, |ind z| ≤ 1 := fun z => by
    by_cases hz : z ∈ U <;> simp [hind, hz]
  have hindi : Integrable ind := integrable_of_bdd_of_vanish hUR hindm hind1
    (fun z hz => by simp [hind, hz])
  have hF := integrable_killedGreenForm hU hR hUR hindm hindm hind1 hindi hindi
  have hdi : ∀ n, Integrable (d n) := fun n =>
    integrable_of_bdd_of_vanish hUR (hd n) (hC n) (hdU n)
  have hC0 : ∀ z, 0 ≤ C := fun z => (abs_nonneg _).trans (hC 0 z)
  have key := tendsto_integral_of_dominated_convergence
    (F := fun n (q : ℂ × ℂ) => d n q.1 * d n q.2 * killedGreen U q.1 q.2)
    (f := fun _ => (0 : ℝ)) (μ := volume)
    (fun q => C ^ 2 * (ind q.1 * ind q.2 * killedGreen U q.1 q.2))
    (fun n => (integrable_killedGreenForm hU hR hUR (hd n) (hd n) (hC n) (hdi n)
      (hdi n)).aestronglyMeasurable)
    (hF.const_mul _)
    (fun n => Eventually.of_forall fun q => ?_) ?_
  · simpa [killedGreenForm] using key
  · have hG := killedGreen_nonneg U q.1 q.2
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hG]
    by_cases h1 : q.1 ∈ U
    · by_cases h2 : q.2 ∈ U
      · simp only [hind, indicator_of_mem h1, indicator_of_mem h2, mul_one]
        have := mul_le_mul (hC n q.1) (hC n q.2) (abs_nonneg _) (hC0 q.1)
        nlinarith [mul_le_mul_of_nonneg_right this hG]
      · rw [hdU n _ h2]
        simp only [abs_zero, mul_zero, zero_mul]
        exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by
          by_cases h : q.1 ∈ U <;> simp [hind, h]) (by simp [hind, h2])) hG)
    · rw [hdU n _ h1]
      simp only [abs_zero, mul_zero, zero_mul]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by simp [hind, h1]) (by
          by_cases h : q.2 ∈ U <;> simp [hind, h])) hG)
  · rw [Measure.volume_eq_prod]
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℂ))
      (ν := (volume : Measure ℂ))).ae hlim
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℂ))
      (ν := (volume : Measure ℂ))).ae hlim
    filter_upwards [h1, h2] with q hq1 hq2
    simpa using (hq1.mul hq2).mul_const (killedGreen U q.1 q.2)

/-! ## Smooth approximation -/

lemma compl_nonempty_of_subset_ball (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R) : (Uᶜ).Nonempty :=
  ⟨c + (R : ℂ), fun h => by
    have := hUR h
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hR] at this
    exact lt_irrefl _ this⟩

/-- the compact exhaustion `Kₙ = {infDist(·, Uᶜ) ≥ 1/(n+1)} ∩ cl B(c, R)` -/
def exhK (U : Set ℂ) (c : ℂ) (R : ℝ) (n : ℕ) : Set ℂ :=
  {x | 1 / ((n : ℝ) + 1) ≤ infDist x Uᶜ} ∩ closedBall c R

lemma isCompact_exhK (n : ℕ) : IsCompact (exhK U c R n) :=
  (isCompact_closedBall c R).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_infDist_pt _)).inter isClosed_closedBall)
    inter_subset_right

lemma exhK_subset (n : ℕ) : exhK U c R n ⊆ U := fun x hx => by
  by_contra hxU
  have h0 := infDist_zero_of_mem (s := Uᶜ) hxU
  have h1 : 1 / ((n : ℝ) + 1) ≤ infDist x Uᶜ := hx.1
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- the cut-off approximations converge in `√B` -/
theorem exists_compact_cut (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (hρU : ∀ z, z ∉ U → ρ z = 0) {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, killedGreenForm U (fun z => ρ z - (exhK U c R n).indicator ρ z)
      (fun z => ρ z - (exhK U c R n).indicator ρ z) < η := by
  classical
  have hne := compl_nonempty_of_subset_ball hR hUR
  have hm : ∀ n : ℕ, MeasurableSet (exhK U c R n) := fun n => (isCompact_exhK n).measurableSet
  have hT := tendsto_killedGreenForm_zero hU hR hUR
    (d := fun n z => ρ z - (exhK U c R n).indicator ρ z) (C := 2 * C)
    (fun n => hρ.sub (hρ.indicator (hm n)))
    (fun n z => by
      by_cases hz : z ∈ exhK U c R n
      · simp only [indicator_of_mem hz, sub_self, abs_zero]
        linarith [(abs_nonneg _).trans (hC z)]
      · simp only [indicator_of_notMem hz, sub_zero]
        linarith [(abs_nonneg _).trans (hC z), hC z])
    (fun n z hz => by
      have : z ∉ exhK U c R n := fun h => hz (exhK_subset n h)
      simp [indicator_of_notMem this, hρU z hz])
    (Eventually.of_forall fun z => ?_)
  · exact (hT.eventually (gt_mem_nhds hη)).exists
  · by_cases hz : z ∈ U
    · have hpos : 0 < infDist z Uᶜ :=
        (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 fun h => h hz
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hmem : z ∈ exhK U c R n := by
        refine ⟨?_, ball_subset_closedBall (hUR hz)⟩
        show 1 / ((n : ℝ) + 1) ≤ infDist z Uᶜ
        refine le_trans ?_ hN.le
        exact Nat.one_div_le_one_div hn
      simp [indicator_of_mem hmem]
    · have : ∀ n, z ∉ exhK U c R n := fun n h => hz (exhK_subset n h)
      simp [indicator_of_notMem (this _), hρU z hz]

end LQGMetric.CONF.ZBM
