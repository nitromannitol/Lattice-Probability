import Mathlib
import LatticeProb.Analysis.VagueLimitMeasurable

/-!
# Masses of compact sets under a vague limit

Let `μ` be a vague limit of measures `μs k` on a proper metric space. For a compact set `K`, the
thickened indicators `compactCutoff K n` of `K` at radius `1 / (n + 1)` are continuous, compactly
supported, bounded by the indicator of the closed `1`-thickening of `K`, and converge pointwise to the
indicator of `K`. Hence (dominated convergence)
`μ K = lim_n ∫ compactCutoff K n dμ = lim_n lim_k ∫ compactCutoff K n d(μs k)`.

So the mass of a compact set is the same for every vague limit, and it is computed from the
approximating measures alone. In particular, as soon as some vague limit exists, the statement
"every vague limit gives `K` the mass `a`" is equivalent to a statement about the sequence `μs` only
(`forall_isVagueLimit_measure_eq_ofReal_iff`).

For a continuous curve `η`, the statement "every vague limit gives `η([s, t])` the mass `t - s` for all
`s ≤ t`" therefore reduces to the countable `CurveMassCondition` on the approximating measures
(`forall_isVagueLimit_measure_image_Icc_iff`), using that rational times suffice
(`measure_image_Icc_eq_ofReal_of_rat`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.VagueLimit

variable {X : Type*} [MetricSpace X]

/-- The thickened indicator of `K` at radius `1 / (n + 1)`, as a real-valued function. -/
noncomputable def compactCutoff (K : Set X) (n : ℕ) : X → ℝ :=
  fun x => (thickenedIndicator (Nat.one_div_pos_of_nat (α := ℝ) (n := n)) K x : ℝ)

theorem continuous_compactCutoff (K : Set X) (n : ℕ) : Continuous (compactCutoff K n) :=
  NNReal.continuous_coe.comp (thickenedIndicator _ K).continuous

theorem compactCutoff_nonneg (K : Set X) (n : ℕ) (x : X) : 0 ≤ compactCutoff K n x :=
  NNReal.coe_nonneg _

theorem compactCutoff_le_one (K : Set X) (n : ℕ) (x : X) : compactCutoff K n x ≤ 1 := by
  unfold compactCutoff
  exact_mod_cast thickenedIndicator_le_one _ K x

theorem compactCutoff_eq_zero_of_notMem {K : Set X} (n : ℕ) {x : X} (hx : x ∉ cthickening 1 K) :
    compactCutoff K n x = 0 := by
  have hsub : thickening (1 / ((n : ℝ) + 1)) K ⊆ cthickening 1 K := by
    refine thickening_subset_cthickening_of_le ?_ K
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold compactCutoff
  rw [thickenedIndicator_zero _ K (fun h => hx (hsub h))]
  rfl

theorem abs_compactCutoff_le_indicator (K : Set X) (n : ℕ) (x : X) :
    ‖compactCutoff K n x‖ ≤ (cthickening 1 K).indicator 1 x := by
  by_cases hx : x ∈ cthickening 1 K
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg K n x)]
    exact compactCutoff_le_one K n x
  · rw [indicator_of_notMem hx, compactCutoff_eq_zero_of_notMem n hx, norm_zero]

theorem tendsto_compactCutoff {K : Set X} (hK : IsClosed K) (x : X) :
    Tendsto (fun n => compactCutoff K n x) atTop (𝓝 (K.indicator 1 x)) := by
  have h := thickenedIndicator_tendsto_indicator_closure
    (fun n : ℕ => Nat.one_div_pos_of_nat (α := ℝ) (n := n)) tendsto_one_div_add_atTop_nhds_zero_nat K
  rw [tendsto_pi_nhds] at h
  have h' := (NNReal.continuous_coe.tendsto _).comp (h x)
  rw [hK.closure_eq] at h'
  have hval : ((K.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ) = K.indicator 1 x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, indicator_of_mem hx]; rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; rfl
  rw [← hval]
  exact h'

variable [ProperSpace X]

theorem hasCompactSupport_compactCutoff {K : Set X} (hK : IsCompact K) (n : ℕ) :
    HasCompactSupport (compactCutoff K n) :=
  HasCompactSupport.intro (hK.cthickening (r := 1)) fun _ hx => compactCutoff_eq_zero_of_notMem n hx

variable [MeasurableSpace X] [BorelSpace X]

/-- Dominated convergence for the thickened indicators of a compact set, for a measure that is finite on
compact sets. -/
theorem tendsto_integral_compactCutoff {μ : Measure X} (hμ : ∀ K : Set X, IsCompact K → μ K < ⊤)
    {K : Set X} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x, compactCutoff K n x ∂μ) atTop (𝓝 (μ.real K)) := by
  have hint : Integrable ((cthickening 1 K).indicator (1 : X → ℝ)) μ :=
    (integrableOn_const (C := (1 : ℝ)) (hμ _ (hK.cthickening (r := 1))).ne).integrable_indicator
      isClosed_cthickening.measurableSet
  have h := tendsto_integral_of_dominated_convergence ((cthickening 1 K).indicator (1 : X → ℝ))
    (fun n => (continuous_compactCutoff K n).aestronglyMeasurable) hint
    (fun n => Eventually.of_forall (abs_compactCutoff_le_indicator K n))
    (Eventually.of_forall (tendsto_compactCutoff hK.isClosed))
  rwa [integral_indicator_one hK.isClosed.measurableSet] at h

/-- **The mass of a compact set from the approximations.** For a vague limit `μ` of `μs`,
`μ K = lim_n lim_k ∫ compactCutoff K n d(μs k)`. -/
theorem IsVagueLimit.tendsto_limUnder_integral_compactCutoff {μs : ℕ → Measure X} {μ : Measure X}
    (h : IsVagueLimit μs μ) {K : Set X} (hK : IsCompact K) :
    Tendsto (fun n => limUnder atTop (fun k => ∫ x, compactCutoff K n x ∂(μs k))) atTop
      (𝓝 (μ.real K)) := by
  refine (tendsto_integral_compactCutoff h.1 hK).congr fun n => ?_
  exact ((h.2 _ (continuous_compactCutoff K n) (hasCompactSupport_compactCutoff hK n)).limUnder_eq).symm

/-- For a vague limit `μ`, a compact set `K` and `a ≥ 0`: `μ K = a` if and only if the iterated limits
`lim_n lim_k ∫ compactCutoff K n d(μs k)` converge to `a`. -/
theorem IsVagueLimit.measure_eq_ofReal_iff {μs : ℕ → Measure X} {μ : Measure X}
    (h : IsVagueLimit μs μ) {K : Set X} (hK : IsCompact K) {a : ℝ} (ha : 0 ≤ a) :
    μ K = ENNReal.ofReal a ↔
      Tendsto (fun n => limUnder atTop (fun k => ∫ x, compactCutoff K n x ∂(μs k))) atTop (𝓝 a) := by
  have hlim := h.tendsto_limUnder_integral_compactCutoff hK
  constructor
  · intro hμK
    have : μ.real K = a := by rw [measureReal_def, hμK, ENNReal.toReal_ofReal ha]
    rwa [this] at hlim
  · intro ha'
    have hreal : μ.real K = a := tendsto_nhds_unique hlim ha'
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (h.1 K hK).ne]

/-- Two vague limits of the same sequence give every compact set the same mass. -/
theorem IsVagueLimit.measure_eq_of_isCompact {μs : ℕ → Measure X} {μ μ' : Measure X}
    (h : IsVagueLimit μs μ) (h' : IsVagueLimit μs μ') {K : Set X} (hK : IsCompact K) :
    μ K = μ' K := by
  rw [← ENNReal.ofReal_toReal (h.1 K hK).ne, ← ENNReal.ofReal_toReal (h'.1 K hK).ne]
  congr 1
  exact tendsto_nhds_unique (h.tendsto_limUnder_integral_compactCutoff hK)
    (h'.tendsto_limUnder_integral_compactCutoff hK)

/-- **Masses of all vague limits through the approximations.** If some vague limit of `μs` exists, then
every vague limit gives the compact set `K` the mass `a ≥ 0` if and only if the iterated limits
`lim_n lim_k ∫ compactCutoff K n d(μs k)` converge to `a`. -/
theorem forall_isVagueLimit_measure_eq_ofReal_iff {μs : ℕ → Measure X} (hex : ∃ μ, IsVagueLimit μs μ)
    {K : Set X} (hK : IsCompact K) {a : ℝ} (ha : 0 ≤ a) :
    (∀ μ, IsVagueLimit μs μ → μ K = ENNReal.ofReal a) ↔
      Tendsto (fun n => limUnder atTop (fun k => ∫ x, compactCutoff K n x ∂(μs k))) atTop (𝓝 a) := by
  obtain ⟨μ, hμ⟩ := hex
  refine ⟨fun hall => (hμ.measure_eq_ofReal_iff hK ha).1 (hall μ hμ), fun hT μ' hμ' => ?_⟩
  exact (hμ'.measure_eq_ofReal_iff hK ha).2 hT

/-! ### Curves parametrized by mass

A curve `η : ℝ → X` is parametrized by the mass of `μ` when `μ (η '' [s, t]) = t - s` for all `s ≤ t`. It
suffices to check this for rational times, and for every vague limit of `μs` it is equivalent to a countable
condition on the approximating measures (`CurveMassCondition`). -/

section Parametrization

private theorem exists_rat_seq_lt (x : ℝ) :
    ∃ q : ℕ → ℚ, (∀ n, (q n : ℝ) < x) ∧ Tendsto (fun n => (q n : ℝ)) atTop (𝓝 x) := by
  choose q hq using fun n : ℕ =>
    exists_rat_btwn (sub_lt_self x (Nat.one_div_pos_of_nat (α := ℝ) (n := n)))
  refine ⟨q, fun n => (hq n).2, ?_⟩
  have h1 : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := x)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
    (fun n => (hq n).1.le) (fun n => (hq n).2.le)

private theorem exists_rat_seq_gt (x : ℝ) :
    ∃ q : ℕ → ℚ, (∀ n, x < (q n : ℝ)) ∧ Tendsto (fun n => (q n : ℝ)) atTop (𝓝 x) := by
  choose q hq using fun n : ℕ =>
    exists_rat_btwn (lt_add_of_pos_right x (Nat.one_div_pos_of_nat (α := ℝ) (n := n)))
  refine ⟨q, fun n => (hq n).1, ?_⟩
  have h1 : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := x)).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => (hq n).1.le) (fun n => (hq n).2.le)

/-- **Rational times suffice.** If `μ (f '' [s, t]) = t - s` for all rational `s ≤ t`, then for all real
`s ≤ t` (monotonicity of `μ` and density of the rationals; no regularity of `f` is needed). -/
theorem measure_image_Icc_eq_ofReal_of_rat {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {f : ℝ → Y}
    (h : ∀ s t : ℚ, s ≤ t → μ (f '' Icc (s : ℝ) t) = ENNReal.ofReal ((t : ℝ) - s))
    {s t : ℝ} (hst : s ≤ t) : μ (f '' Icc s t) = ENNReal.ofReal (t - s) := by
  apply le_antisymm
  · obtain ⟨a, ha, ha'⟩ := exists_rat_seq_lt s
    obtain ⟨b, hb, hb'⟩ := exists_rat_seq_gt t
    refine ge_of_tendsto' (ENNReal.tendsto_ofReal (hb'.sub ha')) fun n => ?_
    have hab : a n ≤ b n := by exact_mod_cast (((ha n).trans_le hst).trans (hb n)).le
    rw [← h _ _ hab]
    exact measure_mono (image_mono (Icc_subset_Icc (ha n).le (hb n).le))
  · rcases hst.eq_or_lt with heq | hlt
    · simp [heq]
    · obtain ⟨a, ha, ha'⟩ := exists_rat_seq_gt s
      obtain ⟨b, hb, hb'⟩ := exists_rat_seq_lt t
      have h1 := ha'.eventually (gt_mem_nhds (show s < (s + t) / 2 by linarith))
      have h2 := hb'.eventually (lt_mem_nhds (show (s + t) / 2 < t by linarith))
      refine le_of_tendsto (ENNReal.tendsto_ofReal (hb'.sub ha')) ?_
      filter_upwards [h1, h2] with n hn1 hn2
      have hab : a n ≤ b n := by exact_mod_cast (hn1.trans hn2).le
      rw [← h _ _ hab]
      exact measure_mono (image_mono (Icc_subset_Icc (ha n).le (hb n).le))

/-- The countable mass condition for a curve `η` and measures `μs`: for all rational `s ≤ t`, the iterated
limits `lim_n lim_k ∫ compactCutoff (η '' [s, t]) n d(μs k)` equal `t - s`. -/
def CurveMassCondition (μs : ℕ → Measure X) (η : ℝ → X) : Prop :=
  ∀ s t : ℚ, s ≤ t → Tendsto (fun n => limUnder atTop
    (fun k => ∫ x, compactCutoff (η '' Icc (s : ℝ) t) n x ∂(μs k))) atTop (𝓝 ((t : ℝ) - s))

/-- Under the countable mass condition, every vague limit parametrizes the curve by its mass. -/
theorem IsVagueLimit.measure_image_Icc_of_curveMassCondition {μs : ℕ → Measure X} {μ : Measure X}
    {η : ℝ → X} (hη : Continuous η) (hμ : IsVagueLimit μs μ) (h : CurveMassCondition μs η) {s t : ℝ}
    (hst : s ≤ t) : μ (η '' Icc s t) = ENNReal.ofReal (t - s) :=
  measure_image_Icc_eq_ofReal_of_rat (fun s' t' hst' => (hμ.measure_eq_ofReal_iff
    (isCompact_Icc.image hη) (sub_nonneg.2 (by exact_mod_cast hst'))).2 (h s' t' hst')) hst

/-- If some vague limit exists, then every vague limit parametrizes the continuous curve `η` by its mass
if and only if the countable mass condition holds. -/
theorem forall_isVagueLimit_measure_image_Icc_iff {μs : ℕ → Measure X} {η : ℝ → X} (hη : Continuous η)
    (hex : ∃ μ, IsVagueLimit μs μ) :
    (∀ μ, IsVagueLimit μs μ → ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) ↔
      CurveMassCondition μs η := by
  refine ⟨fun h s t hst => ?_, fun h μ hμ s t hst => hμ.measure_image_Icc_of_curveMassCondition hη h hst⟩
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  exact (forall_isVagueLimit_measure_eq_ofReal_iff hex (isCompact_Icc.image hη) (sub_nonneg.2 hst')).1
    fun μ hμ => h μ hμ s t hst'

end Parametrization

end LatticeProb.VagueLimit
