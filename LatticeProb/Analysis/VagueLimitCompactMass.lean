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

end LatticeProb.VagueLimit
