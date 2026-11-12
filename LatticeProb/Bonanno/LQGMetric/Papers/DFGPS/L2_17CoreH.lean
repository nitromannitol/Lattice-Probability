/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreH at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepRad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the truncated harmonic part `φ𝔥` (packet P-B of D80)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 2 (T:1224–1230): "Let `φ` be a deterministic, smooth, compactly supported bump function which
is identically equal to 1 on a neighborhood of `W̄'` and which vanishes outside of a compact subset
of `ℂ ∖ cl V`. … The restrictions of the fields `h − φ𝔥` and `h̊` to the set `φ⁻¹(1) ⊃ W̄'` are
identical." Decision D80, packet P-B (`exists_harmFun`).

The harmonic part `𝔥` is only given as a distribution which is a.s. a harmonic function `g` on
`U = ℂ ∖ cl V` (`markov_normAt`). The function `φ𝔥` is realized as
`harmFn φ δ T x = φ(x) · T(radBump δ x) / ∫ radProf δ` (mean value property,
`GM.pair_radBump_of_harmonic`), which is continuous for every distribution `T`, a measurable
function of `T`, and equals `φ g` when `T|_U = g` is harmonic and `B̄(x, δ) ⊆ U` on `{φ ≠ 0}`.

* `harmFn`, `measurable_harmFn`, `harmFn_eq_of_harmonic`, `exists_bound_harmFn`.
* `harmFn_sub_apply` — `(h' − φ𝔥) ψ = h̊ ψ` for `ψ` supported in `φ⁻¹(1)` (deterministic).
* `exists_harmFun` — the random version, with `𝔥` replaced by its `G`-measurable version.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open InnerProductSpace

namespace LQGMetric.DFGPS.L217

open Blueprint

/-- a test function supported in `O` as a test function on `O` -/
def testOnOf {O : Opens ℂ} (ψ : TestC) (hψ : tsupport (ψ : ℂ → ℝ) ⊆ O) : TestOn O :=
  ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩

theorem apply_eq_restrictTo_testOnOf {O : Opens ℂ} (T : DistC) (ψ : TestC)
    (hψ : tsupport (ψ : ℂ → ℝ) ⊆ O) : T ψ = restrictTo O T (testOnOf ψ hψ) := by
  show T ψ = T (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) _)
  congr 1
  ext y
  simp [TestFunction.monoCLM_apply, testOnOf]

/-- `φ · 𝔥` read off a distribution by the mean value property:
`x ↦ φ(x) T(radBump δ x) / ∫ radProf δ` -/
def harmFn (φ : C(ℂ, ℝ)) (δ : ℝ) (hδ : 0 < δ) (T : DistC) : C(ℂ, ℝ) :=
  ⟨fun x => φ x * (T (GM.radBump δ hδ.le x) / ∫ y, GM.radProf δ y),
    φ.continuous.mul (((map_continuous T).comp (GM.continuous_radBump δ hδ.le)).div_const _)⟩

theorem harmFn_apply (φ : C(ℂ, ℝ)) (δ : ℝ) (hδ : 0 < δ) (T : DistC) (x : ℂ) :
    harmFn φ δ hδ T x = φ x * (T (GM.radBump δ hδ.le x) / ∫ y, GM.radProf δ y) := rfl

theorem measurable_harmFn (φ : C(ℂ, ℝ)) (δ : ℝ) (hδ : 0 < δ) : Measurable (harmFn φ δ hδ) :=
  ContinuousMap.measurable_iff_eval.2 fun x =>
    ((measurable_distOn_apply (GM.radBump δ hδ.le x)).div_const _).const_mul _

/-- `harmFn` is `φ g` when `T|_U` is the harmonic `g` and `B̄(x, δ) ⊆ U` on `{φ ≠ 0}` -/
theorem harmFn_eq_of_harmonic {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g U) {T : DistC}
    (hT : ∀ ψ : TestOn U, restrictTo U T ψ = ∫ y, g y * ψ y) {φ : C(ℂ, ℝ)} {δ : ℝ}
    (hδ : 0 < δ) (hφU : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ U) (x : ℂ) :
    harmFn φ δ hδ T x = φ x * g x := by
  rw [harmFn_apply]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  rw [GM.pair_radBump_of_harmonic hg hT hδ (hφU x hx),
    mul_div_assoc, div_self (GM.integral_radProf_pos hδ).ne', mul_one]

theorem exists_bound_harmFn {φ : C(ℂ, ℝ)} (hφ : HasCompactSupport φ) (δ : ℝ) (hδ : 0 < δ)
    (T : DistC) : ∃ M, ∀ x, |harmFn φ δ hδ T x| ≤ M := by
  obtain ⟨C, hC⟩ := (harmFn φ δ hδ T).continuous.bounded_above_of_compact_support
    (hφ.mul_right (f' := fun x => T (GM.radBump δ hδ.le x) / ∫ y, GM.radProf δ y))
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

/-- **`h − φ𝔥 = h̊` on `φ⁻¹(1)`** (T:1229), deterministic form -/
theorem harmFn_sub_apply {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g U)
    {h' hh hz : DistC} (hsum : h' = hh + hz)
    (hT : ∀ ψ : TestOn U, restrictTo U hh ψ = ∫ y, g y * ψ y) {φ : C(ℂ, ℝ)} {δ : ℝ}
    (hδ : 0 < δ) (hφU : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ U) {U₁ : Set ℂ}
    (hφ1 : ∀ x ∈ U₁, φ x = 1) (ψ : TestC) (hψ : tsupport (ψ : ℂ → ℝ) ⊆ U₁) :
    (h' - ofCont (harmFn φ δ hδ hh)) ψ = hz ψ := by
  have hU₁ : tsupport (ψ : ℂ → ℝ) ⊆ U := fun x hx => by
    have h1 := hφ1 x (hψ hx)
    exact hφU x (by rw [h1]; exact one_ne_zero) (mem_closedBall_self hδ.le)
  have e1 : hh ψ = ∫ y, g y * ψ y := by
    rw [apply_eq_restrictTo_testOnOf hh ψ hU₁, hT]; rfl
  have e2 : ofCont (harmFn φ δ hδ hh) ψ = ∫ y, g y * ψ y := by
    rw [ofCont_apply]
    congr 1; funext y
    rw [harmFn_eq_of_harmonic hg hT hδ hφU]
    by_cases hy : ψ y = 0
    · rw [hy]; ring
    · rw [hφ1 y (hψ (subset_tsupport _ hy))]; ring
  rw [sub_apply, hsum, add_apply, e1, e2]
  ring

/-- **The truncated harmonic part** (T:1224–1230, D80 packet P-B): from the Markov data
`h' = 𝔥 + h̊`, `𝔥` a.s. harmonic on `U` and a.s. equal to a `G`-measurable `G₀`, the random
function `fn = harmFn φ δ ∘ G₀` is `G`-measurable, bounded continuous, and `h' − fn = h̊` on
`φ⁻¹(1)` a.s. -/
theorem exists_harmFun {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {U : Opens ℂ}
    {h' hh hz G₀ : Ω → DistC} (hsum : ∀ ω, h' ω = hh ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g U ∧
      ∀ ψ : TestOn U, restrictTo U (hh ω) ψ = ∫ x, g x * ψ x)
    (hae : hh =ᵐ[P] G₀) {φ : C(ℂ, ℝ)} (hφc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hφU : ∀ x, φ x ≠ 0 → closedBall x δ ⊆ U) {U₁ : Set ℂ} (hφ1 : ∀ x ∈ U₁, φ x = 1) :
    (∀ ω, ∃ M, ∀ x, |harmFn φ δ hδ (G₀ ω) x| ≤ M) ∧
      ∀ᵐ ω ∂P, ∀ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ U₁ →
        (h' ω - ofCont (harmFn φ δ hδ (G₀ ω))) ψ = hz ω ψ := by
  refine ⟨fun ω => exists_bound_harmFn hφc δ hδ (G₀ ω), ?_⟩
  filter_upwards [hharm, hae] with ω ⟨g, hg, hT⟩ hω ψ hψ
  rw [← hω]
  exact harmFn_sub_apply hg (hsum ω) hT hδ hφU hφ1 ψ hψ

/-- **the bump function `φ` of Step 2** (T:1226–1227): for a compact `K` inside an open `U` there
are `φ ∈ C_c(ℂ)`, an open `U₁ ⊇ K` with `φ = 1` on `U₁`, and `δ > 0` with `B̄(x, δ) ⊆ U` whenever
`φ(x) ≠ 0` (Urysohn, mathlib `exists_continuous_one_zero_of_isCompact`). -/
theorem exists_bump_of_isCompact {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (φ : C(ℂ, ℝ)) (U₁ : Set ℂ) (δ : ℝ), HasCompactSupport φ ∧ IsOpen U₁ ∧ K ⊆ U₁ ∧
      (∀ x ∈ U₁, φ x = 1) ∧ 0 < δ ∧ ∀ x, φ x ≠ 0 → closedBall x δ ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨φ, h1, h0, hc, -⟩ := exists_continuous_one_zero_of_isCompact (X := ℂ)
    (hK.cthickening (r := r / 2)) (isOpen_thickening (δ := r)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2
      ((cthickening_subset_thickening' hr (by linarith) K)))
  have hts : tsupport φ ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_cthickening).trans hrU
    by_contra hx'
    exact hx (h0 (fun h => hx' (thickening_subset_cthickening r K h)))
  obtain ⟨δ, hδ, hδU⟩ := hc.exists_cthickening_subset_open hU hts
  refine ⟨φ, thickening (r / 2) K, δ, hc, isOpen_thickening, self_subset_thickening hr2 K,
    fun x hx => h1 (thickening_subset_cthickening _ K hx), hδ, fun x hx => ?_⟩
  exact (closedBall_subset_cthickening (subset_tsupport _ hx) δ).trans hδU

end LQGMetric.DFGPS.L217
