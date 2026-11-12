/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Notation

/-!
# DG Lemma 3.2, deterministic part: LGD under `dμ₁ = e^{γ f} dμ₂` (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`:

* Definition 1.3 (`def-restricted-lgd`, DG:304–305): the restricted Liouville graph distance
  `D^ε_h(z,w;U)` is "the smallest `N ∈ ℕ` for which there is a collection of `N` Euclidean balls
  contained in `Ū` which have `γ`-LQG mass at most `ε` with respect to `h` and whose union contains
  a continuous path from `z` to `w`" — `dgLGD μ ε U z w` for the measure `μ = μ_h` (open balls of
  positive radius, as in `lgdFree`; `⊤` if there is no such collection).
* Lemma 3.2 (`lem-tr-compare-square`, DG:994–1004), proof (DG:1005–1007): "This follows from
  Lemma 3.1 applied with `A = γ⁻¹ log C` and the fact that … `dμ_{h¹} = e^{γ(h¹−h²)} dμ_{h²}`."
  `dgLGD_compare_of_withDensity` is the deterministic step: if `μ₁ = e^{γ f} μ₂` and
  `|f| ≤ γ⁻¹ log C` on `Ū`, then `D^{Cε}_{μ₁} ≤ D^ε_{μ₂} ≤ D^{ε/C}_{μ₁}` for all `z, w`.
  The probabilistic half (Lemma 3.1's tail for `max_K |h¹ − h²|` and the identity of the LQG
  measures) is not formalized here (see handoff/P2-DG3A.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- **DG Definition 1.3** (DG:305): the restricted Liouville graph distance `D^ε(z,w;U)` of a
measure `μ`: least number of open Euclidean balls contained in `Ū`, each of `μ`-mass `≤ ε`, whose
union contains a path from `z` to `w`. -/
def dgLGD (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∃ (x : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path z w),
      (∀ i, 0 < ρ i ∧ Metric.ball (x i) (ρ i) ⊆ closure U ∧
        μ (Metric.ball (x i) (ρ i)) ≤ ENNReal.ofReal ε) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)), (N : ℕ∞)

/-- monotonicity: if every ball in `Ū` of `μ₂`-mass `≤ ε₂` has `μ₁`-mass `≤ ε₁`, then
`D^{ε₁}_{μ₁} ≤ D^{ε₂}_{μ₂}` -/
theorem dgLGD_le_of_ball {μ₁ μ₂ : Measure ℂ} {ε₁ ε₂ : ℝ} {U : Set ℂ}
    (H : ∀ x ρ, Metric.ball x ρ ⊆ closure U → μ₂ (Metric.ball x ρ) ≤ ENNReal.ofReal ε₂ →
      μ₁ (Metric.ball x ρ) ≤ ENNReal.ofReal ε₁) (z w : ℂ) :
    dgLGD μ₁ ε₁ U z w ≤ dgLGD μ₂ ε₂ U z w := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  exact iInf₂_le N ⟨x, ρ, P, fun i => ⟨(h1 i).1, (h1 i).2.1,
    H _ _ (h1 i).2.1 (h1 i).2.2⟩, h2⟩

/-- `μ₁ = e^{γ f} μ₂` with `|γ f| ≤ log C` on `Ū`: masses of balls in `Ū` agree up to `C` -/
lemma ball_mass_compare {μ₂ : Measure ℂ} {g : ℂ → ℝ} {U : Set ℂ} {C : ℝ} (hC : 0 < C)
    (hg : ∀ x ∈ closure U, |g x| ≤ Real.log C) {x : ℂ} {ρ : ℝ}
    (hB : Metric.ball x ρ ⊆ closure U) :
    (μ₂.withDensity fun y => ENNReal.ofReal (Real.exp (g y))) (Metric.ball x ρ) ≤
        ENNReal.ofReal C * μ₂ (Metric.ball x ρ) ∧
      μ₂ (Metric.ball x ρ) ≤
        ENNReal.ofReal C * (μ₂.withDensity fun y => ENNReal.ofReal (Real.exp (g y)))
          (Metric.ball x ρ) := by
  rw [withDensity_apply _ Metric.isOpen_ball.measurableSet]
  refine ⟨?_, ?_⟩
  · rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_log hC]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hg y (hB hy)))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy => ?_
    rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_log hC, ← Real.exp_add]
    exact Real.one_le_exp (by linarith [neg_abs_le (g y), hg y (hB hy)])

/-- **DG Lemma 3.2, deterministic step** (DG:1005–1007): if `μ₁ = e^{g} μ₂` (`g = γ(h¹ − h²)`)
and `|g| ≤ log C` on `Ū` (`C > 0`), then for all `z, w`,
`D^{Cε}_{μ₁}(z,w;U) ≤ D^ε_{μ₂}(z,w;U) ≤ D^{ε/C}_{μ₁}(z,w;U)`. -/
theorem dgLGD_compare_of_withDensity {μ₂ : Measure ℂ} {g : ℂ → ℝ} {U : Set ℂ} {C ε : ℝ}
    (hC : 0 < C) (hg : ∀ x ∈ closure U, |g x| ≤ Real.log C) (z w : ℂ) :
    dgLGD (μ₂.withDensity fun y => ENNReal.ofReal (Real.exp (g y))) (C * ε) U z w ≤
        dgLGD μ₂ ε U z w ∧
      dgLGD μ₂ ε U z w ≤
        dgLGD (μ₂.withDensity fun y => ENNReal.ofReal (Real.exp (g y))) (ε / C) U z w := by
  refine ⟨dgLGD_le_of_ball (fun x ρ hB h => ?_) z w, dgLGD_le_of_ball (fun x ρ hB h => ?_) z w⟩
  · refine (ball_mass_compare hC hg hB).1.trans ?_
    rw [ENNReal.ofReal_mul hC.le]
    exact mul_le_mul_right h _
  · refine (ball_mass_compare hC hg hB).2.trans ?_
    calc ENNReal.ofReal C * _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
          mul_le_mul_right h _
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hC.le]; congr 1; field_simp

/-- **DG Lemma 3.2** (`lem-tr-compare-square`, DG:994–1007) from the tail of DG Lemma 3.1:
let `μ₁ = e^{γ g} μ₂` pathwise (DG: `dμ_{h¹} = e^{γ(h¹ − h²)} dμ_{h²}`, `g = h¹ − h²`; for
`ĥ, ĥ^tr` this is DG's definition of their LQG measures, DG:980–986) and suppose
`P[max_{K̄} |g| > A] ≤ c₀ e^{−c₁A²}` for `A > 1` (DG (3.5), Lemma 3.1; DG's `K` is closed).
Then there are `a₀, a₁ > 0` such that for all `C > 1` and `ε`,
`P[¬ (D^{Cε}_{μ₁}(z,w;K) ≤ D^ε_{μ₂}(z,w;K) ≤ D^{ε/C}_{μ₁}(z,w;K) ∀ z,w)] ≤ a₀ e^{−a₁ (log C)²}`.
DG's proof: "Lemma 3.1 applied with `A = γ⁻¹ log C`". -/
theorem dg_lemma32_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ) {K : Set ℂ} (μ₂ : Ω → Measure ℂ)
    (g : Ω → ℂ → ℝ) {c₀ c₁ : ℝ} (hc₁ : 0 < c₁)
    (htail : ∀ A : ℝ, 1 < A →
      P {ω | ¬ ∀ z ∈ closure K, |g ω z| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2))) :
    ∃ a₀ a₁ : ℝ, 0 < a₁ ∧ ∀ C : ℝ, 1 < C → ∀ ε : ℝ,
      P {ω | ¬ ∀ z w : ℂ,
        dgLGD ((μ₂ ω).withDensity fun y => ENNReal.ofReal (Real.exp (γ * g ω y))) (C * ε) K z w ≤
            dgLGD (μ₂ ω) ε K z w ∧
          dgLGD (μ₂ ω) ε K z w ≤
            dgLGD ((μ₂ ω).withDensity fun y => ENNReal.ofReal (Real.exp (γ * g ω y))) (ε / C)
              K z w} ≤
        ENNReal.ofReal (a₀ * Real.exp (-a₁ * Real.log C ^ 2)) := by
  refine ⟨max c₀ (Real.exp c₁), c₁ / γ ^ 2, by positivity, fun C hC ε => ?_⟩
  have hC0 : 0 < C := by linarith
  set A := Real.log C / γ with hA_def
  have hA0 : 0 < A := div_pos (Real.log_pos hC) hγ
  have hexp : -(c₁ / γ ^ 2) * Real.log C ^ 2 = -c₁ * A ^ 2 := by
    rw [hA_def]; field_simp
  rw [hexp]
  have hsub : {ω | ¬ ∀ z w : ℂ,
        dgLGD ((μ₂ ω).withDensity fun y => ENNReal.ofReal (Real.exp (γ * g ω y))) (C * ε) K z w ≤
            dgLGD (μ₂ ω) ε K z w ∧
          dgLGD (μ₂ ω) ε K z w ≤
            dgLGD ((μ₂ ω).withDensity fun y => ENNReal.ofReal (Real.exp (γ * g ω y))) (ε / C)
              K z w} ⊆ {ω | ¬ ∀ z ∈ closure K, |g ω z| ≤ A} := by
    intro ω hω hg
    refine hω fun z w => dgLGD_compare_of_withDensity hC0 (fun x hx => ?_) z w
    rw [abs_mul, abs_of_pos hγ]
    have := hg x hx
    rw [hA_def, le_div_iff₀ hγ] at this
    linarith
  refine (measure_mono hsub).trans ?_
  rcases lt_or_ge 1 A with hA1 | hA1
  · refine (htail A hA1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) ≤ Real.exp c₁ * Real.exp (-c₁ * A ^ 2) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : A ^ 2 ≤ 1 := by nlinarith
          nlinarith
      _ ≤ max c₀ (Real.exp c₁) * Real.exp (-c₁ * A ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end DG
end LQGMetric
