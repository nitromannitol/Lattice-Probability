/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreFM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Ind
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Convergence in law with a fixed marginal (tool for DFGPS Lemma 2.17, Step 3)

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17, Step 3
(T:1236–1264) and Step 4 (T:1268–1278). Decision D80 (`decisions/DEC-80.md`): the passage from
conditioning on `h|_V` to conditioning on `h|_{cl V}` at T:1276–1277 needs the independence
(eqn-limit-metric-ind) with `h|_{cl V}` (not `h|_V`) on the left. `σ(h|_{cl V})` is not generated
by continuous functions of `h`, so (eqn-internal-metric-ind) is passed to the limit with the law
of `h` held fixed: if `(X, Yₙ) → (X, Y)` in law on `S × T` (all with the same `X`), then
`E[F(X) Θ(Yₙ)] → E[F(X) Θ(Y)]` for every bounded *measurable* `F` and bounded continuous `Θ`.

Proof (standard; own elementary argument, DV-D80): approximate `F` in `L¹(law X)` by a bounded
continuous `g` (mathlib `MemLp.exists_boundedContinuous_integral_rpow_sub_le`, which needs the
law of `X` to be weakly regular: `S` pseudo-metrizable with its Borel σ-algebra); the error
`|E[(F − g)(X) Θ(Z)]| ≤ ‖Θ‖_∞ ‖F − g‖_{L¹(law X)}` is uniform in `Z`.

* `L217.exists_boundedContinuous_integral_abs_sub_le` — the `L¹` approximation.
* `L217.tendsto_integral_mul_of_fixed_marginal` — the fixed-marginal convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

section Approx

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [PseudoMetrizableSpace S]

/-- a bounded measurable function is `L¹(ν)`-approximable by bounded continuous functions -/
theorem exists_boundedContinuous_integral_abs_sub_le (ν : Measure S) [IsFiniteMeasure ν]
    {F : S → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ x, |F x| ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : S →ᵇ ℝ, ∫ x, |F x - g x| ∂ν ≤ δ := by
  have hint : Integrable F ν :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hFb x)
  have hmem : MemLp F (ENNReal.ofReal 1) ν := by
    rw [ENNReal.ofReal_one, memLp_one_iff_integrable]; exact hint
  obtain ⟨g, hg, -⟩ := hmem.exists_boundedContinuous_integral_rpow_sub_le one_pos hδ
  exact ⟨g, by simpa [Real.norm_eq_abs] using hg⟩

end Approx

section Integrable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

lemma integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ ω, |f ω| ≤ C) :
    Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb ω)

end Integrable

section FixedMarginal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S T : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PseudoMetrizableSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

omit [PseudoMetrizableSpace S] in
/-- the error of replacing `F` by `g` is uniform in the second coordinate -/
lemma abs_integral_mul_sub_le {X : Ω → S} (hX : Measurable X)
    {F : S → ℝ} (hF : Measurable F) {CF : ℝ} (hFb : ∀ x, |F x| ≤ CF)
    {Θ : T → ℝ} (hΘ : Continuous Θ) {CΘ : ℝ} (hΘb : ∀ y, |Θ y| ≤ CΘ)
    (g : S →ᵇ ℝ) {Z : Ω → T} (hZ : Measurable Z) :
    |∫ ω, F (X ω) * Θ (Z ω) ∂P - ∫ ω, g (X ω) * Θ (Z ω) ∂P| ≤
      |CΘ| * ∫ x, |F x - g x| ∂(P.map X) := by
  have hΘZ : Measurable fun ω => Θ (Z ω) := hΘ.measurable.comp hZ
  have hgm : Measurable fun x : S => g x := g.continuous.measurable
  have hΘb' : ∀ y, |Θ y| ≤ |CΘ| := fun y => (hΘb y).trans (le_abs_self _)
  have h1 : Integrable (fun ω => F (X ω) * Θ (Z ω)) P :=
    integrable_of_abs_le ((hF.comp hX).mul hΘZ) (C := |CF| * |CΘ|) fun ω => by
      rw [abs_mul]
      exact mul_le_mul ((hFb _).trans (le_abs_self _)) (hΘb' _) (abs_nonneg _) (abs_nonneg _)
  have h2 : Integrable (fun ω => g (X ω) * Θ (Z ω)) P :=
    integrable_of_abs_le ((hgm.comp hX).mul hΘZ) (C := ‖g‖ * |CΘ|) fun ω => by
      rw [abs_mul]
      refine mul_le_mul ?_ (hΘb' _) (abs_nonneg _) (norm_nonneg _)
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (X ω)
  have h3 : ∫ x, |F x - g x| ∂(P.map X) = ∫ ω, |F (X ω) - g (X ω)| ∂P :=
    integral_map hX.aemeasurable (hF.sub hgm).norm.aestronglyMeasurable
  have h4 : Integrable (fun ω => |CΘ| * |F (X ω) - g (X ω)|) P :=
    integrable_of_abs_le (((hF.comp hX).sub (hgm.comp hX)).norm.const_mul _)
      (C := |CΘ| * (|CF| + ‖g‖)) fun ω => by
      rw [abs_mul, abs_abs, abs_abs]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
      · exact (hFb _).trans (le_abs_self _)
      · simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (X ω)
  rw [← integral_sub h1 h2, h3, ← integral_const_mul, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) h4
      (Eventually.of_forall fun ω => ?_))
  show ‖F (X ω) * Θ (Z ω) - g (X ω) * Θ (Z ω)‖ ≤ |CΘ| * |F (X ω) - g (X ω)|
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hΘb' _) (abs_nonneg _)

/-- **Convergence in law with a fixed marginal** (DFGPS Lemma 2.17 Step 3, T:1260, in the form
needed by D80): if `(X, Yₙ) → (X, Y)` in law on `S × T`, then `E[F(X) Θ(Yₙ)] → E[F(X) Θ(Y)]` for
every bounded measurable `F : S → ℝ` and bounded continuous `Θ : T → ℝ`. -/
theorem tendsto_integral_mul_of_fixed_marginal
    {X : Ω → S} (hX : Measurable X) {Yn : ℕ → Ω → T} {Y : Ω → T}
    (hYn : ∀ n, Measurable (Yn n)) (hY : Measurable Y)
    (hconv : ∀ φ : S × T → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X ω, Y ω) ∂P)))
    {F : S → ℝ} (hF : Measurable F) {CF : ℝ} (hFb : ∀ x, |F x| ≤ CF)
    {Θ : T → ℝ} (hΘ : Continuous Θ) {CΘ : ℝ} (hΘb : ∀ y, |Θ y| ≤ CΘ) :
    Tendsto (fun n => ∫ ω, F (X ω) * Θ (Yn n ω) ∂P) atTop
      (𝓝 (∫ ω, F (X ω) * Θ (Y ω) ∂P)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := |CΘ| + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := ε / (3 * K) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨g, hg⟩ := exists_boundedContinuous_integral_abs_sub_le (P.map X) hF hFb hδpos
  have hI0 : 0 ≤ ∫ x, |F x - g x| ∂(P.map X) := integral_nonneg fun x => abs_nonneg _
  -- the error terms
  have herr : ∀ (Z : Ω → T), Measurable Z →
      |∫ ω, F (X ω) * Θ (Z ω) ∂P - ∫ ω, g (X ω) * Θ (Z ω) ∂P| ≤ ε / 3 := by
    intro Z hZ
    refine (abs_integral_mul_sub_le hX hF hFb hΘ hΘb g hZ).trans ?_
    calc |CΘ| * ∫ x, |F x - g x| ∂(P.map X) ≤ K * δ :=
          mul_le_mul (by rw [hK]; linarith) hg hI0 hKpos.le
      _ = ε / 3 := by rw [hδ]; field_simp
  -- convergence for the continuous test function `g(x) Θ(y)`
  have hφ : Tendsto (fun n => ∫ ω, g (X ω) * Θ (Yn n ω) ∂P) atTop
      (𝓝 (∫ ω, g (X ω) * Θ (Y ω) ∂P)) := by
    refine hconv (fun p => g p.1 * Θ p.2)
      ((g.continuous.comp continuous_fst).mul (hΘ.comp continuous_snd)) ⟨‖g‖ * |CΘ|, fun p => ?_⟩
    rw [abs_mul]
    refine mul_le_mul ?_ ((hΘb _).trans (le_abs_self _)) (abs_nonneg _) (norm_nonneg _)
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm p.1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hφ (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have e1 := herr (Yn n) (hYn n)
  have e2 := herr Y hY
  have e3 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  calc |∫ ω, F (X ω) * Θ (Yn n ω) ∂P - ∫ ω, F (X ω) * Θ (Y ω) ∂P|
      = |(∫ ω, F (X ω) * Θ (Yn n ω) ∂P - ∫ ω, g (X ω) * Θ (Yn n ω) ∂P) +
          (∫ ω, g (X ω) * Θ (Yn n ω) ∂P - ∫ ω, g (X ω) * Θ (Y ω) ∂P) +
          (∫ ω, g (X ω) * Θ (Y ω) ∂P - ∫ ω, F (X ω) * Θ (Y ω) ∂P)| := by ring_nf
    _ ≤ |∫ ω, F (X ω) * Θ (Yn n ω) ∂P - ∫ ω, g (X ω) * Θ (Yn n ω) ∂P| +
          |∫ ω, g (X ω) * Θ (Yn n ω) ∂P - ∫ ω, g (X ω) * Θ (Y ω) ∂P| +
          |∫ ω, g (X ω) * Θ (Y ω) ∂P - ∫ ω, F (X ω) * Θ (Y ω) ∂P| := abs_add_three _ _ _
    _ < ε := by rw [abs_sub_comm] at e2; linarith

end FixedMarginal

end LQGMetric.DFGPS.L217
