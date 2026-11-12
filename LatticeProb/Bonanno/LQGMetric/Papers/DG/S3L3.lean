/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Notation

/-!
# DG Lemma 3.3, deterministic part: (3.6) ⇒ (3.7) (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.3 (`lem-measure-scale`,
DG:1014–1032). (3.6): a.s. `μ_ĥ(X) = δ^{2+γ²/2} ∫_{δ⁻¹(X−b)} e^{γ ĥ_δ(δ·+b)} dμ_{(ĥ−ĥ_δ)(δ·+b)}`
for all Borel `X`. (3.7): with `T̄ := δ^{−2−γ²/2} exp(−max_U ĥ_δ)`,
`D^ε_ĥ(z,w;U) ≤ D^{T̄ε}_{(ĥ−ĥ_δ)(δ·+b)}(δ⁻¹(z−b), δ⁻¹(w−b); δ⁻¹(U−b))`, and the reverse
inequality with `T̲ := δ^{−2−γ²/2} exp(−min_U ĥ_δ)`. DG's proof (DG:1033–1036): "(3.7) follows
from (3.6) applied to Euclidean balls contained in `U`."

This file proves that deterministic step for arbitrary measures `μ` (for `μ_ĥ`) and `ν` (for
`μ_{(ĥ−ĥ_δ)(δ·+b)}`) related by (3.6), a field `φ` (for `ĥ_δ`) with `m ≤ φ ≤ M` on `Ū`, scale
`a > 0` (for `δ`), shift `b`, exponent `q` (for `2 + γ²/2`):

* `dgLGD_affine_le` — LGD under the affine change of coordinates `y ↦ a y + b`;
* `dg_lemma33_dist` — (3.7), both inequalities.

Convention (proposed deviation DG3A-1): DG's `T̄, T̲` contain `exp(−max ĥ_δ)`, `exp(−min ĥ_δ)`;
(3.6) has the weight `e^{γ ĥ_δ}`, so the constants that (3.6) gives are
`δ^{−2−γ²/2} e^{−γ max ĥ_δ}`, `δ^{−2−γ²/2} e^{−γ min ĥ_δ}`; we use these (`φ = ĥ_δ`, weight
`e^{γφ}`), i.e. we read DG's formula with the factor `γ` in the exponent. (3.6) itself needs the
LQG measure `μ_ĥ` (DG Lemma 3.1) and the coordinate change formula (DS Prop 2.1, node F.AFFINE),
not formalized here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the affine map `y ↦ a y + b` -/
def affineC (a : ℝ) (b y : ℂ) : ℂ := (a : ℂ) * y + b

lemma continuous_affineC (a : ℝ) (b : ℂ) : Continuous (affineC a b) :=
  (continuous_const.mul continuous_id).add continuous_const

lemma dist_affineC {a : ℝ} (ha : 0 < a) (b p y : ℂ) :
    dist (affineC a b p) (affineC a b y) = a * dist p y := by
  rw [dist_eq_norm, dist_eq_norm, affineC, affineC, show (a : ℂ) * p + b - ((a : ℂ) * y + b) =
    (a : ℂ) * (p - y) by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

lemma affineC_inv_affineC {a : ℝ} (ha : 0 < a) (b y : ℂ) :
    affineC a⁻¹ (-b / a) (affineC a b y) = y := by
  have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [affineC]; push_cast; field_simp; ring

lemma affineC_affineC_inv {a : ℝ} (ha : 0 < a) (b x : ℂ) :
    affineC a b (affineC a⁻¹ (-b / a) x) = x := by
  have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [affineC]; push_cast; field_simp; ring

lemma preimage_ball_affineC {a : ℝ} (ha : 0 < a) (b y : ℂ) (r : ℝ) :
    affineC a b ⁻¹' Metric.ball (affineC a b y) (a * r) = Metric.ball y r := by
  ext p
  simp only [mem_preimage, Metric.mem_ball, dist_affineC ha]
  exact mul_lt_mul_iff_of_pos_left ha

/-- the affine image of a ball contained in `cl(T⁻¹ U)` is contained in `cl U` -/
lemma ball_affineC_subset {a : ℝ} {b y : ℂ} {r : ℝ} {U : Set ℂ}
    (h : Metric.ball y r ⊆ closure (affineC a b ⁻¹' U)) :
    affineC a b '' Metric.ball y r ⊆ closure U := by
  rintro _ ⟨p, hp, rfl⟩
  exact (continuous_affineC a b).closure_preimage_subset U (h hp)

/-- **LGD under `y ↦ a y + b`**: if every ball `B(y,r)` whose image `B(ay+b, ar)` lies in `Ū`
and has `ν`-mass `≤ ε'` has image of `μ`-mass `≤ ε`, then
`D^ε_μ(az'+b, aw'+b; U) ≤ D^{ε'}_ν(z', w'; T⁻¹U)`. -/
theorem dgLGD_affine_le {μ ν : Measure ℂ} {a ε ε' : ℝ} (ha : 0 < a) {b : ℂ} {U : Set ℂ}
    (H : ∀ y r, 0 < r → affineC a b '' Metric.ball y r ⊆ closure U →
      ν (Metric.ball y r) ≤ ENNReal.ofReal ε' →
      μ (Metric.ball (affineC a b y) (a * r)) ≤ ENNReal.ofReal ε) (z' w' : ℂ) :
    dgLGD μ ε U (affineC a b z') (affineC a b w') ≤
      dgLGD ν ε' (affineC a b ⁻¹' U) z' w' := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, h1, h2⟩ := hN
  have himg : ∀ i, Metric.ball (affineC a b (x i)) (a * ρ i) ⊆ closure U := fun i q hq => by
    have hq' := affineC_affineC_inv ha b q
    refine hq' ▸ ball_affineC_subset (h1 i).2.1 ⟨_, ?_, rfl⟩
    rw [← preimage_ball_affineC ha b (x i) (ρ i)]
    simpa only [mem_preimage, hq'] using hq
  refine iInf₂_le N ⟨fun i => affineC a b (x i), fun i => a * ρ i,
    P.map (continuous_affineC a b), fun i => ⟨mul_pos ha (h1 i).1, himg i,
      H _ _ (h1 i).1 ((image_subset_iff.2 (fun p hp => by
        rw [mem_preimage, ← preimage_ball_affineC ha b (x i) (ρ i)] at *
        exact himg i hp)).trans subset_rfl) (h1 i).2.2⟩, fun t => ?_⟩
  obtain ⟨i, hi⟩ := h2 t
  refine ⟨i, ?_⟩
  simp only [Path.map_coe, Function.comp_apply, Metric.mem_ball, dist_affineC ha]
  exact mul_lt_mul_of_pos_left hi ha

/-- `∫⁻_B e^{γφ∘T} dν` is between `e^{γm} ν(B)` and `e^{γM} ν(B)` when `T(B) ⊆ Ū` -/
lemma setLIntegral_exp_bounds {ν : Measure ℂ} {a γ m M : ℝ} {b : ℂ} {U : Set ℂ} {φ : ℂ → ℝ}
    (hγ : 0 ≤ γ) (hφ : ∀ x ∈ closure U, m ≤ φ x ∧ φ x ≤ M) {B : Set ℂ} (hB : MeasurableSet B)
    (hTB : affineC a b '' B ⊆ closure U) :
    ENNReal.ofReal (Real.exp (γ * m)) * ν B ≤
        ∫⁻ y in B, ENNReal.ofReal (Real.exp (γ * φ (affineC a b y))) ∂ν ∧
      ∫⁻ y in B, ENNReal.ofReal (Real.exp (γ * φ (affineC a b y))) ∂ν ≤
        ENNReal.ofReal (Real.exp (γ * M)) * ν B := by
  have hb : ∀ y ∈ B, m ≤ φ (affineC a b y) ∧ φ (affineC a b y) ≤ M := fun y hy =>
    hφ _ (hTB ⟨y, hy, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hB fun y hy => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hb y hy).1 hγ))
  · rw [← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hb y hy).2 hγ))

/-- **DG Lemma 3.3, (3.6) ⇒ (3.7)** (DG:1024–1036): if
`μ(X) = a^q ∫_{T⁻¹X} e^{γ φ(T y)} dν(y)` for all Borel `X` (`T y = a y + b`; DG (3.6) with
`a = δ`, `q = 2 + γ²/2`, `φ = ĥ_δ`, `μ = μ_ĥ`, `ν = μ_{(ĥ−ĥ_δ)(δ·+b)}`) and `m ≤ φ ≤ M` on `Ū`,
then with `T̄ = (a^q e^{γM})⁻¹`, `T̲ = (a^q e^{γm})⁻¹`, for all `z', w'`:
`D^ε_μ(Tz', Tw'; U) ≤ D^{T̄ε}_ν(z', w'; T⁻¹U)` and `D^{T̲ε}_ν(z', w'; T⁻¹U) ≤ D^ε_μ(Tz', Tw'; U)`. -/
theorem dg_lemma33_dist {μ ν : Measure ℂ} {a q γ m M ε : ℝ} (ha : 0 < a) {b : ℂ} {U : Set ℂ}
    {φ : ℂ → ℝ} (hγ : 0 ≤ γ) (hφ : ∀ x ∈ closure U, m ≤ φ x ∧ φ x ≤ M)
    (hμ : ∀ X, MeasurableSet X → μ X = ENNReal.ofReal (a ^ q) *
      ∫⁻ y in affineC a b ⁻¹' X, ENNReal.ofReal (Real.exp (γ * φ (affineC a b y))) ∂ν)
    (z' w' : ℂ) :
    dgLGD μ ε U (affineC a b z') (affineC a b w') ≤
        dgLGD ν ((a ^ q * Real.exp (γ * M))⁻¹ * ε) (affineC a b ⁻¹' U) z' w' ∧
      dgLGD ν ((a ^ q * Real.exp (γ * m))⁻¹ * ε) (affineC a b ⁻¹' U) z' w' ≤
        dgLGD μ ε U (affineC a b z') (affineC a b w') := by
  have haq : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  refine ⟨dgLGD_affine_le ha (fun y r hr himg hν => ?_) z' w', ?_⟩
  · -- upper bound
    set c := a ^ q * Real.exp (γ * M)
    have hc : 0 < c := by positivity
    rw [hμ _ Metric.isOpen_ball.measurableSet, preimage_ball_affineC ha]
    have hB := (setLIntegral_exp_bounds (ν := ν) hγ hφ Metric.isOpen_ball.measurableSet himg).2
    calc ENNReal.ofReal (a ^ q) * _ ≤ ENNReal.ofReal (a ^ q) *
          (ENNReal.ofReal (Real.exp (γ * M)) * ν (Metric.ball y r)) := mul_le_mul_right hB _
      _ ≤ ENNReal.ofReal (a ^ q) * (ENNReal.ofReal (Real.exp (γ * M)) *
          ENNReal.ofReal (c⁻¹ * ε)) := mul_le_mul_right (mul_le_mul_right hν _) _
      _ = ENNReal.ofReal ε := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul haq.le, ← ENNReal.ofReal_mul hc.le, ← mul_assoc,
            mul_inv_cancel₀ hc.ne', one_mul]
  · -- lower bound: the same lemma for the inverse map
    set c := a ^ q * Real.exp (γ * m)
    have hc : 0 < c := by positivity
    have hU : affineC a⁻¹ (-b / a) ⁻¹' (affineC a b ⁻¹' U) = U := by
      ext x; simp only [mem_preimage, affineC_affineC_inv ha]
    have h := dgLGD_affine_le (μ := ν) (ν := μ) (ε := c⁻¹ * ε) (ε' := ε) (inv_pos.2 ha)
      (b := -b / a) (U := affineC a b ⁻¹' U) (fun x ρ hρ himg hμ' => ?_)
      (affineC a b z') (affineC a b w')
    · rwa [affineC_inv_affineC ha, affineC_inv_affineC ha, hU] at h
    · set B' := Metric.ball (affineC a⁻¹ (-b / a) x) (a⁻¹ * ρ)
      have hpre : affineC a b ⁻¹' Metric.ball x ρ = B' := by
        have e := preimage_ball_affineC ha b (affineC a⁻¹ (-b / a) x) (a⁻¹ * ρ)
        rwa [affineC_affineC_inv ha, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at e
      have himg' : affineC a b '' B' ⊆ closure U := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ affineC a⁻¹ (-b / a) '' Metric.ball x ρ := by
          refine ⟨affineC a b y, ?_, affineC_inv_affineC ha b y⟩
          rw [← mem_preimage, hpre]; exact hy
        exact (continuous_affineC a b).closure_preimage_subset U (himg hy')
      have hB := (setLIntegral_exp_bounds (ν := ν) hγ hφ Metric.isOpen_ball.measurableSet
        himg').1
      have hμB := hμ (Metric.ball x ρ) Metric.isOpen_ball.measurableSet
      rw [hpre] at hμB
      have h1 : ENNReal.ofReal c * ν B' ≤ μ (Metric.ball x ρ) := by
        rw [hμB, ENNReal.ofReal_mul haq.le, mul_assoc]
        exact mul_le_mul_right hB _
      calc ν B' = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ν B') := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hc).le, inv_mul_cancel₀ hc.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal ε := mul_le_mul_right (h1.trans hμ') _
        _ = ENNReal.ofReal (c⁻¹ * ε) := (ENNReal.ofReal_mul (inv_pos.2 hc).le).symm

end DG
end LQGMetric
