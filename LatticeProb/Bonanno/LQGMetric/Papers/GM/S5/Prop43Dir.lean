/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43Dir at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43Frk

/-!
# GM (5.9): the Dirichlet condition (5.5) for `h − φ` on `E_r` (task P2-M2N, WP-M2n)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
In the proof of Lemma 5.4 (l. 2826) GM state: "Property (B) implies that the Dirichlet energy
condition (5.5) in the definition of `𝔈_r` holds with `h − φ` in place of `h` whenever `E_r`
occurs". Literally (with `Λ = e^{Λ₀}`) this misses the cross term `(φ, ψ)_∇` (DV-B6). Here, with
`(h − φ, ψ)_∇ = (h, ψ)_∇ − (φ, ψ)_∇` and `|(φ, ψ)_∇| ≤ ½((φ,φ)_∇ + (ψ,ψ)_∇)` (pointwise
`|⟨∇φ, ∇ψ⟩| ≤ ½(|∇φ|² + |∇ψ|²)` and the Green identity, QuantumZipper `K3` F3), (B) gives (5.5) at
`h − φ` with the deterministic, scale-free constant `Λ := e^{3Λ₀}`:

* `dirInner_subTest` : `(g − φ, ψ)_∇ = (g, ψ)_∇ − ∫ φ ρ_ψ`;
* `abs_integral_mul_cmTest_le` : `|∫ φ ρ_ψ| ≤ ((φ,φ)_∇ + (ψ,ψ)_∇)/2`;
* `exp_dir_subTest_le` : (B) for `φ, ψ ∈ G` at `g` ⇒ `exp(−(g−φ,ψ)_∇ + ½(ψ,ψ)_∇) ≤ e^{3Λ₀}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Laplacian
open scoped Real

namespace LQGMetric.GM

/-- `(g − φ, ψ)_∇ = (g, ψ)_∇ − ∫ φ ρ_ψ`, `ρ_ψ = −Δψ/(2π)` -/
lemma dirInner_subTest (g : DistC) (φ ψ : TestC) :
    dirInner (subTest g φ) ψ = dirInner g ψ - ∫ x, φ x * cmTest ψ x := by
  have e := pair0_addFun g (-φ) (cmTest0 ψ)
  have e1 : dirInner (subTest g φ) ψ = pair0 (addFun g (testCont (-φ))) (cmTest0 ψ) := by
    rw [← subTest_eq_addFun_neg_cm]; rfl
  rw [e1, e]
  have e2 : ∫ x, (cmTest0 ψ).1 x * (-φ : TestC) x = -∫ x, φ x * cmTest ψ x := by
    rw [← integral_neg]
    congr 1
    funext x
    show cmTest ψ x * (-(φ : ℂ → ℝ) x) = -((φ : ℂ → ℝ) x * cmTest ψ x)
    ring
  rw [e2]
  rfl

lemma integrable_gradInner_cm (φ ψ : TestC) :
    Integrable (QuantumZipper.K3.gradInner φ ψ) := by
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 (ψ : ℂ → ℝ) := ψ.contDiff.of_le (by simp)
  have hi : ∀ v : ℂ, Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z v * fderiv ℝ (ψ : ℂ → ℝ) z v) :=
    fun v => (((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) v).mul_left
  exact (hi 1).add (hi Complex.I)

/-- `|∫ φ ρ_ψ| ≤ ((φ,φ)_∇ + (ψ,ψ)_∇)/2` -/
lemma abs_integral_mul_cmTest_le (φ ψ : TestC) :
    |∫ x, φ x * cmTest ψ x| ≤ (gradEnergy φ + gradEnergy ψ) / 2 := by
  have hψ2 : ContDiff ℝ 2 (ψ : ℂ → ℝ) := contDiff_two_testC ψ
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hG := QuantumZipper.K3.integral_gradInner_eq_neg_integral_mul_laplacian hφ1 hψ2
    ψ.hasCompactSupport
  have e : ∫ x, φ x * cmTest ψ x = (2 * π)⁻¹ * ∫ z, QuantumZipper.K3.gradInner φ ψ z := by
    rw [hG]
    simp only [cmTest_apply]
    rw [show (fun x => (φ : ℂ → ℝ) x * (-(2 * π)⁻¹ * Δ (⇑ψ) x)) =
        fun x => -(2 * π)⁻¹ * ((φ : ℂ → ℝ) x * Δ (⇑ψ) x) from funext fun x => by ring,
      integral_const_mul]
    ring
  have hpt : ∀ z, |QuantumZipper.K3.gradInner φ ψ z| ≤
      (QuantumZipper.K3.gradInner φ φ z + QuantumZipper.K3.gradInner ψ ψ z) / 2 := by
    intro z
    unfold QuantumZipper.K3.gradInner
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (fderiv ℝ (φ : ℂ → ℝ) z 1 - fderiv ℝ (ψ : ℂ → ℝ) z 1),
      sq_nonneg (fderiv ℝ (φ : ℂ → ℝ) z Complex.I - fderiv ℝ (ψ : ℂ → ℝ) z Complex.I),
      sq_nonneg (fderiv ℝ (φ : ℂ → ℝ) z 1 + fderiv ℝ (ψ : ℂ → ℝ) z 1),
      sq_nonneg (fderiv ℝ (φ : ℂ → ℝ) z Complex.I + fderiv ℝ (ψ : ℂ → ℝ) z Complex.I)]
  have hEφ : gradEnergy φ = (2 * π)⁻¹ * ∫ z, QuantumZipper.K3.gradInner φ φ z := by
    simp only [gradEnergy, QuantumZipper.K3.norm_fderiv_sq_eq_gradInner]
  have hEψ : gradEnergy ψ = (2 * π)⁻¹ * ∫ z, QuantumZipper.K3.gradInner ψ ψ z := by
    simp only [gradEnergy, QuantumZipper.K3.norm_fderiv_sq_eq_gradInner]
  have hint := ((integrable_gradInner_cm φ φ).add (integrable_gradInner_cm ψ ψ)).div_const 2
  have hle : |∫ z, QuantumZipper.K3.gradInner φ ψ z| ≤
      ∫ z, (QuantumZipper.K3.gradInner φ φ z + QuantumZipper.K3.gradInner ψ ψ z) / 2 :=
    (abs_integral_le_integral_abs).trans
      (integral_mono (integrable_gradInner_cm φ ψ).abs hint hpt)
  rw [integral_div, integral_add (integrable_gradInner_cm φ φ) (integrable_gradInner_cm ψ ψ)]
    at hle
  have hpi : 0 < (2 * π)⁻¹ := by positivity
  rw [e, abs_mul, abs_of_pos hpi, hEφ, hEψ]
  nlinarith

/-- **GM (5.9)** (l. 2826, as corrected, DV-B6): if Prop 5.2 (B) holds at `g` for `φ, ψ ∈ G`,
then (5.5) holds at `g − φ` for `ψ` with `Λ = e^{3Λ₀}`. -/
lemma exp_dir_subTest_le {G : Set TestC} {Λ₀ : ℝ} {g : DistC}
    (hB : ∀ ψ ∈ G, |dirInner g ψ| + gradEnergy ψ / 2 ≤ Λ₀) {φ : TestC} (hφ : φ ∈ G)
    {ψ : TestC} (hψ : ψ ∈ G) :
    Real.exp (-dirInner (subTest g φ) ψ + gradEnergy ψ / 2) ≤ Real.exp (3 * Λ₀) := by
  refine Real.exp_le_exp.2 ?_
  rw [dirInner_subTest]
  have h1 := hB φ hφ
  have h2 := hB ψ hψ
  have h3 := abs_integral_mul_cmTest_le φ ψ
  have h4 := neg_le_abs (dirInner g ψ)
  have h7 := abs_nonneg (dirInner g ψ)
  have h5 := le_abs_self (∫ x, φ x * cmTest ψ x)
  have h6 := abs_nonneg (dirInner g φ)
  linarith

/-- (5.4) forces the path to hit `B_{2r}(z)` (GM l. 2825: "which implies in particular that
`P^φ ∩ B_{2r}(0) ≠ ∅`") -/
lemma hit_of_frkDist {D D' : DistC → ContMetric} {cs Cs c₂ b₀ r : ℝ} {z : ℂ} {g : DistC}
    {Q : C(unitInterval, ℂ)} (hr : 0 < r) (hQ : frkDist D D' cs Cs c₂ b₀ r z g Q) :
    (range Q ∩ Metric.ball z (2 * r)).Nonempty := by
  obtain ⟨s, -, -, -, -, hs, -⟩ := hQ
  exact ⟨Q s, mem_range_self s, Metric.ball_subset_ball (by linarith) hs⟩

end LQGMetric.GM
