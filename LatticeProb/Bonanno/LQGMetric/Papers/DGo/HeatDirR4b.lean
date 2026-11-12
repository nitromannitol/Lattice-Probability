/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR4b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR4a
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseL4

/-!
# DGo Proposition 3.3 on a square (DG's "Proposition 3.2") (task P2-HEAT3)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, Prop. 3.3 (`prop:coupling`, DGo:549–556;
cited as "DGo Prop 3.2" in DG:1104): for `𝒰 = D = (a, a+L)²`, `V` a box at distance `> ε` from
`∂D` and `δ < ε/4`, `max_V |ĥ^D_δ − η_δ|` has Gaussian tails at level `≫ √(log δ⁻¹)`.

Proof (DGo:702–704): `Δ = ĥ^D_δ − η_δ` is a centred Gaussian process with
`Var(Δ(u) − Δ(v)) ≤ 2A|u−v|/δ + 2√2|u−v|/δ` ((3.9) = `dgo_incr_bound_all` and DDDF L4 for `η`,
`WhiteNoise.variance_phi_sub_le`) and `Var Δ(v) ≤ σ²` ((3.10) = `dgo_var_bound_W`); then the
Fernique–Kolmogorov tail `dgo_prop33_abs_log` (CouplingTail). `Δ` is taken along the
nearest-point map onto `V` so that it is a Gaussian process indexed by `ℂ`.

* **`dgo_prop33_sq`**: for every pair of versions `Y` of `ĥ^D_δ` and `Yη` of `η_δ = φ_{δ,1}`
  continuous on `V`, `P(ζ log δ⁻¹ ≤ max_V |Y − Yη|) ≤ 2 exp(−(ζ log δ⁻¹)²/(8σ²))` once
  `(2K/ζ)² ≤ log δ⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the kernel of `ĥ^D_δ(u) − η_δ(u)` -/
def deltaKer (a L δ : ℝ) (u : ℂ) : WNSpace :=
  Real.sqrt π • dirCircKernel a L δ u - Real.sqrt π • phiKernelL2 δ 1 u

lemma ae_eq_deltaKer (hW : IsWhiteNoise P W) (a L δ : ℝ) (u : ℂ) :
    (fun ω => Real.sqrt π * W (dirCircKernel a L δ u) ω - phi W δ 1 u ω) =ᵐ[P]
      W (deltaKer a L δ u) := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![deltaKer a L δ u, dirCircKernel a L δ u,
    phiKernelL2 δ 1 u] ![1, -Real.sqrt π, Real.sqrt π] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, deltaKer, one_smul, neg_smul]
      rw [norm_eq_zero]; abel)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply, one_mul] at hω
  simp only [phi]
  linarith

lemma norm_sq_deltaKer_sub_le (hW : IsWhiteNoise P W) {a L δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {u v : ℂ}
    (hK : π * ‖dirCircKernel a L δ v - dirCircKernel a L δ u‖ ^ 2 ≤ A * ‖u - v‖ / δ) :
    ‖deltaKer a L δ v - deltaKer a L δ u‖ ^ 2 ≤ (2 * A + 2 * Real.sqrt 2) * ‖u - v‖ / δ := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hφ : π * ‖phiKernelL2 δ 1 v - phiKernelL2 δ 1 u‖ ^ 2 ≤ Real.sqrt 2 * ‖u - v‖ / δ := by
    rw [← variance_sqrtPi_sub hW, norm_sub_rev u v]
    exact variance_phi_sub_le hW hδ hδ1 v u
  have he : deltaKer a L δ v - deltaKer a L δ u =
      Real.sqrt π • (dirCircKernel a L δ v - dirCircKernel a L δ u) -
        Real.sqrt π • (phiKernelL2 δ 1 v - phiKernelL2 δ 1 u) := by
    simp only [deltaKer, smul_sub]; abel
  have hs : ∀ x : WNSpace, ‖Real.sqrt π • x‖ ^ 2 = π * ‖x‖ ^ 2 := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt Real.pi_pos.le]
  rw [he]
  have h1 := norm_sub_le (Real.sqrt π • (dirCircKernel a L δ v - dirCircKernel a L δ u))
    (Real.sqrt π • (phiKernelL2 δ 1 v - phiKernelL2 δ 1 u))
  set p := ‖Real.sqrt π • (dirCircKernel a L δ v - dirCircKernel a L δ u)‖
  set q := ‖Real.sqrt π • (phiKernelL2 δ 1 v - phiKernelL2 δ 1 u)‖
  have hp : p ^ 2 ≤ A * ‖u - v‖ / δ := by rw [hs]; exact hK
  have hq : q ^ 2 ≤ Real.sqrt 2 * ‖u - v‖ / δ := by rw [hs]; exact hφ
  have h2 : ‖Real.sqrt π • (dirCircKernel a L δ v - dirCircKernel a L δ u) -
      Real.sqrt π • (phiKernelL2 δ 1 v - phiKernelL2 δ 1 u)‖ ^ 2 ≤ (p + q) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (p - q)]
  rw [show (2 * A + 2 * Real.sqrt 2) * ‖u - v‖ / δ =
    2 * (A * ‖u - v‖ / δ) + 2 * (Real.sqrt 2 * ‖u - v‖ / δ) by ring]
  linarith

/-- **DGo Proposition 3.3** (`prop:coupling`, DGo:549–556; DG's "Prop 3.2", two-sided,
superpolynomial form) on the square `D = (a, a+L)²` and a box `V` at distance `> ε` from `∂D`. -/
theorem dgo_prop33_sq (hW : IsWhiteNoise P W) {a L ε : ℝ} (hε : 0 < ε) {y : ℂ} {b : ℝ}
    (hb : 0 < b) (hV : ∀ v ∈ ferniqueBox y b, closedBall v ε ⊆ HeatSq.sqOpen a L) :
    ∃ σ2 K : ℝ, 0 < σ2 ∧ ∀ δ ∈ Ioo 0 (min (ε / 4) (1 / 2)), ∀ Y Yη : ℂ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun v => Y v ω) (ferniqueBox y b)) →
      (∀ ω, ContinuousOn (fun v => Yη v ω) (ferniqueBox y b)) →
      (∀ v ∈ ferniqueBox y b, Y v =ᵐ[P] fun ω => Real.sqrt π * W (dirCircKernel a L δ v) ω) →
      (∀ v ∈ ferniqueBox y b, Yη v =ᵐ[P] phi W δ 1 v) →
      ∀ ζ : ℝ, 0 < ζ → (2 * K / ζ) ^ 2 ≤ Real.log δ⁻¹ →
        P.real {ω | ζ * Real.log δ⁻¹ ≤ ⨆ v : ferniqueBox y b, |Y v ω - Yη v ω|} ≤
          2 * Real.exp (-(ζ * Real.log δ⁻¹) ^ 2 / (8 * σ2)) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨A, hA0, hA⟩ := dgo_incr_bound_all a L ε hε
  obtain ⟨σ2, hσ⟩ := dgo_var_bound_W hW a L ε hε
  set A' := 2 * A + 2 * Real.sqrt 2
  have hA' : 0 < A' := by positivity
  refine ⟨max σ2 1, prop33K b A' (max σ2 1) (1 / 2), lt_max_of_lt_right one_pos,
    fun δ hδ Y Yη hY hYη hYv hYηv ζ hζ hℓ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ4 : δ ∈ Ioo 0 (ε / 4) := ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩
  have hδ2 : δ < 1 / 2 := hδ.2.trans_le (min_le_right _ _)
  set c := DZZ.boxClamp y b
  have hcm : ∀ v, c v ∈ ferniqueBox y b := DZZ.boxClamp_mem hb.le
  set Δ : ℂ → Ω → ℝ := fun v ω => Y (c v) ω - Yη (c v) ω
  have hΔW : ∀ v, Δ v =ᵐ[P] W (deltaKer a L δ (c v)) := fun v => by
    filter_upwards [hYv _ (hcm v), hYηv _ (hcm v), ae_eq_deltaKer hW a L δ (c v)] with ω h1 h2 h3
    simp only [Δ, h1, h2]; exact h3
  have hG : IsGaussianProcess Δ P :=
    (hW.isGaussianProcess_comp fun v => deltaKer a L δ (c v)).congr fun v => (hΔW v).symm
  have h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hΔW v), (hW.hasLaw_single _).integral_eq, integral_id_gaussianReal]
  have hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox y b) := fun ω =>
    ((hY ω).sub (hYη ω)).congr fun v hv => by simp only [Δ, c, DZZ.boxClamp_of_mem hv, Pi.sub_apply]
  have hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A' * ‖u - v‖ / δ := by
    intro u hu v hv _
    have hL := hW.hasLaw ![deltaKer a L δ (c v), deltaKer a L δ (c u)] ![1, -1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, neg_one_mul, one_smul, neg_smul, ← sub_eq_add_neg] at hL
    have hae : (fun ω => (Δ v ω - Δ u ω) ^ 2) =ᵐ[P]
        fun ω => (W (deltaKer a L δ (c v)) ω - W (deltaKer a L δ (c u)) ω) ^ 2 := by
      filter_upwards [hΔW v, hΔW u] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae, DDDF.integral_sq_of_hasLaw hL, Real.coe_toNNReal _ (sq_nonneg _)]
    simp only [c, DZZ.boxClamp_of_mem hu, DZZ.boxClamp_of_mem hv]
    exact norm_sq_deltaKer_sub_le hW hδ0 (by linarith)
      (by rw [norm_sub_rev u v]; exact hA δ hδ4 v u (hV v hv) (hV u hu))
  have hvar : ∀ v ∈ ferniqueBox y b, Var[Δ v; P] ≤ max σ2 1 := by
    intro v hv
    have hae : Δ v =ᵐ[P] fun ω => Real.sqrt π * W (dirCircKernel a L δ v) ω - phi W δ 1 v ω := by
      filter_upwards [hYv v hv, hYηv v hv] with ω h1 h2
      simp only [Δ, c, DZZ.boxClamp_of_mem hv, h1, h2]
    rw [variance_congr hae]
    exact (hσ δ hδ4 v (hV v hv)).trans (le_max_left _ _)
  have h := dgo_prop33_abs_log hG h0 hb hδ0 hδ2.le (by norm_num) hA'
    (lt_max_of_lt_right one_pos) hc hinc hvar hζ hℓ
  have hsup : ∀ ω, (⨆ v : ferniqueBox y b, |Δ v ω|) = ⨆ v : ferniqueBox y b, |Y v ω - Yη v ω| :=
    fun ω => iSup_congr fun v => by simp only [Δ, c, DZZ.boxClamp_of_mem v.2]
  simp only [hsup] at h
  exact h

end HeatDir
end DGo
end LQGMetric
