/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR4c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR4a
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4

/-!
# (3.9) and the continuous version of `ĥ^D_δ` at a fixed scale (task P2-HEAT3)

Variants of `dgo_incr_bound_all` (HeatDirR3b) and `dgo_hat_cont_version` (HeatDirR4a) where the
circles `∂B(v, δ)` only have to lie in a fixed compact convex `K ⊆ D = (a, a+L)²`, for every
`δ > 0` (no `δ < ε/4`): this is what a version for all radii `δ ∈ (0, 1/2)` on `𝕊(1/2)`
(`Blueprint.IsCircleAvgVersionSq`) needs.

* `dgo_incr_bound_compact`: `π ‖K_u − K_w‖² ≤ (2/δ + 2C/L) ‖u − w‖` (unit-square bound
  `pi_norm_sq_dirCircKernel_sub_le_unit` on `T⁻¹K`, Brownian scaling `norm_dirCircKernel_sub_affT`);
* `dgo_hat_cont_version_K`: a version of `x ↦ √π W(K_{δ, c(x)})` continuous on `ℂ`;
* `dgo_hat_cont_version_compact`: the R4 form for a compact `V` at distance `> ε` from `∂D`,
  `δ < ε/4` (V lies in a box with the same margin; then `dgo_hat_cont_version`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq WhiteNoise SupTail

lemma isCompact_affT_preimage {a L : ℝ} (hL : 0 < L) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (affT a L ⁻¹' K) := by
  have hne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  let h : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (L : ℂ) hne).trans
    (Homeomorph.addLeft ((a : ℂ) + a * Complex.I))
  have e : affT a L ⁻¹' K = h ⁻¹' K := by ext z; simp [h, affT]
  rw [e, h.isCompact_preimage]; exact hK

lemma convex_affT_preimage (a L : ℝ) {K : Set ℂ} (hKc : Convex ℝ K) :
    Convex ℝ (affT a L ⁻¹' K) := by
  intro x hx y hy s t hs ht hst
  show affT a L (s • x + t • y) ∈ K
  have e : affT a L (s • x + t • y) = s • affT a L x + t • affT a L y := by
    have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
    simp only [affT, Complex.real_smul]
    linear_combination (-(a : ℂ) - a * Complex.I) * hst'
  rw [e]; exact hKc hx hy hs ht hst

/-- **(3.9) for circles in a compact convex `K ⊆ D`**, every radius -/
theorem dgo_incr_bound_compact {a L : ℝ} (hL : 0 < L) {K : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKU : K ⊆ sqOpen a L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ u w : ℂ, closedBall u δ ⊆ K → closedBall w δ ⊆ K →
      π * ‖dirCircKernel a L δ u - dirCircKernel a L δ w‖ ^ 2 ≤ (2 / δ + 2 * C / L) * ‖u - w‖ := by
  set K' := affT a L ⁻¹' K
  have hK'U : K' ⊆ openSquare := fun z hz => by
    rw [← sqOpen_zero_one, ← affT_mem_sqOpen_iff hL]; exact hKU hz
  obtain ⟨C, hC0, hC⟩ := exists_hS_lip hK'U (convex_affT_preimage a L hKc)
    (isCompact_affT_preimage hL hK)
  refine ⟨C, hC0, fun δ hδ u w hu hw => ?_⟩
  obtain ⟨u', rfl⟩ := exists_affT_eq (a := a) hL u
  obtain ⟨w', rfl⟩ := exists_affT_eq (a := a) hL w
  obtain ⟨δ', rfl⟩ : ∃ δ', δ = L * δ' := ⟨δ / L, by field_simp⟩
  have hδ' : 0 < δ' := pos_of_mul_pos_right hδ hL.le
  have hpull : ∀ v : ℂ, closedBall (affT a L v) (L * δ') ⊆ K → closedBall v δ' ⊆ K' :=
    fun v hv z hz => hv (by
      rw [mem_closedBall, dist_affT hL]; exact mul_le_mul_of_nonneg_left hz hL.le)
  have hu' := hpull u' hu
  have hw' := hpull w' hw
  rw [norm_dirCircKernel_sub_affT hL hδ' (sqOpen_zero_one ▸ hu'.trans hK'U)
      (sqOpen_zero_one ▸ hw'.trans hK'U),
    show ‖affT a L u' - affT a L w'‖ = L * ‖u' - w'‖ by
      rw [← dist_eq_norm, dist_affT hL, dist_eq_norm]]
  refine (pi_norm_sq_dirCircKernel_sub_le_unit hK'U hC hδ' hu' hw').trans (le_of_eq ?_)
  field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Continuous version of `ĥ^D_δ`** on a box whose `δ`-neighbourhood lies in a compact
convex `K ⊆ D` (fixed `δ > 0`) -/
theorem dgo_hat_cont_version_K (hW : IsWhiteNoise P W) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    {K : Set ℂ} (hK : IsCompact K) (hKc : Convex ℝ K) (hKU : K ⊆ sqOpen a L) {y : ℂ} {b : ℝ}
    (hb : 0 ≤ b) (hV : ∀ v ∈ ferniqueBox y b, closedBall v δ ⊆ K) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] fun ω => Real.sqrt π * W (clampKer a L δ y b x) ω := by
  obtain ⟨C, hC0, hC⟩ := dgo_incr_bound_compact hL hK hKc hKU
  set B := (2 / δ + 2 * C / L) / π
  have hB : 0 ≤ B := by have := Real.pi_pos; positivity
  refine DZZ.exists_continuous_modification_of_kernel_half hW (clampKer a L δ y b) hB
    (fun x x' => ?_) (Real.sqrt π)
  have h := hC δ hδ _ _ (hV _ (DZZ.boxClamp_mem hb x)) (hV _ (DZZ.boxClamp_mem hb x'))
  have hc := DZZ.norm_boxClamp_sub_le y b x x'
  have hπ := Real.pi_pos
  unfold clampKer
  rw [div_mul_eq_mul_div, le_div_iff₀ hπ, mul_comm _ π]
  exact h.trans (mul_le_mul_of_nonneg_left hc (by positivity))

end HeatDir
end DGo
end LQGMetric
