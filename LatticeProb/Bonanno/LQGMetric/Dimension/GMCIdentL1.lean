/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentL1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable); eLpNorm_one_eq_lintegral_enorm takes the measurability argument, supplied by a.e. measurability of the a.e. limit. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist

/-!
# `L¹` convergence of the circle-average approximations of the square LQG measure
(P2-GMCID, D67)

For a zero-boundary GFF `X` on `𝕍 = (0,1)²`, `0 < γ < 2` and `f` continuous with compact support
in `𝕍`: `∫ f dμ_k → ∫ f dμ` in `L¹(P)`, where `μ_k = areaApprox γ (X ω) k` and
`μ = qAreaMeasureOn γ (X ω) 𝕍` (`tendsto_eLpNorm_areaApprox_sub`), and `∫ f dμ` is integrable.

This is the input "`μ_ε(S)` converges in `L¹(P)` to `μ(S)`" of Berestycki's uniqueness argument
(arXiv:1506.09113, §4, `main.tex` l. 688–689). Proof: the geometric `L¹` rate of the consecutive
increments (`integral_abs_areaApprox_step_le_rate_sq`) and the a.s. limit
(`ae_isVagueLimitOn_qAreaMeasureOn_openSquare`) give `E|Y_k − Y| ≤ ∑_{j ≥ k} E|Y_{j+1} − Y_j|`
(`tendsto_eLpNorm_sub_of_L1_rate`, own elementary proof: telescoping and monotone convergence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology QuantumZipper Real
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma ofReal_abs_sub_le_tsum {G : ℕ → ℝ} {l : ℝ} (hG : Tendsto G atTop (𝓝 l)) (k : ℕ) :
    ENNReal.ofReal |G k - l| ≤ ∑' j, ENNReal.ofReal |G (k + j + 1) - G (k + j)| := by
  have hN : ∀ N, ENNReal.ofReal |G k - G (k + N)| ≤
      ∑' j, ENNReal.ofReal |G (k + j + 1) - G (k + j)| := by
    intro N
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range N))
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : G k - G (k + N) = -∑ j ∈ Finset.range N, (G (k + j + 1) - G (k + j)) := by
      have := Finset.sum_range_sub (fun j => G (k + j)) N
      simp only [← add_assoc] at this
      rw [this]; simp
    rw [e, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hG' : Tendsto (fun N => G (k + N)) atTop (𝓝 l) := by
    have := hG.comp (tendsto_add_atTop_nat k)
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, add_comm]
  have ht : Tendsto (fun N => ENNReal.ofReal |G k - G (k + N)|) atTop
      (𝓝 (ENNReal.ofReal |G k - l|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.sub hG').abs)
  exact le_of_tendsto' ht hN

/-- **`L¹` convergence from a geometric `L¹` rate and an a.s. limit.** -/
theorem tendsto_eLpNorm_sub_of_L1_rate {G : ℕ → Ω → ℝ} {Gl : Ω → ℝ} {k₀ : ℕ} {C q : ℝ}
    (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (hint : ∀ k, k₀ ≤ k → Integrable (G k) P)
    (hstep : ∀ k, k₀ ≤ k → ∫ ω, |G (k + 1) ω - G k ω| ∂P ≤ C * q ^ k)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (Gl ω))) :
    Tendsto (fun k => eLpNorm (G (k₀ + k) - Gl) 1 P) atTop (𝓝 0) := by
  have hGl : AEStronglyMeasurable Gl P :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun k => G (k + k₀))
      (fun k => (hint (k + k₀) (Nat.le_add_left k₀ k)).aestronglyMeasurable)
      (hlim.mono fun ω hω => (tendsto_add_atTop_iff_nat k₀).2 hω)
  have hb : ∀ k, eLpNorm (G (k₀ + k) - Gl) 1 P ≤
      ENNReal.ofReal (C * q ^ k₀ / (1 - q) * q ^ k) := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm ((hint (k₀ + k) (Nat.le_add_right k₀ k)).aestronglyMeasurable.sub hGl)]
    calc ∫⁻ ω, ‖(G (k₀ + k) - Gl) ω‖ₑ ∂P
        ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal |G (k₀ + k + j + 1) ω - G (k₀ + k + j) ω| ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hlim] with ω hω
          rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
          exact ofReal_abs_sub_le_tsum hω _
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal |G (k₀ + k + j + 1) ω - G (k₀ + k + j) ω| ∂P := by
          refine lintegral_tsum fun j => ?_
          exact (((hint _ (by omega)).sub (hint _ (by omega))).abs.aemeasurable).ennreal_ofReal
      _ ≤ ∑' j, ENNReal.ofReal (C * q ^ (k₀ + k) * q ^ j) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hii : Integrable (fun ω => |G (k₀ + k + j + 1) ω - G (k₀ + k + j) ω|) P :=
            ((hint _ (by omega)).sub (hint _ (by omega))).abs
          rw [← ofReal_integral_eq_lintegral_ofReal hii
            (Eventually.of_forall fun _ => abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ((hstep _ (by omega)).trans (le_of_eq ?_))
          rw [show k₀ + k + j = (k₀ + k) + j from rfl, pow_add]; ring
      _ = ENNReal.ofReal (C * q ^ k₀ / (1 - q) * q ^ k) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
            ((summable_geometric_of_lt_one hq0 hq1).mul_left _), tsum_mul_left,
            tsum_geometric_of_lt_one hq0 hq1, pow_add]
          congr 1; ring
  have h0 : Tendsto (fun k => ENNReal.ofReal (C * q ^ k₀ / (1 - q) * q ^ k)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * q ^ k₀ / (1 - q))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hb

/-- The `L¹` limit of an `L¹`-convergent sequence of integrable functions is integrable. -/
lemma integrable_of_tendsto_eLpNorm {G : ℕ → Ω → ℝ} {Gl : Ω → ℝ} (hint : ∀ k, Integrable (G k) P)
    (hGl : AEStronglyMeasurable Gl P)
    (h : Tendsto (fun k => eLpNorm (G k - Gl) 1 P) atTop (𝓝 0)) : Integrable Gl P := by
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  have hm : MemLp (G k - Gl) 1 P := memLp_iff.2 (hk.trans ENNReal.one_lt_top)
  have e : Gl = G k - (G k - Gl) := by abel
  rw [e]; exact (hint k).sub (memLp_one_iff_integrable.1 hm)

variable [IsProbabilityMeasure P] {X : Ω → Measure ℂ → ℝ}

/-- **`L¹` convergence of `∫ f dμ_k` to `∫ f dμ`** for the square LQG measure. -/
theorem tendsto_eLpNorm_areaApprox_sub (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ openSquare) :
    ∃ k₀ : ℕ, (∀ k, k₀ ≤ k → Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (X ω) k)) P) ∧
      Integrable (fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (X ω) openSquare)) P ∧
      Tendsto (fun k => eLpNorm ((fun ω => ∫ z, f z ∂(areaApprox γ (X ω) (k₀ + k))) -
        fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (X ω) openSquare)) 1 P) atTop (𝓝 0) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc hfU
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ z, |f z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hfS : ∀ z ∉ tsupport f, f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  obtain ⟨C, hC0, hC⟩ := integral_abs_areaApprox_step_le_rate_sq hX hγ hγ2 hs
    (isClosed_tsupport f).measurableSet hfc.isCompact.measure_lt_top hTs hf.measurable hM' hfS
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hs
  set q := exp (-AreaExist.areaRate γ * log 2) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos
    (neg_neg_of_pos (AreaExist.areaRate_pos hγ hγ2)) (log_pos one_lt_two))
  have hint : ∀ k, k₀ ≤ k → Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (X ω) k)) P :=
    fun k hk => integrable_integral_areaApprox_sq hX hs (isClosed_tsupport f).measurableSet
      hfc.isCompact.measure_lt_top hTs γ hf.measurable hM' hfS (hk₀ k hk)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, f z ∂(areaApprox γ (X ω) k)) atTop
      (𝓝 (∫ z, f z ∂(qAreaMeasureOn γ (X ω) openSquare))) := by
    filter_upwards [ae_isVagueLimitOn_qAreaMeasureOn_openSquare hX hγ hγ2] with ω h
    exact h.2.2 f hf hfc hfU
  have hT := tendsto_eLpNorm_sub_of_L1_rate (G := fun k ω => ∫ z, f z ∂(areaApprox γ (X ω) k))
    (k₀ := k₀) hC0 (exp_pos _).le hq1 hint (fun k hk => by
      have := hC k (hk₀ k hk)
      have e : exp (-AreaExist.areaRate γ * (k * log 2)) = q ^ k := by
        rw [hq, ← exp_nat_mul]; congr 1; ring
      rw [e] at this
      refine le_trans (le_of_eq ?_) this
      congr 1; funext ω; rw [abs_sub_comm]) hlim
  refine ⟨k₀, hint, ?_, hT⟩
  refine integrable_of_tendsto_eLpNorm (G := fun k ω => ∫ z, f z ∂(areaApprox γ (X ω) (k₀ + k)))
    (fun k => hint _ (by omega)) ?_ hT
  exact aestronglyMeasurable_of_tendsto_ae _
    (fun k => (hint (k + k₀) (by omega)).aestronglyMeasurable)
    (hlim.mono fun ω h => h.comp (tendsto_add_atTop_nat k₀))

end GMCIdent
end LQGMetric
