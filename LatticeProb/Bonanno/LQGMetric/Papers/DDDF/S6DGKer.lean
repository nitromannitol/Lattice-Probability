/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGKer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGWire
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CircleKernel
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc3

/-!
# DGo (3.9)–(3.10) for the free kernel (task P2-DGOKER)

Source: Ding–Goswami arXiv:1610.09998, `Watabiki_final.tex`, proof of Prop 3.3 (DGo:600–704),
with the whole plane as the domain. With `δ = 2^{-K}`, `σ_{v,δ}` the uniform measure on
`∂B_δ(v)`, `k_δ(x) = phiKernelL2 δ 1 x` (the kernel of `η_δ(x)`) and
`freeKer K v = K̂(σ_{v,δ}) − k_δ(v)` (`K̂ = hatMeasKerL2`, the kernel of `ĥ(σ)`):

* **(3.10)** (`pi_sq_norm_freeKer_le`, DGo:612–700): `K̂(σ_{v,δ}) = U_{δ,v} K̂(σ_{0,1}) +
  K̂^{(δ²,1]}(σ_{v,δ})` (`DG.wnScale_hatMeasKerL2`: the times `(0, δ²]` are DGo's `G_{v;2}`,
  which is scale free), and `K̂^{(δ²,1]}(σ_{v,δ}) − k_δ(v) = ∫ (k_δ(x) − k_δ(v)) σ_{v,δ}(dx)` is
  DGo's `G_{v;4}` (DGo:684–700, bounded with DGo Lemma 3.2 as in `DGo.dgo_varG4_le`). Hence
  `π‖freeKer K v‖² ≤ (√π‖K̂(σ_{0,1})‖ + 1)²`.
* **(3.9)** (`pi_sq_norm_freeKer_sub_le`, DGo:702–704): `freeKer K u − freeKer K v =
  (K̂(σ_{u,δ}) − K̂(σ_{v,δ})) − (k_δ(u) − k_δ(v))`. The second term is DGo Lemma 3.2
  (`DGo.norm_sqrtPi_smul_phiKernelL2_sub_le`). For the first, DGo cite Hu–Miller–Peres
  (*Thick points of the GFF*, Prop 2.1): the circle-average increment of a log-correlated field
  has variance `O(|u − v|/δ)`. We use exactly that: on the white noise coupled with a whole-plane
  GFF `h₀` (`DG.exists_wn_wholePlaneGFF`), `h₀_δ(z) = √π W(K̂(σ_{z,δ})) + √π W(L_z)` with
  `L_z = ∫ largeKerL2 dσ_{z,δ}` (`DG.ae_circleAvg_eq_wn`), `Var(h₀_δ(u) − h₀_δ(v)) ≤ 2|u − v|/δ`
  (`CircleAvg.incCov_self_le`, the HMP log computation) and `‖L_u − L_v‖ ≤ |u − v|/√(2π)`
  (`DG.lipschitzWith_largeKerL2`). Constant: `π‖freeKer K u − freeKer K v‖² ≤ 12|u − v|/δ`.

Consequently `FreeKerBounds` holds (`freeKerBounds`), and DDDF (6.99), (1.3) follow from the DG
leaves alone (`dddfEq6_99_of_DG'`, `dddfEq1_3_of_DG'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DGKer

open WhiteNoise DG QuantumZipper GFFExist CircleAvg S6DG

/-- translating the circle measure -/
lemma integral_circleUnif_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} (hF : Continuous F) (u v : ℂ) (δ : ℝ) :
    ∫ x, F x ∂circleUnif u δ = ∫ x, F (x + (u - v)) ∂circleUnif v δ := by
  have h := map_affineC_circleUnif 1 (u - v) v δ
  have e1 : affineC 1 (u - v) v = u := by simp [affineC]
  rw [e1, one_mul] at h
  rw [← h, integral_map (continuous_affineC 1 (u - v)).aemeasurable hF.aestronglyMeasurable]
  simp [affineC]

/-- circle averages of a Lipschitz function are Lipschitz in the centre -/
lemma norm_integral_circleUnif_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} (hF : Continuous F) {c : ℝ} (hc : ∀ x y, ‖F x - F y‖ ≤ c * ‖x - y‖)
    (u v : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ x, F x ∂circleUnif u δ - ∫ x, F x ∂circleUnif v δ‖ ≤ c * ‖u - v‖ := by
  have h1 : Integrable (fun x => F (x + (u - v))) (circleUnif v δ) :=
    integrable_circleUnif_of_continuous' (by fun_prop) hδ
  rw [integral_circleUnif_translate hF u v δ, ← integral_sub h1
    (integrable_circleUnif_of_continuous' hF hδ)]
  refine (norm_integral_le_of_norm_le_const (C := c * ‖u - v‖)
    (Eventually.of_forall fun x => ?_)).trans ?_
  · simpa using hc (x + (u - v)) x
  · simp

/-- **HMP Prop 2.1 for `ĥ`** (the input of DGo (3.9), DGo:702–704):
`π‖K̂(σ_{u,δ}) − K̂(σ_{v,δ})‖² ≤ 4|u − v|/δ + |u − v|²`. -/
theorem pi_sq_norm_hat_sub_le {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    Real.pi * ‖hatMeasKerL2 (circleUnif u δ) - hatMeasKerL2 (circleUnif v δ)‖ ^ 2 ≤
      4 * (‖u - v‖ / δ) + ‖u - v‖ ^ 2 := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := exists_wn_wholePlaneGFF
  have := hW.isProbabilityMeasure
  set Hu := hatMeasKerL2 (circleUnif u δ)
  set Hv := hatMeasKerL2 (circleUnif v δ)
  set Lu : WNSpace := ∫ x, largeKerL2 x ∂circleUnif u δ
  set Lv : WNSpace := ∫ x, largeKerL2 x ∂circleUnif v δ
  set sp := Real.sqrt Real.pi with hsp
  set g : WNSpace := sp • (Hu - Hv) + sp • (Lu - Lv) with hg
  have hcomb := hW.ae_eq_zero_of_norm_eq_zero ![g, Hu, Lu, Hv, Lv] ![1, -sp, -sp, sp, sp] (by
    rw [norm_eq_zero]
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, hg]
    module)
  have hX : cInc h₀ δ u δ v =ᵐ[LQGDimension.ExistAsm.stdP] W g := by
    filter_upwards [ae_circleAvg_eq_wn hW hh hae u hδ, ae_circleAvg_eq_wn hW hh hae v hδ, hcomb]
      with ω e1 e2 e3
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Pi.zero_apply] at e3
    simp only [cInc, e1, e2]
    linarith
  have hvar : ‖g‖ ^ 2 ≤ 2 * (‖u - v‖ / δ) := by
    have h1 := (map_cInc hh hδ hδ u v).2
    rw [variance_congr hX, (hW.hasLaw_single g).variance_eq, variance_id_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg _)] at h1
    have h2 := incCov_self_le hδ hδ u v
    simp only [sub_self, abs_zero, zero_add, min_self] at h2
    linarith
  have hL : ‖Lu - Lv‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * ‖u - v‖ :=
    norm_integral_circleUnif_sub_le continuous_largeKerL2 (fun x y => by
      have := lipschitzWith_largeKerL2.dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this) u v hδ
  have hpi := Real.pi_pos
  have hsp0 : 0 < sp := Real.sqrt_pos.2 hpi
  have hsq : sp ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have h2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hL2 : ‖Lu - Lv‖ ^ 2 ≤ ‖u - v‖ ^ 2 / (2 * Real.pi) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hL 2
    rw [mul_pow, inv_pow, hsq2] at this
    rwa [div_eq_inv_mul]
  have htri : sp * ‖Hu - Hv‖ ≤ ‖g‖ + sp * ‖Lu - Lv‖ := by
    have e : sp • (Hu - Hv) = g - sp • (Lu - Lv) := by rw [hg]; abel
    have := norm_sub_le g (sp • (Lu - Lv))
    rw [← e, norm_smul, norm_smul, Real.norm_of_nonneg hsp0.le] at this
    exact this
  have hA : Real.pi * ‖Hu - Hv‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 + 2 * (Real.pi * ‖Lu - Lv‖ ^ 2) := by
    have h0 : 0 ≤ sp * ‖Hu - Hv‖ := by positivity
    have := pow_le_pow_left₀ h0 htri 2
    rw [mul_pow, hsq] at this
    nlinarith [sq_nonneg (‖g‖ - sp * ‖Lu - Lv‖), norm_nonneg g, norm_nonneg (Lu - Lv)]
  have hB : Real.pi * ‖Lu - Lv‖ ^ 2 ≤ ‖u - v‖ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hL2 hpi.le
    refine this.trans (le_of_eq ?_)
    field_simp
  linarith

/-- the decomposition `freeKer K v = U_{δ,v} K̂(σ_{0,1}) + ∫ (k_δ(x) − k_δ(v)) σ_{v,δ}(dx)`
(fine part `G_{v;2}` and `G_{v;4}`, DGo:618–625) -/
lemma freeKer_eq (K : ℕ) (v : ℂ) {δ : ℝ} (hδdef : δ = (2 : ℝ)⁻¹ ^ K) (hδ : 0 < δ) :
    freeKer K v = wnScale hδ v (hatMeasKerL2 (circleUnif 0 1)) +
      ∫ x, (phiKernelL2 δ 1 x - phiKernelL2 δ 1 v) ∂circleUnif v δ := by
  rw [freeKer, ← hδdef]
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hs := wnScale_hatMeasKerL2 hδ hδ1 v (circleUnif 0 1) (memLp_hatMeasKer_circleUnif 0 one_pos)
  have hm : (circleUnif 0 1).map (affineC δ v) = circleUnif v δ := by
    rw [map_affineC_circleUnif]; simp [affineC]
  rw [hm] at hs
  have hk : Integrable (phiKernelL2 δ 1) (circleUnif v δ) :=
    integrable_circleUnif_of_continuous' (DGo.continuous_phiKernelL2 hδ hδ1) hδ
  rw [hs, integral_sub hk (integrable_const _), integral_phiKernelL2_eq hδ _ hk, integral_const,
    probReal_univ, one_smul]
  abel

/-- **DGo (3.10)** for the free kernel -/
theorem pi_sq_norm_freeKer_le (K : ℕ) (v : ℂ) :
    Real.pi * ‖freeKer K v‖ ^ 2 ≤
      (Real.sqrt Real.pi * ‖hatMeasKerL2 (circleUnif 0 1)‖ + 1) ^ 2 := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set sp := Real.sqrt Real.pi with hsp
  have hpi := Real.pi_pos
  have hsp0 : 0 < sp := Real.sqrt_pos.2 hpi
  set G : WNSpace := ∫ x, (phiKernelL2 δ 1 x - phiKernelL2 δ 1 v) ∂circleUnif v δ with hG
  have hG1 : ‖sp • G‖ ≤ 1 := by
    rw [hG, ← integral_smul]
    refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans (by simp)
    filter_upwards [mem_ae_iff.2 (circleUnif_compl_closedBall hδ v)] with x hx
    refine (DGo.norm_sqrtPi_smul_phiKernelL2_sub_le hδ hδ1 x v).trans ?_
    rw [div_le_one hδ]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hn : sp * ‖freeKer K v‖ ≤ sp * ‖hatMeasKerL2 (circleUnif 0 1)‖ + 1 := by
    rw [freeKer_eq K v hδdef hδ, ← hG]
    have := norm_add_le (sp • wnScale hδ v (hatMeasKerL2 (circleUnif 0 1))) (sp • G)
    rw [← smul_add, norm_smul, norm_smul, Real.norm_of_nonneg hsp0.le,
      LinearIsometry.norm_map] at this
    linarith
  have h0 : 0 ≤ sp * ‖freeKer K v‖ := by positivity
  have := pow_le_pow_left₀ h0 hn 2
  rwa [mul_pow, Real.sq_sqrt hpi.le] at this

/-- **DGo (3.9)** for the free kernel -/
theorem pi_sq_norm_freeKer_sub_le (K : ℕ) (u v : ℂ) (huv : ‖u - v‖ ≤ (2 : ℝ)⁻¹ ^ K) :
    Real.pi * ‖freeKer K u - freeKer K v‖ ^ 2 ≤ 12 * ‖u - v‖ / (2 : ℝ)⁻¹ ^ K := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set sp := Real.sqrt Real.pi with hsp
  have hpi := Real.pi_pos
  have hsp0 : 0 < sp := Real.sqrt_pos.2 hpi
  set t := ‖u - v‖ / δ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hδ]; exact huv
  have hut : ‖u - v‖ ≤ t := by
    rw [ht, le_div_iff₀ hδ]
    exact mul_le_of_le_one_right (norm_nonneg _) hδ1
  have hH := pi_sq_norm_hat_sub_le hδ u v
  have hk := DGo.norm_sqrtPi_smul_phiKernelL2_sub_le hδ hδ1 u v
  set Hd := hatMeasKerL2 (circleUnif u δ) - hatMeasKerL2 (circleUnif v δ)
  set kd := phiKernelL2 δ 1 u - phiKernelL2 δ 1 v
  have e : freeKer K u - freeKer K v = Hd - kd := by
    simp only [freeKer, Hd, kd, ← hδdef]; abel
  have htri : sp * ‖freeKer K u - freeKer K v‖ ≤ sp * ‖Hd‖ + t := by
    rw [e]
    have := norm_sub_le (sp • Hd) (sp • kd)
    rw [← smul_sub, norm_smul sp (Hd - kd), norm_smul sp Hd, norm_smul sp kd,
      Real.norm_of_nonneg hsp0.le] at this
    rw [norm_smul, Real.norm_of_nonneg hsp0.le] at hk
    linarith
  have h0 : 0 ≤ sp * ‖freeKer K u - freeKer K v‖ := by positivity
  have h2 := pow_le_pow_left₀ h0 htri 2
  rw [mul_pow, Real.sq_sqrt hpi.le] at h2
  have hsq : (sp * ‖Hd‖) ^ 2 = Real.pi * ‖Hd‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hpi.le]
  have h3 : (sp * ‖Hd‖ + t) ^ 2 ≤ 2 * (sp * ‖Hd‖) ^ 2 + 2 * t ^ 2 := by
    nlinarith [sq_nonneg (sp * ‖Hd‖ - t)]
  have h4 : ‖u - v‖ ^ 2 ≤ t := by nlinarith [norm_nonneg (u - v)]
  have h5 : t ^ 2 ≤ t := by nlinarith
  rw [mul_div_assoc]
  nlinarith

/-- **`FreeKerBounds`**: DGo (3.9)–(3.10) for the free kernel. -/
theorem freeKerBounds : FreeKerBounds :=
  ⟨12, (Real.sqrt Real.pi * ‖hatMeasKerL2 (circleUnif 0 1)‖ + 1) ^ 2, by norm_num,
    by positivity, fun K => ⟨fun v _ => pi_sq_norm_freeKer_le K v,
      fun u _ v _ huv => pi_sq_norm_freeKer_sub_le K u v huv⟩⟩

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from DG Thm 1.5 (1.5b) alone. -/
theorem dddfEq6_99_of_DG' (hKU : Blueprint.DGThm1_5KU) : Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_DG hKU freeKerBounds

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from DG Thm 1.5 (1.5b) and DG Prop 3.21. -/
theorem dddfEq1_3_of_DG' (hKU : Blueprint.DGThm1_5KU) (hP3 : Blueprint.DGProp3_21) : Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_DG hKU hP3 freeKerBounds

end S6DGKer
end DDDF
end LQGMetric
