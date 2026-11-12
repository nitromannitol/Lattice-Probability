/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsiCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiCmp

/-!
# Continuous versions of `ψ_{a,b}` (task P2-DDDFPSI; blueprint DDDF.D2.psi)

* `exists_continuous_modification_of_kernel`: for any kernel family `F : ℂ → L²` with
  `‖F x − F x'‖² ≤ K |x − x'|²`, the field `x ↦ c · W(F x)` has a modification continuous for
  every `ω`. Same proof as `exists_continuous_modification_phi` (P2-WN): Gaussian 4th moments
  (QZ `KolmG.lintegral_pow_two_mul_of_map_eq`) and Kolmogorov–Čentsov on `Fin 2 → ℝ`
  (QZ `KolmN.exists_continuous_modification_N`; Revuz–Yor Ch. I Thm (2.1)).
* `sq_norm_psiKernelL2_sub_le`: `‖k^{Tr}_x − k^{Tr}_{x'}‖² ≤ K |x − x'|²` for `0 < a ≤ b`
  (the split of `WhiteNoisePsiL4` with the bound `(T_x − T_{x'})² ≤ L²|x − x'|²/(r₀² a²)`).
* `exists_continuous_modification_psi`: the continuous version of `ψ_{a,b}` (DDDF uses the
  a.s. continuous version throughout, e.g. `‖φ_{0,n} − ψ_{0,n}‖_{[0,1]²}` in Prop 5, l. 423).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Continuous version of a white-noise field with Lipschitz kernel.** -/
theorem exists_continuous_modification_of_kernel (hW : IsWhiteNoise P W) (F : ℂ → WNSpace)
    {K : ℝ} (hK : 0 ≤ K) (hF : ∀ x x', ‖F x - F x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ 2) (c : ℝ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] fun ω => c * W (F x) ω := by
  set C : ℝ := c ^ 2 * K with hC
  have hC0 : 0 ≤ C := by positivity
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => c * W (F (finTwoToC q)) ω with hZ
  have hZmeas : ∀ q, Measurable (Z q) := fun q => (hW.measurable _).const_mul _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P 4 4 K R := by
    intro R
    refine ⟨C ^ 2 * QuantumZipper.gaussianAbsMoment 4 * 16, by
      have := QuantumZipper.gaussianAbsMoment_nonneg 4; positivity, fun q _ q' _ => ?_⟩
    have h := hW.hasLaw ![F (finTwoToC q), F (finTwoToC q')] ![c, -c]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hlaw : HasLaw (fun ω => Z q ω - Z q' ω)
        (gaussianReal 0 (‖c • F (finTwoToC q) + (-c) • F (finTwoToC q')‖ ^ 2).toNNReal) P :=
      h.congr (Eventually.of_forall fun ω => by simp only [hZ]; ring)
    have e := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hZmeas q).sub (hZmeas q')) 2 hlaw.map_eq
    simp only [Pi.sub_apply] at e
    rw [show (4 : ℕ) = 2 * 2 from rfl, e]
    refine ENNReal.ofReal_le_ofReal ?_
    set v := ‖c • F (finTwoToC q) + (-c) • F (finTwoToC q')‖ ^ 2
    have hv : v ≤ C * ‖finTwoToC q - finTwoToC q'‖ ^ 2 := by
      simp only [v]
      rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hC, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hF _ _) (sq_nonneg c)
    have hM := QuantumZipper.gaussianAbsMoment_nonneg 4
    have hn := norm_finTwoToC_sub_le q q'
    have hv' : ((v.toNNReal : NNReal) : ℝ) ≤ C * (2 * ‖q - q'‖) ^ 2 := by
      rw [Real.coe_toNNReal']
      refine max_le (hv.trans ?_) (by positivity)
      gcongr
    have hv0 : 0 ≤ ((v.toNNReal : NNReal) : ℝ) := NNReal.coe_nonneg _
    calc ((v.toNNReal : NNReal) : ℝ) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2)
        ≤ (C * (2 * ‖q - q'‖) ^ 2) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2) := by
          gcongr
      _ = C ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2) * 16 * ‖q - q'‖ ^ (4 : ℝ) := by
          rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (d := 2) (P := P) (Z := Z) (fun q => (hZmeas _).aemeasurable)
    (p := 4) (by norm_num) (a := 4) (by norm_num) hmom
  -- a measurable full-measure set on which the dyadic values converge to `Y₀`
  set B : Set Ω := {ω | ¬ ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
    (nhds (Y₀ q ω))} with hB
  set G : Set Ω := (toMeasurable P B)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hG, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp hYt
  have hGt : ∀ ω ∈ G, ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
      (nhds (Y₀ q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  set Y : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => G.indicator (fun ω => Y₀ q ω) ω with hY
  have hYc : ∀ ω, Continuous fun q => Y q ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hYc₀ ω
    · simp only [hY, indicator_of_notMem hω]; exact continuous_const
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => G.indicator (Z (QuantumZipper.KolmD.rndD n q)))
      (fun n => (hZmeas _).indicator hGm) (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hGt ω hω q
    · simp only [hY, indicator_of_notMem hω]; exact tendsto_const_nhds
  have hYm : ∀ q, (fun ω => Y q ω) =ᵐ[P] Z q := by
    intro q
    filter_upwards [hGae, hYm₀ q] with ω h1 h2
    simp only [hY, indicator_of_mem h1]
    exact h2
  let fromC : ℂ → Fin 2 → ℝ := fun z => ![z.re, z.im]
  have hfc : Continuous fromC := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  have hft : ∀ z, finTwoToC (fromC z) = z := fun z => by
    apply Complex.ext <;> simp [finTwoToC, fromC]
  refine ⟨fun x ω => Y (fromC x) ω, fun ω => (hYc ω).comp hfc, fun x => hYmeas _, fun x => ?_⟩
  have := hYm (fromC x)
  simp only [hZ, hft] at this
  exact this


namespace PsiParams

variable (Q : PsiParams)

/-- The pointwise split with the constant bound `(T_x − T_{x'})² ≤ (L|x − x'|/(r₀ a))²`. -/
lemma sq_psiKernel_sub_le_const {L : NNReal} (hL : LipschitzWith L Q.cut.Φ) {a : ℝ}
    (ha : 0 < a) (b : ℝ) (x x' : ℂ) (p : ℝ × ℂ) :
    (Q.psiKernel a b x p - Q.psiKernel a b x' p) ^ 2 ≤
      2 * (phiKernel a b x p - phiKernel a b x' p) ^ 2 +
        2 * (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator (fun p =>
          (L * ‖x - x'‖ / (Q.r₀ * a)) ^ 2 * heatKernel (p.1 / 2) x' p.2 ^ 2) p := by
  by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
  · have ht : 0 < p.1 := lt_of_lt_of_le (by positivity) (mem_prod.mp hp).1.1
    have hsa : a ≤ Real.sqrt p.1 := by
      rw [← Real.sqrt_sq ha.le]; exact Real.sqrt_le_sqrt (mem_prod.mp hp).1.1
    simp only [psiKernel, phiKernel, indicator_of_mem hp]
    set A := heatKernel (p.1 / 2) x p.2
    set B := heatKernel (p.1 / 2) x' p.2
    set T := Q.trunc x p
    set T' := Q.trunc x' p
    have hT0 := Q.trunc_nonneg x p
    have hT1 := Q.trunc_le_one x p
    have hd := Q.abs_trunc_sub_le hL x x' p ht
    have hd' : |T - T'| ≤ L * ‖x - x'‖ / (Q.r₀ * a) := hd.trans
      (div_le_div_of_nonneg_left (by positivity) (mul_pos Q.r₀_pos ha)
        (mul_le_mul_of_nonneg_left hsa Q.r₀_pos.le))
    have hsq : (T - T') ^ 2 ≤ (L * ‖x - x'‖ / (Q.r₀ * a)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd' 2
    have e : A * T - B * T' = (A - B) * T + B * (T - T') := by ring
    rw [e]
    have h1 : ((A - B) * T) ^ 2 ≤ (A - B) ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)
    have h2 : (B * (T - T')) ^ 2 ≤ (L * ‖x - x'‖ / (Q.r₀ * a)) ^ 2 * B ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    nlinarith [sq_nonneg ((A - B) * T - B * (T - T'))]
  · simp [psiKernel, phiKernel, indicator_of_notMem hp]

/-- `‖k^{Tr}_{a,b,x} − k^{Tr}_{a,b,x'}‖² ≤ K |x − x'|²` for `0 < a ≤ b`. -/
theorem exists_sq_norm_psiKernelL2_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x x' : ℂ,
      ‖Q.psiKernelL2 a b x - Q.psiKernelL2 a b x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ 2 := by
  obtain ⟨L, hL⟩ := Q.cut.exists_lipschitz
  have hpi := Real.pi_pos
  have hr₀ := Q.r₀_pos
  have ha2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hba : 0 ≤ b ^ 2 - a ^ 2 := by linarith
  set M : ℝ := (L : ℝ) / (Q.r₀ * a)
  refine ⟨2 * ((b ^ 2 - a ^ 2) / (2 * a ^ 4) / Real.pi) +
    2 * (M ^ 2 * ((b ^ 2 - a ^ 2) * (2 * Real.pi * a ^ 2)⁻¹)), by positivity,
    fun x x' => ?_⟩
  set r := ‖x - x'‖
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht =>
    lt_of_lt_of_le (by positivity) ht.1
  -- the `φ` part
  have hφ : ∫ p, (phiKernel a b x p - phiKernel a b x' p) ^ 2 ≤
      (b ^ 2 - a ^ 2) / (2 * a ^ 4) / Real.pi * r ^ 2 := by
    have h := sq_norm_phiKernelL2_sub ha b x x'
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hpi.le, sq_norm_phiKernelL2_sub' ha] at h
    have h2 := incrVar_le ha hab x x'
    rw [← h] at h2
    have e : ‖x - x'‖ ^ 2 / (2 * a ^ 4) * (b ^ 2 - a ^ 2) = (b ^ 2 - a ^ 2) / (2 * a ^ 4) * r ^ 2 := by
      simp only [r]; ring
    rw [e] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    linarith
  -- the truncation part
  have hFub := integral_timeWeight (a := a) (b := b)
    (w := fun _ => (L * r / (Q.r₀ * a)) ^ 2) (g := fun t => heatKernel t x' x')
    (G := fun p => heatKernel (p.1 / 2) x' p.2 ^ 2)
    continuousOn_const (fun t ht => by positivity) measurable_const
    (continuousOn_heatKernel_time a ha b x' x') (by
      have := measurable_heatKernel_half x'; fun_prop)
    (fun p _ => sq_nonneg _)
    (fun t ht => by
      simpa [sq] using integrable_heatKernel_mul_heatKernel (t / 2) (by linarith [hpos t ht]) x' x')
    (fun t ht => by
      simp only [sq]
      rw [integral_heatKernel_mul_heatKernel (t / 2) (by linarith [hpos t ht])]
      congr 1; ring)
  have hheat : ∫ t in Icc (a ^ 2) (b ^ 2), (L * r / (Q.r₀ * a)) ^ 2 * heatKernel t x' x' ≤
      (L * r / (Q.r₀ * a)) ^ 2 * ((b ^ 2 - a ^ 2) * (2 * Real.pi * a ^ 2)⁻¹) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (a ^ 2) (b ^ 2))
      (f := fun t => heatKernel t x' x') (C := (2 * Real.pi * a ^ 2)⁻¹)
      (by simp [Real.volume_Icc]) (fun t ht => by
        have ht0 := hpos t ht
        rw [Real.norm_of_nonneg (heatKernel_nonneg _ ht0.le _ _)]
        unfold heatKernel
        simp only [sub_self, norm_zero]
        norm_num
        gcongr
        exact ht.1)
    rw [Real.volume_real_Icc_of_le ha2] at hb
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, mul_comm] using hb)
  have hint1 := integrable_sq_sub (Q.memLp_psiKernel a b ha x) (Q.memLp_psiKernel a b ha x')
  have hint2 := integrable_sq_sub (memLp_phiKernel a b ha x) (memLp_phiKernel a b ha x')
  have hmono := integral_mono hint1 ((hint2.const_mul 2).add (hFub.1.const_mul 2))
    (Q.sq_psiKernel_sub_le_const hL ha b x x')
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hint2.const_mul 2) (hFub.1.const_mul 2), integral_const_mul,
    integral_const_mul, hFub.2] at hmono
  rw [Q.sq_norm_psiKernelL2_sub ha]
  have e : (L * r / (Q.r₀ * a)) ^ 2 = M ^ 2 * r ^ 2 := by simp only [M]; ring
  have hM : 0 ≤ M ^ 2 * ((b ^ 2 - a ^ 2) * (2 * Real.pi * a ^ 2)⁻¹) := by positivity
  set I1 := ∫ p, (Q.psiKernel a b x p - Q.psiKernel a b x' p) ^ 2
  set I2 := ∫ p, (phiKernel a b x p - phiKernel a b x' p) ^ 2
  set I3 := ∫ t in Icc (a ^ 2) (b ^ 2), (L * r / (Q.r₀ * a)) ^ 2 * heatKernel t x' x'
  have hm : I1 ≤ 2 * I2 + 2 * I3 := by convert hmono using 3
  have hI3 : I3 ≤ (L * r / (Q.r₀ * a)) ^ 2 * ((b ^ 2 - a ^ 2) * (2 * Real.pi * a ^ 2)⁻¹) := hheat
  rw [e] at hI3
  nlinarith

end PsiParams

/-- **Continuous version of `ψ_{a,b}`** for `0 < a ≤ b`. -/
theorem exists_continuous_modification_psi (hW : IsWhiteNoise P W) (Q : PsiParams) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] psi Q W a b x := by
  obtain ⟨K, hK, hF⟩ := Q.exists_sq_norm_psiKernelL2_sub_le ha hab
  exact exists_continuous_modification_of_kernel hW (Q.psiKernelL2 a b) hK hF _

end WhiteNoise
end LQGMetric
