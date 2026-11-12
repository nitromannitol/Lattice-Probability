/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGFree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGCmp
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CouplingTail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2ContBox

/-!
# The free-kernel DGo Prop 3.3 from the variance bounds (3.9)–(3.10) (task P2-DDDFDG)

Source: Ding–Goswami arXiv:1610.09998, `Watabiki_final.tex`, proof of Prop 3.3 (`prop:coupling`,
DGo:604–616): "suppose that (3.9) `Var(Δ_δ(v) − Δ_δ(w)) = O(|v − w|/δ)` for `|v − w| ≤ δ` and
(3.10) `max_v Var Δ_δ(v) = O(1)`. … the conditions of Lemma 3.4 are satisfied". Here
`Δ_δ(v) = ĥ(σ_{v,δ}) − ĥ_δ(v) = √π W(k_δ(v))` with the kernel
`k_δ(v) = hatMeasKerL2 σ_{v,δ} − phiKernelL2 δ 1 v` (free heat kernel, times `(0,1]` minus times
`(δ², 1]` at the centre). The bounds (3.9)–(3.10) for `k_δ` are the open input `FreeKerBounds`
(deterministic kernel estimates); from them:

* a continuous modification of `Δ_δ` on `[0,1]²` (`DG.exists_box_modification_tail`, Kolmogorov:
  `‖k_δ(u) − k_δ(v)‖² ≤ L_δ |u − v|` on the whole box follows from (3.9) and (3.10));
* the tail `P(max |Δ_δ| ≥ ζ log δ⁻¹) ≤ 2 e^{−(ζ log δ⁻¹)²/(8σ²)}` (`DGo.dgo_prop33_abs_log`, DGo
  Prop 3.3 with DGo Lemma 3.4);

hence `FreeDGoCompare` (`freeDGoCompare_of_bounds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open WhiteNoise SupTail DG QuantumZipper GFFExist

/-- the kernel of `Δ_δ(v) = ĥ(σ_{v,δ}) − ĥ_δ(v)` at `δ = 2^{-K}` (up to the factor `√π`) -/
def freeKer (K : ℕ) (v : ℂ) : WNSpace :=
  hatMeasKerL2 (circleUnif v ((2 : ℝ)⁻¹ ^ K)) - phiKernelL2 ((2 : ℝ)⁻¹ ^ K) 1 v

/-- **DGo (3.9)–(3.10) for the free kernel** (DGo:604–606 and the computations DGo:618–704 with
`𝒰 = ℂ`): `Var Δ_δ(v) = π‖k_δ(v)‖² ≤ σ²` and `Var(Δ_δ(u) − Δ_δ(v)) ≤ A|u − v|/δ` for
`|u − v| ≤ δ`, uniformly in `δ = 2^{-K}` and `u, v ∈ [0,1]²`. -/
def FreeKerBounds : Prop :=
  ∃ A σ2 : ℝ, 0 < A ∧ 0 < σ2 ∧ ∀ K : ℕ,
    (∀ v ∈ ferniqueBox 0 1, Real.pi * ‖freeKer K v‖ ^ 2 ≤ σ2) ∧
    ∀ u ∈ ferniqueBox 0 1, ∀ v ∈ ferniqueBox 0 1, ‖u - v‖ ≤ (2 : ℝ)⁻¹ ^ K →
      Real.pi * ‖freeKer K u - freeKer K v‖ ^ 2 ≤ A * ‖u - v‖ / (2 : ℝ)⁻¹ ^ K

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma wn_sub_ae (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f - g, f, g] ![1, -1, 1] (by
    simp [Fin.sum_univ_three]; abel)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at hω
  linarith

lemma integral_sq_sqrtPi_wn (hW : IsWhiteNoise P W) (f : WNSpace) :
    ∫ ω, (Real.sqrt Real.pi * W f ω) ^ 2 ∂P = Real.pi * ‖f‖ ^ 2 := by
  have e : ∀ ω, (Real.sqrt Real.pi * W f ω) ^ 2 = Real.pi * (W f ω * W f ω) := fun ω => by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  simp_rw [e]
  rw [integral_const_mul, wn_integral_mul hW, real_inner_self_eq_norm_sq]

/-- **Free-kernel DGo Prop 3.3** from (3.9)–(3.10). -/
theorem freeDGoCompare_of_bounds (hB : FreeKerBounds) : FreeDGoCompare := by
  intro Ω _ P W hW
  have := hW.isProbabilityMeasure
  obtain ⟨A, σ2, hA, hσ, hb⟩ := hB
  have hpi := Real.pi_pos
  have hbox : ∀ K : ℕ, ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧
      (∀ z, Measurable (Y z)) ∧
      ∀ z ∈ ferniqueBox (0 : ℂ) 1, Y z =ᵐ[P] fun ω => Real.sqrt Real.pi * W (freeKer K z) ω := by
    intro K
    set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨hv, hi⟩ := hb K
    obtain ⟨Y, hYc, hYm, hYW, -⟩ := exists_box_modification_tail hW (freeKer K) (y := 0)
      one_pos (L := (A + 4 * σ2) / (Real.pi * δ)) (by positivity) fun x hx c hc => by
        rcases le_or_gt ‖x - c‖ δ with hxc | hxc
        · have := hi x hx c hc hxc
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          rw [le_div_iff₀ hδ0] at this
          nlinarith [norm_nonneg (x - c), norm_nonneg (freeKer K x - freeKer K c)]
        · have h1 := hv x hx
          have h2 := hv c hc
          have h3 : ‖freeKer K x - freeKer K c‖ ^ 2 ≤
              2 * ‖freeKer K x‖ ^ 2 + 2 * ‖freeKer K c‖ ^ 2 := by
            have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (freeKer K x) (freeKer K c)) 2
            nlinarith [sq_nonneg (‖freeKer K x‖ - ‖freeKer K c‖)]
          have h4 : 1 ≤ ‖x - c‖ / δ := by rw [le_div_iff₀ hδ0]; linarith
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have h5 : Real.pi * ‖freeKer K x - freeKer K c‖ ^ 2 ≤ 4 * σ2 := by nlinarith
          have h6 : δ ≤ ‖x - c‖ := hxc.le
          nlinarith
    exact ⟨Y, hYc, hYm, hYW⟩
  choose Y hYc hYm hYW using hbox
  refine ⟨Y, fun K ω => (hYc K ω).continuousOn, fun K z hz => ?_, fun ζ hζ => ?_⟩
  · have hz' : z ∈ ferniqueBox (0 : ℂ) 1 := unit_subset_fernique hz
    have hv := isPhiVersion_phiMN hW (Nat.zero_le K)
    filter_upwards [hYW K z hz', wn_sub_ae hW (hatMeasKerL2 (circleUnif z ((2 : ℝ)⁻¹ ^ K)))
      (phiKernelL2 ((2 : ℝ)⁻¹ ^ K) 1 z), hv.ae_eq z] with ω e1 e2 e3
    rw [e1, freeKer, e2, e3, dgHat, phi, pow_zero]
    ring
  -- the tail, from DGo Prop 3.3
  set cl : ℂ → ℂ := DZZ.boxClamp 0 1 with hcl
  have hclm : ∀ v, cl v ∈ ferniqueBox (0 : ℂ) 1 := fun v => DZZ.boxClamp_mem zero_le_one v
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ζ' := ζ / Real.log 2 with hζ'
  have hζ'0 : 0 < ζ' := div_pos hζ hlog2
  set κ := DGo.prop33K 1 A σ2 (1 / 2) with hκ
  -- eventually the threshold condition of `dgo_prop33_abs_log` holds
  have hev : ∀ᶠ K : ℕ in atTop, 1 ≤ K ∧ (2 * κ / ζ') ^ 2 ≤ (K : ℝ) * Real.log 2 := by
    refine (eventually_ge_atTop 1).and ?_
    have : Tendsto (fun K : ℕ => (K : ℝ) * Real.log 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hlog2
    exact this.eventually_ge_atTop _
  have hlim : Tendsto (fun K : ℕ => ENNReal.ofReal
      (2 * Real.exp (-(ζ' * ((K : ℝ) * Real.log 2)) ^ 2 / (8 * σ2)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => (ζ' * ((K : ℝ) * Real.log 2)) ^ 2 / (8 * σ2)) atTop atTop :=
      Tendsto.atTop_div_const (by positivity) ((tendsto_pow_atTop two_ne_zero).comp
        ((tendsto_natCast_atTop_atTop.atTop_mul_const hlog2).const_mul_atTop hζ'0))
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 2
    rw [mul_zero] at h2
    have h3 : Tendsto (fun K : ℕ => 2 * Real.exp (-(ζ' * ((K : ℝ) * Real.log 2)) ^ 2 / (8 * σ2)))
        atTop (𝓝 0) := h2.congr fun K => by simp only [Function.comp, neg_div]
    simpa using ENNReal.tendsto_ofReal h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with K ⟨hK1, hKℓ⟩
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ12 : δ ≤ 1 / 2 := by
    rw [hδ]
    calc (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK1
      _ = 1 / 2 := by norm_num
  have hlogδ : Real.log δ⁻¹ = (K : ℝ) * Real.log 2 := by
    rw [hδ, ← inv_pow, inv_inv, Real.log_pow]
  obtain ⟨hv, hi⟩ := hb K
  -- the clamped Gaussian process
  set Δ : ℂ → Ω → ℝ := fun v ω => Y K (cl v) ω with hΔ
  have hΔae : ∀ v, Δ v =ᵐ[P] fun ω => W (Real.sqrt Real.pi • freeKer K (cl v)) ω := fun v => by
    filter_upwards [hYW K (cl v) (hclm v), hW.smul_ae (Real.sqrt Real.pi) (freeKer K (cl v))]
      with ω e1 e2
    simp only [hΔ, e1, e2]
  have hΔG : IsGaussianProcess Δ P :=
    (hW.isGaussianProcess_comp fun v => Real.sqrt Real.pi • freeKer K (cl v)).congr
      fun v => (hΔae v).symm
  have h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0 := fun v => by
    rw [integral_congr_ae (hΔae v),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  have hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox 0 1) := fun ω =>
    ((hYc K ω).comp (DZZ.continuous_boxClamp 0 1)).continuousOn
  have hinc : ∀ u ∈ ferniqueBox (0 : ℂ) 1, ∀ v ∈ ferniqueBox (0 : ℂ) 1, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A * ‖u - v‖ / δ := by
    intro u hu v hv' huv
    have e : (fun ω => (Δ v ω - Δ u ω) ^ 2) =ᵐ[P]
        fun ω => (Real.sqrt Real.pi * W (freeKer K v - freeKer K u) ω) ^ 2 := by
      filter_upwards [hYW K v hv', hYW K u hu, wn_sub_ae hW (freeKer K v) (freeKer K u)]
        with ω e1 e2 e3
      simp only [hΔ, hcl, DZZ.boxClamp_of_mem hu, DZZ.boxClamp_of_mem hv', e1, e2, e3]
      ring
    rw [integral_congr_ae e, integral_sq_sqrtPi_wn hW, norm_sub_rev]
    exact hi u hu v hv' huv
  have hvar : ∀ v ∈ ferniqueBox (0 : ℂ) 1, Var[Δ v; P] ≤ σ2 := by
    intro v hv'
    have h := hW.hasLaw ![Real.sqrt Real.pi • freeKer K v] ![1]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Matrix.cons_val_zero, one_mul, one_smul] at h
    rw [variance_congr (hΔae v), hcl, DZZ.boxClamp_of_mem hv', h.variance_eq,
      variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _), norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpi.le]
    exact hv v hv'
  have hℓ : (2 * κ / ζ') ^ 2 ≤ Real.log δ⁻¹ := by rw [hlogδ]; exact hKℓ
  have htail := DGo.dgo_prop33_abs_log hΔG h0 one_pos hδ0 hδ12 (by norm_num) hA hσ hc hinc hvar
    hζ'0 hℓ
  rw [hlogδ] at htail
  have hζK : ζ' * ((K : ℝ) * Real.log 2) = ζ * K := by
    rw [hζ']; field_simp
  rw [hζK] at htail
  have hcpt : IsCompact (ferniqueBox (0 : ℂ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet, |Y K z ω| ≤ ζ * K} ⊆
      {ω | ζ * K ≤ ⨆ v : ferniqueBox (0 : ℂ) 1, |Δ v ω|} := by
    intro ω hω
    simp only [mem_setOf_eq, not_forall, not_le] at hω ⊢
    obtain ⟨z, hz, hlt⟩ := hω
    have hz' := unit_subset_fernique hz
    have : CompactSpace (ferniqueBox (0 : ℂ) 1) := isCompact_iff_compactSpace.1 hcpt
    have hbdd : BddAbove (range fun v : ferniqueBox (0 : ℂ) 1 => |Δ v ω|) :=
      (isCompact_range ((((hYc K ω).comp (DZZ.continuous_boxClamp 0 1)).abs).comp
        continuous_subtype_val)).bddAbove
    refine hlt.le.trans (le_of_eq_of_le ?_ (le_ciSup hbdd ⟨z, hz'⟩))
    simp only [hΔ, hcl, DZZ.boxClamp_of_mem hz']
  calc _ ≤ P {ω | ζ * K ≤ ⨆ v : ferniqueBox (0 : ℂ) 1, |Δ v ω|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | ζ * K ≤ ⨆ v : ferniqueBox (0 : ℂ) 1, |Δ v ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [← hζK]; simpa [hζK] using htail)

/-- **`WPPhiCompare` from DGo (3.9)–(3.10) for the free kernel.** -/
theorem wpPhiCompare_of_kerBounds (hB : FreeKerBounds) : WPPhiCompare :=
  wpPhiCompare_of_free (freeDGoCompare_of_bounds hB)

end S6DG
end DDDF
end LQGMetric
