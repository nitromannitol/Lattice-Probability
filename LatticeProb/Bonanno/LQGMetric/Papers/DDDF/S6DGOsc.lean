/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up0
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1

/-!
# The oscillation of `φ_{0,K}` at scale `2^{-K}` is `o(K)` (task P2-DDDFDG)

DDDF = arXiv:1904.08021, `tightness.tex`, (2.17) (`eq:OscBoundExp`, l. 337) in the form proved at
l. 345–352 with `a_n = a` (`S6U.osc_expMoment0`: `E e^{2^{-n} ‖∇φ_{0,n}‖_{[0,1]²}} ≤ K e^{c√n}`).
By Markov's inequality and the mean value theorem, for each `C, ζ > 0`, with probability tending
to `1` as `K → ∞`, `|φ_{0,K}(z) − φ_{0,K}(w)| ≤ ζ K` for all `z, w ∈ [0,1]²` with
`|z − w| ≤ C 2^{-K}` (`phiMN_osc_tendsto`). This is the "continuity estimate for `ĥ_δ`" used in
the proof of DG Lemma 3.7 (DG:1104–1106, there from `lem-use-btis`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma unit_subset_fernique : (rectAB 1 1).toSet ⊆ ferniqueBox 0 1 := by
  intro z hz
  simpa [MarkedRect.toSet, rectAB, ferniqueBox] using hz

lemma convex_unit : Convex ℝ (rectAB 1 1).toSet :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- `K e^{c√n − an} → 0` -/
lemma tendsto_exp_sqrt_sub {K c a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => K * Real.exp (c * √(n : ℝ) - a * n)) atTop (𝓝 0) := by
  have hb : ∀ n : ℕ, c * √(n : ℝ) - a * n ≤ c ^ 2 / (2 * a) - a / 2 * n := by
    intro n
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h := sq_nonneg (a * √(n : ℝ) - c)
    have h' : (a * √(n : ℝ) - c) ^ 2 = a ^ 2 * n - 2 * a * c * √(n : ℝ) + c ^ 2 := by
      rw [sub_sq, mul_pow, hs]; ring
    rw [div_sub' (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [h, h']
  have h1 : Tendsto (fun n : ℕ => Real.exp (c ^ 2 / (2 * a) - a / 2 * n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => a / 2 * (n : ℝ) - c ^ 2 / (2 * a)) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).congr fun n => ?_
    simp only [Function.comp]; congr 1; ring
  have h2 : Tendsto (fun n : ℕ => |K| * Real.exp (c ^ 2 / (2 * a) - a / 2 * n)) atTop (𝓝 0) := by
    simpa using h1.const_mul |K|
  refine squeeze_zero_norm (fun n => ?_) h2
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hb n)) (abs_nonneg _)

/-- **Oscillation of `φ_{0,K}` at scale `C 2^{-K}`**: for `C, ζ > 0`,
`P(∃ z, w ∈ [0,1]², |z − w| ≤ C 2^{-K}, |φ_{0,K}(z) − φ_{0,K}(w)| > ζ K) → 0`. -/
theorem phiMN_osc_tendsto (hW : IsWhiteNoise P W) {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ) :
    Tendsto (fun K : ℕ => P {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet, ∀ w ∈ (rectAB 1 1).toSet,
      ‖z - w‖ ≤ C * (2 : ℝ)⁻¹ ^ K → |phiMN W P 0 K z ω - phiMN W P 0 K w ω| ≤ ζ * K})
      atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  obtain ⟨c, K', -, hK'0, hmom⟩ := S6U.osc_expMoment0 (a := 1) one_pos
  set a := ζ / C with ha
  have ha0 : 0 < a := div_pos hζ hC
  have hu : Tendsto (fun n : ℕ => ENNReal.ofReal (K' * Real.exp (c * √(n : ℝ) - a * n)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_exp_sqrt_sub (K := K') (c := c) ha0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpn : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y, -, hYae, hYm, hYc, -⟩ := exists_C1_modification_phi hW (a := ((2 : ℝ) ^ n)⁻¹)
    (b := 1) (by positivity) hpn
  have hmn := hmom hW n hn Y hYae hYc
  set X : Ω → ℝ := fun ω => ((2 : ℝ) ^ n)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖ with hX
  have hXm : AEMeasurable X P := aemeasurable_osc hW n hYae hYc
  have hv := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hind : ∀ᵐ ω ∂P, ∀ x, phiMN W P 0 n x ω = Y x ω :=
    T20C.ae_forall_eq_of_cont hv.cont (fun ω => (hYc ω).continuous) fun x =>
      (hv.ae_eq x).trans (by rw [inv_pow, pow_zero]; exact (hYae x).symm)
  have hN := ae_iff.1 hind
  have hcpt : IsCompact (ferniqueBox (0 : ℂ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet, ∀ w ∈ (rectAB 1 1).toSet,
      ‖z - w‖ ≤ C * (2 : ℝ)⁻¹ ^ n → |phiMN W P 0 n z ω - phiMN W P 0 n w ω| ≤ ζ * n} ⊆
      {ω | ENNReal.ofReal (Real.exp (a * n)) ≤ ENNReal.ofReal (Real.exp (X ω))} ∪
        {ω | ¬ ∀ x, phiMN W P 0 n x ω = Y x ω} := by
    intro ω hω
    by_contra hn'
    simp only [mem_union, mem_setOf_eq, not_or, not_not, not_le] at hn' hω
    obtain ⟨hlt, heq⟩ := hn'
    have hXlt : X ω < a * n := Real.exp_lt_exp.1
      ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).1 hlt)
    apply hω
    intro z hz w hw hzw
    rw [heq z, heq w]
    have : CompactSpace (ferniqueBox (0 : ℂ) 1) := isCompact_iff_compactSpace.1 hcpt
    have hfc : Continuous fun x => ‖fderiv ℝ (fun x => Y x ω) x‖ :=
      ((hYc ω).continuous_fderiv one_ne_zero).norm
    have hbdd : BddAbove (range fun y : ferniqueBox (0 : ℂ) 1 =>
        ‖fderiv ℝ (fun x => Y x ω) y‖) :=
      (isCompact_range (hfc.comp continuous_subtype_val)).bddAbove
    set G := ⨆ y : ferniqueBox (0 : ℂ) 1, ‖fderiv ℝ (fun x => Y x ω) y‖ with hG
    have hbound : ∀ x ∈ (rectAB 1 1).toSet, ‖fderiv ℝ (fun x => Y x ω) x‖ ≤ G := fun x hx =>
      le_ciSup (f := fun y : ferniqueBox (0 : ℂ) 1 => ‖fderiv ℝ (fun x => Y x ω) y‖) hbdd
        ⟨x, unit_subset_fernique hx⟩
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => ((hYc ω).differentiable one_ne_zero) x) hbound convex_unit hw hz
    rw [Real.norm_eq_abs, norm_sub_rev] at hmv
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hbound z hz)
    have hXG : X ω = ((2 : ℝ) ^ n)⁻¹ * G := rfl
    have hz' : ‖z - w‖ ≤ C * ((2 : ℝ) ^ n)⁻¹ := by rw [← inv_pow]; exact hzw
    have e : a * C = ζ := by rw [ha]; field_simp
    calc |Y z ω - Y w ω| ≤ G * ‖z - w‖ := by rw [norm_sub_rev] at hmv; exact hmv
      _ ≤ G * (C * ((2 : ℝ) ^ n)⁻¹) := mul_le_mul_of_nonneg_left hz' hG0
      _ = C * X ω := by rw [hXG]; ring
      _ ≤ C * (a * n) := mul_le_mul_of_nonneg_left hXlt.le hC.le
      _ = ζ * n := by rw [← e]; ring
  have hεne : ENNReal.ofReal (Real.exp (a * n)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = P {ω | ENNReal.ofReal (Real.exp (a * n)) ≤ ENNReal.ofReal (Real.exp (X ω))} := by
        rw [hN, add_zero]
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P) / ENNReal.ofReal (Real.exp (a * n)) :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp_aemeasurable
          (Real.measurable_exp.comp_aemeasurable hXm)) hεne ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K' * Real.exp (c * √(n : ℝ))) / ENNReal.ofReal (Real.exp (a * n)) := by
        gcongr
        simpa [hX, one_mul] using hmn
    _ = ENNReal.ofReal (K' * Real.exp (c * √(n : ℝ) - a * n)) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), Real.exp_sub, mul_div_assoc]

end S6DG
end DDDF
end LQGMetric
