/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7Cont at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsi
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Continuous versions of white-noise fields with `1/2`-Hölder kernels (P2-DZZPRE, WP-112)

DZZ's fields `h̃`, `η` (and their band differences `Δ_i`) only have `E(X(u) − X(v))² ≤ K|u − v|`
(Lemma 2.5), so the Lipschitz-kernel Kolmogorov lemma of the white-noise layer
(`WhiteNoise.exists_continuous_modification_of_kernel`, fourth moments) does not apply; with sixth
moments `E|X(u) − X(v)|⁶ = 15 Var³ ≤ C|u − v|³` and `3 > 2 = d` Kolmogorov–Čentsov
(QuantumZipper `KolmN.exists_continuous_modification_N`) gives a continuous version. The proof is
the existing one with the exponents changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Continuous version of a white-noise field with `1/2`-Hölder kernel** (`‖F x − F x'‖² ≤
K|x − x'|`; Kolmogorov–Čentsov with sixth moments). Adapted from
`WhiteNoise.exists_continuous_modification_of_kernel`. -/
theorem exists_continuous_modification_of_kernel_half (hW : IsWhiteNoise P W) (F : ℂ → WNSpace)
    {K : ℝ} (hK : 0 ≤ K) (hF : ∀ x x', ‖F x - F x'‖ ^ 2 ≤ K * ‖x - x'‖) (c : ℝ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] fun ω => c * W (F x) ω := by
  set C : ℝ := c ^ 2 * K with hC
  have hC0 : 0 ≤ C := by positivity
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => c * W (F (finTwoToC q)) ω with hZ
  have hZmeas : ∀ q, Measurable (Z q) := fun q => (hW.measurable _).const_mul _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P 6 3 K R := by
    intro R
    refine ⟨C ^ 3 * QuantumZipper.gaussianAbsMoment 6 * 8, by
      have := QuantumZipper.gaussianAbsMoment_nonneg 6; positivity, fun q _ q' _ => ?_⟩
    have h := hW.hasLaw ![F (finTwoToC q), F (finTwoToC q')] ![c, -c]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hlaw : HasLaw (fun ω => Z q ω - Z q' ω)
        (gaussianReal 0 (‖c • F (finTwoToC q) + (-c) • F (finTwoToC q')‖ ^ 2).toNNReal) P :=
      h.congr (Eventually.of_forall fun ω => by simp only [hZ]; ring)
    have e := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hZmeas q).sub (hZmeas q')) 3 hlaw.map_eq
    simp only [Pi.sub_apply] at e
    refine e.trans_le (ENNReal.ofReal_le_ofReal ?_)
    set v := ‖c • F (finTwoToC q) + (-c) • F (finTwoToC q')‖ ^ 2
    have hv : v ≤ C * ‖finTwoToC q - finTwoToC q'‖ := by
      simp only [v]
      rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hC, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hF _ _) (sq_nonneg c)
    have hM := QuantumZipper.gaussianAbsMoment_nonneg 6
    have hn := norm_finTwoToC_sub_le q q'
    have hv' : ((v.toNNReal : NNReal) : ℝ) ≤ C * (2 * ‖q - q'‖) := by
      rw [Real.coe_toNNReal']
      refine max_le (hv.trans ?_) (by positivity)
      gcongr
    have hv0 : 0 ≤ ((v.toNNReal : NNReal) : ℝ) := NNReal.coe_nonneg _
    calc ((v.toNNReal : NNReal) : ℝ) ^ 3 * QuantumZipper.gaussianAbsMoment (2 * 3)
        ≤ (C * (2 * ‖q - q'‖)) ^ 3 * QuantumZipper.gaussianAbsMoment (2 * 3) := by
          gcongr
      _ = C ^ 3 * QuantumZipper.gaussianAbsMoment (2 * 3) * 8 * ‖q - q'‖ ^ (3 : ℝ) := by
          rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (d := 2) (P := P) (Z := Z) (fun q => (hZmeas _).aemeasurable)
    (p := 6) (by norm_num) (a := 3) (by norm_num) hmom
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


end DZZ
end LQGMetric
