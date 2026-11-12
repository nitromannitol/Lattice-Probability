/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.FerniqueKolm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DZZ Lemma 2.3: existence of the continuous version

Ding–Zeitouni–Zhang, arXiv:1807.00422, Lemma 2.3 (LaTeX lines 364–373), full statement: under
`E (G_v - G_u)² ≤ |u - v| / b` on a square `B` of side `b`, a centered Gaussian field
`{G_v}_{v ∈ B}` has a version continuous on `B`, and for it `E max_B G ≤ C_F`
(`dzz_lemma23`, `dzz_lemma23_exists`).

Continuity: the field is extended to `ℝ²` by composing with the nearest-point map onto `B`
(`boxClamp`, coordinatewise `projIcc`, `√2`-Lipschitz from the sup norm to `|·|`); a centered
Gaussian increment of variance `≤ √2 ‖q - q'‖ / b` has sixth moment
`≤ (√2/b)³ E|N(0,1)|⁶ ‖q - q'‖³`, so the Kolmogorov–Čentsov criterion in two parameters with
exponents `p = 6`, `a = 3 > 2` (`QuantumZipper.KolmN.exists_continuous_modification_N`;
Revuz–Yor, Ch. I, Thm (2.1)) gives a continuous modification. The bound on `E max` is
`SupTail.dzz_lemma23_continuous`. (DZZ attribute the lemma to Fernique 1975 and Adler 1990,
Thm 4.1, where continuity comes out of the same entropy bound; deriving it from
Kolmogorov–Čentsov is a different, standard route.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric

namespace SupTail

/-- The nearest-point map of `ℝ²` onto the square `ferniqueBox x₀ b`. -/
def boxClamp (x₀ : ℂ) {b : ℝ} (hb : 0 ≤ b) (q : Fin 2 → ℝ) : ℂ :=
  ⟨(projIcc x₀.re (x₀.re + b) (by linarith) (q 0) : ℝ),
    (projIcc x₀.im (x₀.im + b) (by linarith) (q 1) : ℝ)⟩

variable {x₀ : ℂ} {b : ℝ}

lemma boxClamp_mem (hb : 0 ≤ b) (q : Fin 2 → ℝ) : boxClamp x₀ hb q ∈ ferniqueBox x₀ b := by
  exact ⟨(projIcc x₀.re (x₀.re + b) (by linarith) (q 0)).2,
    (projIcc x₀.im (x₀.im + b) (by linarith) (q 1)).2⟩

lemma boxClamp_reIm (hb : 0 ≤ b) {v : ℂ} (hv : v ∈ ferniqueBox x₀ b) :
    boxClamp x₀ hb (reIm v) = v := by
  apply Complex.ext
  · simp [boxClamp, reIm, projIcc_of_mem _ hv.1]
  · simp [boxClamp, reIm, projIcc_of_mem _ hv.2]

lemma norm_boxClamp_sub_le (hb : 0 ≤ b) (q q' : Fin 2 → ℝ) :
    ‖boxClamp x₀ hb q - boxClamp x₀ hb q'‖ ≤ √2 * ‖q - q'‖ := by
  refine (Complex.norm_le_sqrt_two_mul_max _).trans ?_
  gcongr
  refine max_le ?_ ?_
  · simp only [boxClamp, Complex.sub_re]
    exact (Set.abs_projIcc_sub_projIcc _).trans (by simpa using norm_le_pi_norm (q - q') 0)
  · simp only [boxClamp, Complex.sub_im]
    exact (Set.abs_projIcc_sub_projIcc _).trans (by simpa using norm_le_pi_norm (q - q') 1)

lemma continuous_reIm : Continuous reIm :=
  continuous_pi fun i => by
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Sixth moment of a centered Gaussian variable: `E|U|⁶ ≤ s³ E|N(0,1)|⁶` if `E U² ≤ s`. -/
lemma lintegral_abs_pow_six_le {U : Ω → ℝ} (hU : HasGaussianLaw U P) (h0 : ∫ ω, U ω ∂P = 0)
    {s : ℝ} (hs : ∫ ω, U ω ^ 2 ∂P ≤ s) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ 6) ∂P ≤
      ENNReal.ofReal (s ^ 3 * QuantumZipper.gaussianAbsMoment 6) := by
  have hP := hU.isProbabilityMeasure
  have hvar : Var[U; P] = ∫ ω, U ω ^ 2 ∂P := variance_of_integral_eq_zero hU.aemeasurable h0
  have hmap := hU.map_eq_gaussianReal
  rw [h0] at hmap
  set U' := hU.aemeasurable.mk U
  have hae : U =ᵐ[P] U' := hU.aemeasurable.ae_eq_mk
  have hmap' : P.map U' = gaussianReal 0 (Var[U; P]).toNNReal := by
    rw [← Measure.map_congr hae, hmap]
  have h := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq
    hU.aemeasurable.measurable_mk 3 hmap'
  rw [show (2 * 3 : ℕ) = 6 from rfl] at h
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω]), h]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
    (QuantumZipper.gaussianAbsMoment_nonneg 6))
  rw [Real.coe_toNNReal _ (variance_nonneg _ _), hvar]
  exact pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) hs 3

/-- **DZZ Lemma 2.3** (arXiv:1807.00422, lines 364–373): a centered Gaussian field on the
square `B` of side `b > 0` with `E (G_v - G_u)² ≤ |u - v| / b` on `B` has a version `G'`
continuous on `ℂ` (hence on `B`), and `E max_B G' ≤ C_F` with the universal `C_F = ferniqueCF`. -/
theorem dzz_lemma23 (hb : 0 < b) {G : ℂ → Ω → ℝ}
    (hG : IsGaussianProcess (fun v : ferniqueBox x₀ b => G v) P)
    (h0 : ∀ v ∈ ferniqueBox x₀ b, ∫ ω, G v ω ∂P = 0)
    (hinc : ∀ u ∈ ferniqueBox x₀ b, ∀ v ∈ ferniqueBox x₀ b,
      ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ ‖u - v‖ / b) :
    ∃ G' : ℂ → Ω → ℝ, (∀ v ∈ ferniqueBox x₀ b, G' v =ᵐ[P] G v) ∧
      (∀ ω, Continuous fun v => G' v ω) ∧
      Integrable (fun ω => ⨆ v : ferniqueBox x₀ b, G' v ω) P ∧
      ∫ ω, (⨆ v : ferniqueBox x₀ b, G' v ω) ∂P ≤ ferniqueCF := by
  set c := boxClamp x₀ hb.le
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => G (c q)
  have hZm : ∀ q, AEMeasurable (Z q) P := fun q =>
    hG.aemeasurable ⟨c q, boxClamp_mem hb.le q⟩
  set K : ℝ := (√2 / b) ^ 3 * QuantumZipper.gaussianAbsMoment 6
  have hK : 0 ≤ K := by have := QuantumZipper.gaussianAbsMoment_nonneg 6; positivity
  have hmom : ∀ R : ℕ, ∃ K', 0 ≤ K' ∧ QuantumZipper.KolmG.MomentBoundG Z P 6 3 K' R := by
    intro R
    refine ⟨K, hK, fun q _ q' _ => ?_⟩
    have hU := hG.hasGaussianLaw_fun_sub (s := ⟨c q, boxClamp_mem hb.le q⟩)
      (t := ⟨c q', boxClamp_mem hb.le q'⟩)
    have hi : ∀ q, Integrable (Z q) P := fun q =>
      (hG.hasGaussianLaw_eval ⟨c q, boxClamp_mem hb.le q⟩).integrable
    have hU0 : ∫ ω, (Z q ω - Z q' ω) ∂P = 0 := by
      rw [integral_sub (hi q) (hi q'), h0 _ (boxClamp_mem hb.le q),
        h0 _ (boxClamp_mem hb.le q'), sub_zero]
    have hs : ∫ ω, (Z q ω - Z q' ω) ^ 2 ∂P ≤ √2 / b * ‖q - q'‖ := by
      refine (hinc _ (boxClamp_mem hb.le q') _ (boxClamp_mem hb.le q)).trans ?_
      rw [norm_sub_rev, div_mul_eq_mul_div, mul_comm (√2)]
      gcongr
      rw [mul_comm]
      exact norm_boxClamp_sub_le hb.le q q'
    refine (lintegral_abs_pow_six_le hU hU0 hs).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  obtain ⟨Y, hYc, hYZ, -⟩ := QuantumZipper.KolmN.exists_continuous_modification_N hZm
    (by norm_num : 0 < 6) (by norm_num : ((2 : ℕ) : ℝ) < 3) hmom
  set G' : ℂ → Ω → ℝ := fun v ω => Y (reIm v) ω
  have hae : ∀ v ∈ ferniqueBox x₀ b, G' v =ᵐ[P] G v := by
    intro v hv
    have := hYZ (reIm v)
    simp only [Z, c, boxClamp_reIm hb.le hv] at this
    exact this
  have hG'c : ∀ ω, Continuous fun v => G' v ω := fun ω => (hYc ω).comp continuous_reIm
  refine ⟨G', hae, hG'c, ?_⟩
  have hG' : IsGaussianProcess (fun v : ferniqueBox x₀ b => G' v) P :=
    hG.congr fun v => (hae v v.2).symm
  refine dzz_lemma23_continuous hb hG' (fun v hv => by rw [integral_congr_ae (hae v hv), h0 v hv])
    (fun u hu v hv => ?_) (fun ω => (hG'c ω).continuousOn)
  rw [integral_congr_ae (g := fun ω => (G v ω - G u ω) ^ 2)]
  · exact hinc u hu v hv
  · filter_upwards [hae u hu, hae v hv] with ω h1 h2
    rw [h1, h2]

end SupTail

end LQGMetric
