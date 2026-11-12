/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentTilde at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentWN
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentVer
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Exp

/-!
# The white-noise filtration of the coarse scales and a `𝓖_n`-measurable version of `h̃_{2^{-n}}`
(P2-GMCID, D67)

DZZ (`LBM_LGDarXiv.tex` l. 430–433, 653): `h̃_δ(v) = √π ∫_{𝕍 × (δ², ∞)} p_𝕍(s/2; v, w) W(dw, ds)`;
the white-noise approximations of the LQG measure form a martingale for the filtration of the
coarse scales. Here:

* `wnFil hW` : the filtration `𝓖_n = σ(W g : g supported in (4^{-n}, ∞) × ℂ)`;
* `supportedIn_wndKernelL2` : DZZ's kernels `1_I(s) p_A(s/2; v, ·)` are supported in `I × ℂ`;
* `integral_abs_le_sqrt_of_hasLaw` : `E|Z| ≤ √v` for `Z ∼ N(0, v)`;
* `tildeVer W n` (`dyVer` of `h̃_{2^{-n}}`) is `Borel ⊗ 𝓖_n`-measurable
  (`measurable_tildeVer`) and a version of `h̃_{2^{-n}}` (`tildeVer_ae_eq`), from DZZ Lemma 2.5
  (`pi_sq_norm_tildeHKernel_sub_le`: `π‖K_u − K_v‖² ≤ 28|u − v|/δ`).

This is the `𝓕_n`-measurability of the martingale approximation `μ^n` in Berestycki
(arXiv:1506.09113, §4, l. 649).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the coarse scales `s > 4^{-n}` -/
def coarseSet (n : ℕ) : Set (ℝ × ℂ) := Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2) ×ˢ univ

lemma coarseSet_mono : Monotone coarseSet := by
  intro i j hij p hp
  refine ⟨mem_Ioi.2 (lt_of_le_of_lt ?_ (mem_Ioi.1 hp.1)), trivial⟩
  have h : (2 : ℝ)⁻¹ ^ j ≤ (2 : ℝ)⁻¹ ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  exact pow_le_pow_left₀ (by positivity) h 2

lemma supportedIn_mono {A B : Set (ℝ × ℂ)} (hAB : A ⊆ B) {g : WNSpace} (hg : SupportedIn A g) :
    SupportedIn B g :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 hAB) hg

omit mΩ in
lemma wnSigma_mono {A B : Set (ℝ × ℂ)} (hAB : A ⊆ B) : wnSigma W A ≤ wnSigma W B := by
  have hρ : Measurable (fun (x : {g // SupportedIn B g} → ℝ) (g : {g // SupportedIn A g}) =>
      x ⟨g.1, supportedIn_mono hAB g.2⟩) := measurable_pi_iff.2 fun g => measurable_pi_apply _
  have hF : Measurable[wnSigma W B] (fun ω (g : {g // SupportedIn B g}) => W g ω) :=
    comap_measurable _
  exact (hρ.comp hF).comap_le

/-- **The white-noise filtration of the coarse scales**, `𝓖_n = σ(W|_{(4^{-n},∞) × ℂ})`. -/
def wnFil (hW : IsWhiteNoise P W) : Filtration ℕ mΩ where
  seq n := wnSigma W (coarseSet n)
  mono' _ _ hij := wnSigma_mono (coarseSet_mono hij)
  le' _ := wnSigma_le hW _

/-- A function vanishing off `S` gives an element of `L²` supported in `S`. -/
lemma supportedIn_toLp {S : Set (ℝ × ℂ)} (hS : MeasurableSet S) {f : ℝ × ℂ → ℝ}
    (hf : MemLp f 2 volume) (h0 : ∀ p ∉ S, f p = 0) : SupportedIn S (hf.toLp f) := by
  unfold SupportedIn
  filter_upwards [ae_restrict_of_ae hf.coeFn_toLp, ae_restrict_mem hS.compl] with p h1 h2
  rw [h1]; exact h0 p h2

/-- DZZ's kernels `1_I(s) p_A(s/2; v, ·)` are supported in `I × ℂ`. -/
lemma supportedIn_wndKernelL2 (A : Set ℂ) {I : Set ℝ} (hI : MeasurableSet I) (v : ℂ) :
    SupportedIn (I ×ˢ univ) (wndKernelL2 A I v) := by
  unfold wndKernelL2
  split_ifs with h
  · refine supportedIn_toLp (hI.prod MeasurableSet.univ) h fun p hp => ?_
    have : p.1 ∉ I := fun h1 => hp ⟨h1, trivial⟩
    simp [wndKernel, this]
  · unfold SupportedIn
    exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 volume)

/-- `E|Z| ≤ √v` for `Z ∼ N(0, v)`. -/
lemma integral_abs_le_sqrt_of_hasLaw [IsProbabilityMeasure P] {Z : Ω → ℝ} {v : NNReal}
    (hZ : HasLaw Z (gaussianReal 0 v) P) : ∫ ω, |Z ω| ∂P ≤ Real.sqrt v := by
  refine integral_abs_le_sqrt (hZ.memLp (memLp_id_gaussianReal' 2 (by simp)))
    ((hZ.integral_eq).trans integral_id_gaussianReal) (le_of_eq ?_)
  rw [hZ.variance_eq, variance_id_gaussianReal]

variable (W) in
/-- the `Borel ⊗ 𝓖_n`-measurable version of `h̃_{2^{-n}}` -/
def tildeVer (n : ℕ) : ℂ → Ω → ℝ := dyVer (tildeHInf W ((2 : ℝ)⁻¹ ^ n))

lemma measurable_tildeHInf_fil (hW : IsWhiteNoise P W) (n : ℕ) (z : ℂ) :
    Measurable[wnFil hW n] (tildeHInf W ((2 : ℝ)⁻¹ ^ n) z) :=
  (measurable_wnSigma (supportedIn_wndKernelL2 openSquare measurableSet_Ioi z)).const_mul _

theorem measurable_tildeVer (hW : IsWhiteNoise P W) (n : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnFil hW n)]
      fun p : ℂ × Ω => tildeVer W n p.1 p.2 :=
  measurable_dyVer (measurable_tildeHInf_fil hW n)

theorem tildeVer_ae_eq (hW : IsWhiteNoise P W) (n : ℕ) (z : ℂ) :
    tildeVer W n z =ᵐ[P] tildeHInf W ((2 : ℝ)⁻¹ ^ n) z := by
  have := hW.isProbabilityMeasure
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n with hδ
  have hδ0 : 0 < δ := by positivity
  set K := fun v => wndKernelL2 openSquare (Ioi (δ ^ 2)) v
  set q : ℝ := Real.sqrt (1 / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set a : ℝ := Real.sqrt (56 / δ)
  have hterm : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal |tildeHInf W δ (dyadicRoundC j z) ω -
      tildeHInf W δ z ω| ∂P ≤ ENNReal.ofReal (a * q ^ j) := by
    intro j
    set d := dyadicRoundC j z
    have hL := hW.hasLaw ![K d, K z] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hL
    have hL' : HasLaw (fun ω => tildeHInf W δ d ω - tildeHInf W δ z ω)
        (gaussianReal 0 (‖Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z‖ ^ 2).toNNReal) P := by
      refine hL.congr (Eventually.of_forall fun ω => ?_)
      simp only [tildeHInf, wnField, K]; ring
    have hint : Integrable (fun ω => |tildeHInf W δ d ω - tildeHInf W δ z ω|) P :=
      (hL'.integrable (memLp_one_iff_integrable.1
        (memLp_id_gaussianReal' 1 (by simp)))).abs
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((integral_abs_le_sqrt_of_hasLaw hL').trans ?_)
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    have e : Real.sqrt Real.pi • K d + (-Real.sqrt Real.pi) • K z =
        Real.sqrt Real.pi • (K d - K z) := by rw [smul_sub, neg_smul, ← sub_eq_add_neg]
    have hv : ‖Real.sqrt Real.pi • (K d - K z)‖ ^ 2 ≤ 56 / δ * (1 / 2) ^ j := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt Real.pi_pos.le]
      refine (pi_sq_norm_tildeHKernel_sub_le hW hδ0 d z).trans ?_
      have hd := CircleCont.norm_dyadicRoundC_sub_le j z
      rw [div_le_iff₀ hδ0]
      have : 56 / δ * (1 / 2) ^ j * δ = 28 * (2 * (1 / 2 ^ j)) := by
        calc 56 / δ * (1 / 2) ^ j * δ = 56 * (1 / 2) ^ j := by field_simp
          _ = 28 * (2 * (1 / 2 ^ j)) := by rw [one_div_pow]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hd (by norm_num)
    rw [e]
    refine (Real.sqrt_le_sqrt hv).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), show (1 / 2 : ℝ) ^ j = (q ^ j) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)],
      Real.sqrt_sq (by positivity)]
  refine dyVer_ae_eq (fun v => (measurable_tildeHInf_fil hW n v).mono (wnSigma_le hW _) le_rfl
    |>.aemeasurable) z (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _)]
  exact ENNReal.ofReal_ne_top

end GMCIdent
end LQGMetric
