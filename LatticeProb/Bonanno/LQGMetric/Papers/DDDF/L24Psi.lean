/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L24Psi at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable). -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiProp5
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# DDDF Lemma 24, first step: `Var log L^{(k)}_{1,1}(ψ) ≤ C k` (`k ≥ 1`)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1064–1065 (proof of `Lem:Apriori`): "By using
Lemma 23 we get `Var(log L^{(k)}_{1,1}(φ)) ≤ C k` … This implies the same bound for `ψ` by
Proposition 5" (the source has "`ψ`" twice; blueprint DDDF.L24 reads the first one as `φ`).

Implementation of "by Proposition 5": `|log L^{(k)}(ψ) − log L^{(k)}(φ)| ≤ |ξ| X_{1,1}`
(`X_{1,1} = sup_n ‖φ_{0,n} − ψ_{0,n}‖_{[0,1]²}`, DDDF l. 482–485), Prop. 5's Gaussian tail
`P(X_{1,1} ≥ x) ≤ C e^{−cx²}` (`dddf_prop5`) gives `E (log L(ψ) − log L(φ))² ≤ C ξ² / c`
uniformly in `k` (layer-cake formula), and `Var A ≤ 2 Var B + 2 E (A − B)²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

namespace L24

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- an exponential tail gives integrability and `E D ≤ C / b` -/
lemma integrable_integral_le_of_exp_tail {D : Ω → ℝ} (hDm : Measurable D) (hD0 : ∀ ω, 0 ≤ D ω)
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (ht : ∀ t : ℝ, 0 < t → P {ω | t ≤ D ω} ≤ ENNReal.ofReal (C * exp (-b * t))) :
    Integrable D P ∧ ∫ ω, D ω ∂P ≤ C / b := by
  have hint : IntegrableOn (fun t : ℝ => C * exp (-b * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul C
  have hval : ∫ t in Ioi (0 : ℝ), C * exp (-b * t) = C / b := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, exp_zero]
    field_simp
  have hle : ∫⁻ ω, ENNReal.ofReal (D ω) ∂P ≤ ENNReal.ofReal (C / b) := by
    rw [lintegral_eq_lintegral_meas_le P (ae_of_all _ hD0) hDm.aemeasurable, ← hval,
      ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by positivity)]
    exact setLIntegral_mono' measurableSet_Ioi fun t ht' => ht t ht'
  have hI : Integrable D P :=
    (lintegral_ofReal_ne_top_iff_integrable hDm.aestronglyMeasurable (ae_of_all _ hD0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hI, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hD0) hDm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hC hb.le) hle

/-- `Var A ≤ 2 Var B + 2 E (A − B)²` -/
lemma variance_le_two_mul [IsProbabilityMeasure P] {A B : Ω → ℝ} (hA : Measurable A)
    (hB : MemLp B 2 P) (hAB : Integrable (fun ω => (A ω - B ω) ^ 2) P) :
    MemLp A 2 P ∧ Var[A; P] ≤ 2 * Var[B; P] + 2 * ∫ ω, (A ω - B ω) ^ 2 ∂P := by
  have hABm : MemLp (fun ω => A ω - B ω) 2 P :=
    (memLp_two_iff_integrable_sq (hA.aestronglyMeasurable.sub hB.aestronglyMeasurable)).2 hAB
  have hAL : MemLp A 2 P := by
    have := hABm.add hB
    convert this using 1
    ext ω; simp
  refine ⟨hAL, ?_⟩
  set m := ∫ ω, B ω ∂P
  rw [← variance_sub_const hA.aestronglyMeasurable m]
  refine (variance_le_expectation_sq (hA.sub measurable_const).aestronglyMeasurable).trans ?_
  have hB2 : Integrable (fun ω => (B ω - m) ^ 2) P := (hB.sub (memLp_const m)).integrable_sq
  rw [variance_eq_integral hB.aestronglyMeasurable.aemeasurable]
  show ∫ ω, (A ω - m) ^ 2 ∂P ≤ 2 * ∫ ω, (B ω - m) ^ 2 ∂P + 2 * ∫ ω, (A ω - B ω) ^ 2 ∂P
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hB2.const_mul 2)
    (hAB.const_mul 2)]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
    ((hB2.const_mul 2).add (hAB.const_mul 2)) (ae_of_all _ fun ω => ?_)
  simp only
  nlinarith [sq_nonneg (A ω - 2 * B ω + m)]

/-- continuous functions are bounded on `[0,1]²` -/
lemma exists_bound_sq01 {f : ℂ → ℝ} (hf : Continuous f) : ∃ M, ∀ x ∈ L23.sq01, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := ((rectAB 1 1).isCompact_toSet.image_of_continuousOn
    (continuous_abs.comp hf).continuousOn).isBounded.bddAbove
  exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩

variable {W : WNSpace → Ω → ℝ}

/-- `log L^{(k)}_{1,1}(ψ)` -/
def logLenPsi (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (k : ℕ) :
    Ω → ℝ :=
  fun ω => Real.log (lenObs ξ (psiMN Q W P 0 k) (rectAB 1 1) ω)

/-- pointwise comparison through `X_{1,1}` -/
lemma sq_sub_le (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) (k : ℕ) (ω : Ω) {c : ℝ}
    (hc : 0 ≤ c)
    (hX : ENNReal.ofReal c < XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω)
      1 1 → False) :
    |logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)| ≤ |ξ| * c := by
  have hφ := (isPhiVersion_phiMN hW (Nat.zero_le k)).cont ω
  have hψ := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont ω
  obtain ⟨M, hM⟩ := exists_bound_sq01 hψ
  obtain ⟨M', hM'⟩ := exists_bound_sq01 hφ
  refine L23.abs_logLen_sub_le (ξ := ξ) hM hM' fun x hx => ?_
  have hle : ENNReal.ofReal |phiMN W P 0 k x ω - psiMN Q W P 0 k x ω| ≤
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 1 :=
    le_iSup_of_le k (le_iSup₂_of_le x hx le_rfl)
  have h2 : ENNReal.ofReal |phiMN W P 0 k x ω - psiMN Q W P 0 k x ω| ≤ ENNReal.ofReal c :=
    le_of_not_gt fun h => hX (h.trans_le hle)
  rw [abs_sub_comm]
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h2

/-- **`E (log L^{(k)}(ψ) − log L^{(k)}(φ))² ≤ M` uniformly in `k`** (from DDDF Prop. 5) -/
theorem integral_sq_sub_le (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      Integrable (fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2) P ∧
      ∫ ω, (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ∂P ≤ M := by
  obtain ⟨C, c, hC, hc, h5⟩ := dddf_prop5 hW Q
  refine ⟨C * (ξ ^ 2 + 1) / c, by positivity, fun k => ?_⟩
  set D := fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2
  have hmψ : Measurable (logLenPsi ξ Q W P k) :=
    (measurable_lenObs (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont
      (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).meas _).log
  have hmφ : Measurable fun ω => Real.log (lenN ξ W P 1 1 k ω) :=
    (measurable_lenMN (ξ := ξ) hW 1 1 (Nat.zero_le k)).log
  have hDm : Measurable D := (hmψ.sub hmφ).pow_const 2
  have hb : 0 < c / (ξ ^ 2 + 1) := by positivity
  have h := integrable_integral_le_of_exp_tail (P := P) hDm (fun ω => sq_nonneg _)
    hC.le hb fun t ht => ?_
  · refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    field_simp
  -- `{t ≤ D} ⊆ {√t/√(ξ²+1) ≤ X_{1,1}}`
  set x := √t / √(ξ ^ 2 + 1) with hx
  have hx0 : 0 < x := by positivity
  refine (measure_mono fun ω (hω : t ≤ D ω) => ?_).trans ((h5 x hx0).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · show ENNReal.ofReal x ≤ _
    by_contra hcon
    push_neg at hcon
    -- `X < x` so `|A − B| ≤ |ξ| x`
    obtain ⟨c', hc'0, hc'x, hc'⟩ : ∃ c', 0 ≤ c' ∧ c' < x ∧
        ¬ ENNReal.ofReal c' < XAB (fun n y => phiMN W P 0 n y ω)
          (fun n y => psiMN Q W P 0 n y ω) 1 1 := by
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcon
      refine ⟨r, hr0, (ENNReal.ofReal_lt_ofReal_iff hx0).1 hr2, fun h => ?_⟩
      exact absurd (hr1.trans h) (lt_irrefl _)
    have hab := sq_sub_le hW Q ξ k ω hc'0 hc'
    have hD : D ω ≤ (|ξ| * c') ^ 2 := by
      show (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ≤ _
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have hξ : |ξ| ≤ √(ξ ^ 2 + 1) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have hlt : |ξ| * c' < √t := by
      have h1 : |ξ| * c' ≤ √(ξ ^ 2 + 1) * c' := mul_le_mul_of_nonneg_right hξ hc'0
      have h2 : √(ξ ^ 2 + 1) * c' < √(ξ ^ 2 + 1) * x :=
        mul_lt_mul_of_pos_left hc'x (by positivity)
      have h3 : √(ξ ^ 2 + 1) * x = √t := by rw [hx]; field_simp
      linarith
    have : (|ξ| * c') ^ 2 < t := by
      have := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      rwa [Real.sq_sqrt ht.le] at this
    linarith
  · rw [hx, div_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (by positivity)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) hC.le
    ring

end L24
end DDDF
end LQGMetric
