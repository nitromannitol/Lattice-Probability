/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatRefl2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 12: the law of the maximum of a Brownian bridge
(task P2-KILLED, D-KHK1)

`measureReal_bridge_max_gt`: for a planar bridge `X` of length `t > 0`, each coordinate and
`a > 0`, `P(max_{s ≤ t} X_s^{(b)} > a) = e^{−2a²/t}` — the reflection principle in the form
DZZ use at `LBM_LGDarXiv.tex` l. 491–499 (`P(max (B_s − (s/t)B_t)_1 ∈ [u_1, v_1]) =
e^{−2u_1²/t} − e^{−2v_1²/t}`).

Proof (Doob's time change; Revuz–Yor Ch. I Ex. 3.10, Karatzas–Shreve §5.6.B):
`V_u = ((t+u)/t) X_{tu/(t+u)}` is a Brownian motion (`isPreBrownianReal_timeChange`); the bridge
exceeds `a` iff `V_u − (a/t)u > a` for some `u`; QuantumZipper's drift-hitting law
(`prob_hit_neg_eq`) gives `e^{−2(a/t)a}`, with the strict/non-strict level handled by squeezing
between the hitting events of `−a` and `−a − ε`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

open QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma continuous_tcTime {t : ℝ≥0} (ht : t ≠ 0) : Continuous (tcTime t) := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  refine continuous_induced_rng.2 ?_
  show Continuous fun u ↦ ((tcTime t u : ℝ≥0) : ℝ)
  simp only [tcTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
  exact Continuous.div (by fun_prop) (by fun_prop) (fun u ↦ by positivity)

lemma ae_coordProc_end {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) : ∀ᵐ ω ∂P, coordProc X (b, t) ω = 0 := by
  have hG := hX.gauss.hasGaussianLaw_eval (b, t)
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hc : bridgeCov t (b, t) (b, t) = 0 := by
    simp [bridgeCov]
  have hlaw : HasLaw (coordProc X (b, t)) (gaussianReal 0 0) P := by
    refine ⟨hX.gauss.aemeasurable _, ?_⟩
    rw [hG.map_eq_gaussianReal, hX.mean, ← covariance_self (hX.gauss.aemeasurable _),
      hX.cov _ _ le_rfl le_rfl, hc]
    simp
  rw [gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac

lemma tcTime_inv {t s : ℝ≥0} (hst : s < t) : tcTime t (t * s / (t - s)) = s := by
  have hts : (0 : ℝ) < t - s := by
    have : (s : ℝ) < t := by exact_mod_cast hst
    linarith
  apply NNReal.eq
  simp only [tcTime]
  push_cast
  rw [NNReal.coe_sub hst.le]
  field_simp
  ring

/-- **Reflection principle for the bridge** (DZZ l. 491–499). -/
theorem measureReal_bridge_max_gt {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ s : ℝ≥0, s ≤ t ∧ a < coordProc X (b, s) ω} = Real.exp (-(2 * a ^ 2 / t)) := by
  have := hX.gauss.isProbabilityMeasure
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hVpre := isPreBrownianReal_timeChange ht hX b
  have hVc : ∀ᵐ ω ∂P, Continuous (fun u ↦ timeChange t X b u ω) := by
    filter_upwards [hX.cont] with ω hω
    have hc : Continuous fun u ↦ coordProc X (b, tcTime t u) ω := by
      cases b
      · exact Complex.continuous_re.comp (hω.comp (continuous_tcTime ht))
      · exact Complex.continuous_im.comp (hω.comp (continuous_tcTime ht))
    exact ((continuous_const.add NNReal.continuous_coe).div_const _).smul hc
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := QuantumZipper.CharFun.exists_good_version ⟨hVpre, hVc⟩
  set G : Set Ω := {ω | B' 0 ω = 0} with hG
  have hGm : MeasurableSet G := measurableSet_eq_fun (hB'm 0) measurable_const
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hB'eq, hVpre.eval_zero_ae_eq_zero] with ω h1 h2
    show B' 0 ω = 0
    rw [h1 0, h2]
  set b1 : ℝ≥0 → Ω → ℝ := fun u ω ↦ if ω ∈ G then -B' u ω else 0 with hb1
  have hb1V : ∀ᵐ ω ∂P, ∀ u, b1 u ω = -timeChange t X b u ω := by
    filter_upwards [hGae, hB'eq] with ω hω h u
    simp only [hb1, hω, ↓reduceIte, h u]
  have hgood : GoodBM b1 P := by
    refine ⟨hVpre.neg.congr fun u ↦ hb1V.mono fun ω h ↦ (h u).symm, fun u ↦
      Measurable.ite hGm (hB'm u).neg measurable_const, fun ω ↦ ?_, fun ω ↦ ?_⟩
    · by_cases hω : ω ∈ G
      · simp only [hb1, hω, ↓reduceIte]
        exact (hB'c ω).neg
      · simp only [hb1, hω, ↓reduceIte]
        exact continuous_const
    · by_cases hω : ω ∈ G
      · simp only [hb1, hω, ↓reduceIte]
        rw [show B' 0 ω = 0 from hω, neg_zero]
      · simp only [hb1, hω, ↓reduceIte]
  set μ : ℝ := a / t with hμ
  have hμ0 : 0 < μ := div_pos ha ht'
  -- the event in terms of the drift Brownian motion
  have hEF : P.real {ω | ∃ s : ℝ≥0, s ≤ t ∧ a < coordProc X (b, s) ω} =
      P.real {ω | ∃ u, dpath 1 μ b1 ω u < -a} := by
    refine measureReal_congr ?_
    filter_upwards [hb1V, ae_coordProc_end ht hX b] with ω hV hend
    apply propext
    simp only [dpath, hV, one_mul, timeChange, smul_eq_mul, hμ]
    constructor
    · rintro ⟨s, hs, has⟩
      have hst : s < t := lt_of_le_of_ne hs (by rintro rfl; rw [hend] at has; linarith)
      refine ⟨t * s / (t - s), ?_⟩
      rw [tcTime_inv hst]
      have hu : (0 : ℝ) ≤ ((t * s / (t - s) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      set u : ℝ := ((t * s / (t - s) : ℝ≥0) : ℝ)
      have h1 : ((t : ℝ) + u) / t * a < ((t : ℝ) + u) / t * coordProc X (b, s) ω :=
        mul_lt_mul_of_pos_left has (by positivity)
      have h2 : ((t : ℝ) + u) / t * a = a + a / t * u := by field_simp
      linarith
    · rintro ⟨u, hu⟩
      refine ⟨tcTime t u, tcTime_le t u, ?_⟩
      have hpos : (0 : ℝ) < ((t : ℝ) + u) / t := by positivity
      have h2 : ((t : ℝ) + u) / t * a = a + a / t * u := by field_simp
      have : ((t : ℝ) + u) / t * a < ((t : ℝ) + u) / t * coordProc X (b, tcTime t u) ω := by
        linarith
      exact lt_of_mul_lt_mul_left this hpos.le
  rw [hEF]
  have hcont : ∀ ω, Continuous (dpath 1 μ b1 ω) := fun ω ↦ by
    unfold dpath
    exact ((hgood.cont ω).const_smul (1 : ℝ) |>.congr fun _ ↦ by simp).add
      (continuous_const.mul NNReal.continuous_coe)
  apply le_antisymm
  · -- upper bound: crossing below `-a` forces hitting `-a`
    have hsub : {ω | ∃ u, dpath 1 μ b1 ω u < -a} ⊆ {ω | ∃ u, dpath 1 μ b1 ω u = -a} := by
      rintro ω ⟨u, hu⟩
      exact exists_eq_of_le (hcont ω) (by simp [dpath, hgood.zero ω]) ha hu.le
    calc P.real {ω | ∃ u, dpath 1 μ b1 ω u < -a}
        ≤ P.real {ω | ∃ u, dpath 1 μ b1 ω u = -a} := measureReal_mono hsub
      _ = Real.exp (-(2 * a ^ 2 / t)) := by
        rw [prob_hit_neg_eq hgood one_pos hμ0 (neg_lt_zero.mpr ha), hμ]
        congr 1
        field_simp
  · -- lower bound: hitting `-a - ε` forces crossing below `-a`
    have hlow : ∀ ε > 0, Real.exp (2 * μ * (-a - ε) / 1 ^ 2) ≤
        P.real {ω | ∃ u, dpath 1 μ b1 ω u < -a} := by
      intro ε hε
      rw [← prob_hit_neg_eq hgood one_pos hμ0 (by linarith : -a - ε < 0)]
      refine measureReal_mono fun ω ⟨u, hu⟩ ↦ ⟨u, ?_⟩
      rw [hu]
      linarith
    have htend : Tendsto (fun ε : ℝ ↦ Real.exp (2 * μ * (-a - ε) / 1 ^ 2)) (𝓝[>] 0)
        (𝓝 (Real.exp (2 * μ * (-a - 0) / 1 ^ 2))) :=
      ((by fun_prop : Continuous fun ε : ℝ ↦ Real.exp (2 * μ * (-a - ε) / 1 ^ 2)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have := le_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε ↦ hlow ε hε)
    calc Real.exp (-(2 * a ^ 2 / t)) = Real.exp (2 * μ * (-a - 0) / 1 ^ 2) := by
          rw [hμ]
          congr 1
          field_simp
          ring
      _ ≤ _ := this

end KilledHeat
end LQGMetric
