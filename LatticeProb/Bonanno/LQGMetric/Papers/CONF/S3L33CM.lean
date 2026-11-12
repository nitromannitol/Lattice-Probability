/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L33CM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41

/-!
# CONF Lemma 3.3, Step 2: the Cameron–Martin bound for the zero-boundary GFF

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381, proof of Lemma 3.3, Step 2,
C:1229–1231: "By a standard calculation for the GFF, the laws of `h̊^U` and `h̊^U − f` are
mutually absolutely continuous and the law of the Radon–Nikodym derivative depends only on the
Dirichlet energy of `f` … It follows that `P[G^U]` is bounded below by a constant depending only
on [the Dirichlet energy]." We make this quantitative by Cauchy–Schwarz (the second moment of the
Cameron–Martin density is `exp((F,F)_∇)`):

* `zb_shift_le_sqrt` : for a zero-boundary GFF `h̊` on a bounded nonempty open `U`,
  `F ∈ C_c^∞(U)` and `G = ∫ F ·`, `P[h̊ + G ∈ A] ≤ (P[h̊ ∈ A] · exp((F,F)_∇))^{1/2}`;
* `zb_lower_of_shift` : hence `P[h̊ + G ∈ A]² · exp(−(F,F)_∇) ≤ P[h̊ ∈ A]` (the lower bound of
  C:1231 with `f = −F`).

Cameron–Martin for the zero-boundary GFF: `MQ.map_tiltMeasure_cmSigma` (Berestycki–Powell
arXiv:2404.16642, Prop. `lem:CMGFF`); second moment `MQ.lintegral_rnDeriv_tilt_rpow`. The
Cauchy–Schwarz step follows `CameronMartin.lawPair0_addFun_le_sqrt` (whole-plane version).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open scoped ENNReal

namespace LQGMetric.CONF

open QuantumZipper QuantumZipper.CameronMartin MarkovZB Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Cameron–Martin, Cauchy–Schwarz form, for the zero-boundary GFF.** -/
theorem zb_shift_le_sqrt {U : Opens ℂ} (hUb : Bornology.IsBounded (U : Set ℂ))
    (hne : (U : Set ℂ).Nonempty) {ht : Ω → DistOn U} (hzb : IsZeroBoundaryGFF U ht P)
    (f : zsSub (U : Set ℂ)) {G : DistOn U} (hG : ∀ φ : TestOn U, G φ = ∫ x, f.1 x * φ x)
    {A : Set (DistOn U)} (hA : MeasurableSet A) :
    P {ω | ht ω + G ∈ A} ≤
      (P {ω | ht ω ∈ A} * ENNReal.ofReal (Real.exp (dirichletEnergyOn U f.1))) ^ (1 / 2 : ℝ) := by
  have hadm : ZBAdmissible U := zbAdmissible_of_isBounded hUb
  set X : TestOn U → Ω → ℝ := fun φ ω => ht ω φ
  have hX : IsZBGFFProcess U X P := hzb.process
  set Q := tiltMeasure X P (MQ.cmSigma f)
  have hQ : IsProbabilityMeasure Q :=
    isProbabilityMeasure_tiltMeasure hX.gaussian hX.measurable hX.centered _
  have hhtm : Measurable ht := hzb.measurable
  have hpath : Measurable fun ω (j : TestOn U) => X j ω := measurable_pi_iff.mpr hX.measurable
  have hev : Measurable (fun (T : DistOn U) (φ : TestOn U) => T φ) :=
    measurable_iff_comap_le.2 le_rfl
  have hsh : Measurable fun ω => ht ω + G :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hhtm).add_const (G φ)
  -- the law of `h̊ + G` is the push-forward of the tilt
  have hμ : P.map (fun ω => ht ω + G) = Q.map ht := by
    refine MQ.measure_distOn_ext ?_
    rw [Measure.map_map hev hsh, Measure.map_map hev hhtm]
    have e1 : (fun (T : DistOn U) (φ : TestOn U) => T φ) ∘ ht = fun ω j => X j ω := rfl
    rw [e1, MQ.map_tiltMeasure_cmSigma hadm hne hX f]
    congr 1
    funext ω φ
    simp only [Function.comp_apply]
    have e2 : (ht ω + G) φ = ht ω φ + G φ := rfl
    rw [e2, hG]
  have h1 : Q ≪ P := withDensity_absolutelyContinuous _ _
  set g : Ω → ℝ≥0∞ := Q.rnDeriv P
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  have hg2 : ∫⁻ ω, g ω ^ (2 : ℝ) ∂P =
      ENNReal.ofReal (Real.exp (dirichletEnergyOn U f.1)) := by
    rw [MQ.lintegral_rnDeriv_tilt_rpow hX.gaussian hX.measurable hX.centered,
      MQ.covNorm_cmSigma hadm hX f]
    congr 2; ring
  have hS : MeasurableSet (ht ⁻¹' A) := hhtm hA
  have hind : ∫⁻ ω, ((ht ⁻¹' A).indicator (1 : Ω → ℝ≥0∞) ω) ^ (2 : ℝ) ∂P = P (ht ⁻¹' A) := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ ht ⁻¹' A <;> simp [hω]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    ((measurable_one.indicator hS).aemeasurable) hg.aemeasurable
  rw [hind, hg2] at hHolder
  have e3 : {ω | ht ω + G ∈ A} = (fun ω => ht ω + G) ⁻¹' A := rfl
  rw [e3, ← Measure.map_apply hsh hA, hμ, Measure.map_apply hhtm hA,
    ← Measure.setLIntegral_rnDeriv h1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc ∫⁻ ω in ht ⁻¹' A, g ω ∂P = ∫⁻ ω, ((ht ⁻¹' A).indicator (1 : Ω → ℝ≥0∞) * g) ω ∂P := by
        rw [← lintegral_indicator hS]
        refine lintegral_congr fun ω => ?_
        by_cases hω : ω ∈ ht ⁻¹' A <;> simp [hω]
    _ ≤ _ := hHolder

/-- **Lower bound of CONF C:1231**: `P[h̊ + G ∈ A]² · exp(−(F,F)_∇) ≤ P[h̊ ∈ A]`. -/
theorem zb_lower_of_shift {U : Opens ℂ} (hUb : Bornology.IsBounded (U : Set ℂ))
    (hne : (U : Set ℂ).Nonempty) {ht : Ω → DistOn U} (hzb : IsZeroBoundaryGFF U ht P)
    (f : zsSub (U : Set ℂ)) {G : DistOn U} (hG : ∀ φ : TestOn U, G φ = ∫ x, f.1 x * φ x)
    {A : Set (DistOn U)} (hA : MeasurableSet A) :
    P {ω | ht ω + G ∈ A} ^ 2 * ENNReal.ofReal (Real.exp (-dirichletEnergyOn U f.1)) ≤
      P {ω | ht ω ∈ A} := by
  have key := zb_shift_le_sqrt hUb hne hzb f hG hA
  set a := P {ω | ht ω + G ∈ A}
  set b := P {ω | ht ω ∈ A}
  set E := dirichletEnergyOn U f.1
  have hsq : a ^ 2 ≤ b * ENNReal.ofReal (Real.exp E) := by
    have h2 := pow_le_pow_left₀ (by positivity) key 2
    have e : ((b * ENNReal.ofReal (Real.exp E)) ^ (1 / 2 : ℝ)) ^ 2 =
        b * ENNReal.ofReal (Real.exp E) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rwa [e] at h2
  have hinv : ENNReal.ofReal (Real.exp E) * ENNReal.ofReal (Real.exp (-E)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc a ^ 2 * ENNReal.ofReal (Real.exp (-E))
      ≤ b * ENNReal.ofReal (Real.exp E) * ENNReal.ofReal (Real.exp (-E)) := by gcongr
    _ = b := by rw [mul_assoc, hinv, mul_one]

end LQGMetric.CONF
