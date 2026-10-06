/-
# The multivariate orthant: vocabulary for the Sazonov smoothing inequality (mvbe C1)

The multivariate Berry–Esseen route (`scratch/pk/mvbe-route.md`, ingredient C) needs a smoothing
inequality for **orthants** of `ℝ^m` with the dimension factor `m^{1/4}`.  The frozen target's
vocabulary — `mvbeGram`, `mvbeCoeffNorm`, `mvbeQuadForm` — is fixed in
`MultivariateBerryEsseenTarget.lean`; that file records the one remaining gap as exactly this
smoothing inequality, which has no reference formalization and no Mathlib infrastructure.

This module builds the missing **C-1 vocabulary**, so the inequality can be stated and attacked
precisely:

* `orthantSet`, `orthantProb` — the orthant `{y | ∀ j, y j ≤ h j}` and its `μ`-mass;
* `charFunVec` — the multivariate characteristic function `t ↦ ∫ exp (i ∑ j, t j * y j) ∂μ`;
* `covMatrix`, `NearIsotropic` — the covariance matrix of a measure on `Fin m → ℝ`, and the
  near-isotropy condition `(1-δ)‖v‖² ≤ vᵀ S v ≤ (1+δ)‖v‖²` (the frozen admissibility hypothesis,
  phrased through the existing `mvbeQuadForm`);
* `sazonovRemainder`, `sazonovTail` — the two terms of the smoothing inequality: the Sazonov Fourier
  functional over a ball and the Gaussian-orthant tail;
* `SazonovSmoothingInequality` — the named `Prop` (route C1) with the explicit `m^{1/4}` factor.

The proved lemmas are the structural facts of the orthant mass (`orthantProb ∈ [0,1]`, monotone in
the threshold, `1` in dimension `0`), the monotonicity of the near-isotropy relaxation, the basic
facts of the multivariate characteristic function (`charFunVec 0 = 1` and `‖charFunVec‖ ≤ 1`), the
diagonal/positivity of the Sazonov functional, and the `m^{1/4}` bandwidth balance
`sazonovTail m (m^{3/4}) = m^{1/4}` that converts the `m`-scaled tail into the dimension factor.
Further Sazonov facts: the functional is symmetric (`sazonovRemainder_comm`) and the tail is
nonnegative and antitone (`sazonovTail_nonneg`, `sazonovTail_antitone`), with the balance
threshold `T ≥ m^{3/4} → sazonovTail m T ≤ m^{1/4}` (`sazonovTail_le_quarter`).
-/
import Mathlib
import LatticeProb.Prob.MultivariateBerryEsseenTarget

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- **The orthant** `{y : Fin m → ℝ | ∀ j, y j ≤ h j}` of thresholds `h`. -/
def orthantSet {m : ℕ} (h : Fin m → ℝ) : Set (Fin m → ℝ) := {y | ∀ j, y j ≤ h j}

/-- The orthant is measurable. -/
theorem measurableSet_orthant {m : ℕ} (h : Fin m → ℝ) : MeasurableSet (orthantSet h) := by
  simp only [orthantSet, Set.setOf_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const

/-- **The orthant mass** of `μ` at threshold `h`. -/
noncomputable def orthantProb {m : ℕ} (μ : Measure (Fin m → ℝ)) (h : Fin m → ℝ) : ℝ :=
  (μ (orthantSet h)).toReal

/-- The orthant mass of a probability measure lies in `[0, 1]`. -/
theorem orthantProb_mem_Icc {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (h : Fin m → ℝ) : orthantProb μ h ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : μ (orthantSet h) ≤ 1 := by
    calc μ (orthantSet h) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ⟨ENNReal.toReal_nonneg,
    (ENNReal.toReal_mono (b := 1) (by simp) hle).trans_eq (by simp)⟩

/-- The orthant mass is monotone in the threshold. -/
theorem orthantProb_mono {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    {h h' : Fin m → ℝ} (hh : h ≤ h') :
    orthantProb μ h ≤ orthantProb μ h' := by
  refine ENNReal.toReal_mono ?_ (measure_mono fun y hy j => le_trans (hy j) (hh j))
  exact ne_top_of_le_ne_top (by rw [measure_univ]; simp)
    (measure_mono (Set.subset_univ _))

/-- In dimension `0` the orthant is the whole space, so its mass is `1`. -/
theorem orthantProb_zero {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (h : Fin m → ℝ) (hm : m = 0) : orthantProb μ h = 1 := by
  subst hm
  have huniv : orthantSet h = Set.univ :=
    Set.eq_univ_of_forall fun y => fun j => Fin.elim0 j
  rw [orthantProb, huniv, measure_univ, ENNReal.toReal_one]

/-- **The multivariate characteristic function** `t ↦ ∫ exp (i ∑ j, t j * y j) ∂μ`. -/
noncomputable def charFunVec {m : ℕ} (μ : Measure (Fin m → ℝ)) (t : Fin m → ℝ) : ℂ :=
  ∫ y, Complex.exp (((∑ j, t j * y j : ℝ) : ℂ) * Complex.I) ∂μ

/-- **The covariance matrix** of a measure on `Fin m → ℝ`. -/
noncomputable def covMatrix {m : ℕ} (μ : Measure (Fin m → ℝ)) : Matrix (Fin m) (Fin m) ℝ :=
  fun j k => ∫ y, y j * y k ∂μ

/-- **Near-isotropy** for the Sazonov hypothesis: the quadratic form of `S` is between `1 - δ` and
`1 + δ` times the squared Euclidean norm, phrased through the frozen `mvbeQuadForm`. -/
def NearIsotropic {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ) : Prop :=
  ∀ v : Fin m → ℝ,
    (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm S v ∧ mvbeQuadForm S v ≤ (1 + δ) * ∑ j, v j ^ 2

/-- The near-isotropy relaxation: a larger `δ` is a weaker hypothesis. -/
theorem NearIsotropic.mono {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (h : NearIsotropic S δ) : NearIsotropic S δ' := by
  intro v
  obtain ⟨h1, h2⟩ := h v
  have hnn : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) hnn) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) hnn)⟩

/-- **The Sazonov Fourier functional** over the ball of radius `T`: the first term of the
multivariate smoothing inequality. -/
noncomputable def sazonovRemainder {m : ℕ} (μ μ' : Measure (Fin m → ℝ)) (T : ℝ) : ℝ :=
  ∫ t in {t : Fin m → ℝ | (∑ j, t j ^ 2) ≤ T ^ 2},
    ‖charFunVec μ t - charFunVec μ' t‖ ∂volume

/-- **The Gaussian orthant tail** left after cutting the Fourier integral at `T`: the second term
of the smoothing inequality, controlled by the Gaussian orthant estimate. -/
noncomputable def sazonovTail (m : ℕ) (T : ℝ) : ℝ :=
  (m : ℝ) * (T : ℝ)⁻¹

/-- **Ingredient C1, the Sazonov-type multivariate smoothing inequality** (the named open input of
the mvbe route, cf. `MultivariateBerryEsseenTarget.lean`): two probability measures with
near-isotropic covariances are compared on every orthant by the Sazonov Fourier functional plus a
Gaussian tail, with the dimension factor `m^{1/4}`. -/
def SazonovSmoothingInequality : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (δ T : ℝ) (μ μ' : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure μ'],
      0 < δ → 0 < T → NearIsotropic (covMatrix μ) δ → NearIsotropic (covMatrix μ') δ →
      ∀ h : Fin m → ℝ,
        |orthantProb μ h - orthantProb μ' h|
          ≤ C * ((m : ℝ) ^ ((1 : ℝ) / 4) * (1 + δ⁻¹)) * sazonovRemainder μ μ' T
            + sazonovTail m T

/-- The multivariate characteristic function is `1` at the origin. -/
theorem charFunVec_zero {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] :
    charFunVec μ 0 = 1 := by
  rw [charFunVec]
  simp

/-- The multivariate characteristic function of a probability measure has norm at most `1`. -/
theorem charFunVec_norm_le_one {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (t : Fin m → ℝ) : ‖charFunVec μ t‖ ≤ 1 := by
  rw [charFunVec]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hconst : (fun y : Fin m → ℝ =>
        ‖Complex.exp (((∑ j, t j * y j : ℝ) : ℂ) * Complex.I)‖) = fun _ => (1 : ℝ) := by
    funext y
    rw [Complex.norm_exp]
    simp
  rw [hconst]
  simp

/-- The Sazonov functional vanishes on the diagonal. -/
theorem sazonovRemainder_self {m : ℕ} (μ : Measure (Fin m → ℝ)) (T : ℝ) :
    sazonovRemainder μ μ T = 0 := by
  rw [sazonovRemainder]
  simp

/-- The Sazonov functional is nonnegative. -/
theorem sazonovRemainder_nonneg {m : ℕ} (μ μ' : Measure (Fin m → ℝ)) (T : ℝ) :
    0 ≤ sazonovRemainder μ μ' T := by
  rw [sazonovRemainder]
  exact integral_nonneg fun t => norm_nonneg _

/-- The Sazonov tail is positive. -/
theorem sazonovTail_pos {m : ℕ} (hm : 0 < m) {T : ℝ} (hT : 0 < T) :
    0 < sazonovTail m T := by
  rw [sazonovTail]
  exact mul_pos (Nat.cast_pos.mpr hm) (inv_pos.mpr hT)

/-- The `m^{1/4}` factor is positive. -/
theorem rpow_quarter_pos {m : ℕ} (hm : 0 < m) : 0 < (m : ℝ) ^ ((1 : ℝ) / 4) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _

/-- **The `m^{1/4}` bandwidth balance.**  At the bandwidth `T = m^{3/4}` the Gaussian tail
`sazonovTail m T = m / T` is exactly `m^{1/4}`: the `T`-vs-`m` trade-off that turns the `m`-scaled
tail into the dimension factor `m^{1/4}` of route C1. -/
theorem sazonovTail_bandwidth {m : ℕ} (hm : 0 < m) :
    sazonovTail m ((m : ℝ) ^ ((3 : ℝ) / 4)) = (m : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [sazonovTail]
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hb : (m : ℝ) ^ ((3 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hm0 _).ne'
  field_simp
  rw [← Real.rpow_add hm0, show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]

/-- The Sazonov functional is symmetric in its two measures. -/
theorem sazonovRemainder_comm {m : ℕ} (μ μ' : Measure (Fin m → ℝ)) (T : ℝ) :
    sazonovRemainder μ μ' T = sazonovRemainder μ' μ T := by
  rw [sazonovRemainder, sazonovRemainder]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  exact norm_sub_rev _ _

/-- The Sazonov tail is nonnegative. -/
theorem sazonovTail_nonneg {m : ℕ} {T : ℝ} (hT : 0 ≤ T) : 0 ≤ sazonovTail m T := by
  rw [sazonovTail]
  exact mul_nonneg (Nat.cast_nonneg m) (inv_nonneg.mpr hT)

/-- The Sazonov tail is antitone in the bandwidth. -/
theorem sazonovTail_antitone {m : ℕ} {T T' : ℝ} (hT : 0 < T) (hTT : T ≤ T') :
    sazonovTail m T' ≤ sazonovTail m T := by
  rw [sazonovTail, sazonovTail]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using one_div_le_one_div_of_le hT hTT) (Nat.cast_nonneg m)

/-- **The `m^{1/4}` balance threshold.**  Once the bandwidth reaches `T ≥ m^{3/4}` the Gaussian
tail `m / T` is at most the dimension factor `m^{1/4}`. -/
theorem sazonovTail_le_quarter {m : ℕ} (hm : 0 < m) {T : ℝ}
    (hT : (m : ℝ) ^ ((3 : ℝ) / 4) ≤ T) : sazonovTail m T ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hb : (0 : ℝ) < (m : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hm0 _
  have hq : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hm0 _
  have hT0 : 0 < T := lt_of_lt_of_le hb hT
  have h3 : (m : ℝ) = (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hm0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
  rw [sazonovTail, ← div_eq_mul_inv, div_le_iff₀ hT0]
  calc (m : ℝ) = (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((3 : ℝ) / 4) := h3
    _ ≤ (m : ℝ) ^ ((1 : ℝ) / 4) * T := mul_le_mul_of_nonneg_left hT hq.le

end LatticeProb
