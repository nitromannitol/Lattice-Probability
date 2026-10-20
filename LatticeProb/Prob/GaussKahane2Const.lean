/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/Kahane2Const.lean.
-/
import LatticeProb.Prob.GaussKahaneRpow
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Kahane's inequality up to an additive constant in the covariance

Let `X` and `Y` be centred Gaussian vectors indexed by a nonempty finite set and let `p` be positive
weights. If `Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ) + c` for all `i, j`, with `c ≥ 0`, then for `q ≤ 0` or
`q ≥ 1`

  `E (∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ/2})^q ≤ e^{q(q-1)c/2} E (∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ/2})^q`

(`LatticeProb.Kahane.kahane_rpow_le_add_const`). The proof adds to `Y` an independent
`N(0, c)` variable, which raises all covariances by `c`, and uses
`E e^{q(g - c/2)} = e^{q(q-1)c/2}` for `g ∼ N(0, c)`.
The shifted vector `Yᵢ + g` lives on the product space `Ω' × ℝ` with law `P' ⊗ N(0, c)`
(`LatticeProb.Kahane.shiftVec`), and the inequality is then Kahane's convexity inequality for the
moments (`LatticeProb.Kahane.kahane_convexity_rpow`).

The namespace `Kahane2ConstExample` shows that the hypotheses are satisfiable: with `Y = X` and
`c = 0` the covariance comparison holds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal

namespace LatticeProb

namespace Kahane

variable {ι : Type*} [Fintype ι]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {P' : Measure Ω'}

/-- The vector `Y` shifted by an independent scalar: `(ω, g) ↦ (Yᵢ ω + g)ᵢ`. -/
def shiftVec (Y : Ω' → ι → ℝ) : Ω' × ℝ → ι → ℝ := fun z i => Y z.1 i + z.2

/-- The law of the shifted vector: `P' ⊗ N(0, c)`. -/
def shiftMeas (P' : Measure Ω') (c : ℝ≥0) : Measure (Ω' × ℝ) := P'.prod (gaussianReal 0 c)

/-- The law `P' ⊗ N(0, c)` of the shifted vector is a probability measure when `P'` is. -/
instance isProbabilityMeasure_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) :
    IsProbabilityMeasure (shiftMeas P' c) := by
  unfold shiftMeas; infer_instance

/-- The first marginal of the shifted law is `P'`. -/
lemma map_fst_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) :
    (shiftMeas P' c).map Prod.fst = P' := by
  rw [shiftMeas, Measure.map_fst_prod, measure_univ, one_smul]

/-- The second marginal of the shifted law is `N(0, c)`. -/
lemma map_snd_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) :
    (shiftMeas P' c).map Prod.snd = gaussianReal 0 c := by
  rw [shiftMeas, Measure.map_snd_prod, measure_univ, one_smul]

/-- Shifting a Gaussian vector by an independent `N(0, c)` scalar gives a Gaussian vector. -/
lemma hasGaussianLaw_shiftVec {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P') (c : ℝ≥0) :
    HasGaussianLaw (shiftVec Y) (shiftMeas P' c) := by
  have := hY.isProbabilityMeasure
  have hY1 : HasGaussianLaw (fun z : Ω' × ℝ => Y z.1) (shiftMeas P' c) := by
    have hae : AEMeasurable Y ((shiftMeas P' c).map Prod.fst) := by
      rw [map_fst_shiftMeas]; exact hY.aemeasurable
    have hmap : (shiftMeas P' c).map (fun z : Ω' × ℝ => Y z.1) = P'.map Y := by
      conv_rhs => rw [← map_fst_shiftMeas (P' := P') c]
      rw [AEMeasurable.map_map_of_aemeasurable hae measurable_fst.aemeasurable]
      rfl
    have : IsGaussian ((shiftMeas P' c).map fun z : Ω' × ℝ => Y z.1) := by
      rw [hmap]; exact hY.isGaussian_map
    exact IsGaussian.hasGaussianLaw
  have hg : HasGaussianLaw (fun z : Ω' × ℝ => z.2) (shiftMeas P' c) := by
    have : IsGaussian ((shiftMeas P' c).map fun z : Ω' × ℝ => z.2) := by
      rw [show (fun z : Ω' × ℝ => z.2) = Prod.snd from rfl, map_snd_shiftMeas]; infer_instance
    exact IsGaussian.hasGaussianLaw
  have hind : (fun z : Ω' × ℝ => Y z.1) ⟂ᵢ[shiftMeas P' c] (fun z : Ω' × ℝ => z.2) :=
    indepFun_prod₀ hY.aemeasurable measurable_id.aemeasurable
  have hj := ProbabilityTheory.IndepFun.hasGaussianLaw hY1 hg hind
  set L : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ +
      ContinuousLinearMap.pi fun _ => ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ
  have he : shiftVec Y = fun ω => L (Y ω.1, ω.2) := by
    funext z i; simp [L, shiftVec]
  rw [he]
  exact hj.map_fun L

/-- Integrals of functions of the first coordinate under the shifted law are integrals under
`P'`. -/
lemma integral_fst_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) (f : Ω' → ℝ) :
    ∫ z, f z.1 ∂shiftMeas P' c = ∫ x, f x ∂P' := by
  rw [shiftMeas, integral_fun_fst, probReal_univ, one_smul]

/-- Integrals of functions of the second coordinate under the shifted law are integrals under
`N(0, c)`. -/
lemma integral_snd_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) (f : ℝ → ℝ) :
    ∫ z, f z.2 ∂shiftMeas P' c = ∫ y, f y ∂gaussianReal 0 c := by
  rw [shiftMeas, integral_fun_snd, probReal_univ, one_smul]

/-- The shifted vector stays centred when `Y` is centred. -/
lemma integral_shiftVec {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P')
    (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0) (i : ι) :
    ∫ z, shiftVec Y z i ∂shiftMeas P' c = 0 := by
  have := hY.isProbabilityMeasure
  have h1 : Integrable (fun z : Ω' × ℝ => Y z.1 i) (shiftMeas P' c) := by
    have := (Pitt.memLp_coord hY i).integrable one_le_two
    rw [← map_fst_shiftMeas (P' := P') c] at this
    exact this.comp_measurable measurable_fst
  have h2 : Integrable (fun z : Ω' × ℝ => z.2) (shiftMeas P' c) := by
    have : Integrable (fun y : ℝ => y) (gaussianReal 0 c) :=
      (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 c)).integrable
    rw [← map_snd_shiftMeas (P' := P') c] at this
    exact this.comp_measurable measurable_snd
  simp only [shiftVec]
  rw [integral_add h1 h2, integral_fst_shiftMeas c (fun x => Y x i),
    integral_snd_shiftMeas c (fun y => y), hYm i, integral_id_gaussianReal, add_zero]

/-- The first coordinate of the shifted vector is square integrable under the shifted law. -/
lemma memLp_fst_shiftMeas {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P') (c : ℝ≥0) (i : ι) :
    MemLp (fun z : Ω' × ℝ => Y z.1 i) 2 (shiftMeas P' c) := by
  have := hY.isProbabilityMeasure
  have h := Pitt.memLp_coord hY i
  rw [← map_fst_shiftMeas (P' := P') c] at h
  exact h.comp_of_map measurable_fst.aemeasurable

/-- The second coordinate of the shifted law is square integrable. -/
lemma memLp_snd_shiftMeas [IsProbabilityMeasure P'] (c : ℝ≥0) :
    MemLp (fun z : Ω' × ℝ => z.2) 2 (shiftMeas P' c) := by
  have h : MemLp (fun y : ℝ => y) 2 (gaussianReal 0 c) :=
    (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 c)).memLp_two
  rw [← map_snd_shiftMeas (P' := P') c] at h
  exact h.comp_of_map measurable_snd.aemeasurable

/-- **Covariance of the shifted vector**: `Cov(Yᵢ + g, Yⱼ + g) = Cov(Yᵢ, Yⱼ) + c`. -/
lemma cov_shiftVec {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P')
    (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0) (i j : ι) :
    cov[fun z => shiftVec Y z i, fun z => shiftVec Y z j; shiftMeas P' c] =
      cov[fun ω => Y ω i, fun ω => Y ω j; P'] + c := by
  have := hY.isProbabilityMeasure
  have hA := memLp_fst_shiftMeas hY c
  have hG := memLp_snd_shiftMeas (P' := P') c
  have hGm : ∫ z : Ω' × ℝ, z.2 ∂shiftMeas P' c = 0 := by
    rw [integral_snd_shiftMeas c (fun y => y), integral_id_gaussianReal]
  have hAm : ∀ i, ∫ z : Ω' × ℝ, Y z.1 i ∂shiftMeas P' c = 0 := fun i => by
    rw [integral_fst_shiftMeas c (fun x => Y x i), hYm i]
  have hAA : ∀ i j, cov[fun z : Ω' × ℝ => Y z.1 i, fun z => Y z.1 j; shiftMeas P' c] =
      cov[fun ω => Y ω i, fun ω => Y ω j; P'] := fun i j => by
    unfold covariance
    rw [integral_fst_shiftMeas c (fun x => Y x i), integral_fst_shiftMeas c (fun x => Y x j)]
    exact integral_fst_shiftMeas c
      (fun x => (Y x i - ∫ ω, Y ω i ∂P') * (Y x j - ∫ ω, Y ω j ∂P'))
  have hAG : ∀ i, cov[fun z : Ω' × ℝ => Y z.1 i, fun z => z.2; shiftMeas P' c] = 0 := fun i => by
    unfold covariance
    rw [hAm i, hGm, shiftMeas]
    simp only [sub_zero]
    rw [integral_prod_mul (fun x => Y x i) (fun y : ℝ => y), integral_id_gaussianReal, mul_zero]
  have hGG : cov[fun z : Ω' × ℝ => z.2, fun z => z.2; shiftMeas P' c] = c := by
    have h1 : cov[fun z : Ω' × ℝ => z.2, fun z => z.2; shiftMeas P' c] =
        cov[fun y : ℝ => y, fun y => y; gaussianReal 0 c] := by
      unfold covariance
      rw [integral_snd_shiftMeas c (fun y => y)]
      exact integral_snd_shiftMeas c (fun y => (y - ∫ y, y ∂gaussianReal 0 c) *
        (y - ∫ y, y ∂gaussianReal 0 c))
    rw [h1, covariance_self (X := fun y : ℝ => y) measurable_id'.aemeasurable,
      variance_fun_id_gaussianReal]
  have he : ∀ i, (fun z => shiftVec Y z i) =
      (fun z : Ω' × ℝ => Y z.1 i) + fun z : Ω' × ℝ => z.2 := fun i => rfl
  rw [he i, he j, covariance_add_left (hA i) hG ((hA j).add hG),
    covariance_add_right (hA i) (hA j) hG, covariance_add_right hG (hA j) hG, hAA, hAG,
    covariance_comm (fun z : Ω' × ℝ => z.2), hAG, hGG]
  ring

/-- **Variance of the shifted vector**: `Var(Yᵢ + g) = Var(Yᵢ) + c`. -/
lemma variance_shiftVec {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P')
    (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0) (i : ι) :
    Var[fun z => shiftVec Y z i; shiftMeas P' c] = Var[fun ω => Y ω i; P'] + c := by
  have := hY.isProbabilityMeasure
  have h := cov_shiftVec hY hYm c i i
  have hm : AEMeasurable (fun z => shiftVec Y z i) (shiftMeas P' c) :=
    ((memLp_fst_shiftMeas hY c i).add
      (memLp_snd_shiftMeas (P' := P') c)).aestronglyMeasurable.aemeasurable
  rwa [covariance_self hm,
    covariance_self (Pitt.memLp_coord hY i).aestronglyMeasurable.aemeasurable] at h

/-- **Moments of the shifted vector**:
`E (∑ pᵢ e^{Yᵢ + g - Var(Yᵢ + g)/2})^q = e^{q(q-1)c/2} E (∑ pᵢ e^{Yᵢ - Var Yᵢ/2})^q`. -/
lemma integral_rpow_shiftVec {Y : Ω' → ι → ℝ} (hY : HasGaussianLaw Y P')
    (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (q : ℝ) :
    ∫ z, (∑ i, p i * Real.exp (shiftVec Y z i -
        Var[fun z => shiftVec Y z i; shiftMeas P' c] / 2)) ^ q ∂shiftMeas P' c =
      Real.exp (q * (q - 1) * c / 2) *
        ∫ ω, (∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)) ^ q ∂P' := by
  have := hY.isProbabilityMeasure
  set S : Ω' → ℝ := fun ω => ∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)
  have hS : ∀ ω, 0 ≤ S ω := fun ω =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le
  have hpt : ∀ z : Ω' × ℝ, (∑ i, p i * Real.exp (shiftVec Y z i -
      Var[fun z => shiftVec Y z i; shiftMeas P' c] / 2)) ^ q =
      S z.1 ^ q * Real.exp (q * (z.2 - c / 2)) := by
    intro z
    have : (∑ i, p i * Real.exp (shiftVec Y z i -
        Var[fun z => shiftVec Y z i; shiftMeas P' c] / 2)) =
        Real.exp (z.2 - c / 2) * S z.1 := by
      simp_rw [variance_shiftVec hY hYm c]
      simp only [S, Finset.mul_sum, shiftVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [this, Real.mul_rpow (Real.exp_pos _).le (hS _), ← Real.exp_mul, mul_comm,
      mul_comm (z.2 - c / 2)]
  simp_rw [hpt]
  rw [shiftMeas, integral_prod_mul (fun x => S x ^ q)
    (fun y : ℝ => Real.exp (q * (y - c / 2)))]
  have hg : ∫ y, Real.exp (q * (y - c / 2)) ∂gaussianReal 0 c =
      Real.exp (q * (q - 1) * c / 2) := by
    have h1 : (fun y : ℝ => Real.exp (q * (y - c / 2))) =
        fun y => Real.exp (-(q * c / 2)) * Real.exp (q * y) := by
      funext y; rw [← Real.exp_add]; congr 1; ring
    have h2 := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := c)) q
    rw [mgf] at h2
    rw [h1, integral_const_mul, h2, ← Real.exp_add]
    congr 1; ring
  rw [hg, mul_comm]

/-- **Kahane's inequality, covariance comparison up to `+ c`** (`q ≤ 0` or `q ≥ 1`).

For centred Gaussian vectors `X` and `Y` with positive weights `p` and
`Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ) + c` for all `i, j`, with `c ≥ 0`,

  `E (∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ/2})^q ≤ e^{q(q-1)c/2} E (∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ/2})^q`. -/
theorem kahane_rpow_le_add_const [Nonempty ι] {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P') (hXm : ∀ i, ∫ ω, X ω i ∂P = 0)
    (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0) (c : ℝ≥0)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      cov[fun ω => Y ω i, fun ω => Y ω j; P'] + c) :
    ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ q ∂P ≤
      Real.exp (q * (q - 1) * c / 2) *
        ∫ ω, (∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)) ^ q ∂P' := by
  have h := kahane_convexity_rpow hq hp hX (hasGaussianLaw_shiftVec hY c) hXm
    (integral_shiftVec hY hYm c) fun i j => by rw [cov_shiftVec hY hYm c]; exact hcov i j
  rwa [integral_rpow_shiftVec hY hYm c (fun i => (hp i).le)] at h

namespace Kahane2ConstExample

/-- With `Y = X` and `c = 0` the covariance comparison holds with equality, so
`kahane_rpow_le_add_const` applies to any centred Gaussian vector `X` with positive weights,
for `q = 2`. -/
example [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) :
    ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ (2 : ℝ) ∂P ≤
      Real.exp (2 * (2 - 1) * ((0 : ℝ≥0) : ℝ) / 2) *
        ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ (2 : ℝ) ∂P :=
  kahane_rpow_le_add_const (q := 2) (Or.inr (by norm_num)) hp hX hX hXm hXm 0 fun _ _ => by simp

end Kahane2ConstExample

end Kahane

end LatticeProb
