/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux2
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Node `B57`, auxiliary file 3: Gaussian fields indexed by triples

For a family of vectors `β : Tri → E` (`E` finite dimensional) and `x ∼ stdGaussian E`, the field
`Yf β x q = ⟪β q, x⟫` is a centered Gaussian field on triples.

* `gLaw F`: the canonical law on `Tri → ℝ` of a centered Gaussian field with covariance `kap`
  on the finite set `F` (and `0` off `F`).
* `transfer`: if `β` realises `kap` on `F`, then for every measurable `Φ` which only depends on
  the coordinates in `F`, `E Φ(Yf β x) = ∫ Φ d(gLaw F)`, and integrability transfers.
* `integral_mul_of_orth`: functionals of two mutually orthogonal groups of Gram vectors are
  independent (`E[ΦΨ] = E Φ E Ψ`).
* `integrable_of_le_exp`: domination by `c e^{t⟪v,x⟫}` gives integrability.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian field of a family of vectors: `Y_x(q) = ⟪β q, x⟫`. -/
def Yf (β : Tri → E) (x : E) : Tri → ℝ := fun q => ⟪β q, x⟫

omit [FiniteDimensional ℝ E] in
theorem measurable_Yf (β : Tri → E) : Measurable (Yf β) :=
  Measurable.of_eval fun q => (continuous_const.inner continuous_id).measurable

/-- `Φ` only depends on the coordinates in `F`. -/
def IsLoc (F : Finset Tri) (Φ : (Tri → ℝ) → ℝ) : Prop :=
  ∀ Y Y' : Tri → ℝ, (∀ q ∈ F, Y q = Y' q) → Φ Y = Φ Y'

theorem IsLoc.mono {F G : Finset Tri} {Φ : (Tri → ℝ) → ℝ} (h : IsLoc F Φ) (hFG : F ⊆ G) :
    IsLoc G Φ := fun Y Y' hY => h Y Y' fun q hq => hY q (hFG hq)

/-- Extension by zero of a vector indexed by `F` (Euclidean version). -/
def extQ (F : Finset Tri) (y : EuclideanSpace ℝ F) : Tri → ℝ :=
  fun q => if h : q ∈ F then y ⟨q, h⟩ else 0

theorem measurable_extQ (F : Finset Tri) : Measurable (extQ F) := by
  refine Measurable.of_eval fun q => ?_
  by_cases h : q ∈ F
  · simp only [extQ, h, dite_true]
    exact (PiLp.continuous_apply 2 (fun _ : F => ℝ) ⟨q, h⟩).measurable
  · simp only [extQ, h, dite_false]
    exact measurable_const

/-- Extension by zero of a vector indexed by `F` (plain function version). -/
def extF (F : Finset Tri) (y : F → ℝ) : Tri → ℝ :=
  fun q => if h : q ∈ F then y ⟨q, h⟩ else 0

theorem measurable_extF (F : Finset Tri) : Measurable (extF F) := by
  refine Measurable.of_eval fun q => ?_
  by_cases h : q ∈ F
  · simp only [extF, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extF, h, dite_false]
    exact measurable_const

/-- The canonical Gaussian law with covariance `kap` on `F`. -/
def gLaw (F : Finset Tri) : Measure (Tri → ℝ) :=
  (multivariateGaussian 0 (Matrix.of fun i j : F => kap i j)).map (extQ F)

theorem gLaw_eq_map (F : Finset Tri) (β : Tri → E)
    (hβ : ∀ q ∈ F, ∀ q' ∈ F, ⟪β q, β q'⟫ = kap q q') :
    gLaw F = (stdGaussian E).map (extQ F ∘ gramMap F β) := by
  rw [← Measure.map_map (measurable_extQ F) (gramMap F β).continuous.measurable,
    map_gramMap_stdGaussian]
  unfold gLaw
  congr 2
  ext i j
  simp [hβ i i.2 j j.2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem Yf_eq_extQ (F : Finset Tri) (β : Tri → E) (x : E) :
    ∀ q ∈ F, Yf β x q = extQ F (gramMap F β x) q := by
  intro q hq
  simp [Yf, extQ, hq, gramMap_apply]

/-- **Transfer of laws.** -/
theorem transfer_integral (F : Finset Tri) (β : Tri → E)
    (hβ : ∀ q ∈ F, ∀ q' ∈ F, ⟪β q, β q'⟫ = kap q q') {Φ : (Tri → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hloc : IsLoc F Φ) : ∫ x, Φ (Yf β x) ∂stdGaussian E = ∫ Y, Φ Y ∂gLaw F := by
  rw [gLaw_eq_map F β hβ, integral_map ((measurable_extQ F).comp
    (gramMap F β).continuous.measurable).aemeasurable hΦ.aestronglyMeasurable]
  congr 1
  funext x
  exact hloc _ _ (Yf_eq_extQ F β x)

theorem transfer_integrable (F : Finset Tri) (β : Tri → E)
    (hβ : ∀ q ∈ F, ∀ q' ∈ F, ⟪β q, β q'⟫ = kap q q') {Φ : (Tri → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hloc : IsLoc F Φ) :
    Integrable (fun x => Φ (Yf β x)) (stdGaussian E) ↔ Integrable Φ (gLaw F) := by
  rw [gLaw_eq_map F β hβ, integrable_map_measure hΦ.aestronglyMeasurable
    ((measurable_extQ F).comp (gramMap F β).continuous.measurable).aemeasurable]
  have : (fun x => Φ (Yf β x)) = Φ ∘ (extQ F ∘ gramMap F β) := by
    funext x
    exact hloc _ _ (Yf_eq_extQ F β x)
  rw [this]

/-! ## Independence of orthogonal groups -/

theorem cov_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; stdGaussian E] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply]

theorem indepFun_orth {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → E) (w : κ → E)
    (h : ∀ i j, ⟪v i, w j⟫ = 0) :
    IndepFun (fun x i => ⟪v i, x⟫) (fun x j => ⟪w j, x⟫) (stdGaussian E) := by
  set L : E →L[ℝ] (ι → ℝ) × (κ → ℝ) :=
    (ContinuousLinearMap.pi fun i => innerSL ℝ (v i)).prod
      (ContinuousLinearMap.pi fun j => innerSL ℝ (w j)) with hL
  have hG : HasGaussianLaw (fun x => (fun i => ⟪v i, x⟫, fun j => ⟪w j, x⟫)) (stdGaussian E) := by
    have := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun L
    exact this
  exact HasGaussianLaw.indepFun_of_covariance_eval (X := fun i x => ⟪v i, x⟫)
    (Y := fun j x => ⟪w j, x⟫) hG fun i j => by rw [cov_inner_stdGaussian, h]

/-- **Independence**: functionals of two orthogonal groups of Gram vectors. -/
theorem integral_mul_of_orth (β : Tri → E) (A B : Finset Tri)
    (horth : ∀ q ∈ A, ∀ q' ∈ B, ⟪β q, β q'⟫ = 0) {Φ Ψ : (Tri → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hΨ : Measurable Ψ) (hΦl : IsLoc A Φ) (hΨl : IsLoc B Ψ) :
    ∫ x, Φ (Yf β x) * Ψ (Yf β x) ∂stdGaussian E =
      (∫ x, Φ (Yf β x) ∂stdGaussian E) * ∫ x, Ψ (Yf β x) ∂stdGaussian E := by
  have hind := indepFun_orth (fun i : A => β i) (fun j : B => β j)
    (fun i j => horth i i.2 j j.2)
  have hA : ∀ x, Φ (Yf β x) = (Φ ∘ extF A) (fun i : A => ⟪β i, x⟫) := fun x =>
    hΦl _ _ fun q hq => by simp [Yf, extF, hq]
  have hB : ∀ x, Ψ (Yf β x) = (Ψ ∘ extF B) (fun j : B => ⟪β j, x⟫) := fun x =>
    hΨl _ _ fun q hq => by simp [Yf, extF, hq]
  simp_rw [hA, hB]
  have hmA : Measurable fun x : E => fun i : A => ⟪β i, x⟫ :=
    Measurable.of_eval fun i => (continuous_const.inner continuous_id).measurable
  have hmB : Measurable fun x : E => fun j : B => ⟪β j, x⟫ :=
    Measurable.of_eval fun j => (continuous_const.inner continuous_id).measurable
  exact hind.integral_fun_comp_mul_comp hmA.aemeasurable hmB.aemeasurable
    (hΦ.comp (measurable_extF A)).aestronglyMeasurable
    (hΨ.comp (measurable_extF B)).aestronglyMeasurable

/-! ## Integrability and exponential moments -/

theorem integrable_of_le_exp {F : E → ℝ} (hF : AEStronglyMeasurable F (stdGaussian E))
    (c t : ℝ) (v : E) (hb : ∀ x, |F x| ≤ c * Real.exp (t * ⟪v, x⟫)) :
    Integrable F (stdGaussian E) :=
  Integrable.mono' ((GaussianMax.integrable_exp_mul_inner v t).const_mul c) hF
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem integral_exp_inner (v : E) (t : ℝ) :
    ∫ x, Real.exp (t * ⟪v, x⟫) ∂stdGaussian E = Real.exp (‖v‖ ^ 2 * t ^ 2 / 2) :=
  GaussianMax.integral_exp_mul_inner v t

end LQGDimension.BlockCons
