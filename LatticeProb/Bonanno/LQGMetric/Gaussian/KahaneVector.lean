/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.KahaneVector at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.KahaneInterp
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector

/-!
# Kahane's convexity inequality for Gaussian vectors

`LQGMetric.Kahane.kahane_convexity`: let `X`, `Y` be centred Gaussian vectors indexed by a finite
set `ι` (on possibly different probability spaces) with `Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ)` for all
`i, j`, let `pᵢ > 0`, and let `F` be convex with polynomial growth (`KahaneFun`).  Then

  `E F(∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ / 2}) ≤ E F(∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ / 2})`.

This is J.-P. Kahane, *Sur le chaos multiplicatif*, Ann. Sci. Math. Québec 9 (1985), for a
measure `σ = ∑ pᵢ δ_{xᵢ}` with finite support; Rhodes–Vargas arXiv:1305.6221, Theorem 2.1 (stated
there for general `σ`, proved by the finite-dimensional interpolation); Berestycki–Powell
arXiv:2404.16642, Theorem 3.18.

Proof: both vectors are realised on one standard Gaussian space `H = ℝ^{ι ⊕ ι}` with orthogonal
Gram vectors `u i = (v i, 0)`, `u' i = (0, v' i)` (Gram representation
`LQGMetric.Pitt.exists_gram_map_eq` and its law identification, generalised here to any `H`),
and the Gram form `LQGMetric.Kahane.integral_kW_zero_le` applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace Kahane

open Pitt

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Law identification for a Gram representation in any space** (the second half of the proof
of `LQGMetric.Pitt.exists_gram_map_eq`, for an arbitrary finite-dimensional `H`). -/
theorem map_eq_gram_of_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) (v : ι → H)
    (hvv : ∀ i j, ⟪v i, v j⟫ = cov[fun ω => X ω i, fun ω => X ω j; P]) :
    P.map X = (stdGaussian H).map (fun x => (fun i => ∫ ω, X ω i ∂P) + gramCLM v x) := by
  classical
  have := hX.isProbabilityMeasure
  set γ := stdGaussian H
  set m : ι → ℝ := fun i => ∫ ω, X ω i ∂P with hm
  set Y : H → ι → ℝ := fun x => m + gramCLM v x with hY
  have hYmap : γ.map Y = (γ.map (gramCLM v)).map (fun y => m + y) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  have : IsGaussian (γ.map Y) := by rw [hYmap]; infer_instance
  have hYG : HasGaussianLaw Y γ := IsGaussian.hasGaussianLaw (by fun_prop)
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [hX.charFunDual_map_eq_fun, hYG.charFunDual_map_eq_fun]
  have hint : ∀ i, Integrable (fun ω => X ω i) P := fun i =>
    (memLp_coord hX i).integrable one_le_two
  have hLX : (fun ω => L (X ω)) = fun ω => ∑ i, L (unitVec i) * X ω i := by
    funext ω; rw [dual_apply_eq_sum L]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hLY : (fun x => L (Y x)) = fun x => L m + (innerSL ℝ (∑ i, L (unitVec i) • v i)) x := by
    funext x; rw [hY, map_add, ← dual_comp_gramCLM L v, ContinuousLinearMap.comp_apply]
  have hmean : ∫ ω, L (X ω) ∂P = ∫ x, L (Y x) ∂γ := by
    have h1 : ∫ ω, L (X ω) ∂P = ∑ i, L (unitVec i) * m i := by
      rw [hLX, integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp only [integral_const_mul, hm]
    have h2 : ∫ x, L (Y x) ∂γ = L m := by
      have hi : Integrable (fun x : H => (innerSL ℝ (∑ i, L (unitVec i) • v i)) x) γ :=
        (innerSL ℝ (∑ i, L (unitVec i) • v i)).integrable_comp IsGaussian.integrable_id
      rw [hLY, integral_add (integrable_const _) hi, integral_strongDual_stdGaussian]
      simp
    rw [h1, h2, dual_apply_eq_sum L m]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hvar : Var[fun ω => L (X ω); P] = Var[fun x => L (Y x); γ] := by
    rw [hLX, hLY, variance_sum_coord hX,
      variance_const_add (innerSL ℝ _).continuous.aestronglyMeasurable,
      variance_dual_stdGaussian, innerSL_apply_norm, ← real_inner_self_eq_norm_sq,
      inner_sum_smul_sum_smul]
    simp only [hvv]
  rw [hmean, hvar]

/-- The left block embedding `ℝ^ι → ℝ^{ι ⊕ ι}`. -/
def embL (a : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun k => a k) 0)

/-- The right block embedding `ℝ^ι → ℝ^{ι ⊕ ι}`. -/
def embR (a : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim 0 (fun k => a k))

lemma inner_embL_embL (a b : EuclideanSpace ℝ ι) : ⟪embL a, embL b⟫ = ⟪a, b⟫ := by
  simp [embL, PiLp.inner_apply, Fintype.sum_sum_type]

lemma inner_embR_embR (a b : EuclideanSpace ℝ ι) : ⟪embR a, embR b⟫ = ⟪a, b⟫ := by
  simp [embR, PiLp.inner_apply, Fintype.sum_sum_type]

lemma inner_embL_embR (a b : EuclideanSpace ℝ ι) : ⟪embL a, embR b⟫ = 0 := by
  simp [embL, embR, PiLp.inner_apply, Fintype.sum_sum_type]

variable {F F' F'' : ℝ → ℝ} {C : ℝ} {k : ℕ}

/-- The expectation of `F(∑ pᵢ e^{Xᵢ - Var Xᵢ/2})` through a Gram representation. -/
lemma integral_F_eq_kW [Nonempty ι] (hFK : KahaneFun F F' F'' C k) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) {u u' : ι → EuclideanSpace ℝ (ι ⊕ ι)} {θ : ℝ}
    (v : ι → EuclideanSpace ℝ (ι ⊕ ι))
    (hvU : ∀ i, v i = kU u u' θ i)
    (hvv : ∀ i j, ⟪v i, v j⟫ = cov[fun ω => X ω i, fun ω => X ω j; P]) :
    ∫ ω, F (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ∂P =
      ∫ x, F (kW p u u' θ x) ∂(stdGaussian (EuclideanSpace ℝ (ι ⊕ ι))) := by
  have := hX.isProbabilityMeasure
  set f : (ι → ℝ) → ℝ := fun y => F (∑ i, p i * Real.exp (y i - Var[fun ω => X ω i; P] / 2))
  have hfc : Continuous f := by
    refine hFK.continuousOn.comp_continuous (by fun_prop) fun y => ?_
    exact Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty
  have hmap := map_eq_gram_of_inner hX v hvv
  have hm0 : (fun i => ∫ ω, X ω i ∂P) = 0 := funext hXm
  rw [hm0] at hmap
  calc ∫ ω, F (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ∂P
      = ∫ y, f y ∂(P.map X) := (integral_map hX.aemeasurable hfc.aestronglyMeasurable).symm
    _ = ∫ x, f (0 + gramCLM v x) ∂(stdGaussian (EuclideanSpace ℝ (ι ⊕ ι))) := by
        rw [hmap, integral_map (by fun_prop) hfc.aestronglyMeasurable]
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [f, zero_add, gramCLM_apply, kW, kw]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hvU i, hvv i i, covariance_self
          (hX.aemeasurable.eval i : AEMeasurable (fun ω => X ω i) P)]

/-- **Kahane's convexity inequality** for centred Gaussian vectors (finite-dimensional case of
Kahane 1985; Rhodes–Vargas arXiv:1305.6221, Theorem 2.1; Berestycki–Powell arXiv:2404.16642,
Theorem 3.18). -/
theorem kahane_convexity [Nonempty ι] (hFK : KahaneFun F F' F'' C k) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      cov[fun ω => Y ω i, fun ω => Y ω j; P']) :
    ∫ ω, F (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ∂P ≤
      ∫ ω, F (∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)) ∂P' := by
  obtain ⟨v, hv, -⟩ := exists_gram_map_eq hX
  obtain ⟨v', hv', -⟩ := exists_gram_map_eq hY
  set u : ι → EuclideanSpace ℝ (ι ⊕ ι) := fun i => embL (v i)
  set u' : ι → EuclideanSpace ℝ (ι ⊕ ι) := fun i => embR (v' i)
  have huu : ∀ i j, ⟪u i, u j⟫ = cov[fun ω => X ω i, fun ω => X ω j; P] := fun i j => by
    simp only [u, inner_embL_embL, hv]
  have huu' : ∀ i j, ⟪u' i, u' j⟫ = cov[fun ω => Y ω i, fun ω => Y ω j; P'] := fun i j => by
    simp only [u', inner_embR_embR, hv']
  rw [integral_F_eq_kW hFK hp hX hXm (u := u) (u' := u') (θ := 0) u
      (fun i => (kU_zero u u' i).symm) huu,
    integral_F_eq_kW hFK hp hY hYm (u := u) (u' := u') (θ := π / 2) u'
      (fun i => (kU_pi_div_two u u' i).symm) huu']
  refine integral_kW_zero_le hFK hp (fun i j => inner_embL_embR _ _) fun i j => ?_
  rw [huu, huu']
  exact hcov i j

end Kahane

end LQGMetric
