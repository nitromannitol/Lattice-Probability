/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/KahaneStein.lean.
-/
import LatticeProb.Prob.GaussSteinIBP
import LatticeProb.Prob.GaussLipConcentration

/-!
# Gaussian integration by parts for functions of exponential growth

`LatticeProb.GaussConc.integral_inner_mul_stdGaussian` (in `GaussSteinIBP`) assumes that `G`
and its gradient `G'` are bounded. This file proves the same identity

  `E[⟪a, x⟫ G(x)] = E[⟪G'(x), a⟫]`   (`LatticeProb.Kahane.integral_inner_mul_stdGaussian_of_le`)

for a standard Gaussian vector `x` of a finite-dimensional inner product space, under the weaker
hypotheses `|G x|, ‖G' x‖ ≤ A e^{B ‖x‖}`. The proof is the bounded proof with the boundedness
hypotheses replaced by integrability: the one-dimensional integration by parts and its
coordinate versions are stated under integrability of `g`, `g'` and `x g(x)` against the
Gaussian law. The integrability of `e^{B ‖x‖}` comes from the Gaussian concentration bound
`LatticeProb.GaussConc.integrable_exp_of_lipschitz` applied to the `1`-Lipschitz norm.

The file also gives a nonvacuity example with `G x = e^{⟪v, x⟫}`, which grows exponentially and
so is outside the reach of the bounded version.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb

namespace Kahane

open GaussConc

/-! ### One-dimensional and coordinate Stein identities under integrability -/

/-- One-dimensional Stein identity under integrability hypotheses: for `x ∼ N(0,1)`, if `g` is
differentiable and `x ↦ x g(x)`, `g'` and `g` are integrable, then `E[x g(x)] = E[g'(x)]`. -/
theorem integral_mul_gaussianReal_std_of_integrable {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (h1 : Integrable (fun x => x * g x) (gaussianReal 0 1))
    (h2 : Integrable g' (gaussianReal 0 1)) (h3 : Integrable g (gaussianReal 0 1)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  rw [integrable_gaussianReal_std_iff] at h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g)
    (v := gaussianPDFReal 0 1) (u' := g') (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal_std x) ?_ ?_ ?_
  · simp only [smul_eq_mul]
    have e1 : (fun x => gaussianPDFReal 0 1 x * (x * g x)) =
        fun x => -(g x * (-x * gaussianPDFReal 0 1 x)) := by
      funext x; ring
    rw [e1, integral_neg, ibp, neg_neg]
    congr 1; funext x; ring
  · have e : (g * fun x => -x * gaussianPDFReal 0 1 x) =
        fun x => -(gaussianPDFReal 0 1 x * (x * g x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h1.neg
  · have e : (g' * gaussianPDFReal 0 1) = fun x => gaussianPDFReal 0 1 x * g' x := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h2
  · have e : (g * gaussianPDFReal 0 1) = fun x => gaussianPDFReal 0 1 x * g x := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h3

/-- Stein identity in one coordinate of a standard Gaussian vector of `ℝ^{n+1}`, under
integrability hypotheses. -/
theorem integral_coord_mul_pi_succ_of_integrable {n : ℕ} (k : Fin (n + 1))
    {h h' : (Fin (n + 1) → ℝ) → ℝ}
    (hh : ∀ c t, HasDerivAt (fun s : ℝ => h (c + s • Pi.single k 1))
      (h' (c + t • Pi.single k 1)) t)
    (hint1 : Integrable (fun c : Fin (n + 1) → ℝ => c k * h c)
      (Measure.pi fun _ => gaussianReal 0 1))
    (hint2 : Integrable h' (Measure.pi fun _ => gaussianReal 0 1))
    (hint3 : Integrable h (Measure.pi fun _ => gaussianReal 0 1)) :
    ∫ c, c k * h c ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, h' c ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  have hmp :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) k).symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k with he
  have hint1' : Integrable (fun x : ℝ × (Fin n → ℝ) => e.symm x k * h (e.symm x))
      ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)) :=
    hmp.integrable_comp_of_integrable hint1
  have hint2' : Integrable (fun x : ℝ × (Fin n → ℝ) => h' (e.symm x))
      ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)) :=
    hmp.integrable_comp_of_integrable hint2
  have hint3' : Integrable (fun x : ℝ × (Fin n → ℝ) => h (e.symm x))
      ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)) :=
    hmp.integrable_comp_of_integrable hint3
  rw [← hmp.integral_comp' (fun c => c k * h c), ← hmp.integral_comp' h',
    integral_prod_symm _ hint1', integral_prod_symm _ hint2']
  refine integral_congr_ae ?_
  filter_upwards [hint1'.prod_left_ae, hint2'.prod_left_ae, hint3'.prod_left_ae] with r h1 h2 h3
  simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same] at h1 h2 h3 ⊢
  refine integral_mul_gaussianReal_std_of_integrable (g := fun t => h (Fin.insertNth k t r))
    (g' := fun t => h' (Fin.insertNth k t r)) (fun t => ?_) h1 h2 h3
  have := hh (Fin.insertNth k 0 r) t
  simp only [← insertNth_eq_add_smul_single] at this
  exact this

/-- Stein identity in one coordinate of a standard Gaussian vector of `ℝᴺ`, under integrability
hypotheses. -/
theorem integral_coord_mul_pi_of_integrable {N : ℕ} (k : Fin N) {h h' : (Fin N → ℝ) → ℝ}
    (hh : ∀ c t, HasDerivAt (fun s : ℝ => h (c + s • Pi.single k 1))
      (h' (c + t • Pi.single k 1)) t)
    (hint1 : Integrable (fun c : Fin N → ℝ => c k * h c) (Measure.pi fun _ => gaussianReal 0 1))
    (hint2 : Integrable h' (Measure.pi fun _ => gaussianReal 0 1))
    (hint3 : Integrable h (Measure.pi fun _ => gaussianReal 0 1)) :
    ∫ c, c k * h c ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, h' c ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  cases N with
  | zero => exact k.elim0
  | succ n => exact integral_coord_mul_pi_succ_of_integrable k hh hint1 hint2 hint3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Exponential moments of the norm -/

/-- `x ↦ e^{B ‖x‖}` is integrable for the standard Gaussian. -/
lemma integrable_exp_mul_norm_stdGaussian (B : ℝ) :
    Integrable (fun x : E => Real.exp (B * ‖x‖)) (stdGaussian E) := by
  have h := GaussConc.integrable_exp_of_lipschitz (E := E) (F := fun x : E => ‖x‖)
    lipschitzWith_one_norm B
  set m := ∫ y, ‖y‖ ∂(stdGaussian E)
  have e : (fun x : E => Real.exp (B * ‖x‖)) =
      fun x => Real.exp (B * m) * Real.exp (B * (‖x‖ - m)) := by
    funext x; rw [← Real.exp_add]; ring_nf
  rw [e]
  exact h.const_mul _

/-- A function dominated by `A e^{B ‖x‖}` is integrable for the standard Gaussian. -/
lemma integrable_of_le_exp {f : E → ℝ} (hf : AEStronglyMeasurable f (stdGaussian E)) {A B : ℝ}
    (hle : ∀ x, |f x| ≤ A * Real.exp (B * ‖x‖)) : Integrable f (stdGaussian E) :=
  ((integrable_exp_mul_norm_stdGaussian B).const_mul A).mono' hf
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hle x)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `A ≥ 0`, the product `‖x‖ · A e^{B ‖x‖}` is dominated by `A e^{(B+1) ‖x‖}`. -/
lemma norm_mul_exp_le (A B : ℝ) (hA : 0 ≤ A) (x : E) :
    ‖x‖ * (A * Real.exp (B * ‖x‖)) ≤ A * Real.exp ((B + 1) * ‖x‖) := by
  have h1 : ‖x‖ ≤ Real.exp ‖x‖ := (le_add_of_nonneg_right zero_le_one).trans
    (Real.add_one_le_exp _)
  calc ‖x‖ * (A * Real.exp (B * ‖x‖)) ≤ Real.exp ‖x‖ * (A * Real.exp (B * ‖x‖)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hA (Real.exp_pos _).le)
    _ = A * Real.exp ((B + 1) * ‖x‖) := by
        rw [add_mul, one_mul, Real.exp_add]; ring

/-! ### Stein's lemma for functions of exponential growth -/

/-- **Stein's lemma for functions of exponential growth.** Let `x` be a standard Gaussian vector
of `E`, `a : E`, and `G : E → ℝ` continuous, with continuous gradient `G'` (given along lines),
and `|G x|, ‖G' x‖ ≤ A e^{B ‖x‖}`.  Then `E[⟪a, x⟫ G(x)] = E[⟪G'(x), a⟫]`. -/
theorem integral_inner_mul_stdGaussian_of_le {G : E → ℝ} {G' : E → E} {A B : ℝ}
    (hG : ∀ x e t, HasDerivAt (fun s : ℝ => G (x + s • e)) ⟪G' (x + t • e), e⟫ t)
    (hG_cont : Continuous G) (hG'_cont : Continuous G')
    (hG_le : ∀ x, |G x| ≤ A * Real.exp (B * ‖x‖))
    (hG'_le : ∀ x, ‖G' x‖ ≤ A * Real.exp (B * ‖x‖)) (a : E) :
    ∫ x, ⟪a, x⟫ * G x ∂(stdGaussian E) = ∫ x, ⟪G' x, a⟫ ∂(stdGaussian E) := by
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans (hG_le 0)
    simpa using this
  set B' := stdOrthonormalBasis ℝ E with hB
  have hT : Continuous (coordSum (N := Module.finrank ℝ E) B') := continuous_coordSum _
  have hPi : stdGaussian E =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map (coordSum B') := rfl
  -- integrability in `E`
  have iG : Integrable G (stdGaussian E) := integrable_of_le_exp hG_cont.aestronglyMeasurable hG_le
  have iG' : ∀ v : E, Integrable (fun x => ⟪G' x, v⟫) (stdGaussian E) := fun v =>
    integrable_of_le_exp (A := A * ‖v‖) (B := B)
      (hG'_cont.inner continuous_const).aestronglyMeasurable fun x => by
        refine (abs_real_inner_le_norm _ _).trans ?_
        calc ‖G' x‖ * ‖v‖ ≤ A * Real.exp (B * ‖x‖) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (hG'_le x) (norm_nonneg _)
          _ = _ := by ring
  have iaG : ∀ v : E, Integrable (fun x => ⟪v, x⟫ * G x) (stdGaussian E) := fun v =>
    integrable_of_le_exp (A := ‖v‖ * A) (B := B + 1)
      ((continuous_const.inner continuous_id).mul hG_cont).aestronglyMeasurable fun x => by
        rw [abs_mul]
        calc |⟪v, x⟫| * |G x| ≤ (‖v‖ * ‖x‖) * (A * Real.exp (B * ‖x‖)) :=
              mul_le_mul (abs_real_inner_le_norm _ _) (hG_le x) (abs_nonneg _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = ‖v‖ * (‖x‖ * (A * Real.exp (B * ‖x‖))) := by ring
          _ ≤ ‖v‖ * (A * Real.exp ((B + 1) * ‖x‖)) :=
              mul_le_mul_of_nonneg_left (norm_mul_exp_le A B hA x) (norm_nonneg _)
          _ = _ := by ring
  -- transfer to the coordinates
  have hmap : ∀ f : E → ℝ, Integrable f (stdGaussian E) →
      Integrable (fun c => f (coordSum B' c))
        (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) := by
    intro f hf
    rw [hPi] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable hT.aemeasurable).1 hf
  have hcoord : ∀ (c : Fin (Module.finrank ℝ E) → ℝ) k, ⟪B' k, coordSum B' c⟫ = c k := by
    intro c k
    exact B'.orthonormal.inner_right_fintype c k
  have hk : ∀ k, ∫ c, c k * G (coordSum B' c) ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, ⟪G' (coordSum B' c), B' k⟫ ∂(Measure.pi fun _ => gaussianReal 0 1) := by
    intro k
    refine integral_coord_mul_pi_of_integrable k (h := fun c => G (coordSum B' c))
      (h' := fun c => ⟪G' (coordSum B' c), B' k⟫) (fun c t => ?_) ?_ (hmap _ (iG' (B' k)))
      (hmap _ iG)
    · simp only [coordSum_add_smul_single]
      exact hG (coordSum B' c) (B' k) t
    · have := hmap _ (iaG (B' k))
      simpa only [hcoord] using this
  rw [hPi, integral_map (f := fun x : E => ⟪a, x⟫ * G x) hT.aemeasurable
      ((continuous_const.inner continuous_id).mul hG_cont).aestronglyMeasurable,
    integral_map (f := fun x : E => ⟪G' x, a⟫) hT.aemeasurable
      (hG'_cont.inner continuous_const).aestronglyMeasurable]
  have e1 : ∀ c, ⟪a, coordSum B' c⟫ * G (coordSum B' c) =
      ∑ k, ⟪a, B' k⟫ * (c k * G (coordSum B' c)) := by
    intro c
    simp only [coordSum, inner_sum, real_inner_smul_right, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ c, ⟪G' (coordSum B' c), a⟫ = ∑ k, ⟪a, B' k⟫ * ⟪G' (coordSum B' c), B' k⟫ := by
    intro c
    rw [← B'.sum_inner_mul_inner (G' (coordSum B' c)) a]
    exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm a (B' k)]; ring
  simp only [e1, e2]
  rw [integral_finsetSum _ fun k _ => ?_, integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul, hk k]
  · exact (hmap _ (iG' (B' k))).const_mul _
  · have := hmap _ (iaG (B' k))
    simp only [hcoord] at this
    exact this.const_mul _

/-! ### Nonvacuity examples -/

namespace SteinExample

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

/-- **Stein's identity for an exponential of a linear form** on `EuclideanSpace ℝ (Fin 2)`:
for `G x = e^{⟪v, x⟫}`, whose gradient is `G' x = e^{⟪v, x⟫} • v`, both `G` and `G'` satisfy
the growth bounds with `A = 1 + ‖v‖` and `B = ‖v‖`, so
`E[⟪a, X⟫ e^{⟪v, X⟫}] = E[e^{⟪v, X⟫} ⟪v, a⟫]`. -/
theorem integral_inner_mul_exp_inner (a v : EuclideanSpace ℝ (Fin 2)) :
    ∫ x, ⟪a, x⟫ * Real.exp ⟪v, x⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      ∫ x, ⟪Real.exp ⟪v, x⟫ • v, a⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  have hG : ∀ (x e : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
      HasDerivAt (fun s : ℝ => Real.exp ⟪v, x + s • e⟫)
        ⟪Real.exp ⟪v, x + t • e⟫ • v, e⟫ t := by
    intro x e t
    have hf : (fun s : ℝ => ⟪v, x + s • e⟫) = fun s => ⟪v, x⟫ + s * ⟪v, e⟫ := by
      funext s; simp [inner_add_right, real_inner_smul_right]
    have h1 : HasDerivAt (fun s : ℝ => ⟪v, x + s • e⟫) ⟪v, e⟫ t := by
      rw [hf]
      simpa using ((hasDerivAt_id t).mul_const ⟪v, e⟫).const_add ⟪v, x⟫
    convert h1.exp using 1
    rw [real_inner_smul_left]
  have hG_le : ∀ x : EuclideanSpace ℝ (Fin 2),
      |Real.exp ⟪v, x⟫| ≤ (1 + ‖v‖) * Real.exp (‖v‖ * ‖x‖) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.2 (real_inner_le_norm v x)).trans
      (le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith [norm_nonneg v]))
  have hG'_le : ∀ x : EuclideanSpace ℝ (Fin 2),
      ‖Real.exp ⟪v, x⟫ • v‖ ≤ (1 + ‖v‖) * Real.exp (‖v‖ * ‖x‖) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h := Real.exp_le_exp.2 (real_inner_le_norm v x)
    have h0 := Real.exp_nonneg (‖v‖ * ‖x‖)
    nlinarith [norm_nonneg v]
  exact integral_inner_mul_stdGaussian_of_le (G := fun x => Real.exp ⟪v, x⟫)
    (G' := fun x => Real.exp ⟪v, x⟫ • v) (A := 1 + ‖v‖) (B := ‖v‖) hG (by fun_prop)
    (by fun_prop) hG_le hG'_le a

end SteinExample

end Kahane

end LatticeProb
