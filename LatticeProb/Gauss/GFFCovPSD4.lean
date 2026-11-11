import Mathlib
import LatticeProb.Gauss.GFFCovPSD1
import LatticeProb.Gauss.GFFCovPSD3

/-!
# Gaussian positive semidefiniteness of the smeared logarithmic kernel

For `s > 0` put
`G_s(X, Y) = ∫∫ w_X(a) w_Y(b) exp(-s|p_X a - p_Y b|²)` over two smearing representations (`SmearRep`, `LatticeProb.Gauss.GFFCovPSD1`).
The Gaussian convolution identity `integral_gauss_mul` (`LatticeProb.Gauss.GFFCovPSD3`) writes the kernel as a convolution square, so that
`G_s(X, Y) = (4s/π) ∫_w u_X(w) u_Y(w) dw`, with the smoothed weight `u_X(w) = ∫_a w_X(a) exp(-2s|p_X a - w|²) dλ_X(a)`.
Hence, for every finite family and real weights `d_i`,
`∑_{i,j} d_i d_j G_s(X_i, X_j) = (4s/π) ∫_w (∑_i d_i u_i(w))² dw ≥ 0`.

Terminology: smearing representation (Duplantier-Sheffield 2011, Section 3.1); Gaussian heat kernel (Armitage-Gardiner,
Ch. 3, for the logarithmic kernel as a superposition of heat kernels).
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss.GFFCovPSD

namespace SmearRep

/-- The Gaussian-smoothed weight `u_X(w) = ∫_a w_X(a) exp(-2s|p_X a - w|²) dλ_X(a)`. -/
noncomputable def gaussW {o : GFFObservable} (X : SmearRep o) (s : ℝ) (w : ℂ) : ℝ :=
  ∫ a, X.w a * Real.exp (-(2 * s) * ‖X.p a - w‖ ^ 2) ∂X.lam

/-- The Gaussian Gram entry `G_s(X, Y) = ∫∫ w_X(a) w_Y(b) exp(-s|p_X a - p_Y b|²)`. -/
noncomputable def gaussG {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') (s : ℝ) : ℝ :=
  ∫ q, X.w q.1 * Y.w q.2 * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)) ∂(X.lam.prod Y.lam)

lemma measurable_gaussKer {o : GFFObservable} (X : SmearRep o) (s : ℝ) :
    Measurable (fun q : X.α × ℂ => X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - q.2‖ ^ 2)) :=
  (X.w_meas.comp measurable_fst).mul (Real.measurable_exp.comp
    (measurable_const.mul ((((X.p_meas.comp measurable_fst).sub measurable_snd).norm).pow_const 2)))

/-- The smeared Gaussian kernel is integrable on the product of the smearing measure and Lebesgue measure on `ℂ`. -/
lemma integrable_gaussKer {o : GFFObservable} (X : SmearRep o) {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : X.α × ℂ => X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - q.2‖ ^ 2))
      (X.lam.prod volume) := by
  rw [integrable_prod_iff (measurable_gaussKer X s).aestronglyMeasurable]
  refine ⟨ae_of_all _ fun a => (integrable_gauss (b := 2 * s) (by linarith) (X.p a)).const_mul (X.w a), ?_⟩
  have h1 : ∀ a : X.α, ∫ w : ℂ, ‖X.w a * Real.exp (-(2 * s) * ‖X.p a - w‖ ^ 2)‖
      = ‖X.w a‖ * (π / (2 * s)) := fun a => by
    calc ∫ w : ℂ, ‖X.w a * Real.exp (-(2 * s) * ‖X.p a - w‖ ^ 2)‖
        = ∫ w : ℂ, ‖X.w a‖ * Real.exp (-(2 * s) * ‖X.p a - w‖ ^ 2) :=
          integral_congr_ae (ae_of_all _ fun w => by
            dsimp only
            rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le])
      _ = ‖X.w a‖ * (π / (2 * s)) := by
          rw [integral_const_mul, integral_gauss (b := 2 * s) (by linarith) (X.p a)]
  exact Integrable.congr (X.w_int.norm.mul_const (π / (2 * s))) (ae_of_all _ fun a => (h1 a).symm)

/-- The smoothed weight `u_X` is integrable on `ℂ`. -/
lemma integrable_gaussW {o : GFFObservable} (X : SmearRep o) {s : ℝ} (hs : 0 < s) :
    Integrable (X.gaussW s) :=
  (integrable_gaussKer X hs).integral_prod_right

/-- The smoothed weight is bounded uniformly in `w`, since the Gaussian factor is at most one. -/
lemma norm_gaussW_le {o : GFFObservable} (X : SmearRep o) {s : ℝ} (hs : 0 ≤ s) (w : ℂ) :
    ‖X.gaussW s w‖ ≤ ∫ a, ‖X.w a‖ ∂X.lam := by
  refine norm_integral_le_of_norm_le X.w_int.norm (ae_of_all _ fun a => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
  have := sq_nonneg ‖X.p a - w‖
  nlinarith

/-- The product of two smoothed weights is integrable (bounded times integrable). -/
lemma integrable_gaussW_mul {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') {s : ℝ} (hs : 0 < s) :
    Integrable (fun w => X.gaussW s w * Y.gaussW s w) :=
  (Y.integrable_gaussW hs).bdd_mul (X.integrable_gaussW hs).aestronglyMeasurable
    (c := ∫ a, ‖X.w a‖ ∂X.lam) (ae_of_all _ fun w => X.norm_gaussW_le hs.le w)

/-- The integrability of the four-factor integrand `(w_X(a) e^{-2s|p_X a - w|²}) (w_Y(b) e^{-2s|p_Y b - w|²})`
on `(λ_X ⊗ λ_Y) ⊗ Leb(ℂ)`. -/
lemma integrable_gaussQuad {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : (X.α × Y.α) × ℂ =>
      (X.w p.1.1 * Real.exp (-(2 * s) * ‖X.p p.1.1 - p.2‖ ^ 2)) *
        (Y.w p.1.2 * Real.exp (-(2 * s) * ‖Y.p p.1.2 - p.2‖ ^ 2)))
      ((X.lam.prod Y.lam).prod volume) := by
  have mX : Measurable (fun p : (X.α × Y.α) × ℂ => X.w p.1.1) := X.w_meas.comp (measurable_fst.comp measurable_fst)
  have mY : Measurable (fun p : (X.α × Y.α) × ℂ => Y.w p.1.2) := Y.w_meas.comp (measurable_snd.comp measurable_fst)
  have eX : Measurable (fun p : (X.α × Y.α) × ℂ => Real.exp (-(2 * s) * ‖X.p p.1.1 - p.2‖ ^ 2)) :=
    Real.measurable_exp.comp (measurable_const.mul
      ((((X.p_meas.comp (measurable_fst.comp measurable_fst)).sub measurable_snd).norm).pow_const 2))
  have eY : Measurable (fun p : (X.α × Y.α) × ℂ => Real.exp (-(2 * s) * ‖Y.p p.1.2 - p.2‖ ^ 2)) :=
    Real.measurable_exp.comp (measurable_const.mul
      ((((Y.p_meas.comp (measurable_snd.comp measurable_fst)).sub measurable_snd).norm).pow_const 2))
  have hmeas : Measurable (fun p : (X.α × Y.α) × ℂ =>
      (X.w p.1.1 * Real.exp (-(2 * s) * ‖X.p p.1.1 - p.2‖ ^ 2)) *
        (Y.w p.1.2 * Real.exp (-(2 * s) * ‖Y.p p.1.2 - p.2‖ ^ 2))) :=
    (mX.mul eX).mul (mY.mul eY)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · -- for fixed `q`, the integrand in `w` is a constant times a product of two Gaussians
    refine ae_of_all _ fun q => ?_
    have hG : Integrable (fun w : ℂ => Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2) *
        Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)) := by
      refine Integrable.mono' (integrable_gauss (b := 2 * s) (by linarith) (X.p q.1)) ?_ ?_
      · have := Y.p_meas
        exact (by fun_prop : Measurable fun w : ℂ => Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2) *
          Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)).aestronglyMeasurable
      · refine ae_of_all _ fun w => ?_
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
        refine mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.mpr ?_)
        have := sq_nonneg ‖Y.p q.2 - w‖
        nlinarith
    exact Integrable.congr (hG.const_mul (X.w q.1 * Y.w q.2)) (ae_of_all _ fun w => by ring)
  · -- the absolute integral in `w` is `(π / 4s) |w_X||w_Y| e^{-s|p_X - p_Y|²}`
    have hval : ∀ q : X.α × Y.α, ∫ w : ℂ, ‖(X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
        (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2))‖
        = (π / (4 * s)) * (‖X.w q.1‖ * ‖Y.w q.2‖) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)) := by
      intro q
      calc ∫ w : ℂ, ‖(X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
            (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2))‖
          = ∫ w : ℂ, (‖X.w q.1‖ * ‖Y.w q.2‖) * (Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2) *
              Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)) :=
            integral_congr_ae (ae_of_all _ fun w => by
              dsimp only
              rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
                Real.norm_of_nonneg (Real.exp_pos _).le]
              ring)
        _ = (‖X.w q.1‖ * ‖Y.w q.2‖) * (π / (4 * s) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))) := by
            rw [integral_const_mul, integral_gauss_mul hs]
        _ = π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)) := by ring
    have hbd : Integrable (fun q : X.α × Y.α => (π / (4 * s)) * (‖X.w q.1‖ * ‖Y.w q.2‖)) (X.lam.prod Y.lam) :=
      ((X.w_int.norm).mul_prod (Y.w_int.norm)).const_mul _
    have hc : 0 ≤ π / (4 * s) := div_nonneg Real.pi_pos.le (by linarith)
    have hfmeas : Measurable (fun q : X.α × Y.α =>
        π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))) := by
      have := X.w_meas
      have := Y.w_meas
      have := X.p_meas
      have := Y.p_meas
      fun_prop
    have hfin : Integrable (fun q : X.α × Y.α =>
        π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)))
        (X.lam.prod Y.lam) := by
      refine Integrable.mono' hbd hfmeas.aestronglyMeasurable (ae_of_all _ fun q => ?_)
      have h0 : 0 ≤ ‖X.w q.1‖ * ‖Y.w q.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h1 : Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := sq_nonneg ‖X.p q.1 - Y.p q.2‖; nlinarith)
      have hpi : 0 ≤ π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) := mul_nonneg hc h0
      rw [Real.norm_of_nonneg (mul_nonneg hpi (Real.exp_pos _).le)]
      calc π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))
          ≤ π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) * 1 := mul_le_mul_of_nonneg_left h1 hpi
        _ = π / (4 * s) * (‖X.w q.1‖ * ‖Y.w q.2‖) := mul_one _
    exact Integrable.congr hfin (ae_of_all _ fun q => (hval q).symm)

/-- The Gaussian convolution identity for two smearing representations:
`∫_w u_X(w) u_Y(w) dw = (π / 4s) G_s(X, Y)`. -/
lemma integral_gaussW_mul_eq {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') {s : ℝ} (hs : 0 < s) :
    ∫ w, X.gaussW s w * Y.gaussW s w = π / (4 * s) * X.gaussG Y s := by
  have hpt : ∀ w : ℂ, X.gaussW s w * Y.gaussW s w = ∫ q : X.α × Y.α,
      (X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
        (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)) ∂(X.lam.prod Y.lam) := fun w =>
    (integral_prod_mul (μ := X.lam) (ν := Y.lam)
      (fun a => X.w a * Real.exp (-(2 * s) * ‖X.p a - w‖ ^ 2))
      (fun b => Y.w b * Real.exp (-(2 * s) * ‖Y.p b - w‖ ^ 2))).symm
  calc ∫ w, X.gaussW s w * Y.gaussW s w
      = ∫ w, ∫ q : X.α × Y.α, (X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
          (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)) ∂(X.lam.prod Y.lam) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ q : X.α × Y.α, (∫ w : ℂ, (X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
          (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2))) ∂(X.lam.prod Y.lam) :=
        integral_integral_swap (f := fun (w : ℂ) (q : X.α × Y.α) =>
          (X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) * (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)))
          (integrable_gaussQuad X Y hs).swap
    _ = ∫ q : X.α × Y.α, π / (4 * s) * (X.w q.1 * Y.w q.2 * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))) ∂(X.lam.prod Y.lam) :=
        integral_congr_ae (ae_of_all _ fun q => by
          calc ∫ w : ℂ, (X.w q.1 * Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2)) *
                (Y.w q.2 * Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2))
              = ∫ w : ℂ, (X.w q.1 * Y.w q.2) * (Real.exp (-(2 * s) * ‖X.p q.1 - w‖ ^ 2) *
                  Real.exp (-(2 * s) * ‖Y.p q.2 - w‖ ^ 2)) :=
                integral_congr_ae (ae_of_all _ fun w => by ring)
            _ = (X.w q.1 * Y.w q.2) * (π / (4 * s) * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))) := by
                rw [integral_const_mul, integral_gauss_mul hs]
            _ = π / (4 * s) * (X.w q.1 * Y.w q.2 * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2))) := by ring)
    _ = π / (4 * s) * X.gaussG Y s := by
        unfold gaussG
        rw [integral_const_mul]

/-- Positive semidefiniteness of the Gaussian Gram matrix: for `s > 0` and any finite family of smearing
representations `X i` of admissible observables and real weights `d i`,
`0 ≤ ∑_i ∑_j d_i d_j G_s(X_i, X_j)`. -/
lemma gaussG_gram_nonneg {ι : Type} [Fintype ι] {ob : ι → GFFObservable} (X : ∀ i, SmearRep (ob i))
    {s : ℝ} (hs : 0 < s) (d : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, d i * d j * (X i).gaussG (X j) s := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hG : ∀ i j, (X i).gaussG (X j) s = 4 * s / π * ∫ w, (X i).gaussW s w * (X j).gaussW s w := by
    intro i j
    rw [integral_gaussW_mul_eq (X i) (X j) hs]
    field_simp
  have hexp : ∀ w : ℂ, (∑ i, d i * (X i).gaussW s w) ^ 2
      = ∑ i, ∑ j, d i * d j * ((X i).gaussW s w * (X j).gaussW s w) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint : ∫ w, (∑ i, d i * (X i).gaussW s w) ^ 2
      = ∑ i, ∑ j, d i * d j * ∫ w, (X i).gaussW s w * (X j).gaussW s w := by
    rw [integral_congr_ae (ae_of_all _ hexp)]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      ((integrable_gaussW_mul (X i) (X j) hs).const_mul (d i * d j))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => ((integrable_gaussW_mul (X i) (X j) hs).const_mul (d i * d j)))]
    refine Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have h4 : 0 ≤ 4 * s / π := div_nonneg (by linarith) Real.pi_pos.le
  have hsum : ∑ i, ∑ j, d i * d j * (X i).gaussG (X j) s
      = 4 * s / π * ∫ w, (∑ i, d i * (X i).gaussW s w) ^ 2 := by
    rw [hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG i j]
    ring
  rw [hsum]
  exact mul_nonneg h4 (integral_nonneg fun w => sq_nonneg _)

end SmearRep

end LatticeProb.Gauss.GFFCovPSD
