import Mathlib
import LatticeProb.Gauss.GFFCovPSD4

/-!
# Frullani representation of the logarithmic energy, and conditional negativity

For two smearing representations
`X`, `Y` put `Λ(X, Y) = ∫∫ w_X(a) w_Y(b) log|p_X a - p_Y b|` and `B_X = ∫ w_X`. The Frullani integral
`∫_{s>0} s⁻¹ (e^{-A s} - e^{-s}) ds = -log A` (`LatticeProb.Gauss.GFFCovPSD3`), with `A = |p_X a - p_Y b|²`, gives

  `Λ(X, Y) = -(1/2) ∫_{s>0} s⁻¹ (G_s(X, Y) - e^{-s} B_X B_Y) ds`,

and the Fubini exchange is justified by the absolute Frullani integral and the logarithmic integrability
`integrable_log_mul` (`LatticeProb.Gauss.GFFCovPSD1`). Summing against weights `d_i` with `∑ d_i B_i = 0`, the terms `e^{-s} B_i B_j` cancel and
the Gaussian positivity of `LatticeProb.Gauss.GFFCovPSD4` gives `∑_{i,j} d_i d_j Λ(X_i, X_j) ≤ 0` (conditional negativity of the logarithm on
measures of total mass zero; Armitage-Gardiner, Ch. 3, and Saff-Totik, Ch. I, for the logarithmic energy).
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss.GFFCovPSD

namespace SmearRep

/-- The total smearing mass `B_X = ∫ w_X dλ_X`. -/
noncomputable def mass {o : GFFObservable} (X : SmearRep o) : ℝ := ∫ a, X.w a ∂X.lam

/-- The Frullani integrand on `(λ_X ⊗ λ_Y) ⊗ Leb_{(0,∞)}`:
`(q, s) ↦ w_X(q₁) w_Y(q₂) s⁻¹ (e^{-A s} - e^{-s})`, with `A = |p_X q₁ - p_Y q₂|²`. -/
lemma integrable_frullani {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') :
    Integrable (fun p : (X.α × Y.α) × ℝ => X.w p.1.1 * Y.w p.1.2 *
        (p.2⁻¹ • (Real.exp (-(‖X.p p.1.1 - Y.p p.1.2‖ ^ 2 * p.2)) - Real.exp (-(1 * p.2)))))
      ((X.lam.prod Y.lam).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have mX : Measurable (fun p : (X.α × Y.α) × ℝ => X.w p.1.1) :=
    X.w_meas.comp (measurable_fst.comp measurable_fst)
  have mY : Measurable (fun p : (X.α × Y.α) × ℝ => Y.w p.1.2) :=
    Y.w_meas.comp (measurable_snd.comp measurable_fst)
  have hmeas : Measurable (fun p : (X.α × Y.α) × ℝ => X.w p.1.1 * Y.w p.1.2 *
        (p.2⁻¹ • (Real.exp (-(‖X.p p.1.1 - Y.p p.1.2‖ ^ 2 * p.2)) - Real.exp (-(1 * p.2))))) := by
    have := X.p_meas
    have := Y.p_meas
    fun_prop
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [X.ae_ne Y] with q hq
    have hA : 0 < ‖X.p q.1 - Y.p q.2‖ ^ 2 := by
      have : X.p q.1 - Y.p q.2 ≠ 0 := sub_ne_zero.mpr hq
      positivity
    exact (frullani_integrableOn hA).const_mul (X.w q.1 * Y.w q.2)
  · have hae : ∀ᵐ q ∂(X.lam.prod Y.lam),
        ∫ s in Ioi (0 : ℝ), ‖X.w q.1 * Y.w q.2 *
          (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s))))‖
        = 2 * |X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖| := by
      filter_upwards [X.ae_ne Y] with q hq
      have hA : 0 < ‖X.p q.1 - Y.p q.2‖ ^ 2 := by
        have : X.p q.1 - Y.p q.2 ≠ 0 := sub_ne_zero.mpr hq
        positivity
      calc ∫ s in Ioi (0 : ℝ), ‖X.w q.1 * Y.w q.2 *
            (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s))))‖
          = ∫ s in Ioi (0 : ℝ), ‖X.w q.1 * Y.w q.2‖ *
            ‖s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s)))‖ :=
            integral_congr_ae (ae_of_all _ fun s => norm_mul _ _)
        _ = ‖X.w q.1 * Y.w q.2‖ * ∫ s in Ioi (0 : ℝ),
            ‖s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s)))‖ :=
            integral_const_mul _ _
        _ = |X.w q.1 * Y.w q.2| * |Real.log (‖X.p q.1 - Y.p q.2‖ ^ 2)| := by
            rw [Real.norm_eq_abs, frullani_norm hA]
        _ = 2 * |X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖| := by
            rw [Real.log_pow, abs_mul, abs_mul]
            norm_num
            ring
    exact Integrable.congr ((integrable_log_mul X Y).abs.const_mul 2) (hae.mono fun q hq => hq.symm)

/-- The integrand `w_X(q₁) w_Y(q₂) e^{-s|p_X q₁ - p_Y q₂|²}` is integrable on the product, for `s ≥ 0`. -/
lemma integrable_wwE {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun q : X.α × Y.α => X.w q.1 * Y.w q.2 * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)))
      (X.lam.prod Y.lam) := by
  have mX : Measurable (fun q : X.α × Y.α => X.w q.1) := X.w_meas.comp measurable_fst
  have mY : Measurable (fun q : X.α × Y.α => Y.w q.2) := Y.w_meas.comp measurable_snd
  have := X.p_meas
  have := Y.p_meas
  refine Integrable.mono' ((X.w_int.norm).mul_prod (Y.w_int.norm)) ?_ (ae_of_all _ fun q => ?_)
  · fun_prop
  · rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_le_one_iff.mpr ?_)
    have := sq_nonneg ‖X.p q.1 - Y.p q.2‖
    nlinarith

/-- The `s`-marginal of the Frullani integrand is integrable on `(0, ∞)`. -/
lemma frullani_inner_eq {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') {s : ℝ} (hs : 0 < s) :
    ∫ q, X.w q.1 * Y.w q.2 * (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s))))
      ∂(X.lam.prod Y.lam)
      = s⁻¹ * (X.gaussG Y s - Real.exp (-s) * (X.mass * Y.mass)) := by
  have hE : ∀ q : X.α × Y.α, Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s))
      = Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)) := fun q => by rw [mul_comm]
  have hpt : ∀ q : X.α × Y.α,
      X.w q.1 * Y.w q.2 * (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s))))
      = s⁻¹ * (X.w q.1 * Y.w q.2 * Real.exp (-(s * ‖X.p q.1 - Y.p q.2‖ ^ 2)))
        - (s⁻¹ * Real.exp (-s)) * (X.w q.1 * Y.w q.2) := by
    intro q
    rw [hE q, smul_eq_mul, one_mul]
    ring
  have hI1 := (integrable_wwE X Y hs.le).const_mul s⁻¹
  have hI2 := (X.w_int.mul_prod Y.w_int).const_mul (s⁻¹ * Real.exp (-s))
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hI1 hI2, integral_const_mul, integral_const_mul,
    integral_prod_mul X.w Y.w]
  unfold gaussG mass
  ring

/-- The Frullani representation of the logarithmic energy of two smearing representations:
`∫_q w_X w_Y log‖p_X - p_Y‖ = -(1/2) ∫_{s>0} s⁻¹ (G_s(X, Y) - e^{-s} B_X B_Y) ds`. -/
lemma log_eq_frullani {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') :
    ∫ q, X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖ ∂(X.lam.prod Y.lam)
      = -(1 / 2) * ∫ s in Ioi (0 : ℝ), s⁻¹ * (X.gaussG Y s - Real.exp (-s) * (X.mass * Y.mass)) := by
  have h1 : ∀ᵐ q ∂(X.lam.prod Y.lam), X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖
      = -(1 / 2) * ∫ s in Ioi (0 : ℝ), X.w q.1 * Y.w q.2 *
          (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s)))) := by
    filter_upwards [X.ae_ne Y] with q hq
    have hA : 0 < ‖X.p q.1 - Y.p q.2‖ ^ 2 := by
      have : X.p q.1 - Y.p q.2 ≠ 0 := sub_ne_zero.mpr hq
      positivity
    rw [integral_const_mul, frullani_exp hA, Real.log_pow]
    push_cast
    ring
  rw [integral_congr_ae h1, integral_const_mul,
    integral_integral_swap (f := fun (q : X.α × Y.α) (s : ℝ) => X.w q.1 * Y.w q.2 *
      (s⁻¹ • (Real.exp (-(‖X.p q.1 - Y.p q.2‖ ^ 2 * s)) - Real.exp (-(1 * s)))))
      (integrable_frullani X Y)]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs => frullani_inner_eq X Y hs

end SmearRep

/-- Conditional negativity of the logarithmic energy on measures of total mass zero (Armitage-Gardiner, Ch. 3;
Saff-Totik, Ch. I): for smearing representations `X i` of admissible observables and weights `d i` with
`∑ d_i B_i = 0`, `∑_{i,j} d_i d_j Λ(X_i, X_j) ≤ 0`, where `Λ(X, Y) = ∫∫ w_X w_Y log|p_X - p_Y|`. -/
theorem sum_log_nonpos {ι : Type} [Fintype ι] {ob : ι → GFFObservable} (X : ∀ i, SmearRep (ob i))
    (d : ι → ℝ) (hd : ∑ i, d i * (X i).mass = 0) :
    ∑ i, ∑ j, d i * d j * (∫ q, (X i).w q.1 * (X j).w q.2 * Real.log ‖(X i).p q.1 - (X j).p q.2‖
      ∂((X i).lam.prod (X j).lam)) ≤ 0 := by
  have e1 : ∀ i j, d i * d j * (∫ q, (X i).w q.1 * (X j).w q.2 * Real.log ‖(X i).p q.1 - (X j).p q.2‖
      ∂((X i).lam.prod (X j).lam))
      = -(1 / 2) * ∫ s in Ioi (0 : ℝ), d i * d j *
          (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))) := by
    intro i j
    rw [SmearRep.log_eq_frullani (X i) (X j), integral_const_mul]
    ring
  have hint : ∀ i j, Integrable (fun s : ℝ => d i * d j *
      (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro i j
    refine ((SmearRep.integrable_frullani (X i) (X j)).integral_prod_right.const_mul (d i * d j)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [SmearRep.frullani_inner_eq (X i) (X j) hs]
  have hΨ : ∀ s : ℝ, 0 < s → 0 ≤ ∑ i, ∑ j, d i * d j *
      (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))) := by
    intro s hs
    have hBB : ∑ i, ∑ j, d i * d j * ((X i).mass * (X j).mass) = 0 := by
      have h : ∑ i, ∑ j, d i * d j * ((X i).mass * (X j).mass) = (∑ i, d i * (X i).mass) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h, hd]
      ring
    have hG := SmearRep.gaussG_gram_nonneg X hs d
    have hsplit : ∑ i, ∑ j, d i * d j *
        (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass)))
        = s⁻¹ * ∑ i, ∑ j, d i * d j * (X i).gaussG (X j) s := by
      have hterm : ∀ i j, d i * d j *
          (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass)))
          = s⁻¹ * (d i * d j * (X i).gaussG (X j) s)
            - (s⁻¹ * Real.exp (-s)) * (d i * d j * ((X i).mass * (X j).mass)) := fun i j => by ring
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hBB, mul_zero, sub_zero]
    rw [hsplit]
    exact mul_nonneg (inv_nonneg.mpr hs.le) hG
  have hnn : 0 ≤ ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j, d i * d j *
      (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))) :=
    setIntegral_nonneg measurableSet_Ioi fun s hs => hΨ s hs
  have hswap : ∑ i, ∑ j, (∫ s in Ioi (0 : ℝ), d i * d j *
      (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))))
      = ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j, d i * d j *
        (s⁻¹ * ((X i).gaussG (X j) s - Real.exp (-s) * ((X i).mass * (X j).mass))) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
  simp only [← Finset.mul_sum]
  rw [hswap]
  linarith

end LatticeProb.Gauss.GFFCovPSD
