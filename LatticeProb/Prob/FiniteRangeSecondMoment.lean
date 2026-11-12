import Mathlib.MeasureTheory.Integral.Prod

/-!
# Second moment of a random integral with finite-range correlations

Let `T : Ω → E → ℝ` be a jointly measurable random field over a σ-finite measure space `(E, ν)`, with
`E[T_z²] ≤ B` and `E[T_z T_w] = 0` for every pair `(z, w)` outside a measurable set `S ⊆ E × E` (finite-range
correlations). Then for every integrable weight `g`,
`E[(∫ g T dν)²] ≤ B ∫∫_S |g(z)| |g(w)| dν(z) dν(w)`
(`integral_sq_integral_le`), and `(∫ g T dν)²` is integrable (`integrable_sq_integral`). Only the values of `T_z`
at points where `g z ≠ 0` enter the hypotheses. With `E|Y| ≤ (E Y² / t + t) / 2`
(`integral_abs_le_of_integrable_sq`) this gives the L¹ bound used in the second-moment method.

This is the second-moment step of the truncated second-moment method for Gaussian multiplicative chaos
(Duplantier-Sheffield 2011, Section 3; Berestycki-Powell, Gaussian free field and Liouville quantum gravity,
Chapter 3), where `S` is the set of pairs at distance less than twice the regularization scale.
-/

open MeasureTheory Function

namespace LatticeProb.FiniteRange

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω} {ν : Measure E}

/-- `E|XY| ≤ (E X² + E Y²) / 2`. -/
theorem integral_abs_mul_le {X Y : Ω → ℝ} (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) :
    ∫ ω, |X ω * Y ω| ∂P ≤ (∫ ω, X ω ^ 2 ∂P + ∫ ω, Y ω ^ 2 ∂P) / 2 := by
  rw [← integral_add hX2 hY2, ← integral_div]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
    ((hX2.add hY2).div_const 2 : Integrable (fun ω => (X ω ^ 2 + Y ω ^ 2) / 2) P)
    (ae_of_all _ fun ω => ?_)
  show |X ω * Y ω| ≤ (X ω ^ 2 + Y ω ^ 2) / 2
  rw [abs_mul]
  nlinarith [sq_nonneg (|X ω| - |Y ω|), sq_abs (X ω), sq_abs (Y ω)]

/-- A product of two square-integrable random variables is integrable. -/
theorem integrable_mul_of_integrable_sq {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X P)
    (hY : AEStronglyMeasurable Y P) (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) : Integrable (fun ω => X ω * Y ω) P := by
  refine ((hX2.add hY2).div_const 2 : Integrable (fun ω => (X ω ^ 2 + Y ω ^ 2) / 2) P).mono'
    (hX.mul hY) (ae_of_all _ fun ω => ?_)
  show ‖X ω * Y ω‖ ≤ (X ω ^ 2 + Y ω ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|X ω| - |Y ω|), sq_abs (X ω), sq_abs (Y ω)]

/-- The integrand `(ω, (z, w)) ↦ g(z) T_z(ω) g(w) T_w(ω)` of the second moment is integrable on `P ⊗ (ν ⊗ ν)`. -/
theorem integrable_mul_prod_of_sq [SFinite P] [SFinite ν] {T : Ω → E → ℝ}
    (hT : Measurable fun q : Ω × E => T q.1 q.2) {g : E → ℝ} (hgm : Measurable g) (hg : Integrable g ν) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B) :
    Integrable (uncurry fun (ω : Ω) (p : E × E) => g p.1 * T ω p.1 * (g p.2 * T ω p.2)) (P.prod (ν.prod ν)) := by
  set F : Ω → E × E → ℝ := fun ω p => g p.1 * T ω p.1 * (g p.2 * T ω p.2) with hFdef
  have hTz : ∀ z, Measurable fun ω => T ω z := fun z => hT.comp (measurable_id.prodMk measurable_const)
  have hFm : Measurable (uncurry F) := by
    show Measurable fun q : Ω × (E × E) => g q.2.1 * T q.1 q.2.1 * (g q.2.2 * T q.1 q.2.2)
    have h1 : Measurable fun q : Ω × (E × E) => T q.1 q.2.1 :=
      hT.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable fun q : Ω × (E × E) => T q.1 q.2.2 :=
      hT.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact ((hgm.comp (measurable_fst.comp measurable_snd)).mul h1).mul
      ((hgm.comp (measurable_snd.comp measurable_snd)).mul h2)
  have hE : ∀ z w, g z ≠ 0 → g w ≠ 0 → ∫ ω, |T ω z * T ω w| ∂P ≤ B := fun z w hz hw =>
    (integral_abs_mul_le (hsq z hz) (hsq w hw)).trans (by linarith [hB z hz, hB w hw])
  have hint : ∀ p : E × E, Integrable (fun ω => F ω p) P := by
    intro p
    by_cases h1 : g p.1 = 0
    · simp [hFdef, h1]
    by_cases h2 : g p.2 = 0
    · simp [hFdef, h2]
    refine ((integrable_mul_of_integrable_sq (hTz p.1).aestronglyMeasurable (hTz p.2).aestronglyMeasurable
      (hsq _ h1) (hsq _ h2)).const_mul (g p.1 * g p.2)).congr (ae_of_all _ fun ω => ?_)
    simp only [hFdef]
    ring
  have hnorm : ∀ p : E × E, ∫ ω, ‖F ω p‖ ∂P ≤ |g p.1| * |g p.2| * B := by
    intro p
    by_cases h1 : g p.1 = 0
    · simp [hFdef, h1]
    by_cases h2 : g p.2 = 0
    · simp [hFdef, h2]
    have heq : (fun ω => ‖F ω p‖) = fun ω => |g p.1| * |g p.2| * |T ω p.1 * T ω p.2| := by
      funext ω
      simp only [hFdef, Real.norm_eq_abs, abs_mul]
      ring
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hE _ _ h1 h2) (by positivity)
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun p => hint p, ?_⟩
  refine ((hg.abs.mul_prod hg.abs).mul_const B).mono'
    (hFm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  exact hnorm p

/-- **Second moment of a random integral with finite-range correlations.** If `E[T_z²] ≤ B` wherever `g z ≠ 0`
and `E[T_z T_w] = 0` for `(z, w) ∉ S`, then `E[(∫ g T dν)²] ≤ B ∫_S |g(z)| |g(w)| d(ν ⊗ ν)(z, w)`. -/
theorem integral_sq_integral_le [SFinite P] [SFinite ν] {T : Ω → E → ℝ}
    (hT : Measurable fun q : Ω × E => T q.1 q.2) {g : E → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    {S : Set (E × E)} (hS : MeasurableSet S) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (horth : ∀ z w, g z ≠ 0 → g w ≠ 0 → (z, w) ∉ S → ∫ ω, T ω z * T ω w ∂P = 0) :
    ∫ ω, (∫ z, g z * T ω z ∂ν) ^ 2 ∂P ≤
      B * ∫ p, S.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) := by
  classical
  set F : Ω → E × E → ℝ := fun ω p => g p.1 * T ω p.1 * (g p.2 * T ω p.2) with hFdef
  have hE : ∀ z w, g z ≠ 0 → g w ≠ 0 → ∫ ω, |T ω z * T ω w| ∂P ≤ B := fun z w hz hw =>
    (integral_abs_mul_le (hsq z hz) (hsq w hw)).trans (by linarith [hB z hz, hB w hw])
  have hpt : ∀ p : E × E, ∫ ω, F ω p ∂P = g p.1 * g p.2 * ∫ ω, T ω p.1 * T ω p.2 ∂P := by
    intro p
    rw [← integral_const_mul]
    congr 1
    funext ω
    simp only [hFdef]
    ring
  have hFint : Integrable (uncurry F) (P.prod (ν.prod ν)) := integrable_mul_prod_of_sq hT hgm hg hsq hB
  have hsqeq : ∀ ω, (∫ z, g z * T ω z ∂ν) ^ 2 = ∫ p, F ω p ∂(ν.prod ν) := by
    intro ω
    rw [sq]
    exact (integral_prod_mul (fun z => g z * T ω z) (fun z => g z * T ω z)).symm
  calc ∫ ω, (∫ z, g z * T ω z ∂ν) ^ 2 ∂P = ∫ ω, ∫ p, F ω p ∂(ν.prod ν) ∂P :=
        integral_congr_ae (ae_of_all _ hsqeq)
    _ = ∫ p, ∫ ω, F ω p ∂P ∂(ν.prod ν) := integral_integral_swap hFint
    _ ≤ ∫ p, B * S.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) := by
        refine integral_mono hFint.integral_prod_right
          (((hg.abs.mul_prod hg.abs).indicator hS).const_mul B) fun p => ?_
        show ∫ ω, F ω p ∂P ≤ B * S.indicator (fun p => |g p.1| * |g p.2|) p
        rw [hpt p]
        by_cases h1 : g p.1 = 0
        · rw [Set.indicator_apply]
          split_ifs <;> simp [h1]
        by_cases h2 : g p.2 = 0
        · rw [Set.indicator_apply]
          split_ifs <;> simp [h2]
        by_cases hp : p ∈ S
        · rw [Set.indicator_of_mem hp]
          have hab : |∫ ω, T ω p.1 * T ω p.2 ∂P| ≤ B :=
            (abs_integral_le_integral_abs).trans (hE _ _ h1 h2)
          calc g p.1 * g p.2 * ∫ ω, T ω p.1 * T ω p.2 ∂P
              ≤ |g p.1 * g p.2 * ∫ ω, T ω p.1 * T ω p.2 ∂P| := le_abs_self _
            _ = |g p.1| * |g p.2| * |∫ ω, T ω p.1 * T ω p.2 ∂P| := by rw [abs_mul, abs_mul]
            _ ≤ |g p.1| * |g p.2| * B := mul_le_mul_of_nonneg_left hab (by positivity)
            _ = B * (|g p.1| * |g p.2|) := by ring
        · rw [Set.indicator_of_notMem hp, horth _ _ h1 h2 hp]
          simp
    _ = B * ∫ p, S.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) := integral_const_mul _ _

/-- The square of the random integral `∫ g T dν` is integrable. -/
theorem integrable_sq_integral [SFinite P] [SFinite ν] {T : Ω → E → ℝ}
    (hT : Measurable fun q : Ω × E => T q.1 q.2) {g : E → ℝ} (hgm : Measurable g) (hg : Integrable g ν) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B) :
    Integrable (fun ω => (∫ z, g z * T ω z ∂ν) ^ 2) P := by
  refine (integrable_mul_prod_of_sq hT hgm hg hsq hB).integral_prod_left.congr (ae_of_all _ fun ω => ?_)
  show ∫ p, g p.1 * T ω p.1 * (g p.2 * T ω p.2) ∂(ν.prod ν) = (∫ z, g z * T ω z ∂ν) ^ 2
  rw [sq]
  exact integral_prod_mul (fun z => g z * T ω z) (fun z => g z * T ω z)

/-- `E|Y| ≤ (E Y² / t + t) / 2` for every `t > 0`, on a probability space. -/
theorem integral_abs_le_of_integrable_sq [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |Y ω| ∂P ≤ ((∫ ω, Y ω ^ 2 ∂P) / t + t) / 2 := by
  have hb : Integrable (fun ω => (Y ω ^ 2 / t + t) / 2) P :=
    ((hY2.div_const t).add (integrable_const t)).div_const 2
  have hpt : ∀ ω, |Y ω| ≤ (Y ω ^ 2 / t + t) / 2 := by
    intro ω
    rw [show (Y ω ^ 2 / t + t) / 2 = (Y ω ^ 2 + t ^ 2) / (2 * t) by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|Y ω| - t), sq_abs (Y ω)]
  refine (integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) hb (ae_of_all _ hpt)).trans
    (le_of_eq ?_)
  rw [integral_div, integral_add (hY2.div_const t) (integrable_const t), integral_div, integral_const]
  simp

end LatticeProb.FiniteRange
