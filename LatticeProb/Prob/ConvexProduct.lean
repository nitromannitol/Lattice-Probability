/-
Convex comparison of finite products with integrable coordinates: a Lipschitz-implies-integrable
fact, and the tensorization lemma that a convex-order comparison between two one-dimensional
laws with a first moment lifts to any finite product of independent copies, tested against a
convex Lipschitz function of all coordinates.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
namespace LatticeProb.ConvexOrder
open MeasureTheory
open scoped NNReal

/-- Lipschitz observables are integrable when the coordinate has a first moment. -/
theorem integrable_real_lipschitz {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (hi : Integrable (id : E → E) μ) :
    Integrable f μ := by
  refine Integrable.mono' ((hi.norm.const_mul (K : ℝ)).add (integrable_const ‖f 0‖))
    hf.continuous.measurable.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := hf.dist_le_mul x 0
  simp only [dist_eq_norm, sub_zero] at h
  have hn := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at hn
  change ‖f x‖ ≤ (K : ℝ) * ‖x‖ + ‖f 0‖
  linarith

/-- The identity function on a finite product space is integrable once each coordinate's
identity function is. -/
theorem integrable_id_pi {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Integrable (id : ℝ → ℝ) (μ i)) :
    Integrable (id : (ι → ℝ) → (ι → ℝ)) (Measure.pi μ) :=
  integrable_pi_iff.mpr fun i => integrable_eval (hμ i)

/-- Inserting the first coordinate is nonexpansive. -/
theorem lipschitzWith_fin_cons_left {n : ℕ} (x : Fin n → ℝ) :
    LipschitzWith 1 (fun a : ℝ => (Fin.cons a x : Fin (n + 1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Inserting a fixed first coordinate is nonexpansive. -/
theorem lipschitzWith_fin_cons_right {n : ℕ} (a : ℝ) :
    LipschitzWith 1 (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n + 1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using dist_le_pi_dist x y j

/-- Fixing every coordinate but the first of a convex function leaves a convex function of the
first coordinate. -/
theorem convexOn_fin_cons_left {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun a : ℝ => f (Fin.cons a x)) := by
  refine ⟨convex_univ, fun a _ b _ c e hc he hce => ?_⟩
  have h := hf.2 (Set.mem_univ (Fin.cons a x)) (Set.mem_univ (Fin.cons b x)) hc he hce
  have heq : Fin.cons (c • a + e • b) x = c • Fin.cons a x + e • Fin.cons b x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change x j = c * x j + e * x j
      rw [← add_mul, hce, one_mul]
  change f (Fin.cons (c • a + e • b) x) ≤ c • f (Fin.cons a x) + e • f (Fin.cons b x)
  rw [heq]
  exact h

/-- Fixing the first coordinate of a convex function leaves a convex function of the
remaining coordinates. -/
theorem convexOn_fin_cons_right {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (a : ℝ) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => f (Fin.cons a x)) := by
  refine ⟨convex_univ, fun x _ y _ c e hc he hce => ?_⟩
  have h := hf.2 (Set.mem_univ (Fin.cons a x)) (Set.mem_univ (Fin.cons a y)) hc he hce
  have heq : Fin.cons a (c • x + e • y) = c • Fin.cons a x + e • Fin.cons a y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change a = c * a + e * a
      rw [← add_mul, hce, one_mul]
    · rfl
  change f (Fin.cons a (c • x + e • y)) ≤ c • f (Fin.cons a x) + e • f (Fin.cons a y)
  rw [heq]
  exact h

/-- A Lipschitz first-coordinate section has an integrable first moment. -/
theorem integrable_fin_cons_left {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (x : Fin n → ℝ) :
    Integrable (fun a : ℝ => f (Fin.cons a x)) μ :=
  integrable_real_lipschitz (hf.comp (lipschitzWith_fin_cons_left x)) hi

/-- Averaging a coordinate preserves its Lipschitz constant in the other coordinates. -/
theorem lipschitzWith_integral_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) :
    LipschitzWith K (fun x : Fin n → ℝ => ∫ a, f (Fin.cons a x) ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (integrable_fin_cons_left hf hi x)
    (integrable_fin_cons_left hf hi y)]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (ae_of_all μ fun a => (hf.comp (lipschitzWith_fin_cons_right a)).norm_sub_le x y)
  simpa only [NNReal.coe_mul, NNReal.coe_one, mul_one, probReal_univ, Real.norm_eq_abs,
    ← dist_eq_norm, Function.comp_def] using h

/-- Averaging a coordinate preserves convexity. -/
theorem convexOn_integral_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable (id : ℝ → ℝ) μ) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => ∫ a, f (Fin.cons a x) ∂μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := integral_mono (integrable_fin_cons_left hf hi (a • x + b • y))
    (((integrable_fin_cons_left hf hi x).const_mul a).add
      ((integrable_fin_cons_left hf hi y).const_mul b))
    (fun z => (convexOn_fin_cons_right hc z).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab)
  change (∫ z, f (Fin.cons z (a • x + b • y)) ∂μ) ≤
    ∫ z, a * f (Fin.cons z x) + b * f (Fin.cons z y) ∂μ at h
  rw [integral_add ((integrable_fin_cons_left hf hi x).const_mul a)
    ((integrable_fin_cons_left hf hi y).const_mul b), integral_const_mul, integral_const_mul] at h
  exact h
end LatticeProb.ConvexOrder

namespace LatticeProb.ConvexOrder
open MeasureTheory
open scoped NNReal

/-- Fubini with the first coordinate integrated inside. -/
theorem integral_pi_fin_succ {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f (Measure.pi (fun _ => μ))) :
    ∫ x, f x ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ x, ∫ a, f (Fin.cons a x) ∂μ ∂(Measure.pi (fun _ : Fin n => μ)) := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  have hprod : Integrable (fun z : ℝ × (Fin n → ℝ) => f (Fin.cons z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq, Function.comp_def]
      using he.integrable_comp_of_integrable hf
  calc
    _ = ∫ z : ℝ × (Fin n → ℝ), f (Fin.cons z.1 z.2)
        ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
      rw [← he.integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
    _ = _ := (integral_prod _ hprod).trans (integral_integral_swap hprod)

/-- Convex comparison of one-dimensional laws tensorizes to finite products. -/
theorem convex_lipschitz_integral_le_pi {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    (n : ℕ) {f : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hc : ConvexOn ℝ Set.univ f) (hf : LipschitzWith K f) :
    ∫ x, f x ∂(Measure.pi (fun _ : Fin n => μ)) ≤
      ∫ x, f x ∂(Measure.pi (fun _ : Fin n => ν)) := by
  induction n generalizing K with
  | zero =>
      have hconst : f = fun _ => f 0 := by
        funext x
        congr 1
        exact Subsingleton.elim _ _
      rw [hconst]
      simp
  | succ n ih =>
      have hfiμ := integrable_real_lipschitz hf (integrable_id_pi (fun _ => μ) (fun _ => hμ))
      have hfiν := integrable_real_lipschitz hf (integrable_id_pi (fun _ => ν) (fun _ => hν))
      rw [integral_pi_fin_succ hfiμ, integral_pi_fin_succ hfiν]
      let gμ : (Fin n → ℝ) → ℝ := fun x => ∫ a, f (Fin.cons a x) ∂μ
      let gν : (Fin n → ℝ) → ℝ := fun x => ∫ a, f (Fin.cons a x) ∂ν
      have hgμ : LipschitzWith K gμ := lipschitzWith_integral_fin_cons hf hμ
      have hgν : LipschitzWith K gν := lipschitzWith_integral_fin_cons hf hν
      have hgνc : ConvexOn ℝ Set.univ gν := convexOn_integral_fin_cons hf hc hν
      calc (∫ x, gμ x ∂(Measure.pi (fun _ : Fin n => μ))) ≤
          ∫ x, gν x ∂(Measure.pi (fun _ : Fin n => μ)) := by
            apply integral_mono
              (integrable_real_lipschitz hgμ (integrable_id_pi (fun _ => μ) (fun _ => hμ)))
              (integrable_real_lipschitz hgν (integrable_id_pi (fun _ => μ) (fun _ => hμ)))
            intro x
            exact hcomp _ (K * 1) (convexOn_fin_cons_left hc x)
              (hf.comp (lipschitzWith_fin_cons_left x))
        _ ≤ ∫ x, gν x ∂(Measure.pi (fun _ : Fin n => ν)) := ih hgνc hgν
end LatticeProb.ConvexOrder

namespace LatticeProb.ConvexOrder
open MeasureTheory
open scoped NNReal

/-- The finite-product convex comparison with arbitrary finite indices. -/
theorem convex_lipschitz_integral_le_finite_pi {ι : Type*} [Fintype ι] {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    {f : (ι → ℝ) → ℝ} {K : ℝ≥0}
    (hc : ConvexOn ℝ Set.univ f) (hf : LipschitzWith K f) :
    ∫ x, f x ∂(Measure.pi (fun _ : ι => μ)) ≤
      ∫ x, f x ∂(Measure.pi (fun _ : ι => ν)) := by
  let e := (Fintype.equivFin ι).symm
  let r : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun x i => x (e.symm i)
  have hr : LipschitzWith 1 r := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    exact fun i => dist_le_pi_dist x y (e.symm i)
  have hcr : ConvexOn ℝ Set.univ (f ∘ r) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    exact hc.2 (Set.mem_univ (r x)) (Set.mem_univ (r y)) ha hb hab
  have h := convex_lipschitz_integral_le_pi hμ hν hcomp (Fintype.card ι) hcr (hf.comp hr)
  rw [← (measurePreserving_piCongrLeft (fun _ : ι => μ) e).integral_comp',
    ← (measurePreserving_piCongrLeft (fun _ : ι => ν) e).integral_comp']
  have heq : (Equiv.piCongrLeft (fun _ : ι => ℝ) e) = r := by
    funext x i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [r]
  simpa only [MeasurableEquiv.coe_piCongrLeft, heq, Function.comp_def] using h
end LatticeProb.ConvexOrder
