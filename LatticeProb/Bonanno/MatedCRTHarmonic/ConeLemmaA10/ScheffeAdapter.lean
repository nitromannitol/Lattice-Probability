/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.ScheffeAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A Scheffé adapter for nonnegative real densities

On any measure space, almost-everywhere convergence of nonnegative integrable densities together
with convergence of their total integrals implies convergence in the real `L¹` distance. This is
the form of Scheffé's lemma used to pass finite rooting densities to their limiting area density.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology

namespace MatedCRTHarmonic.ConeLemmaA10

/-- Scheffé's lemma for real-valued densities, with the `L¹` distance written as the integral of
the absolute difference. -/
theorem tendsto_integral_abs_sub_zero_of_scheffe
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) μ) (hgi : Integrable g μ)
    (hfnn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hint : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n => ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  let m : ℕ → α → ℝ := fun n x => min (f n x) (g x)
  have hmm : ∀ n, Measurable (m n) := by
    intro n
    exact (hfm n).min hgm
  have hmin_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ m n x := by
    intro n
    filter_upwards [hfnn n, hgn] with x hfx hgx
    exact le_min hfx hgx
  have hmin_le_g : ∀ n, ∀ᵐ x ∂μ, m n x ≤ g x := by
    intro n
    exact Eventually.of_forall fun x => min_le_right _ _
  have hmi : ∀ n, Integrable (m n) μ := by
    intro n
    apply hgi.mono' ((hmm n).aestronglyMeasurable)
    filter_upwards [hfnn n, hgn] with x hfx hgx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfx hgx)]
    exact min_le_right _ _
  have hmlim : ∀ᵐ x ∂μ, Tendsto (fun n => m n x) atTop (𝓝 (g x)) := by
    filter_upwards [hae] with x hx
    have hmin := hx.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)))
    simpa [m] using hmin
  have hmint : Tendsto (fun n => ∫ x, m n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) :=
    tendsto_integral_of_dominated_convergence g (fun n => (hmm n).aestronglyMeasurable)
      hgi (fun n => by
        filter_upwards [hfnn n, hgn] with x hfx hgx
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfx hgx)]
        exact min_le_right _ _) hmlim
  have hdist_eq (n : ℕ) :
      ∫ x, |f n x - g x| ∂μ =
        (∫ x, f n x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, m n x ∂μ) := by
    have habs : ∀ᵐ x ∂μ,
        |f n x - g x| = f n x + g x - 2 * m n x := by
      filter_upwards [hfnn n, hgn] with x hfx hgx
      dsimp [m]
      by_cases h : f n x ≤ g x
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · have h' : g x ≤ f n x := le_of_not_ge h
        rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h')]
        ring
    calc
      _ = ∫ x, (f n x + g x - 2 * m n x) ∂μ := integral_congr_ae habs
      _ = (∫ x, f n x + g x ∂μ) - (∫ x, (2 : ℝ) * m n x ∂μ) := by
        exact integral_sub ((hfi n).add hgi) ((hmi n).const_mul 2)
      _ = (∫ x, f n x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, m n x ∂μ) := by
        rw [integral_add (hfi n) hgi, integral_const_mul]
  have hexpr : Tendsto
      (fun n => (∫ x, f n x ∂μ) + (∫ x, g x ∂μ) -
        2 * (∫ x, m n x ∂μ)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => ∫ x, g x ∂μ) atTop
        (𝓝 (∫ x, g x ∂μ)) := tendsto_const_nhds
    have hsum : Tendsto (fun n => (∫ x, f n x ∂μ) + (∫ x, g x ∂μ)) atTop
        (𝓝 ((∫ x, g x ∂μ) + (∫ x, g x ∂μ))) := by
      simpa using hint.add hconst
    have hmul : Tendsto (fun n => 2 * (∫ x, m n x ∂μ)) atTop
        (𝓝 (2 * (∫ x, g x ∂μ))) := by
      simpa using hmint.const_mul (2 : ℝ)
    convert hsum.sub hmul using 1
    ring_nf
  exact hexpr.congr fun n => (hdist_eq n).symm

end MatedCRTHarmonic.ConeLemmaA10

