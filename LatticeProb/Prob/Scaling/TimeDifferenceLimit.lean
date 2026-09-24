/- Locally uniform limits of time quotients are derivatives of their primitives.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.TimeDifferenceIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter Topology

noncomputable section
namespace LatticeProb.Scaling.TimeDifference

/-- Identifying a locally uniform limit of forward quotients uses time averages
of the continuous primitive and the uniform-limit theorem for derivatives. -/
theorem hasDerivAt_of_tendsto_difference
    {f v : ℝ → ℝ} (hf : Continuous f) {O : Set ℝ} (hO : IsOpen O)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝[>] 0))
    (hlim : TendstoLocallyUniformlyOn
      (fun n s => (f (s + h n) - f s) / h n) v atTop O)
    {s : ℝ} (hs : s ∈ O) : HasDerivAt f (v s) s := by
  let F : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, f r
  have hF : ∀ t, HasDerivAt F (f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hO hlim
    (f := fun n t => (F (t + h n) - F t) / h n) _ _ hs
  · apply Filter.Eventually.of_forall
    intro n t _
    simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one] using
      (((hF (t + h n)).comp t ((hasDerivAt_id t).add_const (h n))).sub (hF t)).div_const (h n)
  · intro t _
    have ht := (hF t).tendsto_slope_zero_right.comp hh
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht

/-- Compact convergence in space-time restricts to locally uniform convergence
on each open time slice. -/
theorem tendstoLocallyUniformlyOn_slice {E : Type*} [TopologicalSpace E]
    {O : Set (ℝ × E)} (hO : IsOpen O)
    {f : ℕ → ℝ × E → ℝ} {v : ℝ × E → ℝ}
    (hlim : ∀ K, IsCompact K → K ⊆ O → TendstoUniformlyOn f v atTop K) (x : E) :
    TendstoLocallyUniformlyOn (fun n s => f n (s, x)) (fun s => v (s, x))
      atTop {s | (s, x) ∈ O} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (hO.preimage (continuous_id.prodMk continuous_const))).mpr
  intro K hKO hK
  have hl := hlim ((fun s : ℝ => (s, x)) '' K)
    (hK.image (continuous_id.prodMk continuous_const)) (by
      rintro _ ⟨s, hs, rfl⟩
      exact hKO hs)
  exact (hl.comp (fun s : ℝ => (s, x))).mono (fun s hs => ⟨s, hs, rfl⟩)

end LatticeProb.Scaling.TimeDifference
