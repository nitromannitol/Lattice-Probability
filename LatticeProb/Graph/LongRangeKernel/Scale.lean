import LatticeProb.Prob.RegularVariation

/-!
# Scale and asymptotic inverse conventions

Scale functions are represented on the reals and constrained on the nonnegative half-line.
Their values on the negative half-line do not enter any graph estimate or limit at infinity.
-/

namespace LatticeProb.Graph.LongRangeKernel

open Filter Topology MeasureTheory

noncomputable section

/-- The integral scale in MSC, with the source's continuous extension at zero. -/
def eta (γ : ℝ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then γ * φ 0 else r ^ γ / ∫ s in (0 : ℝ)..r, s ^ (γ - 1) / φ s

/-- Asymptotic inverse means both compositions divided by the identity tend to one. -/
def IsAsymptoticInverse (f g : ℝ → ℝ) : Prop :=
  Tendsto (fun t => f (g t) / t) atTop (𝓝 1) ∧
    Tendsto (fun t => g (f t) / t) atTop (𝓝 1)

/-- The volume profile is positive, continuous, strictly increasing, and doubling. -/
def IsVolumeProfile (V : ℝ → ℝ) : Prop :=
  ContinuousOn V (Set.Ici 0) ∧ StrictMonoOn V (Set.Ici 0) ∧
    (∀ r, 0 ≤ r → 0 < V r) ∧
    ∃ C_D : ℝ, 1 < C_D ∧ ∀ r, 0 < r → V (2 * r) ≤ C_D * V r

/-- The jump scale has the source's range, continuity and positive regular variation index. -/
def IsJumpScale (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Ici 0) ∧ (∀ r, 0 ≤ r → 1 ≤ φ r) ∧
    ∃ β : ℝ, 0 < β ∧ LatticeProb.RegularlyVaryingAtTop φ β

/-- The inverse scale is continuous, nondecreasing, bounded below by one, and asymptotic. -/
def IsInverseScale (γ : ℝ) (φ ζ : ℝ → ℝ) : Prop :=
  ContinuousOn ζ (Set.Ici 0) ∧ MonotoneOn ζ (Set.Ici 0) ∧
    (∀ r, 0 ≤ r → 1 ≤ ζ r) ∧ IsAsymptoticInverse (eta γ φ) ζ

/-- The source assumptions imply actual integrability of the scale integrand. -/
theorem intervalIntegrable_eta_integrand {γ : ℝ} {φ : ℝ → ℝ}
    (hγ : 1 < γ) (hφ : IsJumpScale φ) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (fun s => s ^ (γ - 1) / φ s) volume 0 r := by
  have hsub : Set.uIcc 0 r ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hr]
    exact fun _ hs => hs.1
  apply ContinuousOn.intervalIntegrable
  refine (Real.continuous_rpow_const (by linarith : 0 ≤ γ - 1)).continuousOn.div
    (hφ.1.mono hsub) ?_
  intro s hs
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hφ.2.1 s (hsub hs)))

/-- At every positive radius, the integral denominator is strictly positive. -/
theorem integral_eta_integrand_pos {γ : ℝ} {φ : ℝ → ℝ}
    (hγ : 1 < γ) (hφ : IsJumpScale φ) {r : ℝ} (hr : 0 < r) :
    0 < ∫ s in (0 : ℝ)..r, s ^ (γ - 1) / φ s := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_eta_integrand hγ hφ hr.le) ?_ hr
  intro s hs
  exact div_pos (Real.rpow_pos_of_pos hs.1 _)
    (lt_of_lt_of_le zero_lt_one (hφ.2.1 s hs.1.le))

/-- The definition retains the continuous-at-zero value specified after equation (3.1). -/
theorem eta_zero (γ : ℝ) (φ : ℝ → ℝ) : eta γ φ 0 = γ * φ 0 := by
  simp only [eta, ite_true]

/-- The scale is strictly positive everywhere on its source domain. -/
theorem eta_pos {γ : ℝ} {φ : ℝ → ℝ} (hγ : 1 < γ) (hφ : IsJumpScale φ)
    {r : ℝ} (hr : 0 ≤ r) : 0 < eta γ φ r := by
  by_cases hzero : r = 0
  · rw [hzero, eta_zero]
    exact mul_pos (by linarith) (lt_of_lt_of_le zero_lt_one (hφ.2.1 0 le_rfl))
  · have hr0 : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    rw [eta, if_neg hzero]
    exact div_pos (Real.rpow_pos_of_pos hr0 _) (integral_eta_integrand_pos hγ hφ hr0)

end

end LatticeProb.Graph.LongRangeKernel
