/- Integrating out time preserves smooth compactly supported test functions.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory Set
open scoped Convolution

noncomputable section
namespace LatticeProb.Scaling.CompactTimeIntegral
variable {E : Type*} [NormedAddCommGroup E]

/-- A compactly supported smooth function remains smooth after time integration.
The parameter-dependent convolution theorem supplies differentiation under the integral. -/
theorem contDiff [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ψ : ℝ × E → ℝ} {n : ℕ∞}
    (hψ : ContDiff ℝ n ψ) (hc : HasCompactSupport ψ) :
    ContDiff ℝ n (fun x => ∫ s : ℝ, ψ (s, x)) := by
  have hk : IsCompact (Prod.fst '' tsupport ψ) := hc.isCompact.image continuous_fst
  have hz : ∀ (x : E) (s : ℝ), x ∈ (univ : Set E) →
      s ∉ Prod.fst '' tsupport ψ → ψ (s, x) = 0 := by
    intro x s _ hs
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hs ⟨(s, x), hp, rfl⟩
  have h := contDiffOn_convolution_left_with_param_comp
    (μ := (volume : Measure ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ)
    (v := fun _ : E => (0 : ℝ)) (f := fun _ : ℝ => (1 : ℝ))
    (g := fun x s => ψ (s, x)) contDiffOn_const isOpen_univ hk hz
    (locallyIntegrable_const 1) (hψ.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  simpa only [contDiffOn_univ, convolution, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_one] using h

/-- The spatial support of the time integral lies in the spatial projection of the
original compact support. -/
theorem tsupport_subset {ψ : ℝ × E → ℝ} (hc : HasCompactSupport ψ) :
    tsupport (fun x => ∫ s : ℝ, ψ (s, x)) ⊆ Prod.snd '' tsupport ψ := by
  apply closure_minimal _ (hc.isCompact.image continuous_snd).isClosed
  intro x hx
  by_contra hn
  have hz : ∀ s : ℝ, ψ (s, x) = 0 := by
    intro s
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hn ⟨(s, x), hp, rfl⟩
  exact hx (by simp only [hz, integral_zero])

/-- The time integral of a compactly supported function has compact support. -/
theorem hasCompactSupport {ψ : ℝ × E → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun x => ∫ s : ℝ, ψ (s, x)) :=
  (hc.isCompact.image continuous_snd).of_isClosed_subset (isClosed_tsupport _) (tsupport_subset hc)

end LatticeProb.Scaling.CompactTimeIntegral
