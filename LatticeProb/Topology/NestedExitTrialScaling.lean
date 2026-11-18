import LatticeProb.Topology.FirstHitBallAbsorption

/-!
# Scaling and time-change invariance of nested exit trials

The nested exit trial `nestedExitTrialEvent η t₀ z r a k` asks whether some ball of radius
`a` lies in the trace of `η` between its first exits, after time `t₀`, from the concentric
balls `B(z, r k)` and `B(z, r (k + 1))`. This file shows that the event does not change when

* the target is dilated by a factor `c > 0` and every radius is multiplied by `c`
  (`nestedExitTrialEvent_smul`);
* time is changed linearly, `t ↦ l t` with `l > 0`, and the starting time is divided by `l`
  (`nestedExitTrialEvent_comp_mul`);
* both changes are combined with a translation of the target
  (`nestedExitTrialEvent_affine`).

These are the deterministic parts of the scale and translation invariance arguments used for
space-filling curves whose law is invariant under `η ↦ x + c η(l ·)` for suitable `c`, `l`.

## Main results

* `setOf_exit_smul`, `exists_ball_subset_image_smul`, `nestedExitTrialEvent_smul`;
* `setOf_exit_comp_mul`, `image_Icc_comp_mul`, `nestedExitTrialEvent_comp_mul`;
* `nestedExitTrialEvent_affine`.
-/

open Set Metric
open scoped Pointwise

namespace LatticeProb

section Dilation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The times after `t₀` spent outside a ball are unchanged when the curve, the center and
the radius are dilated by the same factor `c > 0`. -/
theorem setOf_exit_smul {c : ℝ} (hc : 0 < c) (w : ℝ → E) (t₀ : ℝ) (z : E) (ρ : ℝ) :
    {t : ℝ | t₀ ≤ t ∧ c • w t ∉ ball (c • z) (c * ρ)} =
      {t : ℝ | t₀ ≤ t ∧ w t ∉ ball z ρ} := by
  ext t
  simp only [mem_ofPred_eq, mem_ball, dist_smul₀, Real.norm_of_nonneg hc.le,
    mul_lt_mul_iff_right₀ hc]

/-- A trace contains a ball of radius `a` if and only if its dilation by `c > 0` contains a
ball of radius `c * a`. -/
theorem exists_ball_subset_image_smul {c : ℝ} (hc : 0 < c) (w : ℝ → E) (I : Set ℝ)
    (a : ℝ) :
    (∃ v, ball v (c * a) ⊆ (fun t => c • w t) '' I) ↔ ∃ v, ball v a ⊆ w '' I := by
  have hc0 : c ≠ 0 := hc.ne'
  have himg : (fun t => c • w t) '' I = c • (w '' I) := by
    rw [← image_smul, image_image]
  have hball : ∀ v : E, ball (c • v) (c * a) = c • ball v a := fun v => by
    rw [_root_.smul_ball hc0, Real.norm_of_nonneg hc.le]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨c⁻¹ • v, ?_⟩
    have hv' : ball (c • (c⁻¹ • v)) (c * a) ⊆ c • (w '' I) := by
      rwa [smul_inv_smul₀ hc0, ← himg]
    rw [hball] at hv'
    exact (smul_set_subset_smul_set_iff₀ hc0).1 hv'
  · rintro ⟨v, hv⟩
    refine ⟨c • v, ?_⟩
    rw [himg, hball]
    exact smul_set_mono hv

/-- Nested exit trials are unchanged when the curve, the center, the radii and the ball
radius are all dilated by the same factor `c > 0`. -/
theorem nestedExitTrialEvent_smul {Ω : Type*} {c : ℝ} (hc : 0 < c) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    nestedExitTrialEvent (fun ω t => c • η ω t) t₀ (c • z) (fun j => c * r j) (c * a) k =
      nestedExitTrialEvent η t₀ z r a k := by
  ext ω
  show (∃ v, ball v (c * a) ⊆ (fun t => c • η ω t) '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ c • η ω t ∉ ball (c • z) (c * r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ c • η ω t ∉ ball (c • z) (c * r (k + 1))})) ↔ _
  rw [setOf_exit_smul hc, setOf_exit_smul hc]
  exact exists_ball_subset_image_smul hc (η ω) _ a

end Dilation

section TimeChange

variable {E : Type*} [PseudoMetricSpace E]

/-- Under the linear time change `t ↦ l t` with `l > 0` and the starting time `l⁻¹ t₀`, the
set of exit times is the image of the original one under multiplication by `l⁻¹`. -/
theorem setOf_exit_comp_mul {l : ℝ} (hl : 0 < l) (w : ℝ → E) (t₀ : ℝ) (z : E) (ρ : ℝ) :
    {t : ℝ | l⁻¹ * t₀ ≤ t ∧ w (l * t) ∉ ball z ρ} =
      l⁻¹ • {s : ℝ | t₀ ≤ s ∧ w s ∉ ball z ρ} := by
  ext t
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv, smul_eq_mul]
  simp only [mem_ofPred_eq, inv_mul_le_iff₀ hl]

/-- The trace of `t ↦ w (l t)` on `[l⁻¹ A, l⁻¹ B]` is the trace of `w` on `[A, B]`. -/
theorem image_Icc_comp_mul {α : Type*} {l : ℝ} (hl : 0 < l) (w : ℝ → α) (A B : ℝ) :
    (fun t => w (l * t)) '' Icc (l⁻¹ * A) (l⁻¹ * B) = w '' Icc A B := by
  have hcomp : (fun t => w (l * t)) = w ∘ (fun t => l * t) := rfl
  rw [hcomp, image_comp, image_mul_left_Icc' hl, mul_inv_cancel_left₀ hl.ne',
    mul_inv_cancel_left₀ hl.ne']

/-- Nested exit trials are unchanged under the linear time change `t ↦ l t`, `l > 0`, when
the starting time is replaced by `l⁻¹ t₀`. -/
theorem nestedExitTrialEvent_comp_mul {Ω : Type*} {l : ℝ} (hl : 0 < l) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    nestedExitTrialEvent (fun ω t => η ω (l * t)) (fun ω => l⁻¹ * t₀ ω) z r a k =
      nestedExitTrialEvent η t₀ z r a k := by
  ext ω
  show (∃ v, ball v a ⊆ (fun t => η ω (l * t)) '' Icc
      (sInf {t : ℝ | l⁻¹ * t₀ ω ≤ t ∧ η ω (l * t) ∉ ball z (r k)})
      (sInf {t : ℝ | l⁻¹ * t₀ ω ≤ t ∧ η ω (l * t) ∉ ball z (r (k + 1))})) ↔ _
  rw [setOf_exit_comp_mul hl, setOf_exit_comp_mul hl,
    Real.sInf_smul_of_nonneg (inv_nonneg.2 hl.le),
    Real.sInf_smul_of_nonneg (inv_nonneg.2 hl.le), smul_eq_mul, smul_eq_mul,
    image_Icc_comp_mul hl]
  rfl

end TimeChange

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nested exit trials are unchanged under the affine change `η ↦ x + c η(l ·)` with
`c, l > 0`, when the center is moved to `x + c z`, the radii and the ball radius are
multiplied by `c`, and the starting time is divided by `l`. -/
theorem nestedExitTrialEvent_affine {Ω : Type*} {c l : ℝ} (hc : 0 < c) (hl : 0 < l) (x : E)
    (η : Ω → ℝ → E) (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    nestedExitTrialEvent (fun ω t => x + c • η ω (l * t)) (fun ω => l⁻¹ * t₀ ω)
        (x + c • z) (fun j => c * r j) (c * a) k =
      nestedExitTrialEvent η t₀ z r a k := by
  have htr := nestedExitTrialEvent_isometryEquiv (IsometryEquiv.addLeft x)
    (fun ω t => c • η ω (l * t)) (fun ω => l⁻¹ * t₀ ω) (c • z) (fun j => c * r j) (c * a) k
  simp only [IsometryEquiv.addLeft_apply] at htr
  rw [htr, nestedExitTrialEvent_smul hc (fun ω t => η ω (l * t)),
    nestedExitTrialEvent_comp_mul hl]

end Affine

end LatticeProb
