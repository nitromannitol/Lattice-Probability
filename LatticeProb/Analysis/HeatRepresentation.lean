import Mathlib
import LatticeProb.Analysis.HeatKernel
import LatticeProb.Analysis.HeatMollify

/-!
# Local representation formula and interior bounds for the heat equation

For the operator `L = (2d)⁻¹ Δ` of `LatticeProb.WhiteNoise.contOp` on `ℝ × ℝ ^ d`, let `Φ` be the
heat kernel `heatKernel`. We assume the Duhamel formula `v p = ∫ Φ (p - q) ((∂_s - L) v) q dq` for
smooth compactly supported `v`, and that `Φ` is smooth off `{x = 0}`. From these we prove:

* `heatRepresentation_of_duhamel`. Let `w` solve `∂_s w = L w` classically in an open set `O`, and
  let `ζ` be a smooth compactly supported cutoff with `tsupport ζ ⊆ O` and `ζ ≡ 1` near `p`. Then
  `w p = ∫ q, repKernel d ζ p q * w q`.
* `heatInteriorBounds_of_duhamel`. For a compact `K ⊆ O` there are a compact `K' ⊆ O` and a
  constant `C` with the following property: for every classical solution `w` in `O` and every
  `p ∈ K`, both `|w p|` and `‖fderiv ℝ w p‖` are at most `C ∫_{K'} |w|`.

The bounds on the derivatives of the kernel away from `{x = 0}` are also a hypothesis of both
theorems, but the proofs do not use them.

The representation formula applies the Duhamel formula to `ζ w`. On `O`,
`(∂_s - L) (ζ w) = w (∂_s ζ - L ζ) - d⁻¹ ∇ζ · ∇w`. The cross term is integrated by parts in each
space variable (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`). This works because
`q ↦ Φ (p - q) ∂ᵢζ q w q` is smooth and compactly supported: `∇ζ` vanishes near `p` and off
`tsupport ζ`.

For the interior bounds, take a cutoff `ζ ≡ 1` on the closed `2r`-thickening of `K`. For `p` within
`r` of `K`, the kernel only sees points `q` at distance at least `r` from `p`. There `Φ` is smooth,
so the kernel is bounded and Lipschitz in `p`. The derivative bound follows from
`HasFDerivAt.le_of_lip'`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

/-- The cutoff kernel of the local representation formula: with `ζ` a cutoff,
`w p = ∫ q, repKernel d ζ p q * w q` for `ζ ≡ 1` near `p`. -/
noncomputable def repKernel (d : ℕ) (ζ : ℝ × (Fin d → ℝ) → ℝ) (p q : ℝ × (Fin d → ℝ)) : ℝ :=
  heatKernel d (p.1 - q.1) (p.2 - q.2) *
      (deriv (fun s => ζ (s, q.2)) q.1 + contOp d (fun y => ζ (q.1, y)) q.2) +
    (1 / (d : ℝ)) * ∑ i : Fin d,
      deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) *
        deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i)

/-- If `g` is integrable with integral zero, adding it does not change the integral of `f`, whether
or not `f` is integrable. -/
theorem integral_add_eq_of_integral_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hg : Integrable g μ) (hg0 : ∫ x, g x ∂μ = 0) :
    ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_add hf hg, hg0, add_zero]
  · rw [integral_undef hf, integral_undef]
    exact fun h => hf ((h.sub hg).congr (ae_of_all _ fun x => by simp))

/-- The second derivative of a product of smooth functions of one variable. -/
theorem deriv_deriv_mul_of_contDiff {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (x : ℝ) :
    deriv (fun s => deriv (fun t => a t * b t) s) x =
      deriv (fun s => deriv a s) x * b x + 2 * (deriv a x * deriv b x) +
        a x * deriv (fun s => deriv b s) x := by
  have ha1 : Differentiable ℝ a := ha.differentiable (by simp)
  have hb1 : Differentiable ℝ b := hb.differentiable (by simp)
  have ha2 : Differentiable ℝ fun s => deriv a s :=
    (contDiff_infty_iff_deriv.mp ha).2.differentiable (by simp)
  have hb2 : Differentiable ℝ fun s => deriv b s :=
    (contDiff_infty_iff_deriv.mp hb).2.differentiable (by simp)
  have h1 : (fun s => deriv (fun t => a t * b t) s) = fun s => deriv a s * b s + a s * deriv b s :=
    funext fun s => deriv_fun_mul (ha1 s) (hb1 s)
  have h2 : HasDerivAt (fun s => deriv a s * b s + a s * deriv b s)
      (deriv (fun s => deriv a s) x * b x + deriv a x * deriv b x +
        (deriv a x * deriv b x + a x * deriv (fun s => deriv b s) x)) x :=
    ((ha2 x).hasDerivAt.mul (hb1 x).hasDerivAt).add ((ha1 x).hasDerivAt.mul (hb2 x).hasDerivAt)
  rw [h1, h2.deriv]
  ring

section Slices

variable {d : ℕ}

theorem tendsto_slice_time (q : ℝ × (Fin d → ℝ)) :
    Tendsto (fun s : ℝ => (s, q.2)) (𝓝 q.1) (𝓝 q) :=
  (continuous_id.prodMk continuous_const).tendsto' q.1 q rfl

theorem tendsto_slice_space (q : ℝ × (Fin d → ℝ)) :
    Tendsto (fun x : Fin d → ℝ => (q.1, x)) (𝓝 q.2) (𝓝 q) :=
  (continuous_const.prodMk continuous_id).tendsto' q.2 q rfl

theorem tendsto_slice_update (q : ℝ × (Fin d → ℝ)) (i : Fin d) :
    Tendsto (fun t : ℝ => (q.1, Function.update q.2 i t)) (𝓝 (q.2 i)) (𝓝 q) :=
  (continuous_const.prodMk (continuous_const.update i continuous_id)).tendsto' (q.2 i) q
    (by simp)

variable {f g : ℝ × (Fin d → ℝ) → ℝ} {q : ℝ × (Fin d → ℝ)}

theorem deriv_slice_time_congr (h : f =ᶠ[𝓝 q] g) :
    deriv (fun s => f (s, q.2)) q.1 = deriv (fun s => g (s, q.2)) q.1 := by
  have h' : (fun s => f (s, q.2)) =ᶠ[𝓝 q.1] fun s => g (s, q.2) :=
    h.comp_tendsto (tendsto_slice_time q)
  exact h'.deriv_eq

theorem lap_slice_congr (h : f =ᶠ[𝓝 q] g) :
    lap (fun y => f (q.1, y)) q.2 = lap (fun y => g (q.1, y)) q.2 := by
  have h' : (fun y => f (q.1, y)) =ᶠ[𝓝 q.2] fun y => g (q.1, y) :=
    h.comp_tendsto (tendsto_slice_space q)
  exact lap_congr_of_eventuallyEq h'

theorem contOp_slice_congr (h : f =ᶠ[𝓝 q] g) :
    contOp d (fun y => f (q.1, y)) q.2 = contOp d (fun y => g (q.1, y)) q.2 := by
  unfold contOp
  rw [lap_slice_congr h]

theorem slice_update_eventuallyEq (h : f =ᶠ[𝓝 q] g) (i : Fin d) :
    (fun t => f (q.1, Function.update q.2 i t)) =ᶠ[𝓝 (q.2 i)]
      fun t => g (q.1, Function.update q.2 i t) :=
  h.comp_tendsto (tendsto_slice_update q i)

theorem deriv_slice_update_congr (h : f =ᶠ[𝓝 q] g) (i : Fin d) :
    deriv (fun t => f (q.1, Function.update q.2 i t)) (q.2 i) =
      deriv (fun t => g (q.1, Function.update q.2 i t)) (q.2 i) :=
  (slice_update_eventuallyEq h i).deriv_eq

theorem deriv_deriv_slice_update_congr (h : f =ᶠ[𝓝 q] g) (i : Fin d) :
    deriv (fun s => deriv (fun t => f (q.1, Function.update q.2 i t)) s) (q.2 i) =
      deriv (fun s => deriv (fun t => g (q.1, Function.update q.2 i t)) s) (q.2 i) :=
  (slice_update_eventuallyEq h i).deriv.deriv_eq

theorem deriv_slice_time_eq_zero {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) :
    deriv (fun s => f (s, q.2)) q.1 = 0 := by
  rw [deriv_slice_time_congr (show f =ᶠ[𝓝 q] fun _ => c from h)]
  simp

theorem contOp_slice_eq_zero {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) :
    contOp d (fun y => f (q.1, y)) q.2 = 0 := by
  rw [contOp_slice_congr (show f =ᶠ[𝓝 q] fun _ => c from h)]
  simp [contOp, lap]

theorem deriv_slice_update_eq_zero {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) (i : Fin d) :
    deriv (fun t => f (q.1, Function.update q.2 i t)) (q.2 i) = 0 := by
  rw [deriv_slice_update_congr (show f =ᶠ[𝓝 q] fun _ => c from h)]
  simp

theorem deriv_deriv_slice_update_eq_zero {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) (i : Fin d) :
    deriv (fun s => deriv (fun t => f (q.1, Function.update q.2 i t)) s) (q.2 i) = 0 := by
  rw [deriv_deriv_slice_update_congr (show f =ᶠ[𝓝 q] fun _ => c from h)]
  simp

theorem fderiv_eventually_eq_zero {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) :
    ∀ᶠ y in 𝓝 q, fderiv ℝ f y = 0 :=
  h.eventually_nhds.mono fun y hy => by
    rw [Filter.EventuallyEq.fderiv_eq (show f =ᶠ[𝓝 y] fun _ => c from hy)]
    simp

theorem deriv_slice_update_eq_fderiv (hf : Differentiable ℝ f) (q : ℝ × (Fin d → ℝ)) (i : Fin d) :
    deriv (fun t => f (q.1, Function.update q.2 i t)) (q.2 i) = fderiv ℝ f q (spaceDir d i) := by
  have h := hasDerivAt_slice_space hf q.1 q.2 i (q.2 i)
  rw [Function.update_eq_self] at h
  exact h.deriv

theorem contDiff_slice_update (hf : ContDiff ℝ ∞ f) (s : ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ContDiff ℝ ∞ (fun t => f (s, Function.update x i t)) :=
  hf.comp (contDiff_const.prodMk (contDiff_update _ x i))

/-- The Laplacian of a product of smooth functions, on a space slice. -/
theorem lap_slice_mul (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (q : ℝ × (Fin d → ℝ)) :
    lap (fun y => f (q.1, y) * g (q.1, y)) q.2 =
      f q * lap (fun y => g (q.1, y)) q.2 + g q * lap (fun y => f (q.1, y)) q.2 +
        2 * ∑ i, deriv (fun t => f (q.1, Function.update q.2 i t)) (q.2 i) *
          deriv (fun t => g (q.1, Function.update q.2 i t)) (q.2 i) := by
  simp only [lap]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv_deriv_mul_of_contDiff (contDiff_slice_update hf q.1 q.2 i)
    (contDiff_slice_update hg q.1 q.2 i)]
  simp only [Function.update_eq_self, Prod.mk.eta]
  ring

/-- A smooth cutoff times a function smooth on an open set containing its closed support is
smooth. -/
theorem contDiff_mul_of_tsupport_subset {O : Set (ℝ × (Fin d → ℝ))} (hO : IsOpen O)
    (hf : ContDiff ℝ ∞ f) (hfO : tsupport f ⊆ O) (hg : ContDiffOn ℝ ∞ g O) :
    ContDiff ℝ ∞ (fun q => f q * g q) := by
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  by_cases hq : q ∈ O
  · exact hf.contDiffAt.mul (hg.contDiffAt (hO.mem_nhds hq))
  · have h0 : f =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hq (hfO h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (h0.mono fun y hy => ?_)
    simp [hy]

/-- A function smooth on an open set agrees near each of its points with a smooth function. -/
theorem exists_contDiff_eventuallyEq {O : Set (ℝ × (Fin d → ℝ))} (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ g O) (hq : q ∈ O) :
    ∃ G : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝 q] g := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO q hq
  let χ : ContDiffBump q := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun y => χ y * g y, contDiff_mul_of_tsupport_subset hO χ.contDiff ?_ hg, ?_⟩
  · rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball
  · filter_upwards [closedBall_mem_nhds q (show 0 < ε / 4 by positivity)] with y hy
    rw [χ.one_of_mem_closedBall hy, one_mul]

end Slices

section Kernel

variable {d : ℕ}

/-- The heat kernel is smooth at every point of space-time other than the origin, given its
smoothness off `{x = 0}`. -/
theorem contDiffAt_heatKernel_of_ne (hd : 1 ≤ d)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0})
    {z : ℝ × (Fin d → ℝ)} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) z := by
  rcases lt_trichotomy z.1 0 with h | h | h
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto z).eventually (gt_mem_nhds h)] with y hy
    exact heatKernel_of_nonpos hy.le _
  · have h2 : z.2 ≠ 0 := fun h2 => hz (Prod.ext h h2)
    exact hA.contDiffAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds h2)
  · exact (contDiffOn_heatKernel hd).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds h)

/-- The integral of a space partial derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_deriv_slice_update_eq_zero {H : ℝ × (Fin d → ℝ) → ℝ} (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (i : Fin d) :
    Integrable (fun q : ℝ × (Fin d → ℝ) =>
        deriv (fun t => H (q.1, Function.update q.2 i t)) (q.2 i)) ∧
      ∫ q : ℝ × (Fin d → ℝ), deriv (fun t => H (q.1, Function.update q.2 i t)) (q.2 i) = 0 := by
  have hd1 : Differentiable ℝ H := hH.differentiable one_ne_zero
  simp_rw [deriv_slice_update_eq_fderiv hd1]
  have hcont : Continuous fun q => fderiv ℝ H q (spaceDir d i) :=
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : Integrable fun q => fderiv ℝ H q (spaceDir d i) :=
    hcont.integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)
  refine ⟨hint, ?_⟩
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := H)
    (g := fun _ => (1 : ℝ)) (v := spaceDir d i) (by simpa using hint) (by simp)
    (by simpa using hH.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => hd1 x) (fun x _ => differentiableAt_const _)
  simp at key
  linarith

/-- The algebra of the representation formula at one point. -/
theorem rep_algebra (hd : (d : ℝ) ≠ 0) (Φ Ts Cz Cw wq ζq : ℝ) (D b b' c : Fin d → ℝ)
    (hCz : Cz = (∑ i, b' i) / (2 * d)) :
    (Φ * (Ts + Cz) + 1 / d * ∑ i, D i * b i) * wq =
      Φ * (Ts * wq + ζq * Cw - (ζq * Cw + wq * Cz + 1 / d * ∑ i, b i * c i)) +
        1 / d * ∑ i, (D i * b i * wq + Φ * b' i * wq + Φ * b i * c i) := by
  have hs : ∑ i, (D i * b i * wq + Φ * b' i * wq + Φ * b i * c i) =
      (∑ i, D i * b i) * wq + Φ * wq * ∑ i, b' i + Φ * ∑ i, b i * c i := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, hCz]
  field_simp
  ring

end Kernel

/-- **Local representation formula** for a classical solution of the heat equation, assuming the
smoothness of the heat kernel off `{x = 0}` and the Duhamel formula. -/
theorem heatRepresentation_of_duhamel
    (hA : ∀ d : ℕ, 1 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0})
    (_hbd : ∀ (d : ℕ) (n : ℕ) (ρ T : ℝ), 1 ≤ d → 0 < ρ → 0 < T → ∃ C : ℝ, ∀ p : ℝ × (Fin d → ℝ),
      0 < p.1 → p.1 ≤ T → ρ ≤ ‖p.2‖ →
        ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤ C)
    (hD : ∀ d : ℕ, 1 ≤ d → ∀ v : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
      HasCompactSupport v → ∀ (t : ℝ) (x : Fin d → ℝ), v (t, x) =
        ∫ q : ℝ × (Fin d → ℝ), heatKernel d (t - q.1) (x - q.2) *
          (deriv (fun s => v (s, q.2)) q.1 - contOp d (fun y => v (q.1, y)) q.2)) :
    ∀ (d : ℕ), 1 ≤ d → ∀ (O : Set (ℝ × (Fin d → ℝ))), IsOpen O →
      ∀ (ζ w : ℝ × (Fin d → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ O → IsClassicalHeat d O w → ∀ p : ℝ × (Fin d → ℝ),
          (∀ᶠ q in 𝓝 p, ζ q = 1) → w p = ∫ q : ℝ × (Fin d → ℝ), repKernel d ζ p q * w q := by
  intro d hd O hO ζ w hζ hζc hζO hw p hp
  have hA' := hA d hd
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun q => ζ q * w q) :=
    contDiff_mul_of_tsupport_subset hO hζ hζO hw.1
  have hrep := hD d hd (fun q => ζ q * w q) hv hζc.mul_right p.1 p.2
  have hdead : ∀ q, ¬(q ∈ O ∧ q ≠ p) → ∃ c, ∀ᶠ y in 𝓝 q, ζ y = c := by
    intro q hq
    by_cases hqO : q ∈ O
    · have hqp : q = p := by
        by_contra hne
        exact hq ⟨hqO, hne⟩
      exact ⟨1, hqp ▸ hp⟩
    · exact ⟨0, notMem_tsupport_iff_eventuallyEq.1 fun h => hqO (hζO h)⟩
  obtain ⟨H, hH⟩ : ∃ H : Fin d → ℝ × (Fin d → ℝ) → ℝ, H = fun i q =>
      heatKernel d (p.1 - q.1) (p.2 - q.2) * fderiv ℝ ζ q (spaceDir d i) * w q := ⟨_, rfl⟩
  have hHs : ∀ i, ContDiff ℝ 1 (H i) := by
    intro i
    rw [hH]
    refine contDiff_iff_contDiffAt.2 fun q => ?_
    by_cases hlive : q ∈ O ∧ q ≠ p
    · have hne : p - q ≠ 0 := sub_ne_zero.2 (Ne.symm hlive.2)
      have h1 : ContDiffAt ℝ 1
          (fun q : ℝ × (Fin d → ℝ) => heatKernel d (p.1 - q.1) (p.2 - q.2)) q :=
        ((contDiffAt_heatKernel_of_ne hd hA' hne).comp q
          (contDiffAt_const.sub contDiffAt_id)).of_le (by simp)
      exact (h1.mul ((contDiff_fderiv_apply hζ _).contDiffAt.of_le (by simp))).mul
        ((hw.1.contDiffAt (hO.mem_nhds hlive.1)).of_le (by simp))
    · obtain ⟨c, hc⟩ := hdead q hlive
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [fderiv_eventually_eq_zero hc] with y hy
      simp [hy]
  have hHc : ∀ i, HasCompactSupport (H i) := by
    intro i
    refine (hζc.fderiv_apply (𝕜 := ℝ) (spaceDir d i)).mono fun q hq h0 => hq ?_
    rw [hH]
    simp only at h0 ⊢
    rw [h0, mul_zero, zero_mul]
  have hE : ∀ i q, deriv (fun t => H i (q.1, Function.update q.2 i t)) (q.2 i) =
      deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) *
          deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) * w q +
        heatKernel d (p.1 - q.1) (p.2 - q.2) *
          deriv (fun s => deriv (fun t => ζ (q.1, Function.update q.2 i t)) s) (q.2 i) * w q +
        heatKernel d (p.1 - q.1) (p.2 - q.2) *
          deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) *
          deriv (fun t => w (q.1, Function.update q.2 i t)) (q.2 i) := by
    intro i q
    have hslice : (fun t => H i (q.1, Function.update q.2 i t)) = fun t =>
        heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t) *
          deriv (fun t => ζ (q.1, Function.update q.2 i t)) t *
            w (q.1, Function.update q.2 i t) := by
      funext t
      rw [hH, (hasDerivAt_slice_space hζd q.1 q.2 i t).deriv]
    rw [hslice]
    by_cases hlive : q ∈ O ∧ q ≠ p
    · have hne : ((p.1 - q.1, p.2 - q.2) : ℝ × (Fin d → ℝ)) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm hlive.2)
      have ha : HasDerivAt (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t))
          (deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i))
          (q.2 i) := by
        refine DifferentiableAt.hasDerivAt ?_
        have h1 : DifferentiableAt ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2)
            (p.1 - q.1, p.2 - Function.update q.2 i (q.2 i)) := by
          rw [Function.update_eq_self]
          exact (contDiffAt_heatKernel_of_ne hd hA' hne).differentiableAt (by simp)
        have hg : HasDerivAt
            (fun t : ℝ => ((p.1 - q.1, p.2 - Function.update q.2 i t) : ℝ × (Fin d → ℝ)))
            ((0 : ℝ), 0 - Pi.single i (1 : ℝ)) (q.2 i) :=
          (hasDerivAt_const (q.2 i) (p.1 - q.1)).prodMk
            ((hasDerivAt_const (q.2 i) p.2).sub (hasDerivAt_update q.2 i (q.2 i)))
        exact h1.comp (q.2 i) hg.differentiableAt
      have hz : ContDiff ℝ ∞ (fun t => ζ (q.1, Function.update q.2 i t)) :=
        contDiff_slice_update hζ q.1 q.2 i
      have hb : HasDerivAt (fun s => deriv (fun t => ζ (q.1, Function.update q.2 i t)) s)
          (deriv (fun s => deriv (fun t => ζ (q.1, Function.update q.2 i t)) s) (q.2 i))
          (q.2 i) :=
        ((contDiff_infty_iff_deriv.mp hz).2.differentiable (by simp) (q.2 i)).hasDerivAt
      have hc : HasDerivAt (fun t => w (q.1, Function.update q.2 i t))
          (deriv (fun t => w (q.1, Function.update q.2 i t)) (q.2 i)) (q.2 i) := by
        refine DifferentiableAt.hasDerivAt ?_
        have h1 : DifferentiableAt ℝ w (q.1, Function.update q.2 i (q.2 i)) := by
          rw [Function.update_eq_self]
          exact (hw.1.contDiffAt (hO.mem_nhds hlive.1)).differentiableAt (by simp)
        exact h1.comp (q.2 i)
          (((hasDerivAt_const _ _).prodMk (hasDerivAt_update q.2 i (q.2 i))).differentiableAt)
      have hprod : HasDerivAt (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t) *
          deriv (fun t => ζ (q.1, Function.update q.2 i t)) t * w (q.1, Function.update q.2 i t))
          _ (q.2 i) := (ha.mul hb).mul hc
      rw [hprod.deriv]
      simp only [Pi.mul_apply, Function.update_eq_self, Prod.mk.eta]
      ring
    · obtain ⟨c, hc⟩ := hdead q hlive
      have h1 : (fun t => ζ (q.1, Function.update q.2 i t)) =ᶠ[𝓝 (q.2 i)] fun _ => c :=
        slice_update_eventuallyEq (show ζ =ᶠ[𝓝 q] fun _ => c from hc) i
      have hb0 : (fun s => deriv (fun t => ζ (q.1, Function.update q.2 i t)) s) =ᶠ[𝓝 (q.2 i)]
          fun _ => 0 := by
        simpa using h1.deriv
      have hzero : (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t) *
          deriv (fun t => ζ (q.1, Function.update q.2 i t)) t * w (q.1, Function.update q.2 i t))
          =ᶠ[𝓝 (q.2 i)] fun _ => 0 := hb0.mono fun t ht => by simp [ht]
      have hb00 : deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) = 0 :=
        hb0.self_of_nhds
      rw [hzero.deriv_eq, hb00, hb0.deriv_eq]
      simp
  have hpt : ∀ q, repKernel d ζ p q * w q =
      heatKernel d (p.1 - q.1) (p.2 - q.2) *
          (deriv (fun s => ζ (s, q.2) * w (s, q.2)) q.1 -
            contOp d (fun y => ζ (q.1, y) * w (q.1, y)) q.2) +
        1 / (d : ℝ) * ∑ i, deriv (fun t => H i (q.1, Function.update q.2 i t)) (q.2 i) := by
    intro q
    simp only [hE]
    by_cases hqO : q ∈ O
    · obtain ⟨W, hW, hWw⟩ := exists_contDiff_eventuallyEq hO hw.1 hqO
      have hvW : (fun y => ζ y * w y) =ᶠ[𝓝 q] fun y => ζ y * W y :=
        hWw.mono fun y hy => by simp only [hy]
      have hWq : W q = w q := hWw.self_of_nhds
      have hWd : Differentiable ℝ W := hW.differentiable (by simp)
      have ht : deriv (fun s => ζ (s, q.2) * w (s, q.2)) q.1 =
          deriv (fun s => ζ (s, q.2)) q.1 * w q + ζ q * contOp d (fun y => w (q.1, y)) q.2 := by
        rw [deriv_slice_time_congr hvW, deriv_fun_mul
          (hasDerivAt_slice_time hζd q.1 q.2).differentiableAt
          (hasDerivAt_slice_time hWd q.1 q.2).differentiableAt,
          deriv_slice_time_congr hWw, (hw.2 q hqO).deriv]
        simp only [Prod.mk.eta, hWq]
      have hl : contOp d (fun y => ζ (q.1, y) * w (q.1, y)) q.2 =
          ζ q * contOp d (fun y => w (q.1, y)) q.2 + w q * contOp d (fun y => ζ (q.1, y)) q.2 +
            1 / (d : ℝ) * ∑ i, deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) *
              deriv (fun t => w (q.1, Function.update q.2 i t)) (q.2 i) := by
        rw [contOp_slice_congr hvW]
        unfold contOp
        rw [lap_slice_mul hζ hW q, hWq, lap_slice_congr hWw]
        simp only [deriv_slice_update_congr hWw]
        field_simp
      rw [ht, hl]
      unfold repKernel
      exact rep_algebra hdR _ _ _ _ _ _ _ _ _ _ rfl
    · have hz : ∀ᶠ y in 𝓝 q, ζ y = 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h => hqO (hζO h)
      have hv0 : ∀ᶠ y in 𝓝 q, ζ y * w y = 0 := hz.mono fun y hy => by rw [hy, zero_mul]
      unfold repKernel
      rw [deriv_slice_time_eq_zero hz, contOp_slice_eq_zero hz, deriv_slice_time_eq_zero hv0,
        contOp_slice_eq_zero hv0]
      simp [deriv_slice_update_eq_zero hz, deriv_deriv_slice_update_eq_zero hz]
  have hEi := fun i => integral_deriv_slice_update_eq_zero (hHs i) (hHc i) i
  have hGi : Integrable (fun q : ℝ × (Fin d → ℝ) =>
      1 / (d : ℝ) * ∑ i, deriv (fun t => H i (q.1, Function.update q.2 i t)) (q.2 i)) :=
    (integrable_finsetSum _ fun i _ => (hEi i).1).const_mul _
  have hG0 : ∫ q : ℝ × (Fin d → ℝ),
      1 / (d : ℝ) * ∑ i, deriv (fun t => H i (q.1, Function.update q.2 i t)) (q.2 i) = 0 := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hEi i).1]
    simp [fun i => (hEi i).2]
  simp_rw [hpt]
  rw [integral_add_eq_of_integral_eq_zero hGi hG0]
  have hvp : ζ (p.1, p.2) * w (p.1, p.2) = w p := by
    rw [Prod.mk.eta, hp.self_of_nhds, one_mul]
  rw [← hvp]
  exact hrep

section Bounds

variable {d : ℕ}

/-- The cutoff kernel in Fréchet form, off the diagonal or where the space gradient of the cutoff
vanishes. -/
theorem repKernel_eq_fderiv (hd : 1 ≤ d)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0})
    {ζ : ℝ × (Fin d → ℝ) → ℝ} (hζ : ContDiff ℝ ∞ ζ) {x q : ℝ × (Fin d → ℝ)}
    (h : x ≠ q ∨ ∀ i, fderiv ℝ ζ q (spaceDir d i) = 0) :
    repKernel d ζ x q = heatKernel d (x.1 - q.1) (x.2 - q.2) *
        (fderiv ℝ ζ q (timeDir d) +
          (∑ i, fderiv ℝ (fun y => fderiv ℝ ζ y (spaceDir d i)) q (spaceDir d i)) / (2 * d)) -
      1 / (d : ℝ) * ∑ i, fderiv ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) (x - q)
        (spaceDir d i) * fderiv ℝ ζ q (spaceDir d i) := by
  have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
  have hsum : ∑ i, deriv (fun t => heatKernel d (x.1 - q.1) (x.2 - Function.update q.2 i t))
        (q.2 i) * deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) =
      -∑ i, fderiv ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) (x - q) (spaceDir d i) *
        fderiv ℝ ζ q (spaceDir d i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deriv_slice_update_eq_fderiv hζd]
    rcases h with h | h
    · have hne : ((x.1 - q.1, x.2 - q.2) : ℝ × (Fin d → ℝ)) ≠ 0 := sub_ne_zero.2 h
      have hΦ : HasFDerivAt (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2)
          (fderiv ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) (x - q))
          (x.1 - q.1, x.2 - Function.update q.2 i (q.2 i)) := by
        rw [Function.update_eq_self]
        exact ((contDiffAt_heatKernel_of_ne hd hA hne).differentiableAt (by simp)).hasFDerivAt
      have hg : HasDerivAt
          (fun t : ℝ => ((x.1 - q.1, x.2 - Function.update q.2 i t) : ℝ × (Fin d → ℝ)))
          ((0 : ℝ), 0 - Pi.single i (1 : ℝ)) (q.2 i) :=
        (hasDerivAt_const (q.2 i) (x.1 - q.1)).prodMk
          ((hasDerivAt_const (q.2 i) x.2).sub (hasDerivAt_update q.2 i (q.2 i)))
      have hcomp := hΦ.comp_hasDerivAt (q.2 i) hg
      have hD : deriv (fun t => heatKernel d (x.1 - q.1) (x.2 - Function.update q.2 i t)) (q.2 i) =
          fderiv ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) (x - q)
            ((0 : ℝ), 0 - Pi.single i (1 : ℝ)) :=
        hcomp.deriv
      have hdir : (((0 : ℝ), 0 - Pi.single i (1 : ℝ)) : ℝ × (Fin d → ℝ)) = -spaceDir d i := by
        simp [spaceDir]
      rw [hD, hdir, map_neg, neg_mul]
    · rw [h i]
      simp
  unfold repKernel
  rw [hsum, (hasDerivAt_slice_time hζd q.1 q.2).deriv]
  unfold contOp
  rw [lap_slice hζ q.1 q.2]
  simp only [Prod.mk.eta]
  ring

theorem fderiv_apply_eq_zero_of_eventually_const {f : ℝ × (Fin d → ℝ) → ℝ}
    {q : ℝ × (Fin d → ℝ)} {c : ℝ} (h : ∀ᶠ y in 𝓝 q, f y = c) (v w : ℝ × (Fin d → ℝ)) :
    fderiv ℝ f q v = 0 ∧ fderiv ℝ (fun y => fderiv ℝ f y v) q w = 0 := by
  have h0 := fderiv_eventually_eq_zero h
  have h1 : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 q] fun _ => 0 := h0.mono fun y hy => by simp [hy]
  refine ⟨by simp [h0.self_of_nhds], ?_⟩
  rw [h1.fderiv_eq]
  simp

/-- A function that is `C¹` off the origin is bounded and Lipschitz on a ball whose translate by
`-q` stays in an annulus around the origin, with constants depending only on the annulus. -/
theorem exists_lip_bound {g : ℝ × (Fin d → ℝ) → ℝ} (hg : ContDiffOn ℝ 1 g {z | z ≠ 0})
    {r : ℝ} (R : ℝ) (hr : 0 < r) :
    ∃ M, 0 ≤ M ∧ ∀ c q : ℝ × (Fin d → ℝ), (∀ y ∈ ball c r, r ≤ ‖y - q‖ ∧ ‖y - q‖ ≤ R) →
      ∀ a ∈ ball c r, ∀ b ∈ ball c r, |g (a - q)| ≤ M ∧ |g (b - q) - g (a - q)| ≤ M * ‖b - a‖ := by
  obtain ⟨S, hSdef⟩ : ∃ S : Set (ℝ × (Fin d → ℝ)), S = closedBall 0 R ∩ {z | r ≤ ‖z‖} :=
    ⟨_, rfl⟩
  have hS : IsCompact S := by
    rw [hSdef]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hS0 : S ⊆ {z | z ≠ 0} := by
    rw [hSdef]
    rintro z ⟨-, hz⟩ rfl
    have h0 : r ≤ ‖(0 : ℝ × (Fin d → ℝ))‖ := hz
    rw [norm_zero] at h0
    linarith
  have hmem : ∀ c q : ℝ × (Fin d → ℝ), (∀ y ∈ ball c r, r ≤ ‖y - q‖ ∧ ‖y - q‖ ≤ R) →
      ∀ y ∈ ball c r, y - q ∈ S := fun c q hcq y hy => by
    rw [hSdef]
    exact ⟨mem_closedBall_zero_iff.2 (hcq y hy).2, (hcq y hy).1⟩
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn (hg.continuousOn.mono hS0)
  obtain ⟨M₂, hM₂⟩ := hS.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen isOpen_ne le_rfl).mono hS0)
  refine ⟨max (max M₁ M₂) 0, le_max_right _ _, fun c q hcq a ha b hb => ⟨?_, ?_⟩⟩
  · have h := hM₁ (a - q) (hmem c q hcq a ha)
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hdiff : ∀ y ∈ ball c r, DifferentiableAt ℝ (fun y => g (y - q)) y := by
      intro y hy
      have hne : y - q ≠ 0 := hS0 (hmem c q hcq y hy)
      exact ((hg.differentiableOn one_ne_zero).differentiableAt (isOpen_ne.mem_nhds hne)).comp y
        (differentiableAt_id.sub_const q)
    have hbound : ∀ y ∈ ball c r, ‖fderiv ℝ (fun y => g (y - q)) y‖ ≤ max (max M₁ M₂) 0 := by
      intro y hy
      rw [fderiv_comp_sub]
      exact (hM₂ (y - q) (hmem c q hcq y hy)).trans ((le_max_right _ _).trans (le_max_left _ _))
    have h := (convex_ball c r).norm_image_sub_le_of_norm_fderiv_le hdiff hbound ha hb
    simp only [Real.norm_eq_abs] at h
    exact h

theorem abs_mul_sub_mul_sum_le {Φa A MΦ MA : ℝ} {ψ B Mψ MB : Fin d → ℝ} (h1 : |Φa| ≤ MΦ)
    (h2 : |A| ≤ MA) (h3 : ∀ i, |ψ i| ≤ Mψ i) (h4 : ∀ i, |B i| ≤ MB i) (hMΦ : 0 ≤ MΦ)
    (hMψ : ∀ i, 0 ≤ Mψ i) (hd : 0 < (d : ℝ)) :
    |Φa * A - 1 / d * ∑ i, ψ i * B i| ≤ MΦ * MA + 1 / d * ∑ i, Mψ i * MB i := by
  have h := norm_sub_le (Φa * A) (1 / d * ∑ i, ψ i * B i)
  simp only [Real.norm_eq_abs] at h
  refine h.trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hMΦ
  · rw [abs_mul, abs_of_pos (one_div_pos.2 hd)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (one_div_pos.2 hd).le
    rw [abs_mul]
    exact mul_le_mul (h3 i) (h4 i) (abs_nonneg _) (hMψ i)

end Bounds

/-- **Interior bounds** for classical solutions of the heat equation by their local `L¹` norm,
assuming the smoothness of the heat kernel off `{x = 0}` and the Duhamel formula. -/
theorem heatInteriorBounds_of_duhamel
    (hA : ∀ d : ℕ, 1 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0})
    (hbd : ∀ (d : ℕ) (n : ℕ) (ρ T : ℝ), 1 ≤ d → 0 < ρ → 0 < T → ∃ C : ℝ, ∀ p : ℝ × (Fin d → ℝ),
      0 < p.1 → p.1 ≤ T → ρ ≤ ‖p.2‖ →
        ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤ C)
    (hD : ∀ d : ℕ, 1 ≤ d → ∀ v : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
      HasCompactSupport v → ∀ (t : ℝ) (x : Fin d → ℝ), v (t, x) =
        ∫ q : ℝ × (Fin d → ℝ), heatKernel d (t - q.1) (x - q.2) *
          (deriv (fun s => v (s, q.2)) q.1 - contOp d (fun y => v (q.1, y)) q.2)) :
    ∀ (d : ℕ), 1 ≤ d → ∀ (O : Set (ℝ × (Fin d → ℝ))), IsOpen O → ∀ K : Set (ℝ × (Fin d → ℝ)),
      IsCompact K → K ⊆ O → ∃ (K' : Set (ℝ × (Fin d → ℝ))) (C : ℝ), IsCompact K' ∧ K' ⊆ O ∧
        ∀ w : ℝ × (Fin d → ℝ) → ℝ, IsClassicalHeat d O w → ∀ p ∈ K,
          |w p| ≤ C * ∫ q in K', |w q| ∧ ‖fderiv ℝ w p‖ ≤ C * ∫ q in K', |w q| := by
  intro d hd O hO K hK hKO
  have hA' := hA d hd
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = δ / 4 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; linarith
  obtain ⟨ζ, hζ, -, hζ0, hζ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞))
    (s := (thickening (3 * r) K)ᶜ) (t := cthickening (2 * r) K) isOpen_thickening.isClosed_compl
    isClosed_cthickening (disjoint_compl_left_iff_subset.2
      (cthickening_subset_thickening' (by linarith) (by linarith) K))
  have hsupp : tsupport ζ ⊆ cthickening (3 * r) K := by
    refine closure_minimal (fun x hx => thickening_subset_cthickening _ _ ?_) isClosed_cthickening
    by_contra hxK
    exact (Function.mem_support.1 hx) ((hζ0 x).1 hxK)
  have hK'c : IsCompact (tsupport ζ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport ζ) hsupp
  have hζc : HasCompactSupport ζ := hK'c
  have hK'O : tsupport ζ ⊆ O :=
    hsupp.trans ((cthickening_mono (by rw [hr_def]; linarith) K).trans hδO)
  have hone : ∀ x ∈ thickening (2 * r) K, ∀ᶠ y in 𝓝 x, ζ y = 1 := fun x hx =>
    Filter.eventually_of_mem (isOpen_thickening.mem_nhds hx) fun y hy =>
      (hζ1 y).1 (thickening_subset_cthickening _ _ hy)
  have hthick : ∀ p₀ ∈ K, ∀ y ∈ ball p₀ r, y ∈ thickening (2 * r) K := fun p₀ hp₀ y hy =>
    mem_thickening_iff.2 ⟨p₀, hp₀, (mem_ball.1 hy).trans (by linarith)⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ × (Fin d → ℝ) → ℝ, A = fun q => fderiv ℝ ζ q (timeDir d) +
      (∑ i, fderiv ℝ (fun y => fderiv ℝ ζ y (spaceDir d i)) q (spaceDir d i)) / (2 * d) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Fin d → ℝ × (Fin d → ℝ) → ℝ,
      B = fun i q => fderiv ℝ ζ q (spaceDir d i) := ⟨_, rfl⟩
  have hAc : Continuous A := by
    rw [hAdef]
    exact (contDiff_fderiv_apply hζ _).continuous.add ((continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply (contDiff_fderiv_apply hζ _) _).continuous).div_const _)
  have hBc : ∀ i, Continuous (B i) := fun i => by
    rw [hBdef]
    exact (contDiff_fderiv_apply hζ _).continuous
  have hdead : ∀ q, (q ∈ thickening (2 * r) K ∨ q ∉ tsupport ζ) → A q = 0 ∧ ∀ i, B i q = 0 := by
    intro q hq
    obtain ⟨c, hc⟩ : ∃ c, ∀ᶠ y in 𝓝 q, ζ y = c := by
      rcases hq with hq | hq
      · exact ⟨1, hone q hq⟩
      · exact ⟨0, notMem_tsupport_iff_eventuallyEq.1 hq⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [hAdef]
      simp only [(fderiv_apply_eq_zero_of_eventually_const hc (timeDir d) 0).1,
        fun i => (fderiv_apply_eq_zero_of_eventually_const hc (spaceDir d i) (spaceDir d i)).2]
      simp
    · rw [hBdef]
      exact (fderiv_apply_eq_zero_of_eventually_const hc (spaceDir d i) 0).1
  have hbd1 : ∀ F : ℝ × (Fin d → ℝ) → ℝ, Continuous F → (∀ q, q ∉ tsupport ζ → F q = 0) →
      ∃ M, 0 ≤ M ∧ ∀ q, |F q| ≤ M := by
    intro F hF hF0
    obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun q => ?_⟩
    by_cases hq : q ∈ tsupport ζ
    · exact (by simpa [Real.norm_eq_abs] using hM q hq : |F q| ≤ M).trans (le_max_left _ _)
    · rw [hF0 q hq, abs_zero]
      exact le_max_right _ _
  obtain ⟨MA, hMA0, hMA⟩ := hbd1 A hAc fun q hq => (hdead q (Or.inr hq)).1
  have hMBex : ∀ i, ∃ M, 0 ≤ M ∧ ∀ q, |B i q| ≤ M := fun i =>
    hbd1 (B i) (hBc i) fun q hq => (hdead q (Or.inr hq)).2 i
  choose MB hMB0 hMB using hMBex
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ × (Fin d → ℝ) → ℝ, Φ = fun z => heatKernel d z.1 z.2 := ⟨_, rfl⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin d → ℝ × (Fin d → ℝ) → ℝ, ψ = fun i z =>
      fderiv ℝ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) z (spaceDir d i) := ⟨_, rfl⟩
  have hΦsm : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) {z | z ≠ 0} :=
    fun z hz => (contDiffAt_heatKernel_of_ne hd hA' hz).contDiffWithinAt
  have hΦs : ContDiffOn ℝ 1 Φ {z | z ≠ 0} := by
    rw [hΦdef]
    exact hΦsm.of_le (by simp)
  have hψs : ∀ i, ContDiffOn ℝ 1 (ψ i) {z | z ≠ 0} := fun i => by
    rw [hψdef]
    exact (hΦsm.fderiv_of_isOpen isOpen_ne (by simp)).clm_apply contDiffOn_const
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := hK'c.isBounded.subset_closedBall 0
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_lip_bound hΦs (R₁ + r + R₂) hr
  have hMψex := fun i => exists_lip_bound (hψs i) (R₁ + r + R₂) hr
  choose Mψ hMψ0 hMψ using hMψex
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = MΦ * MA + 1 / (d : ℝ) * ∑ i, Mψ i * MB i := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact add_nonneg (mul_nonneg hMΦ0 hMA0) (mul_nonneg (one_div_pos.2 hdpos).le
      (Finset.sum_nonneg fun i _ => mul_nonneg (hMψ0 i) (hMB0 i)))
  have hlive : ∀ p₀ ∈ K, ∀ q, q ∉ thickening (2 * r) K → q ∈ tsupport ζ →
      ∀ y ∈ ball p₀ r, r ≤ ‖y - q‖ ∧ ‖y - q‖ ≤ R₁ + r + R₂ := by
    intro p₀ hp₀ q hq hqK y hy
    have hy' : dist y p₀ < r := hy
    have h1 : 2 * r ≤ dist q p₀ := by
      by_contra hlt
      exact hq (mem_thickening_iff.2 ⟨p₀, hp₀, not_le.1 hlt⟩)
    have hp₀R : ‖p₀‖ ≤ R₁ := mem_closedBall_zero_iff.1 (hR₁ hp₀)
    have hqR : ‖q‖ ≤ R₂ := mem_closedBall_zero_iff.1 (hR₂ hqK)
    have h2 : dist p₀ q ≤ ‖p₀‖ + ‖q‖ := by
      rw [dist_eq_norm]
      exact norm_sub_le _ _
    rw [← dist_eq_norm]
    constructor
    · linarith [dist_triangle q y p₀, dist_comm q y]
    · linarith [dist_triangle y p₀ q]
  have hform : ∀ y ∈ thickening (2 * r) K, ∀ q, repKernel d ζ y q =
      Φ (y - q) * A q - 1 / (d : ℝ) * ∑ i, ψ i (y - q) * B i q := by
    intro y hy q
    have h : y ≠ q ∨ ∀ i, fderiv ℝ ζ q (spaceDir d i) = 0 := by
      by_cases hyq : y = q
      · refine Or.inr fun i => ?_
        have := (hdead q (Or.inl (hyq ▸ hy))).2 i
        rw [hBdef] at this
        exact this
      · exact Or.inl hyq
    rw [repKernel_eq_fderiv hd hA' hζ h]
    subst hAdef hBdef hΦdef hψdef
    rfl
  have hker : ∀ p₀ ∈ K, ∀ a ∈ ball p₀ r, ∀ b ∈ ball p₀ r, ∀ q,
      |repKernel d ζ a q| ≤ C₁ ∧ |repKernel d ζ b q - repKernel d ζ a q| ≤ C₁ * ‖b - a‖ ∧
        (q ∉ tsupport ζ → repKernel d ζ a q = 0) := by
    intro p₀ hp₀ a ha b hb q
    rw [hform a (hthick p₀ hp₀ a ha), hform b (hthick p₀ hp₀ b hb)]
    by_cases hq : q ∈ thickening (2 * r) K ∨ q ∉ tsupport ζ
    · obtain ⟨hA0, hB0⟩ := hdead q hq
      have h0 : ∀ y, Φ (y - q) * A q - 1 / (d : ℝ) * ∑ i, ψ i (y - q) * B i q = 0 := fun y => by
        simp [hA0, hB0]
      rw [h0 a, h0 b, sub_zero, abs_zero]
      exact ⟨hC₁0, mul_nonneg hC₁0 (norm_nonneg _), fun _ => rfl⟩
    · rw [not_or, not_not] at hq
      have hd' := hlive p₀ hp₀ q hq.1 hq.2
      refine ⟨?_, ?_, fun h => absurd hq.2 h⟩
      · rw [hC₁]
        exact abs_mul_sub_mul_sum_le (hMΦ p₀ q hd' a ha a ha).1 (hMA q)
          (fun i => (hMψ i p₀ q hd' a ha a ha).1) (fun i => hMB i q) hMΦ0 hMψ0 hdpos
      · have e : Φ (b - q) * A q - 1 / (d : ℝ) * ∑ i, ψ i (b - q) * B i q -
            (Φ (a - q) * A q - 1 / (d : ℝ) * ∑ i, ψ i (a - q) * B i q) =
            (Φ (b - q) - Φ (a - q)) * A q -
              1 / (d : ℝ) * ∑ i, (ψ i (b - q) - ψ i (a - q)) * B i q := by
          have hs : ∑ i, (ψ i (b - q) - ψ i (a - q)) * B i q =
              ∑ i, ψ i (b - q) * B i q - ∑ i, ψ i (a - q) * B i q := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => sub_mul _ _ _
          rw [hs]
          ring
        rw [e]
        refine (abs_mul_sub_mul_sum_le (hMΦ p₀ q hd' a ha b hb).2 (hMA q)
          (fun i => (hMψ i p₀ q hd' a ha b hb).2) (fun i => hMB i q)
          (mul_nonneg hMΦ0 (norm_nonneg _)) (fun i => mul_nonneg (hMψ0 i) (norm_nonneg _))
          hdpos).trans_eq ?_
        have hs : ∑ i, Mψ i * ‖b - a‖ * MB i = (∑ i, Mψ i * MB i) * ‖b - a‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hC₁, hs]
        ring
  refine ⟨tsupport ζ, C₁, hK'c, hK'O, fun w hw p₀ hp₀ => ?_⟩
  have hp₀b : p₀ ∈ ball p₀ r := mem_ball_self hr
  have hrepx : ∀ x ∈ ball p₀ r, w x = ∫ q, repKernel d ζ x q * w q := fun x hx =>
    heatRepresentation_of_duhamel hA hbd hD d hd O hO ζ w hζ hζc hK'O hw x
      (hone x (hthick p₀ hp₀ x hx))
  have hwK' : ContinuousOn w (tsupport ζ) := hw.1.continuousOn.mono hK'O
  have hmK' : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  have hgi : Integrable ((tsupport ζ).indicator fun q => |w q|) :=
    (integrable_indicator_iff hmK').2 (hwK'.abs.integrableOn_compact hK'c)
  have hgint : ∫ q, (tsupport ζ).indicator (fun q => |w q|) q = ∫ q in tsupport ζ, |w q| :=
    integral_indicator hmK'
  have hbound : ∀ x ∈ ball p₀ r, ∀ q,
      ‖repKernel d ζ x q * w q‖ ≤ C₁ * (tsupport ζ).indicator (fun q => |w q|) q := by
    intro x hx q
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hq : q ∈ tsupport ζ
    · rw [indicator_of_mem hq]
      exact mul_le_mul_of_nonneg_right (hker p₀ hp₀ x hx x hx q).1 (abs_nonneg _)
    · rw [indicator_of_notMem hq, (hker p₀ hp₀ x hx x hx q).2.2 hq]
      simp
  have hΦm : Measurable Φ := by
    rw [hΦdef]
    unfold heatKernel
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) (by fun_prop)
      measurable_const
  have hmeas : ∀ x ∈ ball p₀ r, AEStronglyMeasurable (fun q => repKernel d ζ x q * w q) := by
    intro x hx
    have heq : (fun q => repKernel d ζ x q * w q) = fun q =>
        (Φ (x - q) * A q - 1 / (d : ℝ) * ∑ i, ψ i (x - q) * B i q) *
          (tsupport ζ).indicator w q := by
      funext q
      by_cases hq : q ∈ tsupport ζ
      · rw [indicator_of_mem hq, hform x (hthick p₀ hp₀ x hx) q]
      · rw [indicator_of_notMem hq, (hker p₀ hp₀ x hx x hx q).2.2 hq, zero_mul, mul_zero]
    rw [heq]
    have hsubm : Measurable fun q : ℝ × (Fin d → ℝ) => x - q :=
      (continuous_const.sub continuous_id).measurable
    refine AEStronglyMeasurable.mul (Measurable.aestronglyMeasurable ?_)
      ((aestronglyMeasurable_indicator_iff hmK').2 (hwK'.aestronglyMeasurable hmK'))
    refine ((hΦm.comp hsubm).mul hAc.measurable).sub (measurable_const.mul
      (Finset.measurable_fun_sum _ fun i _ => ?_))
    have hψm : Measurable (ψ i) := by
      rw [hψdef]
      exact measurable_fderiv_apply_const (𝕜 := ℝ)
        (f := fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) (spaceDir d i)
    exact (hψm.comp hsubm).mul (hBc i).measurable
  have hint : ∀ x ∈ ball p₀ r, Integrable (fun q => repKernel d ζ x q * w q) := fun x hx =>
    (hgi.const_mul C₁).mono' (hmeas x hx) (ae_of_all _ (hbound x hx))
  refine ⟨?_, ?_⟩
  · rw [hrepx p₀ hp₀b, ← Real.norm_eq_abs, ← hgint, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hgi.const_mul C₁) (ae_of_all _ (hbound p₀ hp₀b))
  · have hdiff : DifferentiableAt ℝ w p₀ :=
      (hw.1.contDiffAt (hO.mem_nhds (hKO hp₀))).differentiableAt (by simp)
    refine hdiff.hasFDerivAt.le_of_lip'
      (mul_nonneg hC₁0 (integral_nonneg fun q => abs_nonneg _)) ?_
    filter_upwards [ball_mem_nhds p₀ hr] with x hx
    rw [hrepx x hx, hrepx p₀ hp₀b, ← integral_sub (hint x hx) (hint p₀ hp₀b)]
    calc ‖∫ q, (repKernel d ζ x q * w q - repKernel d ζ p₀ q * w q)‖
        ≤ ∫ q, C₁ * ‖x - p₀‖ * (tsupport ζ).indicator (fun q => |w q|) q := by
          refine norm_integral_le_of_norm_le (hgi.const_mul _) (ae_of_all _ fun q => ?_)
          rw [← sub_mul, Real.norm_eq_abs, abs_mul]
          by_cases hq : q ∈ tsupport ζ
          · rw [indicator_of_mem hq]
            exact mul_le_mul_of_nonneg_right (hker p₀ hp₀ p₀ hp₀b x hx q).2.1 (abs_nonneg _)
          · rw [indicator_of_notMem hq, (hker p₀ hp₀ x hx x hx q).2.2 hq,
              (hker p₀ hp₀ p₀ hp₀b p₀ hp₀b q).2.2 hq]
            simp
      _ = C₁ * (∫ q in tsupport ζ, |w q|) * ‖x - p₀‖ := by
          rw [integral_const_mul, hgint]
          ring

end LatticeProb.Heat
