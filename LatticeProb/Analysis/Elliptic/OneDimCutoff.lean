import LatticeProb.Analysis.Elliptic.OneDimExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Smooth cutoffs for one-dimensional extensions

A smooth cutoff equals one on a neighborhood of the closed interval and vanishes
outside a larger bounded interval. Its derivatives have global bounds. Multiplication
by this cutoff turns the interval extension into a compactly supported C² function.
-/

namespace LatticeProb.Elliptic

open Set
open scoped ContDiff

noncomputable section

/-- Every derivative of a compactly supported smooth real function has compact support
and a finite global absolute bound. -/
theorem smooth_compact_iteratedDeriv_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |iteratedDeriv k f t| ≤ B := by
  have hsupport : ∀ n, HasCompactSupport (iteratedDeriv n f) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hs
    | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv
  obtain ⟨B, hB⟩ := (hsupport k).exists_bound_of_continuous
    (hf.continuous_iteratedDeriv k
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k))
  refine ⟨hsupport k, B, ?_, ?_⟩
  · exact (norm_nonneg _).trans (hB 0)
  · intro t
    simpa only [Real.norm_eq_abs] using hB t

/-- A smooth interval cutoff has a unit plateau on the enlarged closed interval,
support in the twice enlarged open interval, and bounded derivatives of every order. -/
theorem exists_smooth_interval_cutoff {α β : ℝ} (hαβ : α < β) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ t ∈ Icc (α - 1) (β + 1), χ t = 1) ∧
      Function.support χ ⊆ Ioo (α - 2) (β + 2) ∧
      ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |iteratedDeriv k χ t| ≤ B := by
  let χ : ContDiffBump ((α + β) / 2) :=
    { rIn := (β - α) / 2 + 1
      rOut := (β - α) / 2 + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, fun t => ⟨χ.nonneg, χ.le_one⟩,
    ?_, ?_, fun k => (smooth_compact_iteratedDeriv_bound χ.contDiff
      χ.hasCompactSupport k).2⟩
  · intro t ht
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -( (β - α) / 2 + 1) ≤ t - (α + β) / 2 ∧
      t - (α + β) / 2 ≤ (β - α) / 2 + 1
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    rw [χ.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    change -( (β - α) / 2 + 2) < t - (α + β) / 2 ∧
      t - (α + β) / 2 < (β - α) / 2 + 2 at ht
    constructor <;> linarith [ht.1, ht.2]

/-- Every derivative of a compactly supported smooth function is globally Lipschitz,
with a finite nonnegative real constant. -/
theorem smooth_compact_iteratedDeriv_lipschitz {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s t,
      |iteratedDeriv k f s - iteratedDeriv k f t| ≤ B * |s - t| := by
  obtain ⟨_, B, hB, hb⟩ := smooth_compact_iteratedDeriv_bound hf hs (k + 1)
  refine ⟨B, hB, fun s t => ?_⟩
  have hd := hf.differentiable_iteratedDeriv k
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
  have hh := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd x)
    (fun x _ => show ‖deriv (iteratedDeriv k f) x‖ ≤ B from by
      simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hb x)
    (mem_univ t) (mem_univ s)
  simpa only [Real.norm_eq_abs] using hh

/-- A bounded globally Lipschitz real function has a global Hölder increment bound
for every exponent between zero and one, by splitting distances at one. -/
theorem holder_bound_of_bounded_lipschitz {f : ℝ → ℝ} {M L σ : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hb : ∀ t, |f t| ≤ M)
    (hl : ∀ s t, |f s - f t| ≤ L * |s - t|) :
    ∀ s t, |f s - f t| ≤ (L + 2 * M) * |s - t| ^ σ := by
  intro s t
  have hr := Real.rpow_nonneg (abs_nonneg (s - t)) σ
  by_cases hd : |s - t| ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (abs_nonneg (s - t)) hd hσ1
    calc
      |f s - f t| ≤ L * |s - t| := hl s t
      _ ≤ L * |s - t| ^ σ := mul_le_mul_of_nonneg_left hp hL
      _ ≤ (L + 2 * M) * |s - t| ^ σ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hr
  · have hp : 1 ≤ |s - t| ^ σ := Real.one_le_rpow (le_of_not_ge hd) hσ
    have hb' : |f s - f t| ≤ 2 * M := by
      calc
        |f s - f t| ≤ |f s| + |f t| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hb s, hb t]
    calc
      |f s - f t| ≤ 2 * M := hb'
      _ ≤ (2 * M) * |s - t| ^ σ := le_mul_of_one_le_right (by positivity) hp
      _ ≤ (L + 2 * M) * |s - t| ^ σ :=
        mul_le_mul_of_nonneg_right (by linarith) hr

/-- Each derivative of a smooth compactly supported real function has a finite global
Hölder constant for exponents between zero and one. -/
theorem smooth_compact_iteratedDeriv_holder {f : ℝ → ℝ} {σ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (k : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ s t,
      |iteratedDeriv k f s - iteratedDeriv k f t| ≤ H * |s - t| ^ σ := by
  obtain ⟨_, M, hM, hb⟩ := smooth_compact_iteratedDeriv_bound hf hs k
  obtain ⟨L, hL, hl⟩ := smooth_compact_iteratedDeriv_lipschitz hf hs k
  exact ⟨L + 2 * M, by positivity,
    holder_bound_of_bounded_lipschitz hM hL hσ hσ1 hb hl⟩

/-- The Hölder increment bound for a product follows from the supremum and increment
bounds of both factors, with the explicit constant `A * K + B * H`. -/
theorem holder_bound_mul {f g : ℝ → ℝ} {A B H K σ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ t, |f t| ≤ A) (hg : ∀ t, |g t| ≤ B)
    (hfH : ∀ s t, |f s - f t| ≤ H * |s - t| ^ σ)
    (hgK : ∀ s t, |g s - g t| ≤ K * |s - t| ^ σ) :
    ∀ s t, |f s * g s - f t * g t| ≤ (A * K + B * H) * |s - t| ^ σ := by
  intro s t
  calc
    |f s * g s - f t * g t| =
        |f s * (g s - g t) + g t * (f s - f t)| := by congr 1; ring
    _ ≤ |f s| * |g s - g t| + |g t| * |f s - f t| := by
      simpa only [abs_mul] using
        abs_add_le (f s * (g s - g t)) (g t * (f s - f t))
    _ ≤ A * (K * |s - t| ^ σ) + B * (H * |s - t| ^ σ) := by
      exact add_le_add
        (mul_le_mul (hf s) (hgK s t) (abs_nonneg _) hA)
        (mul_le_mul (hg t) (hfH s t) (abs_nonneg _) hB)
    _ = (A * K + B * H) * |s - t| ^ σ := by ring

/-- The scalar second derivative of a product of C² functions has the three
Leibniz terms used in the cutoff estimate. -/
theorem second_deriv_mul {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun x => f x * g x)) t =
      deriv (deriv f) t * g t + 2 * deriv f t * deriv g t +
        f t * deriv (deriv g) t := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hg' : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hfd' : Differentiable ℝ (deriv f) := hf'.differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) := hg'.differentiable (by norm_num)
  have hfirst : deriv (fun x => f x * g x) =
      fun x => deriv f x * g x + f x * deriv g x := by
    funext x
    exact deriv_mul (hfd x) (hgd x)
  rw [hfirst]
  have hd := (((hfd' t).hasDerivAt.mul (hgd t).hasDerivAt).add
    ((hfd t).hasDerivAt.mul (hgd' t).hasDerivAt)).deriv
  calc
    _ = _ := hd
    _ = _ := by ring

/-- A finite interior Hölder norm admits a compactly supported global C² extension
agreeing on the original interval. This assertion makes no quantitative norm claim. -/
theorem one_dim_compact_C2_extension_of_holder {α β σ : ℝ}
    (hαβ : α < β) (hσ : 0 < σ) {u : (Fin 1 → ℝ) → ℝ}
    (hu : ContDiffOn ℝ 2 u {x | α < x 0 ∧ x 0 < β})
    (hnorm : c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u < ⊤) :
    ∃ v : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      EqOn v u {x | α < x 0 ∧ x 0 < β} ∧
      Function.support v ⊆ {x | α - 2 < x 0 ∧ x 0 < β + 2} := by
  obtain ⟨v₀, hv₀, heq, _⟩ := one_dim_C2_extension_of_holder hαβ hσ hu hnorm
  obtain ⟨χ, hχ, hs, _, hplateau, hsupp, _⟩ := exists_smooth_interval_cutoff hαβ
  let ψ : (Fin 1 → ℝ) → ℝ := fun x => χ (x 0)
  have hψ : ContDiff ℝ 2 ψ := (hχ.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (by fun_prop)
  have hsψ : HasCompactSupport ψ := by
    exact hs.comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)
  refine ⟨fun x => ψ x * v₀ x, hψ.mul hv₀, hsψ.mul_right, ?_, ?_⟩
  · intro x hx
    have hp : χ (x 0) = 1 := hplateau _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [ψ, hp, one_mul] using heq hx
  · intro x hx
    have hp : χ (x 0) ≠ 0 := (mul_ne_zero_iff.mp hx).1
    exact hsupp hp

/-- A bounded Lipschitz function on a closed interval has a Hölder increment bound
there, with the same explicit near/far constant as on the whole line. -/
theorem holder_bound_on_Icc_of_bounded_lipschitz {f : ℝ → ℝ} {a b M L σ : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hb : ∀ t ∈ Icc a b, |f t| ≤ M)
    (hl : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f s - f t| ≤ L * |s - t|) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |f s - f t| ≤ (L + 2 * M) * |s - t| ^ σ := by
  let p : ℝ → ℝ := fun t => max a (min b t)
  have hp (t : ℝ) : p t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have heq (t : ℝ) (ht : t ∈ Icc a b) : p t = t := by
    dsimp [p]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hLip : LipschitzWith 1 p := (LipschitzWith.id.const_min b).const_max a
  have hdist (s t : ℝ) : |p s - p t| ≤ |s - t| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip.dist_le_mul s t
  have h := holder_bound_of_bounded_lipschitz hM hL hσ hσ1
    (fun t => hb _ (hp t)) (fun s t => (hl _ (hp s) _ (hp t)).trans
      (mul_le_mul_of_nonneg_left (hdist s t) hL))
  intro s hs t ht
  simpa only [heq s hs, heq t ht] using h s t

/-- A factor supported in a closed interval needs bounds for the other factor only
on that interval. Clamping supplies the global product estimate. -/
theorem holder_bound_mul_of_support_subset_Icc {f g : ℝ → ℝ} {a b A B H K σ : ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hs : Function.support f ⊆ Icc a b)
    (hf : ∀ t, |f t| ≤ A) (hg : ∀ t ∈ Icc a b, |g t| ≤ B)
    (hfH : ∀ s t, |f s - f t| ≤ H * |s - t| ^ σ)
    (hgK : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |g s - g t| ≤ K * |s - t| ^ σ) :
    ∀ s t, |f s * g s - f t * g t| ≤ (A * K + B * H) * |s - t| ^ σ := by
  let p : ℝ → ℝ := fun t => max a (min b t)
  have hp (t : ℝ) : p t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have heq (t : ℝ) : f t * g (p t) = f t * g t := by
    by_cases ht : f t = 0
    · simp only [ht, zero_mul]
    · have hm := hs ht
      have hpt : p t = t := by
        dsimp [p]
        rw [min_eq_right hm.2, max_eq_right hm.1]
      rw [hpt]
  have hLip : LipschitzWith 1 p := (LipschitzWith.id.const_min b).const_max a
  have hgH (s t : ℝ) : |g (p s) - g (p t)| ≤ K * |s - t| ^ σ := by
    apply (hgK _ (hp s) _ (hp t)).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.rpow_le_rpow (abs_nonneg _) _ hσ
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip.dist_le_mul s t
  intro s t
  simpa only [heq] using
    holder_bound_mul hA hB hf (fun t => hg _ (hp t)) hfH hgH s t

/-- Scalar Leibniz terms with localized bounds give the global Hölder bound for the
second derivative of a cutoff product. -/
theorem second_deriv_mul_holder_of_local_bounds {χ W : ℝ → ℝ}
    {a b σ A₀ A₁ A₂ H₀ H₁ H₂ B₀ B₁ B₂ K₀ K₁ K₂ : ℝ}
    (hχ : ContDiff ℝ 2 χ) (hW : ContDiff ℝ 2 W) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hs₀ : Function.support χ ⊆ Icc a b)
    (hs₁ : Function.support (deriv χ) ⊆ Icc a b)
    (hs₂ : Function.support (deriv (deriv χ)) ⊆ Icc a b)
    (hb₀ : ∀ t, |χ t| ≤ A₀) (hb₁ : ∀ t, |deriv χ t| ≤ A₁)
    (hb₂ : ∀ t, |deriv (deriv χ) t| ≤ A₂)
    (hh₀ : ∀ s t, |χ s - χ t| ≤ H₀ * |s - t| ^ σ)
    (hh₁ : ∀ s t, |deriv χ s - deriv χ t| ≤ H₁ * |s - t| ^ σ)
    (hh₂ : ∀ s t, |deriv (deriv χ) s - deriv (deriv χ) t| ≤ H₂ * |s - t| ^ σ)
    (hw₀ : ∀ t ∈ Icc a b, |W t| ≤ B₀)
    (hw₁ : ∀ t ∈ Icc a b, |deriv W t| ≤ B₁)
    (hw₂ : ∀ t ∈ Icc a b, |deriv (deriv W) t| ≤ B₂)
    (hk₀ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |W s - W t| ≤ K₀ * |s - t| ^ σ)
    (hk₁ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv W s - deriv W t| ≤ K₁ * |s - t| ^ σ)
    (hk₂ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv (deriv W) s - deriv (deriv W) t| ≤ K₂ * |s - t| ^ σ) :
    ∀ s t, |deriv (deriv (fun x => χ x * W x)) s -
      deriv (deriv (fun x => χ x * W x)) t| ≤
        (A₂ * K₀ + B₀ * H₂ + 2 * (A₁ * K₁ + B₁ * H₁) +
          (A₀ * K₂ + B₂ * H₀)) * |s - t| ^ σ := by
  have h₀ := holder_bound_mul_of_support_subset_Icc hab hA₂ hB₀ hK₀ hσ
    hs₂ hb₂ hw₀ hh₂ hk₀
  have h₁ := holder_bound_mul_of_support_subset_Icc hab hA₁ hB₁ hK₁ hσ
    hs₁ hb₁ hw₁ hh₁ hk₁
  have h₂ := holder_bound_mul_of_support_subset_Icc hab hA₀ hB₂ hK₂ hσ
    hs₀ hb₀ hw₂ hh₀ hk₂
  intro s t
  rw [second_deriv_mul hχ hW s, second_deriv_mul hχ hW t]
  calc
    _ = |(deriv (deriv χ) s * W s - deriv (deriv χ) t * W t) +
        2 * (deriv χ s * deriv W s - deriv χ t * deriv W t) +
        (χ s * deriv (deriv W) s - χ t * deriv (deriv W) t)| := by
      congr 1
      ring
    _ ≤ |deriv (deriv χ) s * W s - deriv (deriv χ) t * W t| +
        2 * |deriv χ s * deriv W s - deriv χ t * deriv W t| +
        |χ s * deriv (deriv W) s - χ t * deriv (deriv W) t| := by
      have h := (abs_add_le
        (deriv (deriv χ) s * W s - deriv (deriv χ) t * W t)
        (2 * (deriv χ s * deriv W s - deriv χ t * deriv W t)))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
      exact (abs_add_le _ _).trans (add_le_add h le_rfl)
    _ ≤ _ := by
      have h := add_le_add (add_le_add (h₀ s t)
        (mul_le_mul_of_nonneg_left (h₁ s t) (by norm_num : (0 : ℝ) ≤ 2))) (h₂ s t)
      calc
        _ ≤ _ := h
        _ = _ := by ring

/-- The uncut extension has uniform value and slope bounds on the enlarged interval.
The common constant is fixed before the datum; the second derivative and its Hölder
increments remain bounded by the original full norm. -/
theorem one_dim_C2_extension_local_bounds {α β σ : ℝ}
    (hαβ : α < β) (hσ : 0 < σ) :
    ∃ D : ℝ, 0 < D ∧ ∀ u : (Fin 1 → ℝ) → ℝ,
      ContDiffOn ℝ 2 u {x | α < x 0 ∧ x 0 < β} →
      c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u < ⊤ →
      ∃ v : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 2 v ∧
        EqOn v u {x | α < x 0 ∧ x 0 < β} ∧
        (∀ x, |secondPartial 0 0 v x| ≤
          (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal) ∧
        (∀ x y, |secondPartial 0 0 v x - secondPartial 0 0 v y| ≤
          (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal *
            |x 0 - y 0| ^ σ) ∧
        (∀ x, x 0 ∈ Icc (α - 2) (β + 2) → |partialDeriv 0 v x| ≤
          D * (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal) ∧
        ∀ x, x 0 ∈ Icc (α - 2) (β + 2) → |v x| ≤
          D * (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal := by
  let R := β - α + 2
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨1 + R + R * R, by positivity, fun u hu hn => ?_⟩
  let I : Set (Fin 1 → ℝ) := {x | α < x 0 ∧ x 0 < β}
  let N := (c2HolderNorm σ I u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have h₀ : supNorm I u ≤ c2HolderNorm σ I u := by
    simp only [c2HolderNorm, Fin.sum_univ_one]
    exact le_self_add.trans (le_self_add.trans le_self_add)
  have h₁ : supNorm I (partialDeriv 0 u) ≤ c2HolderNorm σ I u := by
    simp only [c2HolderNorm, Fin.sum_univ_one]
    exact le_add_self.trans (le_self_add.trans le_self_add)
  have h₂ : supNorm I (secondPartial 0 0 u) ≤ c2HolderNorm σ I u := by
    simp only [c2HolderNorm, Fin.sum_univ_one]
    exact le_add_self.trans le_self_add
  have hH : holderSeminorm σ I (secondPartial 0 0 u) ≤ c2HolderNorm σ I u := by
    simp only [c2HolderNorm, Fin.sum_univ_one]
    exact le_add_self
  have h₂N := ENNReal.toReal_mono hn.ne h₂
  have hHN := ENNReal.toReal_mono hn.ne hH
  have hc : (fun _ : Fin 1 => (α + β) / 2) ∈ I := by
    constructor <;> dsimp <;> linarith
  have hv₀ : |u (fun _ => (α + β) / 2)| ≤ N :=
    (abs_le_supNorm_toReal (lt_of_le_of_lt h₀ hn) hc).trans
      (ENNReal.toReal_mono hn.ne h₀)
  have hv₁ : |partialDeriv 0 u (fun _ => (α + β) / 2)| ≤ N :=
    (abs_le_supNorm_toReal (lt_of_le_of_lt h₁ hn) hc).trans
      (ENNReal.toReal_mono hn.ne h₁)
  obtain ⟨v, hv, heq, hb, hh, hfirst, hvalue⟩ :=
    one_dim_C2_extension_of_holder hαβ hσ hu hn
  have hdist (x : Fin 1 → ℝ) (hx : x 0 ∈ Icc (α - 2) (β + 2)) :
      |x 0 - (α + β) / 2| ≤ R := by
    rw [abs_le]
    dsimp [R]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨v, hv, heq, fun x => (hb x).trans h₂N, ?_, ?_, ?_⟩
  · intro x y
    have hhxy := hh x y
    rw [radius_sub_one_dim] at hhxy
    exact hhxy.trans (mul_le_mul_of_nonneg_right hHN
      (Real.rpow_nonneg (abs_nonneg _) _))
  · intro x hx
    calc
      |partialDeriv 0 v x| ≤ N + N * R := (hfirst x).trans
        (add_le_add hv₁ (mul_le_mul h₂N (hdist x hx) (abs_nonneg _) hN))
      _ ≤ (1 + R + R * R) * N := by nlinarith [mul_nonneg hN (sq_nonneg R)]
  · intro x hx
    calc
      |v x| ≤ N + (N + N * R) * R := (hvalue x).trans
        (add_le_add hv₀ (mul_le_mul
          (add_le_add hv₁ (mul_le_mul h₂N (hdist x hx) (abs_nonneg _) hN))
          (hdist x hx) (abs_nonneg _) (by positivity)))
      _ = (1 + R + R * R) * N := by ring

/-- A supported factor converts a local bound for its partner into a global product bound. -/
theorem abs_mul_le_of_support_subset {f g : ℝ → ℝ} {S : Set ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : Function.support f ⊆ S)
    (hf : ∀ t, |f t| ≤ A) (hg : ∀ t ∈ S, |g t| ≤ B) :
    ∀ t, |f t * g t| ≤ A * B := by
  intro t
  by_cases ht : f t = 0
  · simp only [ht, zero_mul, abs_zero]
    exact mul_nonneg hA hB
  · rw [abs_mul]
    exact mul_le_mul (hf t) (hg t (hs ht)) (abs_nonneg _) hA

/-- Scalar value, slope, curvature, and curvature-increment bounds control exactly
the four components of the one-dimensional Euclidean Hölder norm. -/
theorem c2HolderNorm_le_of_scalar_bounds {v : (Fin 1 → ℝ) → ℝ}
    {σ B₀ B₁ B₂ H : ℝ} (hv : ContDiff ℝ 2 v)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hH : 0 ≤ H)
    (hb₀ : ∀ t, |v (fun _ => t)| ≤ B₀)
    (hb₁ : ∀ t, |deriv (fun s => v (fun _ => s)) t| ≤ B₁)
    (hb₂ : ∀ t, |deriv (deriv (fun s => v (fun _ => s))) t| ≤ B₂)
    (hh : ∀ s t, |deriv (deriv (fun r => v (fun _ => r))) s -
      deriv (deriv (fun r => v (fun _ => r))) t| ≤ H * |s - t| ^ σ) :
    c2HolderNorm σ univ v ≤ ENNReal.ofReal (B₀ + B₁ + B₂ + H) := by
  have hcoord (x : Fin 1 → ℝ) : (fun _ : Fin 1 => x 0) = x := by
    ext i
    fin_cases i
    rfl
  have hp (x : Fin 1 → ℝ) : partialDeriv 0 v x =
      deriv (fun s => v (fun _ => s)) (x 0) := by
    simpa only [hcoord] using
      (partialDeriv_one_dim (t := x 0) (hv.differentiable (by norm_num) (fun _ => x 0)))
  have hpp (x : Fin 1 → ℝ) : secondPartial 0 0 v x =
      deriv (deriv (fun s => v (fun _ => s))) (x 0) := by
    simpa only [laplacian, Fin.sum_univ_one, hcoord] using laplacian_one_dim v (x 0)
  have h₀ : supNorm univ v ≤ ENNReal.ofReal B₀ :=
    supNorm_le_of_abs_le fun x _ => by simpa only [hcoord] using hb₀ (x 0)
  have h₁ : supNorm univ (partialDeriv 0 v) ≤ ENNReal.ofReal B₁ :=
    supNorm_le_of_abs_le fun x _ => by rw [hp]; exact hb₁ (x 0)
  have h₂ : supNorm univ (secondPartial 0 0 v) ≤ ENNReal.ofReal B₂ :=
    supNorm_le_of_abs_le fun x _ => by rw [hpp]; exact hb₂ (x 0)
  have h₃ : holderSeminorm σ univ (secondPartial 0 0 v) ≤ ENNReal.ofReal H :=
    holderSeminorm_le_of_increment fun x _ y _ => by rw [hpp, hpp]; exact hh _ _
  simp only [c2HolderNorm, Fin.sum_univ_one]
  calc
    _ ≤ ENNReal.ofReal B₀ + ENNReal.ofReal B₁ + ENNReal.ofReal B₂ +
        ENNReal.ofReal H := add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃
    _ = ENNReal.ofReal (B₀ + B₁ + B₂ + H) := by
      rw [← ENNReal.ofReal_add hB₀ hB₁,
        ← ENNReal.ofReal_add (add_nonneg hB₀ hB₁) hB₂,
        ← ENNReal.ofReal_add (by positivity) hH]

/-- Every finite interior `C^{2,σ}` norm on an interval admits a compactly supported
extension with a global norm bound uniform in the datum. -/
theorem one_dim_holder_extension_univ {α β σ : ℝ}
    (hαβ : α < β) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin 1 → ℝ) → ℝ,
      ContDiffOn ℝ 2 u {x | α < x 0 ∧ x 0 < β} →
      c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u < ⊤ →
      ∃ v : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        Set.EqOn v u {x | α < x 0 ∧ x 0 < β} ∧
        c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C *
          c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u := by
  obtain ⟨χ, hχ, hs, _, hplateau, hsupp, hb⟩ := exists_smooth_interval_cutoff hαβ
  obtain ⟨D, hD, hext⟩ := one_dim_C2_extension_local_bounds hαβ hσ
  obtain ⟨A₀, hA₀, hb₀⟩ := hb 0
  obtain ⟨A₁, hA₁, hb₁⟩ := hb 1
  obtain ⟨A₂, hA₂, hb₂⟩ := hb 2
  obtain ⟨H₀, hH₀, hh₀⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 0
  obtain ⟨H₁, hH₁, hh₁⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 1
  obtain ⟨H₂, hH₂, hh₂⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 2
  simp only [iteratedDeriv_zero, iteratedDeriv_succ] at hb₀ hb₁ hb₂ hh₀ hh₁ hh₂
  let M := 1 + A₀ + A₁ + A₂ + H₀ + H₁ + H₂
  have hM : 0 < M := by dsimp [M]; linarith
  have hAM : A₀ ≤ M ∧ A₁ ≤ M ∧ A₂ ≤ M := by
    dsimp [M]
    constructor <;> first | constructor <;> linarith | linarith
  have hHM : H₀ ≤ M ∧ H₁ ≤ M ∧ H₂ ≤ M := by
    dsimp [M]
    constructor <;> first | constructor <;> linarith | linarith
  have hχ₂ : ContDiff ℝ 2 χ := hχ.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  let K := Icc (α - 2) (β + 2)
  have hK : α - 2 ≤ β + 2 := by linarith
  have hs₀ : Function.support χ ⊆ K := fun t ht =>
    ⟨(hsupp ht).1.le, (hsupp ht).2.le⟩
  have hts : tsupport χ ⊆ K := closure_minimal hs₀ isClosed_Icc
  have hs₁ : Function.support (deriv χ) ⊆ K := support_deriv_subset.trans hts
  have hs₂ : Function.support (deriv (deriv χ)) ⊆ K :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans hts)
  have hbχ₀ (t : ℝ) : |χ t| ≤ M := (hb₀ t).trans hAM.1
  have hbχ₁ (t : ℝ) : |deriv χ t| ≤ M := (hb₁ t).trans hAM.2.1
  have hbχ₂ (t : ℝ) : |deriv (deriv χ) t| ≤ M := (hb₂ t).trans hAM.2.2
  have hhχ₀ (s t : ℝ) : |χ s - χ t| ≤ M * |s - t| ^ σ :=
    (hh₀ s t).trans (mul_le_mul_of_nonneg_right hHM.1 (Real.rpow_nonneg (abs_nonneg _) _))
  have hhχ₁ (s t : ℝ) : |deriv χ s - deriv χ t| ≤ M * |s - t| ^ σ :=
    (hh₁ s t).trans (mul_le_mul_of_nonneg_right hHM.2.1
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hhχ₂ (s t : ℝ) : |deriv (deriv χ) s - deriv (deriv χ) t| ≤ M * |s - t| ^ σ :=
    (hh₂ s t).trans (mul_le_mul_of_nonneg_right hHM.2.2
      (Real.rpow_nonneg (abs_nonneg _) _))
  let E := D + 1
  have hE : 0 < E := by dsimp [E]; linarith
  have hDE : D ≤ E := by dsimp [E]; linarith
  have h1E : 1 ≤ E := by dsimp [E]; linarith
  refine ⟨23 * M * E, by positivity, fun u hu hn => ?_⟩
  obtain ⟨v₀, hv₀, heq, hsecond, hholder, hfirst, hvalue⟩ := hext u hu hn
  let N := (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  let W : ℝ → ℝ := fun t => v₀ (fun _ => t)
  have hW : ContDiff ℝ 2 W := hv₀.comp (by fun_prop)
  have hp (t : ℝ) : deriv W t = partialDeriv 0 v₀ (fun _ => t) :=
    (partialDeriv_one_dim (hv₀.differentiable (by norm_num) _)).symm
  have hpp (t : ℝ) : deriv (deriv W) t = secondPartial 0 0 v₀ (fun _ => t) := by
    simpa only [laplacian, Fin.sum_univ_one, W] using (laplacian_one_dim v₀ t).symm
  have hw₀ (t : ℝ) (ht : t ∈ K) : |W t| ≤ E * N :=
    (hvalue _ ht).trans (mul_le_mul_of_nonneg_right hDE hN)
  have hw₁ (t : ℝ) (ht : t ∈ K) : |deriv W t| ≤ E * N := by
    rw [hp]
    exact (hfirst _ ht).trans (mul_le_mul_of_nonneg_right hDE hN)
  have hw₂ (t : ℝ) (ht : t ∈ K) : |deriv (deriv W) t| ≤ E * N := by
    rw [hpp]
    exact (hsecond _).trans (le_mul_of_one_le_left hN h1E)
  have hconv : Convex ℝ K := convex_Icc _ _
  have hW' : ContDiff ℝ 1 (deriv W) := hW.deriv'
  have hLip₀ (s : ℝ) (hs : s ∈ K) (t : ℝ) (ht : t ∈ K) :
      |W s - W t| ≤ (E * N) * |s - t| := by
    have h := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hW.differentiable (by norm_num) x)
      (fun x hx => show ‖deriv W x‖ ≤ E * N from by
        simpa only [Real.norm_eq_abs] using hw₁ x hx) ht hs
    simpa only [Real.norm_eq_abs] using h
  have hLip₁ (s : ℝ) (hs : s ∈ K) (t : ℝ) (ht : t ∈ K) :
      |deriv W s - deriv W t| ≤ (E * N) * |s - t| := by
    have h := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hW'.differentiable (by norm_num) x)
      (fun x hx => show ‖deriv (deriv W) x‖ ≤ E * N from by
        simpa only [Real.norm_eq_abs] using hw₂ x hx) ht hs
    simpa only [Real.norm_eq_abs] using h
  have hk₀ : ∀ s ∈ K, ∀ t ∈ K, |W s - W t| ≤ (3 * E * N) * |s - t| ^ σ := by
    intro s hs t ht
    convert holder_bound_on_Icc_of_bounded_lipschitz hK
      (mul_nonneg hE.le hN) (mul_nonneg hE.le hN) hσ.le hσ1.le hw₀ hLip₀ s hs t ht
      using 1
    ring
  have hk₁ : ∀ s ∈ K, ∀ t ∈ K,
      |deriv W s - deriv W t| ≤ (3 * E * N) * |s - t| ^ σ := by
    intro s hs t ht
    convert holder_bound_on_Icc_of_bounded_lipschitz hK
      (mul_nonneg hE.le hN) (mul_nonneg hE.le hN) hσ.le hσ1.le hw₁ hLip₁ s hs t ht
      using 1
    ring
  have hk₂ (s : ℝ) (_hs : s ∈ K) (t : ℝ) (_ht : t ∈ K) :
      |deriv (deriv W) s - deriv (deriv W) t| ≤ (3 * E * N) * |s - t| ^ σ := by
    rw [hpp, hpp]
    apply (hholder (fun _ => s) (fun _ => t)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
    have hNE : N ≤ E * N := le_mul_of_one_le_left hN h1E
    nlinarith
  let V : ℝ → ℝ := fun t => χ t * W t
  let v : (Fin 1 → ℝ) → ℝ := fun x => V (x 0)
  have hv : ContDiff ℝ 2 v := (hχ₂.mul hW).comp (by fun_prop)
  have hsv : HasCompactSupport v :=
    (hs.mul_right (f' := W)).comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)
  have heqv : EqOn v u {x | α < x 0 ∧ x 0 < β} := by
    intro x hx
    have hcoord : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
    have hplate : χ (x 0) = 1 := hplateau _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [v, V, W, hplate, one_mul, hcoord] using heq hx
  have hbV₀ (t : ℝ) : |V t| ≤ M * E * N := by
    simpa only [mul_assoc, V] using
      abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₀ t
  have hbV₁ (t : ℝ) : |deriv V t| ≤ 2 * M * E * N := by
    have h := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₁ hbχ₁ hw₀ t
    have h' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₁ t
    rw [show deriv V t = deriv χ t * W t + χ t * deriv W t from
      deriv_mul (hχ₂.differentiable (by norm_num) t) (hW.differentiable (by norm_num) t)]
    exact (abs_add_le _ _).trans (by nlinarith only [h, h'])
  have hbV₂ (t : ℝ) : |deriv (deriv V) t| ≤ 4 * M * E * N := by
    have h := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₂ hbχ₂ hw₀ t
    have h' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₁ hbχ₁ hw₁ t
    have h'' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₂ t
    rw [second_deriv_mul hχ₂ hW]
    have hmid : |2 * deriv χ t * deriv W t| ≤ 2 * (M * (E * N)) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left h' (by norm_num)
    exact (abs_add_le _ _).trans
      ((add_le_add (abs_add_le _ _) le_rfl).trans (by nlinarith only [h, hmid, h'']))
  have hhV (s t : ℝ) : |deriv (deriv V) s - deriv (deriv V) t| ≤
      (16 * M * E * N) * |s - t| ^ σ := by
    have h := second_deriv_mul_holder_of_local_bounds hχ₂ hW hK hσ.le
      hM.le hM.le hM.le (mul_nonneg hE.le hN) (mul_nonneg hE.le hN)
      (mul_nonneg hE.le hN) (by positivity) (by positivity) (by positivity)
      hs₀ hs₁ hs₂ hbχ₀ hbχ₁ hbχ₂ hhχ₀ hhχ₁ hhχ₂
      hw₀ hw₁ hw₂ hk₀ hk₁ hk₂ s t
    convert h using 1
    ring
  have hnorm : c2HolderNorm σ univ v ≤ ENNReal.ofReal (23 * M * E * N) := by
    have h := c2HolderNorm_le_of_scalar_bounds hv (by positivity) (by positivity)
      (by positivity) (by positivity) hbV₀ hbV₁ hbV₂ hhV
    convert h using 1
    congr 1
    ring
  refine ⟨v, hv, hsv, heqv, hnorm.trans_eq ?_⟩
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 23 * M * E),
    ENNReal.ofReal_toReal hn.ne]

end

end LatticeProb.Elliptic

namespace LatticeProb.Elliptic

open Set
open scoped ContDiff

noncomputable section

/-- Every finite interior `C^{2,σ}` norm admits a global extension vanishing outside
the twice enlarged interval, with a norm bound uniform in the datum. -/
theorem one_dim_holder_extension_support {α β σ : ℝ}
    (hαβ : α < β) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin 1 → ℝ) → ℝ,
      ContDiffOn ℝ 2 u {x | α < x 0 ∧ x 0 < β} →
      c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u < ⊤ →
      ∃ v : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 2 v ∧
        (∀ x : Fin 1 → ℝ, (x 0 ≤ α - 2 ∨ β + 2 ≤ x 0) → v x = 0) ∧
        Set.EqOn v u {x | α < x 0 ∧ x 0 < β} ∧
        c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C *
          c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u := by
  obtain ⟨χ, hχ, hs, _, hplateau, hsupp, hb⟩ := exists_smooth_interval_cutoff hαβ
  obtain ⟨D, hD, hext⟩ := one_dim_C2_extension_local_bounds hαβ hσ
  obtain ⟨A₀, hA₀, hb₀⟩ := hb 0
  obtain ⟨A₁, hA₁, hb₁⟩ := hb 1
  obtain ⟨A₂, hA₂, hb₂⟩ := hb 2
  obtain ⟨H₀, hH₀, hh₀⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 0
  obtain ⟨H₁, hH₁, hh₁⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 1
  obtain ⟨H₂, hH₂, hh₂⟩ := smooth_compact_iteratedDeriv_holder hχ hs hσ.le hσ1.le 2
  simp only [iteratedDeriv_zero, iteratedDeriv_succ] at hb₀ hb₁ hb₂ hh₀ hh₁ hh₂
  let M := 1 + A₀ + A₁ + A₂ + H₀ + H₁ + H₂
  have hM : 0 < M := by dsimp [M]; linarith
  have hAM : A₀ ≤ M ∧ A₁ ≤ M ∧ A₂ ≤ M := by
    dsimp [M]
    constructor <;> first | constructor <;> linarith | linarith
  have hHM : H₀ ≤ M ∧ H₁ ≤ M ∧ H₂ ≤ M := by
    dsimp [M]
    constructor <;> first | constructor <;> linarith | linarith
  have hχ₂ : ContDiff ℝ 2 χ := hχ.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  let K := Icc (α - 2) (β + 2)
  have hK : α - 2 ≤ β + 2 := by linarith
  have hs₀ : Function.support χ ⊆ K := fun t ht =>
    ⟨(hsupp ht).1.le, (hsupp ht).2.le⟩
  have hts : tsupport χ ⊆ K := closure_minimal hs₀ isClosed_Icc
  have hs₁ : Function.support (deriv χ) ⊆ K := support_deriv_subset.trans hts
  have hs₂ : Function.support (deriv (deriv χ)) ⊆ K :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans hts)
  have hbχ₀ (t : ℝ) : |χ t| ≤ M := (hb₀ t).trans hAM.1
  have hbχ₁ (t : ℝ) : |deriv χ t| ≤ M := (hb₁ t).trans hAM.2.1
  have hbχ₂ (t : ℝ) : |deriv (deriv χ) t| ≤ M := (hb₂ t).trans hAM.2.2
  have hhχ₀ (s t : ℝ) : |χ s - χ t| ≤ M * |s - t| ^ σ :=
    (hh₀ s t).trans (mul_le_mul_of_nonneg_right hHM.1 (Real.rpow_nonneg (abs_nonneg _) _))
  have hhχ₁ (s t : ℝ) : |deriv χ s - deriv χ t| ≤ M * |s - t| ^ σ :=
    (hh₁ s t).trans (mul_le_mul_of_nonneg_right hHM.2.1
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hhχ₂ (s t : ℝ) : |deriv (deriv χ) s - deriv (deriv χ) t| ≤ M * |s - t| ^ σ :=
    (hh₂ s t).trans (mul_le_mul_of_nonneg_right hHM.2.2
      (Real.rpow_nonneg (abs_nonneg _) _))
  let E := D + 1
  have hE : 0 < E := by dsimp [E]; linarith
  have hDE : D ≤ E := by dsimp [E]; linarith
  have h1E : 1 ≤ E := by dsimp [E]; linarith
  refine ⟨23 * M * E, by positivity, fun u hu hn => ?_⟩
  obtain ⟨v₀, hv₀, heq, hsecond, hholder, hfirst, hvalue⟩ := hext u hu hn
  let N := (c2HolderNorm σ {x | α < x 0 ∧ x 0 < β} u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  let W : ℝ → ℝ := fun t => v₀ (fun _ => t)
  have hW : ContDiff ℝ 2 W := hv₀.comp (by fun_prop)
  have hp (t : ℝ) : deriv W t = partialDeriv 0 v₀ (fun _ => t) :=
    (partialDeriv_one_dim (hv₀.differentiable (by norm_num) _)).symm
  have hpp (t : ℝ) : deriv (deriv W) t = secondPartial 0 0 v₀ (fun _ => t) := by
    simpa only [laplacian, Fin.sum_univ_one, W] using (laplacian_one_dim v₀ t).symm
  have hw₀ (t : ℝ) (ht : t ∈ K) : |W t| ≤ E * N :=
    (hvalue _ ht).trans (mul_le_mul_of_nonneg_right hDE hN)
  have hw₁ (t : ℝ) (ht : t ∈ K) : |deriv W t| ≤ E * N := by
    rw [hp]
    exact (hfirst _ ht).trans (mul_le_mul_of_nonneg_right hDE hN)
  have hw₂ (t : ℝ) (ht : t ∈ K) : |deriv (deriv W) t| ≤ E * N := by
    rw [hpp]
    exact (hsecond _).trans (le_mul_of_one_le_left hN h1E)
  have hconv : Convex ℝ K := convex_Icc _ _
  have hW' : ContDiff ℝ 1 (deriv W) := hW.deriv'
  have hLip₀ (s : ℝ) (hs : s ∈ K) (t : ℝ) (ht : t ∈ K) :
      |W s - W t| ≤ (E * N) * |s - t| := by
    have h := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hW.differentiable (by norm_num) x)
      (fun x hx => show ‖deriv W x‖ ≤ E * N from by
        simpa only [Real.norm_eq_abs] using hw₁ x hx) ht hs
    simpa only [Real.norm_eq_abs] using h
  have hLip₁ (s : ℝ) (hs : s ∈ K) (t : ℝ) (ht : t ∈ K) :
      |deriv W s - deriv W t| ≤ (E * N) * |s - t| := by
    have h := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hW'.differentiable (by norm_num) x)
      (fun x hx => show ‖deriv (deriv W) x‖ ≤ E * N from by
        simpa only [Real.norm_eq_abs] using hw₂ x hx) ht hs
    simpa only [Real.norm_eq_abs] using h
  have hk₀ : ∀ s ∈ K, ∀ t ∈ K, |W s - W t| ≤ (3 * E * N) * |s - t| ^ σ := by
    intro s hs t ht
    convert holder_bound_on_Icc_of_bounded_lipschitz hK
      (mul_nonneg hE.le hN) (mul_nonneg hE.le hN) hσ.le hσ1.le hw₀ hLip₀ s hs t ht
      using 1
    ring
  have hk₁ : ∀ s ∈ K, ∀ t ∈ K,
      |deriv W s - deriv W t| ≤ (3 * E * N) * |s - t| ^ σ := by
    intro s hs t ht
    convert holder_bound_on_Icc_of_bounded_lipschitz hK
      (mul_nonneg hE.le hN) (mul_nonneg hE.le hN) hσ.le hσ1.le hw₁ hLip₁ s hs t ht
      using 1
    ring
  have hk₂ (s : ℝ) (_hs : s ∈ K) (t : ℝ) (_ht : t ∈ K) :
      |deriv (deriv W) s - deriv (deriv W) t| ≤ (3 * E * N) * |s - t| ^ σ := by
    rw [hpp, hpp]
    apply (hholder (fun _ => s) (fun _ => t)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
    have hNE : N ≤ E * N := le_mul_of_one_le_left hN h1E
    nlinarith
  let V : ℝ → ℝ := fun t => χ t * W t
  let v : (Fin 1 → ℝ) → ℝ := fun x => V (x 0)
  have hv : ContDiff ℝ 2 v := (hχ₂.mul hW).comp (by fun_prop)
  have hsv (x : Fin 1 → ℝ) (hx : x 0 ≤ α - 2 ∨ β + 2 ≤ x 0) : v x = 0 := by
    have hzero : χ (x 0) = 0 := by
      by_contra hne
      have hin := hsupp hne
      rcases hx with hleft | hright
      · exact (not_lt_of_ge hleft) hin.1
      · exact (not_lt_of_ge hright) hin.2
    simp only [v, V, hzero, zero_mul]
  have heqv : EqOn v u {x | α < x 0 ∧ x 0 < β} := by
    intro x hx
    have hcoord : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
    have hplate : χ (x 0) = 1 := hplateau _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [v, V, W, hplate, one_mul, hcoord] using heq hx
  have hbV₀ (t : ℝ) : |V t| ≤ M * E * N := by
    simpa only [mul_assoc, V] using
      abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₀ t
  have hbV₁ (t : ℝ) : |deriv V t| ≤ 2 * M * E * N := by
    have h := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₁ hbχ₁ hw₀ t
    have h' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₁ t
    rw [show deriv V t = deriv χ t * W t + χ t * deriv W t from
      deriv_mul (hχ₂.differentiable (by norm_num) t) (hW.differentiable (by norm_num) t)]
    exact (abs_add_le _ _).trans (by nlinarith only [h, h'])
  have hbV₂ (t : ℝ) : |deriv (deriv V) t| ≤ 4 * M * E * N := by
    have h := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₂ hbχ₂ hw₀ t
    have h' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₁ hbχ₁ hw₁ t
    have h'' := abs_mul_le_of_support_subset hM.le (mul_nonneg hE.le hN) hs₀ hbχ₀ hw₂ t
    rw [second_deriv_mul hχ₂ hW]
    have hmid : |2 * deriv χ t * deriv W t| ≤ 2 * (M * (E * N)) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left h' (by norm_num)
    exact (abs_add_le _ _).trans
      ((add_le_add (abs_add_le _ _) le_rfl).trans (by nlinarith only [h, hmid, h'']))
  have hhV (s t : ℝ) : |deriv (deriv V) s - deriv (deriv V) t| ≤
      (16 * M * E * N) * |s - t| ^ σ := by
    have h := second_deriv_mul_holder_of_local_bounds hχ₂ hW hK hσ.le
      hM.le hM.le hM.le (mul_nonneg hE.le hN) (mul_nonneg hE.le hN)
      (mul_nonneg hE.le hN) (by positivity) (by positivity) (by positivity)
      hs₀ hs₁ hs₂ hbχ₀ hbχ₁ hbχ₂ hhχ₀ hhχ₁ hhχ₂
      hw₀ hw₁ hw₂ hk₀ hk₁ hk₂ s t
    convert h using 1
    ring
  have hnorm : c2HolderNorm σ univ v ≤ ENNReal.ofReal (23 * M * E * N) := by
    have h := c2HolderNorm_le_of_scalar_bounds hv (by positivity) (by positivity)
      (by positivity) (by positivity) hbV₀ hbV₁ hbV₂ hhV
    convert h using 1
    congr 1
    ring
  refine ⟨v, hv, hsv, heqv, hnorm.trans_eq ?_⟩
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 23 * M * E),
    ENNReal.ofReal_toReal hn.ne]


end

end LatticeProb.Elliptic
