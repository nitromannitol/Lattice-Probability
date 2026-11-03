/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.RMTStep1 at commit 31e7483; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (EXT-CA node M1)
-/
import Mathlib.Analysis.Complex.RiemannMapping
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Riemann mapping theorem, step 1, from holomorphic square roots (EXT-CA node M1)

The first step of the proof of the Riemann mapping theorem
(`Complex.exists_injective_not_dense_image_deriv_ne_zero` and
`Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` in Mathlib,
`Mathlib/Analysis/Complex/RiemannMapping.lean`, Yury Kudryashov) uses simple connectivity of the
domain `U ⊆ ℂ` only through the existence of a continuous (hence holomorphic) branch of `√z` on `U`
(`Complex.exists_continuousOn_pow_eq`, Mathlib file `Mathlib/Analysis/Complex/BranchLogRoot.lean`,
proved via covering space theory; see also Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1, where
this is the way the Riemann mapping theorem is proved).

Here we state that property of `U` directly as `HasHoloSqrt U`: every holomorphic function on `U`
without zeros has a holomorphic square root on `U`. We then prove the analogues of the two lemmas
above with `IsSimplyConnected U` replaced by `HasHoloSqrt U`, following Mathlib's proofs verbatim
except for the square root step.

The converse implication `IsSimplyConnected U → HasHoloSqrt U` is *not* proved here: at this pin
Mathlib has continuous branches of `log`/`√z` on simply connected sets (`Complex.BranchLogRoot`),
but no theory of holomorphic logarithms or primitives on simply connected domains, so it would
require substantial new material (a holomorphic logarithm, e.g. via primitives/Morera).

The only place where Mathlib's proof uses more than the *local* statement `s z ^ 2 = z` (for
`z ∈ U`) is injectivity of the constructed map: in Mathlib `s` is a global left inverse of `· ^ 2`,
which we do not get. Since `s` is unconstrained off `U`, we prove injectivity by patching `s`
outside `U` with an explicit injection of `ℂ` into a ball that misses `s '' U` (which is not dense);
this patch is the only deviation from Mathlib's argument, and it is stated explicitly in the proof
of `exists_injective_not_dense_image_deriv_ne_zero_of_hasHoloSqrt`.

## Main results

* `QuantumZipper.CA.RMT.HasHoloSqrt` : the holomorphic square root property of a set `U : Set ℂ`.
* `QuantumZipper.CA.RMT.exists_injective_not_dense_image_deriv_ne_zero_of_hasHoloSqrt`
* `QuantumZipper.CA.RMT.exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_hasHoloSqrt`

## Sources

* Mathlib, `Mathlib/Analysis/Complex/RiemannMapping.lean` (proofs copied, square-root step and the
  injectivity patch excepted).
* L. V. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1 (Riemann mapping theorem via square roots).
-/

open Function Filter Metric Set
open scoped Pointwise Topology

namespace QuantumZipper.CA.RMT

/-- A set `U : Set ℂ` has the **holomorphic square root property** if every holomorphic function on
`U` without zeros has a holomorphic square root on `U`. This is the property of a domain that is
really used in the first step of the Riemann mapping theorem; simple connectivity only enters
through it (via the existence of continuous, hence holomorphic, branches of `√z`). -/
def HasHoloSqrt (U : Set ℂ) : Prop :=
  ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s U ∧ ∀ z ∈ U, s z ^ 2 = g z

/-! ### An explicit injection of `ℂ` into the open unit ball

These are elementary facts (own elementary proofs), used to patch the square root off its domain. -/

lemma one_add_norm_cast (z : ℂ) : (1 : ℂ) + ↑‖z‖ = ((1 + ‖z‖ : ℝ) : ℂ) := by
  push_cast
  ring

lemma norm_one_add_norm (z : ℂ) : ‖(1 : ℂ) + ↑‖z‖‖ = 1 + ‖z‖ := by
  rw [one_add_norm_cast, Complex.norm_of_nonneg (by positivity)]

lemma one_add_norm_ne_zero (z : ℂ) : (1 : ℂ) + ↑‖z‖ ≠ 0 := by
  intro h0
  have h' : ‖(1 : ℂ) + ↑‖z‖‖ = 0 := by rw [h0, norm_zero]
  rw [norm_one_add_norm] at h'
  linarith [norm_nonneg z]

lemma norm_div_one_add_norm_lt_one (z : ℂ) : ‖z / (1 + ↑‖z‖)‖ < 1 := by
  rw [norm_div, norm_one_add_norm, div_lt_one (by positivity)]
  linarith [norm_nonneg z]

lemma injective_div_one_add_norm : Injective fun z : ℂ => z / (1 + ↑‖z‖) := by
  intro z w h
  have hred : z / (1 + ↑‖z‖) = w / (1 + ↑‖w‖) := h
  have hnorm : ‖z‖ = ‖w‖ := by
    have h' : ‖z / (1 + ↑‖z‖)‖ = ‖w / (1 + ↑‖w‖)‖ := by
      simpa using congrArg (fun t : ℂ => ‖t‖) hred
    rw [norm_div, norm_div, norm_one_add_norm, norm_one_add_norm] at h'
    field_simp at h'
    nlinarith [norm_nonneg z, norm_nonneg w]
  rw [hnorm] at hred
  rw [div_eq_mul_inv, div_eq_mul_inv] at hred
  exact mul_right_cancel₀ (inv_ne_zero (one_add_norm_ne_zero w)) hred

lemma not_dense_empty_complex : ¬ Dense (∅ : Set ℂ) := by
  intro h
  have h0 : (0 : ℂ) ∈ closure (∅ : Set ℂ) := h 0
  rw [closure_empty] at h0
  exact absurd h0 (notMem_empty 0)

/-! ### The holomorphic square root property is translation invariant -/

namespace HasHoloSqrt

/-- The holomorphic square root property is invariant under translations. -/
lemma vadd {U : Set ℂ} (h : HasHoloSqrt U) (a : ℂ) : HasHoloSqrt (a +ᵥ U) := by
  intro g hg hg0
  have hmem : ∀ z : ℂ, a + z ∈ a +ᵥ U ↔ z ∈ U := by
    intro z
    rw [mem_vadd_set_iff_neg_vadd_mem]
    simp
  obtain ⟨S, hS, hSsq⟩ := h (fun z => g (a + z))
    (hg.comp
      ((differentiableOn_const a).add (differentiableOn_id : DifferentiableOn ℂ (fun z => z) U))
      fun z hz => (hmem z).mpr hz)
    fun z hz => hg0 (a + z) ((hmem z).mpr hz)
  refine ⟨fun w => S (-a + w), ?_, ?_⟩
  · refine hS.comp
      ((differentiableOn_const (-a)).add (differentiableOn_id :
        DifferentiableOn ℂ (fun z => z) (a +ᵥ U)))
      fun w hw => (hmem (-a + w)).mp (by simpa using hw)
  · intro w hw
    have hw' : -a + w ∈ U := (hmem (-a + w)).mp (by simpa using hw)
    simpa using hSsq (-a + w) hw'

end HasHoloSqrt

/-- **First step of the Riemann mapping theorem, square root form.**

If `U` is open, has the holomorphic square root property, and is not all of `ℂ`, then there is an
injective `f : ℂ → ℂ`, holomorphic on `U` with nonzero derivative, whose image of `U` is not dense
in `ℂ`. This is Mathlib's `Complex.exists_injective_not_dense_image_deriv_ne_zero` with
`IsSimplyConnected U` replaced by `HasHoloSqrt U`; the proof is Mathlib's, except that injectivity
of `f` is obtained by patching the square root outside `U` (where the hypothesis says nothing)
with an explicit injection of `ℂ` into a ball missing `f '' U`. -/
theorem exists_injective_not_dense_image_deriv_ne_zero_of_hasHoloSqrt {U : Set ℂ} (hUo : IsOpen U)
    (hUc : HasHoloSqrt U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  -- The main argument, assuming additionally that `0 ∉ U` and that `U` is nonempty.
  have aux : ∀ {V : Set ℂ}, IsOpen V → HasHoloSqrt V → 0 ∉ V → V.Nonempty →
      ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' V) ∧ ∀ z ∈ V, deriv f z ≠ 0 := by
    intro V hVo hVc hV₀ hVne
    classical
    -- A holomorphic square root of `z ↦ z` on `V`.
    obtain ⟨s, hs_diff, hs_sq⟩ := hVc (fun z => z) (differentiableOn_id :
      DifferentiableOn ℂ (fun z => z) V) fun z hz hz0 => hV₀ (hz0 ▸ hz)
    have hsc : ContinuousOn s V := hs_diff.continuousOn
    -- `0 ∉ s '' V`
    have hs0 : ∀ z ∈ V, s z ≠ 0 := by
      intro z hz hsz
      have hz0 : z = 0 := by simpa [hsz] using (hs_sq z hz).symm
      exact hV₀ (hz0 ▸ hz)
    -- `s` is strictly differentiable at every point of `V`, with derivative `(2 * s z)⁻¹`.
    have hds : ∀ z ∈ V, HasStrictDerivAt s (2 * s z)⁻¹ z := by
      intro z hz
      apply HasStrictDerivAt.of_local_left_inverse (f := fun w => w ^ 2) (f' := 2 * s z)
      · exact hsc.continuousAt (hVo.mem_nhds hz)
      · simpa using hasStrictDerivAt_pow 2 (s z)
      · exact mul_ne_zero two_ne_zero (hs0 z hz)
      · filter_upwards [hVo.mem_nhds hz] with y hy
        exact hs_sq y hy
    -- `s '' V` is not dense: it misses a neighbourhood of `-s x` for any `x ∈ V`.
    have hnd : ¬ Dense (s '' V) := by
      simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
      rcases hVne with ⟨x, hx⟩
      refine ⟨-s x, ?_⟩
      have hnb : s '' V ∈ 𝓝 (s x) := by
        rw [← (hds x hx).map_nhds_eq (by simpa using hs0 x hx)]
        exact Filter.image_mem_map (hVo.mem_nhds hx)
      rw [nhds_neg, eventually_neg]
      filter_upwards [hnb] with y hy hyneg
      rcases hy with ⟨a, ha, rfl⟩
      rcases hyneg with ⟨b, hb, hb'⟩
      obtain rfl : a = b := by
        rw [← hs_sq b hb, hb']
        simp [hs_sq a ha]
      refine hs0 a ha ?_
      linear_combination hb' / 2
    -- Since `s '' V` is not dense, it is disjoint from a ball `ball x ρ`.
    obtain ⟨x, ρ, hρ0, hρ⟩ : ∃ (x : ℂ) (ρ : ℝ), 0 < ρ ∧ ∀ a ∈ V, ρ < dist (s a) x := by
      simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hnd
    -- Patch `s` outside `V` by an injection of `ℂ` into `ball x ρ`.
    set f : ℂ → ℂ := V.piecewise s (fun z => x + ρ * (z / (1 + ↑‖z‖))) with hf
    -- The patched function still maps `V` to `s '' V`.
    have himg : f '' V = s '' V :=
      image_congr fun z hz => by rw [hf]; simp [hz]
    -- Points of `V` and points outside `V` have disjoint images.
    have hstep : ∀ a ∈ V, ∀ b ∉ V, f a ≠ f b := by
      intro a ha b hb hab
      have h1 : s a = x + ρ * (b / (1 + ↑‖b‖)) := by
        rw [hf] at hab
        simpa [ha, hb] using hab
      have hball : x + ρ * (b / (1 + ↑‖b‖)) ∈ ball x ρ := by
        simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hρ0.le]
        nlinarith [norm_div_one_add_norm_lt_one b, hρ0]
      rw [← h1] at hball
      exact absurd hball (not_lt.mpr (hρ a ha).le)
    refine ⟨f, ?_, ?_, ?_⟩
    · -- injectivity
      intro z w hzw
      by_cases hz : z ∈ V
      · by_cases hw : w ∈ V
        · have hszw : s z = s w := by
            rw [hf] at hzw
            simpa [hz, hw] using hzw
          calc z = s z ^ 2 := (hs_sq z hz).symm
            _ = s w ^ 2 := by rw [hszw]
            _ = w := hs_sq w hw
        · exact absurd hzw (hstep z hz w hw)
      · by_cases hw : w ∈ V
        · exact absurd hzw.symm (hstep w hw z hz)
        · have h2 : x + ρ * (z / (1 + ↑‖z‖)) = x + ρ * (w / (1 + ↑‖w‖)) := by
            rw [hf] at hzw
            simpa [hz, hw] using hzw
          have hρc : ((ρ : ℂ)) ≠ 0 := by
            intro h0
            have hz0 : ‖(ρ : ℂ)‖ = 0 := by rw [h0, norm_zero]
            rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le] at hz0
            linarith
          have h3 : ρ * (z / (1 + ↑‖z‖)) = ρ * (w / (1 + ↑‖w‖)) := add_left_cancel h2
          have h4 : z / (1 + ↑‖z‖) = w / (1 + ↑‖w‖) := mul_left_cancel₀ hρc h3
          exact injective_div_one_add_norm h4
    · -- non-density
      rw [himg]
      exact hnd
    · -- nonzero derivative at points of `V`
      intro z hz
      have hfe : f =ᶠ[𝓝 z] s := by
        rw [hf]
        filter_upwards [hVo.mem_nhds hz] with y hy
        simp [hy]
      have hd' : HasStrictDerivAt f (2 * s z)⁻¹ z :=
        (hds z hz).congr_of_eventuallyEq hfe.symm
      rw [hd'.hasDerivAt.deriv]
      exact inv_ne_zero (mul_ne_zero two_ne_zero (hs0 z hz))
  rcases eq_empty_or_nonempty U with hUe | hUne
  · -- `U = ∅` is trivial
    exact ⟨id, injective_id, by rw [hUe, image_empty]; exact not_dense_empty_complex,
      fun z hz => absurd (hUe ▸ hz) (notMem_empty z)⟩
  · by_cases hU₀ : (0 : ℂ) ∈ U
    · -- `0 ∈ U`: translate `U` so that `0` is outside and apply `aux`
      rw [ne_univ_iff_exists_notMem] at hU
      obtain ⟨a, ha⟩ := hU
      have hUne' : ((-a) +ᵥ U).Nonempty := by
        obtain ⟨z, hz⟩ := hUne
        exact ⟨-a + z, by rw [mem_vadd_set_iff_neg_vadd_mem]; simpa using hz⟩
      obtain ⟨f, hfi, hfd, hdf⟩ := aux (hUo.vadd (-a)) (hUc.vadd (-a))
        (by rw [mem_vadd_set_iff_neg_vadd_mem]; simpa using ha) hUne'
      refine ⟨f ∘ fun z => -a + z, fun x y hxy => ?_, ?_, fun z hz => ?_⟩
      · have : -a + x = -a + y := hfi hxy
        simpa using this
      · have himg' : (fun z : ℂ => -a + z) '' U = (-a) +ᵥ U := by
          ext w
          constructor
          · rintro ⟨u, hu, rfl⟩
            rw [mem_vadd_set_iff_neg_vadd_mem]
            simpa using hu
          · intro hw
            rw [mem_vadd_set_iff_neg_vadd_mem] at hw
            exact ⟨a + w, by simpa using hw, by simp⟩
        rw [image_comp, himg']
        exact hfd
      · have hz' : -a + z ∈ (-a) +ᵥ U := by
          rw [mem_vadd_set_iff_neg_vadd_mem]; simpa using hz
        have hd : deriv (f ∘ fun z => -a + z) z = deriv f (-a + z) := by
          simpa only [Function.comp_def] using deriv_comp_const_add (f := f) (a := -a) (x := z)
        rw [hd]
        exact hdf (-a + z) hz'
    · exact aux hUo hUc hU₀ hUne

/-- **Second step of the Riemann mapping theorem, square root form.**

If `U` is open, has the holomorphic square root property and is not all of `ℂ`, then there is
`f : ℂ → ℂ` mapping `U` into the unit ball, injective on `U`, and holomorphic on `U` with nonzero
derivative. This is Mathlib's `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` with
`IsSimplyConnected U` replaced by `HasHoloSqrt U`; the proof is Mathlib's, using
`exists_injective_not_dense_image_deriv_ne_zero_of_hasHoloSqrt` for the first step. -/
lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_hasHoloSqrt {U : Set ℂ} (hUo : IsOpen U)
    (hUc : HasHoloSqrt U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  -- Take an injective, differentiable function on `U` with non-dense image.
  rcases exists_injective_not_dense_image_deriv_ne_zero_of_hasHoloSqrt hUo hUc hU with
    ⟨f, hf_inj, hfd, hdf⟩
  -- Choose a closed ball `closedBall x ε`, `ε > 0`, disjoint from `f '' U`.
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz => by simpa using hε₀.trans (hε z hz)
  -- Then `z ↦ ε / (f z - x)` satisfies all the assertions.
  use fun z => ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

end QuantumZipper.CA.RMT
