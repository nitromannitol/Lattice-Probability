/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.RMTStep2 at commit 31e7483; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (EXT-CA node M2)
-/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep1
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsMontel
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsHurwitz
import Mathlib.Analysis.Complex.AbsMax

/-!
# Riemann mapping theorem, step 2: the extremal problem (EXT-CA node M2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.M, node **M2**.

Fix a domain `U ⊆ ℂ` (open, preconnected, not all of `ℂ`, with the holomorphic square root
property `HasHoloSqrt U` of node M1) and a base point `z₀ ∈ U`. Consider the family
`𝓕 = {g : U → 𝔻 injective holomorphic, g z₀ = 0}`. We show that `𝓕` contains an element `f` for
which `‖deriv g z₀‖` is maximal over `𝓕`.

The argument is the one of Ahlfors, *Complex Analysis*, 3rd ed. (McGraw-Hill 1979), Ch. 6 §1.1,
pp. 230–231 (PDF pp. 245–246), the second part of the proof of the Riemann mapping theorem:

* `𝓕` is nonempty (Ahlfors normalizes the square root of M1 with a disk automorphism; we use the
  simpler affine normalization `z ↦ (f₁ z - f₁ z₀)/2`, which maps `𝔻` into `𝔻`, sends `z₀` to `0`,
  and preserves injectivity and nonzero derivative);
* the numbers `‖deriv g z₀‖`, `g ∈ 𝓕`, are bounded by `1/r` for any `r > 0` with
  `ball z₀ r ⊆ U` (Cauchy's estimate, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`);
* a maximizing sequence `gₙ ∈ 𝓕` is chosen (`sSup` of the set of values), and Montel's theorem
  (node A4, `QuantumZipper.CA.montel`) gives a locally uniformly convergent subsequence
  `g_{φ k} → f`; the limit is holomorphic on `U`, with `f z₀ = 0` and
  `deriv f z₀ = lim deriv (g_{φ k}) z₀`, hence `‖deriv f z₀‖ = s > 0` and `f` is not constant
  (`TendstoLocallyUniformlyOn.tendsto_at`, `TendstoLocallyUniformlyOn.deriv`);
* Hurwitz's theorem (node A5, `QuantumZipper.CA.hurwitz_injOn`) then gives that `f` is injective
  on `U`;
* `‖f z‖ ≤ 1` on `U` follows from `‖gₙ‖ < 1` by continuity of the norm, and the maximum modulus
  principle (`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`) upgrades this to `‖f z‖ < 1`,
  because `f` is not constant.

## Main results

* `QuantumZipper.CA.RMT.IsCandidate` : the family `𝓕` of candidate maps.
* `QuantumZipper.CA.RMT.norm_deriv_le_of_ball_subset` : the Cauchy estimate bounding `𝓕`.
* `QuantumZipper.CA.RMT.exists_extremal_of_hasHoloSqrt` : existence of the extremal map.

## Sources

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1, pp. 230–231 (normal family proof of the
  Riemann mapping theorem; deviation: the affine normalization of `𝓕` mentioned above).
* Mathlib, `Mathlib.Analysis.Complex.LocallyUniformLimit`, `Mathlib.Analysis.Complex.AbsMax`,
  `Mathlib.Analysis.Complex.Liouville`.
-/

noncomputable section

open Set Metric Filter Topology

namespace QuantumZipper.CA.RMT

/-- The family `𝓕` of candidate maps in the extremal problem of the Riemann mapping theorem: an
injective holomorphic map of `U` into the unit disk taking `z₀` to `0`. (Ahlfors, Ch. 6 §1.1,
p. 230, with the normalization `g'(z₀) > 0` omitted since we maximize `‖g'(z₀)‖.) -/
def IsCandidate (U : Set ℂ) (z₀ : ℂ) (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g U ∧ InjOn g U ∧ MapsTo g U (ball 0 1) ∧ g z₀ = 0

/-- **Cauchy's estimate** for the extremal problem: a holomorphic map of `U` into the unit disk has
derivative at `z₀` bounded by `1 / r` whenever `closedBall z₀ r ⊆ U` (Ahlfors, Ch. 6 §1.1, p. 231:
the derivatives `g'(z₀)`, `g ∈ 𝓕`, have a finite least upper bound). -/
lemma norm_deriv_le_of_closedBall_subset {U : Set ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hrU : closedBall z₀ r ⊆ U) {g : ℂ → ℂ} (hgd : DifferentiableOn ℂ g U)
    (hgM : MapsTo g U (ball 0 1)) : ‖deriv g z₀‖ ≤ 1 / r := by
  have hd : DiffContOnCl ℂ g (ball z₀ r) :=
    ⟨hgd.mono (ball_subset_closedBall.trans hrU),
      hgd.continuousOn.mono (by rw [closure_ball z₀ hr.ne']; exact hrU)⟩
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z₀) (C := 1) hr hd
    fun z hz => (mem_ball_zero_iff.1 (hgM (hrU (sphere_subset_closedBall hz)))).le
  simpa using h

/-- **The extremal problem of the Riemann mapping theorem** (Ahlfors, *Complex Analysis*, 3rd ed.,
Ch. 6 §1.1, pp. 230–231). If `U` is open and preconnected, has the holomorphic square root
property, and is not all of `ℂ`, then among the injective holomorphic maps `g : U → 𝔻` with
`g z₀ = 0` there is one maximizing `‖deriv g z₀‖`. -/
theorem exists_extremal_of_hasHoloSqrt {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hsq : HasHoloSqrt U) (hU : U ≠ Set.univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧ Set.MapsTo f U (Metric.ball 0 1) ∧
      f z₀ = 0 ∧ ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → Set.InjOn g U →
        Set.MapsTo g U (Metric.ball 0 1) → g z₀ = 0 → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  classical
  -- A radius `r > 0` with `ball z₀ r ⊆ U`, and a closed disk around `z₀` inside `U`.
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hUo z₀ hz₀
  have hr2 : 0 < r / 2 := by linarith
  have hcbU : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  -- M1: an injective holomorphic map of `U` into the disk with nonvanishing derivative.
  obtain ⟨f₁, hf₁M, hf₁inj, hf₁d⟩ :=
    exists_mapsTo_unitBall_injOn_deriv_ne_zero_of_hasHoloSqrt hUo hsq hU
  have hf₁diff : DifferentiableOn ℂ f₁ U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf₁d z hz)).differentiableWithinAt
  -- ### Step 1: `𝓕` is nonempty, and its derivatives at `z₀` are positive.
  set g₀ : ℂ → ℂ := fun z => (f₁ z - f₁ z₀) / 2 with hg₀
  have hg₀C : IsCandidate U z₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hg₀]
      exact (hf₁diff.sub_const (f₁ z₀)).div_const 2
    · rw [hg₀]
      intro z hz w hw h
      have h2 : (f₁ z - f₁ z₀) = (f₁ w - f₁ z₀) :=
        (div_left_inj' (show (2 : ℂ) ≠ 0 by norm_num)).1 h
      have h3 : f₁ z = f₁ w := by
        have h4 := congrArg (fun t : ℂ => t + f₁ z₀) h2
        simpa using h4
      exact hf₁inj hz hw h3
    · rw [hg₀]
      intro z hz
      have hz1 : ‖f₁ z‖ < 1 := mem_ball_zero_iff.1 (hf₁M hz)
      have hz2 : ‖f₁ z₀‖ < 1 := mem_ball_zero_iff.1 (hf₁M hz₀)
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [mem_ball_zero_iff, norm_div, h2, div_lt_one (by norm_num : (0 : ℝ) < 2)]
      have := norm_sub_le (f₁ z) (f₁ z₀)
      linarith
    · rw [hg₀]
      simp
  have hg₀d : deriv g₀ z₀ ≠ 0 := by
    have hdz : DifferentiableAt ℂ f₁ z₀ := differentiableAt_of_deriv_ne_zero (hf₁d z₀ hz₀)
    have h1 : HasDerivAt (fun z => f₁ z - f₁ z₀) (deriv f₁ z₀) z₀ := hdz.hasDerivAt.sub_const _
    have h2 : HasDerivAt g₀ (deriv f₁ z₀ / 2) z₀ := by
      rw [hg₀]
      exact h1.div_const 2
    rw [h2.deriv]
    exact div_ne_zero (hf₁d z₀ hz₀) two_ne_zero
  -- ### Step 2: the supremum of `‖deriv g z₀‖` over `𝓕` and a maximizing sequence.
  set S : Set ℝ := {c | ∃ g : ℂ → ℂ, IsCandidate U z₀ g ∧ c = ‖deriv g z₀‖} with hS
  have hScand : ∀ g, IsCandidate U z₀ g → ‖deriv g z₀‖ ∈ S := by
    intro g hg
    simp only [hS, mem_ofPred_eq]
    exact ⟨g, hg, rfl⟩
  have hSne : S.Nonempty := ⟨_, hScand g₀ hg₀C⟩
  have hSbd : BddAbove S := by
    refine ⟨1 / (r / 2), fun c hc => ?_⟩
    simp only [hS, mem_ofPred_eq] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    exact norm_deriv_le_of_closedBall_subset hr2 hcbU hg.1 hg.2.2.1
  set s := sSup S with hs
  have hs_ub : ∀ g, IsCandidate U z₀ g → ‖deriv g z₀‖ ≤ s := by
    intro g hg
    rw [hs]
    exact le_csSup hSbd (hScand g hg)
  have hs_pos : 0 < s := lt_of_lt_of_le (norm_pos_iff.2 hg₀d) (hs_ub g₀ hg₀C)
  have happrox : ∀ n : ℕ, ∃ g : ℂ → ℂ, IsCandidate U z₀ g ∧
      s - 1 / ((n : ℝ) + 1) < ‖deriv g z₀‖ := by
    intro n
    have hlt : s - 1 / ((n : ℝ) + 1) < s := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rw [hs] at hlt
    obtain ⟨c, hcS, hc⟩ := exists_lt_of_lt_csSup hSne hlt
    simp only [hS, mem_ofPred_eq] at hcS
    obtain ⟨g, hg, hgc⟩ := hcS
    exact ⟨g, hg, hgc ▸ hc⟩
  choose g hgC hgclose using happrox
  have hg_tendsto : Tendsto (fun n : ℕ => ‖deriv (g n) z₀‖) atTop (𝓝 s) := by
    have hlow : Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (𝓝 s) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (𝓝 (s - 0)) :=
        tendsto_const_nhds.sub h1
      simpa using h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hgclose n).le) fun n => hs_ub (g n) (hgC n)
  -- ### Step 3: Montel's theorem gives a locally uniform limit `f` of a subsequence.
  have hbdd : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖g n z‖ ≤ M :=
    fun K hKU _ => ⟨1, fun n z hz => (mem_ball_zero_iff.1 ((hgC n).2.2.1 (hKU hz))).le⟩
  obtain ⟨φ, f, hφ, hfd, hlim⟩ :=
    QuantumZipper.CA.montel hUo (fun n => (hgC n).1) hbdd
  -- The limit takes the value `0` at `z₀` and has derivative of norm `s` there.
  have hfz₀ : f z₀ = 0 := by
    have h0 : Tendsto (fun k => g (φ k) z₀) atTop (𝓝 0) := by
      have hconst : (fun k => g (φ k) z₀) = fun _ => (0 : ℂ) :=
        funext fun k => (hgC (φ k)).2.2.2
      rw [hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hlim.tendsto_at hz₀) h0
  have hderiv_tendsto : Tendsto (fun k => deriv (g (φ k)) z₀) atTop (𝓝 (deriv f z₀)) := by
    simpa only [Function.comp_apply] using
      (hlim.deriv (Eventually.of_forall fun k => (hgC (φ k)).1) hUo).tendsto_at hz₀
  have hnorm_deriv : ‖deriv f z₀‖ = s :=
    tendsto_nhds_unique hderiv_tendsto.norm (hg_tendsto.comp hφ.tendsto_atTop)
  have hdf_ne : deriv f z₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm_deriv
    linarith
  -- Hence `f` is not constant on `U`.
  have hf_nc : ¬ ∃ c, EqOn f (fun _ => c) U := by
    rintro ⟨c, hc⟩
    have hfe : f =ᶠ[𝓝 z₀] fun _ => c := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz
      exact hc hz
    have h0 : deriv f z₀ = 0 :=
      ((hasDerivAt_const (c := c) (x := z₀)).congr_of_eventuallyEq hfe).deriv
    exact hdf_ne h0
  -- ### Step 4: Hurwitz's theorem makes `f` injective on `U`.
  have hf_inj : InjOn f U :=
    QuantumZipper.CA.hurwitz_injOn hUo hUc (fun k => (hgC (φ k)).1)
      (fun k => (hgC (φ k)).2.1) hlim hf_nc
  -- ### Step 5: `f` maps `U` into the open unit disk.
  have hf_le : ∀ z ∈ U, ‖f z‖ ≤ 1 := by
    intro z hz
    refine le_of_tendsto ((hlim.tendsto_at hz).norm) (Eventually.of_forall fun k => ?_)
    exact (mem_ball_zero_iff.1 ((hgC (φ k)).2.2.1 hz)).le
  have hf_lt : ∀ z ∈ U, ‖f z‖ < 1 := by
    intro z hz
    refine lt_of_le_of_ne (hf_le z hz) fun hEq => ?_
    have hmax : IsMaxOn (norm ∘ f) U z := fun y hy => by
      change ‖f y‖ ≤ ‖f z‖
      rw [hEq]
      exact hf_le y hy
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hfd hz hmax
    exact hf_nc ⟨f z, fun y hy => hconst hy⟩
  -- ### Conclusion.
  refine ⟨f, hfd, hf_inj, fun z hz => mem_ball_zero_iff.2 (hf_lt z hz), hfz₀, ?_⟩
  intro g hgd hginj hgM hg0
  rw [hnorm_deriv]
  exact hs_ub g ⟨hgd, hginj, hgM, hg0⟩

end QuantumZipper.CA.RMT
