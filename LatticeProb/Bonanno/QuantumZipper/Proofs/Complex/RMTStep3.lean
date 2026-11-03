/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.RMTStep3 at commit 31e7483; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (EXT-CA nodes M3, M4)
-/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-!
# Riemann mapping theorem, steps 3–4 (EXT-CA nodes M3, M4)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.M, nodes **M3** and **M4**.

**M3** (`image_eq_ball_of_extremal`). Let `U ⊆ ℂ` be open with the holomorphic square root
property `HasHoloSqrt U`, `z₀ ∈ U`, and let `f : U → 𝔻` be injective holomorphic with `f z₀ = 0`
and `‖deriv f z₀‖` maximal among all such maps (node M2). Then `f` is onto the unit disk.

Suppose `c ∈ 𝔻` is not attained. Then `m_c ∘ f` is holomorphic and zero-free on `U`, where
`m_c w = (w − c)/(1 − c̄ w)`, so `HasHoloSqrt U` gives a holomorphic square root `s` of it. Since
`‖s z‖² = ‖m_c (f z)‖ < 1`, `s` maps `U` into `𝔻`, and `s` is injective because `s² = m_c ∘ f`
and `m_c` is injective on `𝔻`. With `a := s z₀`, the map `g := m_a ∘ s` is again a candidate
(it is injective holomorphic, maps `U` into `𝔻`, and `g z₀ = 0`), and since `a² = s z₀² = m_c 0
= −c` we can write

`f = F ∘ g`,  `F := m_{−c} ∘ (·)² ∘ m_{−a}`,

where `F : 𝔻 → 𝔻` is holomorphic with `F 0 = m_{−c}(a²) = m_{−c}(−c) = 0` and `F` is *not*
injective (`m_{−a}`, `m_{−c}` are bijections of `𝔻` and `(·)²` is not injective). By the Schwarz
lemma `‖deriv F 0‖ ≤ 1`, and equality would force `F` to be a rotation (equality case of the
Schwarz lemma), hence injective; so `‖deriv F 0‖ < 1`. The chain rule gives
`‖deriv f z₀‖ = ‖deriv F 0‖ · ‖deriv g z₀‖ < ‖deriv g z₀‖` (as `deriv g z₀ ≠ 0` because `g` is
injective), contradicting maximality of `f`. Hence `f` attains every point of `𝔻`.

**M4** (`riemann_mapping_of_hasHoloSqrt`). The Riemann mapping theorem, in the form used by the
project: an open, preconnected, nonempty, proper set `U ⊆ ℂ` with `HasHoloSqrt U` admits a
holomorphic bijection `φ : U → 𝔻` whose inverse `ψ` is holomorphic on `𝔻` and satisfies
`ψ (φ z) = z` for `z ∈ U`. Proof: pick `z₀ ∈ U`, take the extremal map `f` of M2 and apply M3 to
see that `f '' U = 𝔻`; then `ψ` is the (holomorphic) inverse of the univalent map `f` from node
A2 (`univalentOPH`, `differentiableOn_univalentOPH_symm`).

## Main results

* `QuantumZipper.CA.RMT.image_eq_ball_of_extremal`
* `QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt`

## Sources

* L. V. Ahlfors, *Complex Analysis*, 3rd ed. (McGraw-Hill 1979), Ch. 6 §1.1, pp. 230–231
  (`literature/Ahlfors_ComplexAnalysis_1979.pdf`, PDF pp. 245–246): the family `𝓕`, the extremal
  map (M2), the square-root argument with `F(z) = √((f(z) − w₀)/(1 − w̄₀ f(z)))`, the recentring
  `W = G(z)` and the closing sentence "the inequality `|f'(z₀)| < |G'(z₀)|` is therefore a
  consequence of Schwarz's lemma". We follow the same route, but replace Ahlfors's normalizations
  `g'(z₀) > 0` (irrelevant for us since we maximize `‖g'(z₀)‖`) by the disk automorphism `m_a`.
* Mathlib, `Mathlib/Analysis/Complex/Schwarz.lean`: `Complex.norm_deriv_le_one_of_mapsTo_ball`
  (Schwarz lemma) and `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` (equality case).
* Project: `BasicsCayley` (disk Möbius maps `diskMobius`), `BasicsAutomorphisms` (injectivity of
  `diskMobius a` on `𝔻`), `BasicsUnivalent` (node A2: `deriv_ne_zero_of_injOn`, `univalentOPH`).
-/

noncomputable section

open Set Metric Filter Topology

namespace QuantumZipper.CA.RMT

/-! ### An elementary fact about disk automorphisms -/

/-- The disk automorphism `diskMobius a` is injective on the closed unit disk when `‖a‖ < 1`
(the inverse is `diskMobius (-a)`). -/
lemma injOn_diskMobius_closedBall {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskMobius a) (closedBall (0 : ℂ) 1) := by
  intro z hz w hw h
  have h' := congrArg (diskMobius (-a)) h
  rwa [diskMobius_neg_diskMobius ha (mem_closedBall_zero_iff.1 hz),
    diskMobius_neg_diskMobius ha (mem_closedBall_zero_iff.1 hw)] at h'

/-! ### M3: extremal maps are onto -/

/-- **Extremal maps in the Riemann mapping theorem are onto** (Ahlfors, *Complex Analysis*,
3rd ed., Ch. 6 §1.1, p. 231). If `f` is an injective holomorphic map of `U` into the unit disk
with `f z₀ = 0` maximizing `‖deriv · z₀‖` over all such maps, then `f` attains every value of the
unit disk. -/
theorem image_eq_ball_of_extremal {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hsq : HasHoloSqrt U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ} (hf : IsCandidate U z₀ f)
    (hmax : ∀ g, IsCandidate U z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    f '' U = Metric.ball 0 1 := by
  have _ := hUc -- `U` is preconnected; the argument itself only uses `HasHoloSqrt U`
  refine eq_of_subset_of_subset (fun w hw => ?_) fun c hc => ?_
  · rcases hw with ⟨z, hz, rfl⟩
    exact hf.2.2.1 hz
  · -- we show that an omitted value `c ∈ 𝔻` yields a candidate with larger derivative
    by_contra hcU
    have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.1 hc
    have hc1' : ‖-c‖ < 1 := by rwa [norm_neg]
    have hfne : ∀ z ∈ U, f z ≠ c := fun z hz h => hcU ⟨z, hz, h⟩
    -- `m_c ∘ f` is holomorphic and zero-free on `U`, hence has a holomorphic square root `s`
    have hφd : DifferentiableOn ℂ (fun z => diskMobius c (f z)) U :=
      (differentiableOn_diskMobius hc1).comp hf.1 fun z hz =>
        mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 (hf.2.2.1 hz)).le
    have hφ0 : ∀ z ∈ U, diskMobius c (f z) ≠ 0 := by
      intro z hz
      exact div_ne_zero (sub_ne_zero.2 (hfne z hz))
        (diskMobius_denom_ne_zero hc1 (mem_ball_zero_iff.1 (hf.2.2.1 hz)).le)
    obtain ⟨s, hsd, hssq⟩ := hsq _ hφd hφ0
    -- `s` maps `U` into `𝔻` and is injective there
    have hs_lt : ∀ z ∈ U, ‖s z‖ < 1 := by
      intro z hz
      have h1 : ‖s z ^ 2‖ < 1 := by
        rw [hssq z hz]
        exact mem_ball_zero_iff.1 (diskMobius_mem_ball hc1 (hf.2.2.1 hz))
      have h2 : ‖s z‖ ^ 2 < 1 := by rwa [norm_pow] at h1
      nlinarith [norm_nonneg (s z)]
    have hs_inj : InjOn s U := by
      intro z hz w hw h
      have h1 : diskMobius c (f z) = diskMobius c (f w) := by
        rw [← hssq z hz, ← hssq w hw, h]
      refine hf.2.1 hz hw ?_
      have h2 := congrArg (diskMobius (-c)) h1
      rwa [diskMobius_neg_diskMobius hc1 (le_of_lt (mem_ball_zero_iff.1 (hf.2.2.1 hz))),
        diskMobius_neg_diskMobius hc1 (le_of_lt (mem_ball_zero_iff.1 (hf.2.2.1 hw)))] at h2
    set a : ℂ := s z₀ with ha_def
    have ha_lt : ‖a‖ < 1 := by
      have h1 : ‖a‖ ^ 2 < 1 := by
        rw [ha_def, ← norm_pow, hssq z₀ hz₀]
        exact mem_ball_zero_iff.1 (diskMobius_mem_ball hc1 (hf.2.2.1 hz₀))
      nlinarith [norm_nonneg a]
    have ha_sq : a ^ 2 = -c := by
      rw [ha_def, hssq z₀ hz₀, hf.2.2.2]
      simp [diskMobius]
    -- the recentred square root `g = m_a ∘ s` is again a candidate
    set g : ℂ → ℂ := fun z => diskMobius a (s z) with hg_def
    have hgC : IsCandidate U z₀ g := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hg_def]
        exact (differentiableOn_diskMobius ha_lt).comp hsd fun z hz =>
          mem_closedBall_zero_iff.2 (le_of_lt (hs_lt z hz))
      · intro z hz w hw h
        refine hs_inj hz hw ?_
        have h1 := congrArg (diskMobius (-a)) h
        simp only [hg_def] at h1
        rwa [diskMobius_neg_diskMobius ha_lt (le_of_lt (hs_lt z hz)),
          diskMobius_neg_diskMobius ha_lt (le_of_lt (hs_lt w hw))] at h1
      · intro z hz
        exact diskMobius_mem_ball ha_lt (mem_ball_zero_iff.2 (hs_lt z hz))
      · simp only [hg_def]
        rw [← ha_def]
        simp [diskMobius]
    -- `f = F ∘ g` with `F = m_{−c} ∘ (·)² ∘ m_{−a}` a non-injective self-map of `𝔻` fixing `0`
    set F : ℂ → ℂ := fun w => diskMobius (-c) ((diskMobius (-a) w) ^ 2) with hF
    have ha_neg : ‖-a‖ < 1 := by rwa [norm_neg]
    have hFd : DifferentiableOn ℂ F (ball 0 1) := by
      rw [hF]
      refine (differentiableOn_diskMobius hc1').comp ?_ ?_
      · exact ((differentiableOn_diskMobius ha_neg).mono ball_subset_closedBall).pow 2
      · intro w hw
        refine mem_closedBall_zero_iff.2 ?_
        have h1 : ‖diskMobius (-a) w‖ < 1 :=
          mem_ball_zero_iff.1 (diskMobius_mem_ball ha_neg hw)
        rw [norm_pow]
        nlinarith [norm_nonneg (diskMobius (-a) w)]
    have hF0 : F 0 = 0 := by
      have h0 : diskMobius (-a) 0 = a := by simp [diskMobius]
      simp only [hF, h0, ha_sq, diskMobius_self]
    have hFM : MapsTo F (ball 0 1) (closedBall (F 0) 1) := by
      rw [hF0]
      intro w hw
      simp only [hF]
      have h1 : ‖diskMobius (-a) w‖ < 1 :=
        mem_ball_zero_iff.1 (diskMobius_mem_ball ha_neg hw)
      have h2 : ‖(diskMobius (-a) w) ^ 2‖ < 1 := by
        rw [norm_pow]
        nlinarith [norm_nonneg (diskMobius (-a) w)]
      exact ball_subset_closedBall (diskMobius_mem_ball hc1' (mem_ball_zero_iff.2 h2))
    have hFnotinj : ¬ InjOn F (ball 0 1) := by
      intro hinj
      have hmem1 : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; norm_num
      have hmem2 : (-(1 / 2 : ℂ)) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_neg]; norm_num
      have h1 : F (diskMobius a (1 / 2)) = F (diskMobius a (-(1 / 2))) := by
        have hs : (diskMobius (-a) (diskMobius a (1 / 2))) ^ 2
            = (diskMobius (-a) (diskMobius a (-(1 / 2)))) ^ 2 := by
          rw [diskMobius_neg_diskMobius (a := a) (z := (1 / 2 : ℂ)) ha_lt
                (le_of_lt (mem_ball_zero_iff.1 hmem1)),
            diskMobius_neg_diskMobius (a := a) (z := (-(1 / 2) : ℂ)) ha_lt
                (le_of_lt (mem_ball_zero_iff.1 hmem2))]
          ring
        simp only [hF]
        exact congrArg (diskMobius (-c)) hs
      have h2 := hinj (diskMobius_mem_ball ha_lt hmem1) (diskMobius_mem_ball ha_lt hmem2) h1
      have h3 : (1 / 2 : ℂ) = -(1 / 2 : ℂ) :=
        injOn_diskMobius_closedBall ha_lt (ball_subset_closedBall hmem1)
          (ball_subset_closedBall hmem2) h2
      norm_num at h3
    -- Schwarz's lemma, plus its equality case, give `‖deriv F 0‖ < 1`
    have hFderiv_lt : ‖deriv F 0‖ < 1 := by
      have hle : ‖deriv F 0‖ ≤ 1 :=
        Complex.norm_deriv_le_one_of_mapsTo_ball hFd hFM (by norm_num)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have hne : deriv F 0 ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at h; norm_num at h
        have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div (c := 0) (R₁ := 1)
          (R₂ := 1) hFd hFM (mem_ball_self one_pos) (by rw [dslope_same, h]; norm_num)
        apply hFnotinj
        intro x hx y hy hxy
        have hx' : F x = x * deriv F 0 := by
          simpa only [hF0, zero_add, dslope_same, sub_zero, Algebra.smul_def, Algebra.algebraMap_self_apply]
            using haff hx
        have hy' : F y = y * deriv F 0 := by
          simpa only [hF0, zero_add, dslope_same, sub_zero, Algebra.smul_def, Algebra.algebraMap_self_apply]
            using haff hy
        exact mul_right_cancel₀ hne (by rw [← hx', ← hy', hxy])
    -- the chain rule at `z₀`
    have hfg : ∀ z ∈ U, f z = (F ∘ g) z := by
      intro z hz
      have h2 : diskMobius (-a) (g z) = s z := by
        simp only [hg_def]
        exact diskMobius_neg_diskMobius ha_lt (le_of_lt (hs_lt z hz))
      simp only [hF, Function.comp_apply]
      rw [h2, hssq z hz,
        diskMobius_neg_diskMobius hc1 (le_of_lt (mem_ball_zero_iff.1 (hf.2.2.1 hz)))]
    have hgda : DifferentiableAt ℂ g z₀ := hgC.1.differentiableAt (hUo.mem_nhds hz₀)
    have hFda : DifferentiableAt ℂ F (g z₀) := by
      rw [hgC.2.2.2]
      exact hFd.differentiableAt (ball_mem_nhds (0 : ℂ) one_pos)
    have hcomp : deriv (F ∘ g) z₀ = deriv F (g z₀) * deriv g z₀ := deriv_comp z₀ hFda hgda
    have hev : f =ᶠ[𝓝 z₀] F ∘ g := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz
      exact hfg z hz
    have hdf : deriv f z₀ = deriv F 0 * deriv g z₀ := by
      rw [hev.deriv_eq, hcomp, hgC.2.2.2]
    have hdg_ne : deriv g z₀ ≠ 0 := deriv_ne_zero_of_injOn hUo hgC.1 hgC.2.1 hz₀
    have hlt : ‖deriv f z₀‖ < ‖deriv g z₀‖ := by
      rw [hdf, norm_mul]
      calc ‖deriv F 0‖ * ‖deriv g z₀‖ < 1 * ‖deriv g z₀‖ :=
            mul_lt_mul_of_pos_right hFderiv_lt (norm_pos_iff.2 hdg_ne)
        _ = ‖deriv g z₀‖ := one_mul _
    have := hmax g hgC
    linarith

/-! ### M4: the Riemann mapping theorem -/

/-- **Riemann mapping theorem**, in the form used by the project (Ahlfors, *Complex Analysis*,
3rd ed., Ch. 6 §1.1, Theorem 1, p. 230; `HasHoloSqrt` replaces simple connectivity as in node
M1). An open, preconnected, proper, nonempty subset of `ℂ` with the holomorphic square root
property is conformally equivalent to the unit disk: there is a bijection `φ : U → 𝔻`,
holomorphic on `U`, whose inverse `ψ : 𝔻 → U` is holomorphic on `𝔻` and a left inverse of `φ`
on `U`.

Existence only: uniqueness of `φ` and the normalization `φ z₀ = 0`, `φ' z₀ > 0` (part of Ahlfors's
Theorem 1) are **not** asserted — no consumer needs them (AUDIT10 C10-4; the earlier citation
"Theorem 6.1" was wrong, the statement expected by node M1 is existence + biholomorphy). -/
theorem riemann_mapping_of_hasHoloSqrt {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hne : U.Nonempty) (hU : U ≠ Set.univ) (hsq : HasHoloSqrt U) :
    ∃ φ : ℂ → ℂ, Set.BijOn φ U (Metric.ball 0 1) ∧ DifferentiableOn ℂ φ U ∧
      ∃ ψ : ℂ → ℂ, Set.BijOn ψ (Metric.ball 0 1) U ∧ DifferentiableOn ℂ ψ (Metric.ball 0 1) ∧
        Set.LeftInvOn ψ φ U := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨f, hfd, hfinj, hfM, hfz₀, hfmax⟩ := exists_extremal_of_hasHoloSqrt hUo hUc hsq hU hz₀
  have himg : f '' U = ball 0 1 :=
    image_eq_ball_of_extremal hUo hUc hsq hz₀ ⟨hfd, hfinj, hfM, hfz₀⟩
      fun g hg => hfmax g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hsrc : (univalentOPH hUo hfd hfinj).source = U := univalentOPH_source hUo hfd hfinj
  have htgt : (univalentOPH hUo hfd hfinj).target = f '' U := univalentOPH_target hUo hfd hfinj
  have hsymm_src : (univalentOPH hUo hfd hfinj).symm.source = ball 0 1 := by
    rw [OpenPartialHomeomorph.symm_source, htgt, himg]
  have hsymm_tgt : (univalentOPH hUo hfd hfinj).symm.target = U := by
    rw [OpenPartialHomeomorph.symm_target, hsrc]
  refine ⟨f, ⟨hfM, hfinj, fun w hw => ?_⟩, hfd,
    (univalentOPH hUo hfd hfinj).symm, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← himg] at hw
    exact hw
  · -- `e.symm` maps `𝔻` into `U`
    intro w hw
    have h := (univalentOPH hUo hfd hfinj).symm.map_source (x := w)
      (by rw [hsymm_src]; exact hw)
    rwa [hsymm_tgt] at h
  · -- and is injective there
    intro w hw w' hw' h
    have h1 : (univalentOPH hUo hfd hfinj) ((univalentOPH hUo hfd hfinj).symm w)
        = (univalentOPH hUo hfd hfinj) ((univalentOPH hUo hfd hfinj).symm w') := by
      rw [h]
    rwa [(univalentOPH hUo hfd hfinj).right_inv (by rw [htgt, himg]; exact hw),
      (univalentOPH hUo hfd hfinj).right_inv (by rw [htgt, himg]; exact hw')] at h1
  · -- and is onto `U`
    intro z hz
    exact ⟨f z, hfM hz, univalentOPH_symm_apply_apply hUo hfd hfinj hz⟩
  · -- `e.symm` is holomorphic on the disk (node A2)
    simpa [himg] using differentiableOn_univalentOPH_symm hUo hfd hfinj
  · -- and is a left inverse of `f` on `U`
    intro z hz
    exact univalentOPH_symm_apply_apply hUo hfd hfinj hz

end QuantumZipper.CA.RMT
