import LatticeProb.Analysis.PoissonBall
import Mathlib

/-!
# Sub-mean-value inequalities from the comparison with harmonic functions on balls

Let `v` be continuous on a closed ball `closedBall a r` of `ℝ ^ d` and suppose `v` satisfies the
*comparison with harmonic functions* on every ball `closedBall a ρ`, `0 < ρ ≤ r`: whenever `h` is
harmonic in `ball a ρ`, continuous on `closedBall a ρ` and `v ≤ h` on `sphere a ρ`, then `v ≤ h` in
`ball a ρ`. Then `v` satisfies the sub-mean-value inequalities

* `le_sphereAverage_of_comparison`: `v a` is at most the average of `v` over `sphere a ρ`;
* `le_ballAverage_of_comparison`: `v a` is at most the average of `v` over `ball a r`.

The comparison principle is a hypothesis here (it is the content of the comparison for viscosity
subharmonic functions). The sphere form applies the comparison to the harmonic extension of `v` from
the sphere (`exists_harmonic_ball`); the ball form integrates the sphere form in polar coordinates
(`MeasureTheory.Measure.toSphere`).
-/

open MeasureTheory Metric Set InnerProductSpace

namespace LatticeProb.Ishii

section Sphere

variable {d : ℕ}

/-- If `v` is below the harmonic extension of its boundary values on `ball a ρ`, then `v a` is at most
the average of `v` over `sphere a ρ`. -/
theorem le_sphereAverage_of_comparison {v : EuclideanSpace ℝ (Fin d) → ℝ}
    {a : EuclideanSpace ℝ (Fin d)} {ρ : ℝ} (hρ : 0 < ρ) (hv : ContinuousOn v (closedBall a ρ))
    (hcmp : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ, HarmonicOnNhd h (ball a ρ) →
      ContinuousOn h (closedBall a ρ) → (∀ z ∈ sphere a ρ, v z ≤ h z) →
        ∀ z ∈ ball a ρ, v z ≤ h z) :
    v a ≤ ⨍ z, v (a + ρ • (z : EuclideanSpace ℝ (Fin d)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  obtain ⟨h, hh, hhc, hheq, hha⟩ := exists_harmonic_ball hρ (hv.mono sphere_subset_closedBall)
  have := hcmp h hh hhc (fun z hz => (hheq hz).ge) a (mem_ball_self hρ)
  rw [← hha]
  exact this

end Sphere


section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The integral over `E` in polar coordinates `x = ρ • z`, `z` on the unit sphere. -/
theorem integral_polar (h : E → ℝ) :
    ∫ x, h x ∂μ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), h ((p.2 : ℝ) • (p.1 : E))
      ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd μ
  have h1 := hmp.integral_comp (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => h ((p.2 : ℝ) • (p.1 : E)))
  rw [← h1]
  calc ∫ x, h x ∂μ
      = ∫ x : ({(0 : E)}ᶜ : Set E), h x.1 ∂(μ.comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl h,
          restrict_compl_singleton]
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [homeomorphUnitSphereProd_apply_fst_coe,
          homeomorphUnitSphereProd_apply_snd_coe]
        rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr x.2)]

omit [Nontrivial E] in
/-- Integrability transfers to polar coordinates. -/
theorem integrable_polar {h : E → ℝ} (hh : Integrable h μ) :
    Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => h ((p.2 : ℝ) • (p.1 : E)))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd μ
  rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
  have h2 : Integrable (fun x : ({(0 : E)}ᶜ : Set E) => h x.1)
      (μ.comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E)) := by
    exact (integrableOn_iff_comap_subtypeVal (μ := μ) (f := h)
      (measurableSet_singleton _).compl).mp hh.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp, homeomorphUnitSphereProd_apply_fst_coe,
    homeomorphUnitSphereProd_apply_snd_coe]
  rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr x.2)]

end Polar


section Ball

variable {d : ℕ}

/-- If `v` satisfies the comparison with harmonic functions on every ball `ball a ρ`, `0 < ρ ≤ r`, then
`v a` is at most the average of `v` over `ball a r`. -/
theorem le_ballAverage_of_comparison {v : EuclideanSpace ℝ (Fin d) → ℝ}
    {a : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hv : ContinuousOn v (closedBall a r))
    (hcmp : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ∀ h : EuclideanSpace ℝ (Fin d) → ℝ,
      HarmonicOnNhd h (ball a ρ) → ContinuousOn h (closedBall a ρ) →
        (∀ z ∈ sphere a ρ, v z ≤ h z) → ∀ z ∈ ball a ρ, v z ≤ h z) :
    v a ≤ ⨍ y in ball a r, v y := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin d)) with hS | hN
  · have hv' : ∀ y, v y = v a := fun y => by rw [Subsingleton.elim y a]
    simp_rw [hv']
    rw [setAverage_const (measure_ball_pos volume a hr).ne' measure_ball_lt_top.ne]
  · set σ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hσ
    have hm : 0 < σ.real univ := by
      have h1 : σ univ ≠ 0 := by
        intro h0
        exact (Measure.toSphere_ne_zero (E := EuclideanSpace ℝ (Fin d)) volume)
          (Measure.measure_univ_eq_zero.mp h0)
      exact ENNReal.toReal_pos h1 (measure_ne_top _ _)
    have hS : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → v a * σ.real univ ≤
        ∫ z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, v (a + ρ • (z : EuclideanSpace ℝ (Fin d)))
          ∂σ := by
      intro ρ hρ hρr
      have h1 := le_sphereAverage_of_comparison hρ
        (hv.mono (closedBall_subset_closedBall hρr)) (hcmp ρ hρ hρr)
      rw [average_eq, smul_eq_mul] at h1
      have h2 := (le_inv_mul_iff₀ hm).mp h1
      linarith
    set h : EuclideanSpace ℝ (Fin d) → ℝ :=
      (ball (0 : EuclideanSpace ℝ (Fin d)) r).indicator (fun x => v (a + x) - v a) with hh
    have hcontB : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => v (a + x) - v a)
        (closedBall 0 r) := by
      refine (hv.comp (show Continuous fun x : EuclideanSpace ℝ (Fin d) => a + x by
        fun_prop).continuousOn fun x hx => ?_).sub continuousOn_const
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hx
    have hint : Integrable h := by
      refine (integrable_indicator_iff measurableSet_ball).mpr ?_
      exact (hcontB.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
    have hkey : 0 ≤ ∫ x, h x := by
      rw [integral_polar volume h, integral_prod_symm _ (integrable_polar volume hint)]
      refine integral_nonneg fun ρ => ?_
      show (0 : ℝ) ≤ _
      have hρpos : 0 < (ρ : ℝ) := ρ.2
      have hnorm : ∀ z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          ‖(ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d))‖ = ρ := fun z => by
        rw [norm_smul, Real.norm_of_nonneg hρpos.le, mem_sphere_zero_iff_norm.mp z.2, mul_one]
      by_cases hρr : (ρ : ℝ) < r
      · have heq : ∀ z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            h ((ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d))) =
              v (a + (ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d))) - v a := fun z => by
          rw [hh, indicator_of_mem]
          rw [mem_ball_zero_iff, hnorm z]
          exact hρr
        simp_rw [heq]
        have hcont : Continuous fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
            v (a + (ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d))) := by
          refine hv.comp_continuous (by fun_prop) fun z => ?_
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm z]
          exact hρr.le
        have hI : Integrable (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
            v (a + (ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d)))) σ :=
          hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [integral_sub hI (integrable_const _), integral_const, smul_eq_mul]
        have := hS ρ hρpos hρr.le
        linarith
      · have heq : ∀ z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            h ((ρ : ℝ) • (z : EuclideanSpace ℝ (Fin d))) = 0 := fun z => by
          rw [hh, indicator_of_notMem]
          rw [mem_ball_zero_iff, hnorm z]
          exact hρr
        simp_rw [heq]
        simp
    have hm' : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
      ENNReal.toReal_pos (measure_ball_pos volume 0 hr).ne' measure_ball_lt_top.ne
    have hint2 : ∫ x, h x = ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, (v (a + x) - v a) := by
      rw [hh, integral_indicator measurableSet_ball]
    have hballfin : volume (ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
      measure_ball_lt_top.ne
    have hcontV : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => v (a + x))
        (closedBall 0 r) := by
      refine hv.comp (show Continuous fun x : EuclideanSpace ℝ (Fin d) => a + x by
        fun_prop).continuousOn fun x hx => ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hx
    have hintB : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => v (a + x))
        (ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
      (hcontV.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
    have hint3 : ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, (v (a + x) - v a) =
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, v (a + x)) -
          volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) r) * v a := by
      rw [integral_sub hintB (integrableOn_const hballfin), setIntegral_const, smul_eq_mul]
    have htrans : ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, v (a + x) =
        ∫ y in ball a r, v y := by
      have hpre : (fun x : EuclideanSpace ℝ (Fin d) => a + x) ⁻¹' ball a r =
          ball 0 r := by
        ext x
        simp [mem_ball, dist_eq_norm]
      rw [← hpre]
      exact (measurePreserving_add_left volume a).setIntegral_preimage_emb
        (measurableEmbedding_addLeft a) v (ball a r)
    have hvol : volume.real (ball a r) =
        volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
      simp only [Measure.real, Measure.addHaar_ball _ _ hr.le]
    rw [setAverage_eq, smul_eq_mul, hvol, ← htrans, le_inv_mul_iff₀ hm']
    rw [hint2, hint3] at hkey
    linarith

end Ball

end LatticeProb.Ishii
