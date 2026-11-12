import LatticeProb.Gauss.GaussianTilt
import LatticeProb.Gauss.CircleAverageApprox2

/-!
# Approximate Palm identity for circle-average approximations of the LQG area measure

Let `h` be a whole-plane Gaussian free field with pairings `hC ω φ` and circle averages `hcirc ω r z`. The
`ε`-approximation of its `γ`-LQG area measure has density `ε^{γ²/2} exp (γ h_ε(z))` with respect to Lebesgue
measure. For a jointly measurable functional `Φ (z, h)` of a root `z ∈ U` and of the whole family of observables
of `h`, the Cameron-Martin (Girsanov) tilt by the Gaussian variable `h_ε(z)` gives the approximate Palm identity

`E ∫_U exp (γ h_ε(z)) Φ (z, h) dz = ∫_U exp (γ² Var h_ε(z) / 2) E [Φ (z, h + γ Cov (h, h_ε(z)))] dz`

(Duplantier-Miller-Sheffield, *Liouville quantum gravity as a mating of trees*, Lemma A.10, and
Duplantier-Sheffield, *Liouville quantum gravity and KPZ*, Section 3.3). Deterministic factors of the density,
such as `ε^{γ²/2}` or the effect of a logarithmic insertion, can be absorbed in `Φ`.

## Main results

* `LatticeProb.Gauss.observablePath`: the family of values of all admissible observables of a sample.
* `LatticeProb.Gauss.IsWholePlaneGFF.measurable_observablePath`: it is a measurable map into the product space.
* `LatticeProb.Gauss.IsWholePlaneGFF.aemeasurable_circle_uncurry`: for `r > 0`, `(ω, z) ↦ h_r(z)` is a.e.
  measurable for the product of `P` with any `σ`-finite measure on `ℂ`.
* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lintegral_exp_circle_mul_eq`: the approximate Palm identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.Gauss

/-- The family `(o ↦ value of the admissible observable o)` of a sample `(hC, hcirc)`. -/
def observablePath {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    GFFObservable.Admissible → ℝ :=
  fun o => o.1.eval (hC ω) (hcirc ω)

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Every observable of a whole-plane GFF is a random variable, so the family of all of them is a measurable map
into the product space. -/
theorem measurable_observablePath (hh : IsWholePlaneGFF P hC hcirc) :
    Measurable (observablePath hC hcirc) := by
  refine measurable_pi_iff.2 fun o => ?_
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact hh.measurable_pairing φ ho
  | circle r z => exact hh.measurable_circle r z ho

/-- For `r > 0`, the circle average `(ω, z) ↦ h_r(z)` is a.e. measurable for the product of `P` with a
`σ`-finite measure on `ℂ`: it is measurable in `ω` for each `z` and almost surely continuous in `z`. -/
theorem aemeasurable_circle_uncurry (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (ν : Measure ℂ) [SFinite ν] :
    AEMeasurable (fun p : Ω × ℂ => hcirc p.1 r p.2) (P.prod ν) := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 hh.ae_continuousOn_circle)
  let u : ℂ → Ω → ℝ := fun z => Nᶜ.indicator fun ω => hcirc ω r z
  have hum : ∀ z, Measurable (u z) := fun z => (hh.measurable_circle r z hr).indicator hNm.compl
  have huc : ∀ ω, Continuous fun z => u z ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have : (fun z => u z ω) = fun _ => 0 := by
        funext z
        exact indicator_of_notMem (notMem_compl_iff.2 hω) _
      rw [this]
      exact continuous_const
    · have hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
        by_contra hnot
        exact hω (hNsub hnot)
      have : (fun z => u z ω) = fun z => hcirc ω r z := by
        funext z
        exact indicator_of_mem (mem_compl hω) _
      rw [this]
      exact hcont.comp_continuous (f := fun z : ℂ => (r, z)) (by fun_prop)
        fun z => ⟨mem_Ioi.2 hr, mem_univ z⟩
  have hmeas : Measurable fun p : Ω × ℂ => u p.2 p.1 :=
    (measurable_uncurry_of_continuous_of_measurable huc hum).comp measurable_swap
  refine hmeas.aemeasurable.congr ?_
  refine measure_mono_null (t := N ×ˢ (univ : Set ℂ)) (fun p hp => ?_) ?_
  · by_contra hpN
    exact hp (indicator_of_mem (mem_compl fun h => hpN ⟨h, mem_univ _⟩) _)
  · rw [Measure.prod_prod, hN0, zero_mul]

/-- **Approximate Palm identity.** For `ε > 0`, a Borel set `U` of roots and a jointly measurable functional
`Φ (z, ·) ≥ 0` of a root and of the family of all observables of the field,
`E ∫_U exp (γ h_ε(z)) Φ (z, h) dz = ∫_U exp (γ² Var h_ε(z) / 2) E [Φ (z, h + γ Cov (h, h_ε(z)))] dz`,
where `h + γ Cov (h, h_ε(z))` is the family `o ↦ h(o) + γ Cov (h(o), h_ε(z))`. -/
theorem lintegral_lintegral_exp_circle_mul_eq (hh : IsWholePlaneGFF P hC hcirc) {γ ε : ℝ} (hε : 0 < ε)
    (U : Set ℂ) {Φ : ℂ → (GFFObservable.Admissible → ℝ) → ℝ≥0∞}
    (hΦ : Measurable fun p : ℂ × (GFFObservable.Admissible → ℝ) => Φ p.1 p.2) :
    ∫⁻ ω, ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * hcirc ω ε z)) * Φ z (observablePath hC hcirc ω) ∂volume ∂P =
      ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ ^ 2 * wholePlaneGFFCov (.circle ε z) (.circle ε z) / 2)) *
        ∫⁻ ω, Φ z (fun o => observablePath hC hcirc ω o + γ * wholePlaneGFFCov o.1 (.circle ε z)) ∂P := by
  have := hh.isProbabilityMeasure
  have hpm := hh.measurable_observablePath
  have hF : AEMeasurable (fun p : Ω × ℂ =>
      ENNReal.ofReal (Real.exp (γ * hcirc p.1 ε p.2)) * Φ p.2 (observablePath hC hcirc p.1))
      (P.prod (volume.restrict U)) := by
    refine AEMeasurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp_aemeasurable
        (Real.measurable_exp.comp_aemeasurable
          ((hh.aemeasurable_circle_uncurry hε (volume.restrict U)).const_mul γ))
    · exact (hΦ.comp (measurable_snd.prodMk (hpm.comp measurable_fst))).aemeasurable
  rw [lintegral_lintegral_swap hF]
  refine lintegral_congr fun z => ?_
  have hq : GFFObservable.IsAdmissible (.circle ε z) := hε
  let Y : GFFObservable.Admissible → Ω → ℝ := fun o ω => o.1.eval (hC ω) (hcirc ω)
  have hYm : ∀ t, Measurable (Y t) := fun t => measurable_pi_iff.1 hpm t
  have hcen : ∀ t, P[Y t] = 0 := fun t => hh.integral_eq_zero t.1 t.2
  let q : GFFObservable.Admissible := ⟨.circle ε z, hq⟩
  have hΦz : Measurable (Φ z) := hΦ.comp measurable_prodMk_left
  have htilt := lintegral_exp_mul_tilt hh.isGaussianProcess hYm hcen q γ hΦz
  have hvar : Var[Y q; P] = wholePlaneGFFCov (.circle ε z) (.circle ε z) := by
    rw [← covariance_self (hYm q).aemeasurable]
    exact hh.covariance_eq _ _ hq hq
  have hcov : ∀ t : GFFObservable.Admissible,
      cov[Y t, Y q; P] = wholePlaneGFFCov t.1 (.circle ε z) := fun t =>
    hh.covariance_eq _ _ t.2 hq
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (γ * hcirc x ε z)) * Φ z (observablePath hC hcirc x) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * Var[Y q; P] / 2)) *
        (ENNReal.ofReal (Real.exp (γ * Y q x - γ ^ 2 * Var[Y q; P] / 2)) *
          Φ z (fun t => Y t x)) := by
    intro x
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    simp only [Y, q, GFFObservable.eval]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htilt, hvar]
  congr 1
  refine lintegral_congr fun x => ?_
  congr 1
  funext t
  rw [hcov t]
  rfl

end IsWholePlaneGFF

end LatticeProb.Gauss
