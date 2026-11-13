import Mathlib
import LatticeProb.Prob.ConvergingTogether
import LatticeProb.Prob.LawFieldPairingContinuous

/-!
# A limit in law of random variables tending to zero in probability vanishes almost surely

Let `Y n` be real random variables on a probability space `(Ω, P)` which converge in law to the
image `ρ.map Φ` of a measure `ρ` under `Φ` (integrals of bounded continuous functions converge),
and which tend to `0` in probability. Converging together (Billingsley, *Convergence of probability
measures*, Theorem 3.1) shows that `Y n` also converges in law to the Dirac mass `δ_0`; by
uniqueness of weak limits `ρ.map Φ = δ_0`, that is `Φ = 0` almost everywhere for `ρ`.

The case of interest is the reversibility pairing
`(ν, P, s) ↦ ∫ f(z) E_{P_z}[g(X_s)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_s)] ψ(z) dν(z)`,
jointly continuous on `FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0` by
`continuous_reversibilityPairing`: if random elements `W n` of this space converge in law to `ρ`
and their pairings tend to `0` in probability, then the continuous mapping theorem (Billingsley,
Theorem 2.7) shows that the pairings converge in law to the image of `ρ` under the pairing, which
therefore vanishes `ρ`-almost everywhere.

* `LatticeProb.tendsto_integral_comp_of_tendstoInMeasure_zero`: real random variables tending to
  `0` in probability converge in law to `δ_0`.
* `LatticeProb.ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_zero`: if `Y n → ρ.map Φ` in law and
  `Y n → 0` in probability, then `Φ = 0` `ρ`-almost everywhere.
* `LatticeProb.ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_comp_zero`: if random elements `W n`
  of a topological space converge in law to `ρ`, `Φ` is continuous and `Φ (W n) → 0` in
  probability, then `Φ = 0` `ρ`-almost everywhere.
* `LatticeProb.ae_reversibilityPairing_eq_zero_of_tendsto_law`: the reversibility pairing of a
  limit in law vanishes almost surely when the pairings tend to `0` in probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

namespace LatticeProb

/-- Real random variables tending to `0` in probability converge in law to the Dirac mass at `0`:
`E[h (Y n)] → h 0` for every bounded continuous `h`. -/
theorem tendsto_integral_comp_of_tendstoInMeasure_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (hY : ∀ n, AEMeasurable (Y n) P)
    (hY0 : TendstoInMeasure P Y atTop 0) (h : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, h (Y n ω) ∂P) atTop (𝓝 (h 0)) := by
  have hY0' : TendstoInMeasure P (fun n => (hY n).mk (Y n)) atTop 0 :=
    hY0.congr' (Eventually.of_forall fun n => (hY n).ae_eq_mk) EventuallyEq.rfl
  have hmain := tendsto_integral_comp_of_tendstoInMeasure_sub (l := atTop) (P := fun _ => P)
    (X := fun _ _ => (0 : ℝ)) (Y := fun n => (hY n).mk (Y n)) (fun _ => measurable_const)
    (fun n => (hY n).measurable_mk) (ν := Measure.dirac 0)
    (fun f => by rw [integral_dirac]; simp)
    (fun η hη => by simpa using (tendstoInMeasure_iff_norm.1 hY0') η hη) h
  rw [integral_dirac] at hmain
  refine hmain.congr fun n => integral_congr_ae ?_
  filter_upwards [(hY n).ae_eq_mk] with ω hω
  rw [hω]

/-- **A limit in law of random variables tending to zero in probability vanishes.** Let `Y n` be
real random variables converging in law to the image `ρ.map Φ` of a measure `ρ` under an
almost everywhere measurable `Φ`. If `Y n → 0` in probability, then `Φ = 0` `ρ`-almost
everywhere. -/
theorem ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_zero {Ω T : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [MeasurableSpace T] {ρ : Measure T} {Φ : T → ℝ}
    (hΦ : AEMeasurable Φ ρ) {Y : ℕ → Ω → ℝ} (hY : ∀ n, AEMeasurable (Y n) P)
    (hlaw : ∀ h : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, h (Y n ω) ∂P) atTop (𝓝 (∫ x, h x ∂(ρ.map Φ))))
    (hY0 : TendstoInMeasure P Y atTop 0) :
    ∀ᵐ t ∂ρ, Φ t = 0 := by
  have h1 : (ρ.map Φ).real Set.univ = 1 := by
    have h := hlaw 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hprob : IsProbabilityMeasure (ρ.map Φ) :=
    ⟨by rw [measureReal_def] at h1; exact (ENNReal.toReal_eq_one_iff _).1 h1⟩
  have hdirac : ρ.map Φ = Measure.dirac 0 := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun h => ?_
    rw [integral_dirac]
    exact tendsto_nhds_unique (hlaw h) (tendsto_integral_comp_of_tendstoInMeasure_zero hY hY0 h)
  have h0 : ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), x = 0 :=
    (ae_dirac_iff (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)).2 rfl
  rw [← hdirac] at h0
  exact ae_of_ae_map hΦ h0

/-- **Continuous mapping to a limit that vanishes.** Let `W n` be random elements of a topological
space `T` converging in law to `ρ` (integrals of bounded continuous functions converge) and
`Φ : T → ℝ` continuous. If `Φ (W n) → 0` in probability, then `Φ = 0` `ρ`-almost everywhere. -/
theorem ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_comp_zero {Ω T : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [TopologicalSpace T]
    [MeasurableSpace T] [OpensMeasurableSpace T] {ρ : Measure T} {W : ℕ → Ω → T}
    (hW : ∀ n, AEMeasurable (W n) P)
    (hlaw : ∀ F : T →ᵇ ℝ, Tendsto (fun n => ∫ ω, F (W n ω) ∂P) atTop (𝓝 (∫ w, F w ∂ρ)))
    {Φ : T → ℝ} (hΦ : Continuous Φ)
    (hΦ0 : TendstoInMeasure P (fun n ω => Φ (W n ω)) atTop 0) :
    ∀ᵐ w ∂ρ, Φ w = 0 := by
  refine ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_zero (Y := fun n ω => Φ (W n ω))
    hΦ.measurable.aemeasurable (fun n => hΦ.measurable.comp_aemeasurable (hW n))
    (fun h => ?_) hΦ0
  have h' := hlaw (h.compContinuous ⟨Φ, hΦ⟩)
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at h'
  rwa [integral_map hΦ.measurable.aemeasurable h.continuous.aestronglyMeasurable]

/-- **The reversibility pairing of a limit in law vanishes.** Let `f, g` be bounded Lipschitz,
`ψ` continuous with compact support, and `W n = (ν n, Q n, s n)` random elements of
`FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0` (with any `σ`-algebra containing the
open sets) converging in law to `ρ`. If the reversibility pairings
`∫ f(z) E_{Q_z}[g(X_s)] ψ(z) dν(z) - ∫ g(z) E_{Q_z}[f(X_s)] ψ(z) dν(z)` of `W n` tend to `0` in
probability, then the pairing of `w` vanishes for `ρ`-almost every `w`. -/
theorem ae_reversibilityPairing_eq_zero_of_tendsto_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [MeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    [OpensMeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)]
    {ρ : Measure (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0)}
    {W : ℕ → Ω → FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0}
    (hW : ∀ n, AEMeasurable (W n) P)
    (hlaw : ∀ F : (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (W n ω) ∂P) atTop (𝓝 (∫ w, F w ∂ρ)))
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hpair : TendstoInMeasure P (fun n ω =>
      (∫ z, f z * (∫ X, g (X (W n ω).2.2) ∂((W n ω).2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z
          ∂((W n ω).1 : Measure ℂ))
        - ∫ z, g z * (∫ X, f (X (W n ω).2.2) ∂((W n ω).2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z
            ∂((W n ω).1 : Measure ℂ)) atTop 0) :
    ∀ᵐ w ∂ρ,
      (∫ z, f z * (∫ X, g (X w.2.2) ∂(w.2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z ∂(w.1 : Measure ℂ))
        - ∫ z, g z * (∫ X, f (X w.2.2) ∂(w.2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z
            ∂(w.1 : Measure ℂ) = 0 :=
  ae_eq_zero_of_tendsto_law_of_tendstoInMeasure_comp_zero hW hlaw
    (continuous_reversibilityPairing hfb hfl hgb hgl hψ hψc) hpair

end LatticeProb
