import LatticeProb.Gauss.PairingCountableTests
import LatticeProb.LQG.LQGMetric
import LatticeProb.LQG.WeylScalingAnnulusCrossing

/-!
# The LQG metric does not depend on the version of the field

Let `𝔇` assign to each pairing functional `T : (ℂ → ℝ) → ℝ` a function `𝔇 T : ℂ → ℂ → ℝ` such that each
`T ↦ 𝔇 T z w` is measurable for `distributionMeasurableSpace`. If two random pairing functionals `F` and `G` have almost
surely the same pairing with each test function separately, and the metrics `𝔇 (F ω)` and `𝔇 (G ω)` are almost surely
jointly continuous, then almost surely `𝔇 (F ω) u v = 𝔇 (G ω) u v` for all `u, v`. The exceptional event does not depend
on `(u, v)`: each `T ↦ 𝔇 T z w` depends on countably many test functions, and continuity extends the equality from a
countable dense set of pairs.

For a γ-LQG metric (`IsLQGMetric`) and two versions `hC`, `hC'` of the whole-plane GFF on the same probability space
(almost surely equal pairings with each test function), the metrics of `hC + f` and `hC' + f` agree almost surely, for
every random continuous function `f`.

* `LatticeProb.LQG.ae_forall_eq_of_ae_eq_pairings`
* `LatticeProb.LQG.ae_forall_eq_of_ae_eq_pairings_of_isEuclideanLengthMetric`
* `LatticeProb.LQG.IsLQGMetric.ae_forall_eq_of_ae_eq_pairings`
-/

open MeasureTheory LatticeProb.Gauss

namespace LatticeProb.LQG

/-- Two random pairing functionals with almost surely the same pairing with each test function have almost surely the
same metric at all pairs of points, for a measurable metric assignment whose metrics are almost surely jointly
continuous at both. -/
theorem ae_forall_eq_of_ae_eq_pairings {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hmeas : ∀ z w, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    {F G : Ω → (ℂ → ℝ) → ℝ} (hFG : ∀ φ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂μ, F ω φ = G ω φ)
    (hF : ∀ᵐ ω ∂μ, Continuous fun q : ℂ × ℂ => 𝔇 (F ω) q.1 q.2)
    (hG : ∀ᵐ ω ∂μ, Continuous fun q : ℂ × ℂ => 𝔇 (G ω) q.1 q.2) :
    ∀ᵐ ω ∂μ, ∀ u v, 𝔇 (F ω) u v = 𝔇 (G ω) u v := by
  set s := TopologicalSpace.denseSeq (ℂ × ℂ)
  have hpts : ∀ᵐ ω ∂μ, ∀ n, 𝔇 (F ω) (s n).1 (s n).2 = 𝔇 (G ω) (s n).1 (s n).2 :=
    ae_all_iff.2 fun n =>
      ae_eq_comp_of_ae_eq_pairings (g := fun T => 𝔇 T (s n).1 (s n).2) (hmeas _ _) hFG
  filter_upwards [hpts, hF, hG] with ω h1 h2 h3 u v
  have h := Continuous.ext_on (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)) h2 h3
    (by rintro _ ⟨n, rfl⟩; exact h1 n)
  exact congrFun h (u, v)

/-- `ae_forall_eq_of_ae_eq_pairings` when both metrics are almost surely Euclidean length metrics. -/
theorem ae_forall_eq_of_ae_eq_pairings_of_isEuclideanLengthMetric {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hmeas : ∀ z w, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    {F G : Ω → (ℂ → ℝ) → ℝ} (hFG : ∀ φ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂μ, F ω φ = G ω φ)
    (hF : ∀ᵐ ω ∂μ, IsEuclideanLengthMetric (𝔇 (F ω)))
    (hG : ∀ᵐ ω ∂μ, IsEuclideanLengthMetric (𝔇 (G ω))) :
    ∀ᵐ ω ∂μ, ∀ u v, 𝔇 (F ω) u v = 𝔇 (G ω) u v :=
  ae_forall_eq_of_ae_eq_pairings hmeas hFG (hF.mono fun _ h => h.continuous_uncurry)
    (hG.mono fun _ h => h.continuous_uncurry)

/-- A γ-LQG metric of a whole-plane GFF plus a random continuous function does not depend on the version of the GFF:
for two whole-plane GFFs `hC`, `hC'` on the same probability space with almost surely the same pairing with each test
function, almost surely `D_{hC + f}(u, v) = D_{hC' + f}(u, v)` for all `u, v`. -/
theorem IsLQGMetric.ae_forall_eq_of_ae_eq_pairings {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} {f : Ω → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hGFF' : IsWholePlaneGFF P hC' hcirc')
    (hfc : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    (hCC' : ∀ φ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P, hC ω φ = hC' ω φ) :
    ∀ᵐ ω ∂P, ∀ u v,
      𝔇 (addFunPairing (hC ω) (f ω)) u v = 𝔇 (addFunPairing (hC' ω) (f ω)) u v :=
  ae_forall_eq_of_ae_eq_pairings_of_isEuclideanLengthMetric h𝔇.measurable_apply
    (fun φ hφ => (hCC' φ hφ).mono fun ω h => by simp only [addFunPairing, h])
    (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hGFF hfc hfm).ae_isEuclideanLengthMetric
    (h𝔇.satisfiesLQGMetricAxioms Ω P hC' hcirc' f hGFF' hfc hfm).ae_isEuclideanLengthMetric

end LatticeProb.LQG
