/- Joint convergence for functionals Lipschitz on an admissible class of paths.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.FddBlockTightness
import LatticeProb.Prob.Scaling.BoundedFunctionalLift

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.Scaling.BoundedFunctionalLift

noncomputable section
namespace LatticeProb.Scaling.FddNiceFunctional

/-- A bounded functional only needs to be Lipschitz on the paths that occur.
The extension to arbitrary paths is constructed before applying the finite-net theorem. -/
theorem tendsto_integral
    {E B : Type*} [PseudoMetricSpace E] [PseudoMetricSpace B] [Nonempty B]
    [MeasurableSpace B] [BorelSpace B]
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι}
    {f : (i : ι) → E → Ω i → ℝ} {g : E → Ω' → ℝ}
    {V : (i : ι) → Ω i → B} {Vlim : Ω' → B}
    {K : Set E} (hK : IsCompact K) {Nice : (E → ℝ) → Prop}
    {G0 : E → ℝ} (hG0 : Nice G0)
    (hfnice : ∀ᶠ i in L, ∀ ω, Nice (fun z => f i z ω))
    (hgnice : ∀ ω, Nice (fun z => g z ω))
    (hVm : ∀ᶠ i in L, Measurable (V i)) (hVlimm : Measurable Vlim)
    (hfm : ∀ᶠ i in L, ∀ z, Measurable (f i z)) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K)
    {Φ : B → (E → ℝ) → ℝ}
    (hfΦm : ∀ᶠ i in L, Measurable fun ω => Φ (V i ω) (fun z => f i z ω))
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun i ω => (V i ω, fun k => f i (x k) ω)) L
        (fun ω => (Vlim ω, fun k => g (x k) ω)) P Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L,
      P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧ η < |f i z ω - f i y ω|}
        ≤ ENNReal.ofReal ε)
    {M C D : ℝ} (hΦb : ∀ b v, |Φ b v| ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hpath : ∀ b v w, Nice v → Nice w →
      |Φ b v - Φ b w| ≤ C * supDistOn K v w)
    (hblock : ∀ a b v, Nice v → |Φ a v - Φ b v| ≤ D * dist a b) :
    Tendsto (fun i => ∫ ω, Φ (V i ω) (fun z => f i z ω) ∂P i) L
      (𝓝 (∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦb (Classical.arbitrary B) G0)
  let Φ' : B → (E → ℝ) → ℝ := fun b => liftPhiOn K (Φ b) Nice (C + 2 * M)
  have hL : 0 ≤ C + 2 * M := by positivity
  have heq : ∀ b v, Nice v → Φ' b v = Φ b v := by
    intro b v hv
    exact liftPhiOn_eq_of_nice K (Φ b) Nice (hΦb b) hv
      (fun w hw => hpath b v w hv hw) hC
  have hmeas : ∀ᶠ i in L, Measurable fun ω => Φ' (V i ω) (fun z => f i z ω) := by
    filter_upwards [hfΦm, hfnice] with i hi hn
    have hh : (fun ω => Φ' (V i ω) (fun z => f i z ω)) =
        (fun ω => Φ (V i ω) (fun z => f i z ω)) :=
      funext fun ω => heq _ _ (hn ω)
    rwa [hh]
  have hbound : ∀ b v, |Φ' b v| ≤ M + (C + 2 * M) := fun b v =>
    abs_liftPhiOn_le K (Φ b) Nice hG0 (hΦb b) hL v
  have hmod := block_modulus_liftPhiOn K Φ Nice hG0 hΦb hL hD hblock
  have hconv := FddBlockTightness.tendsto_integral_of_fdd_of_equicontinuous
    hK hVm hVlimm hfm hgm hgc hmeas hfdd htight hbound hmod
  have hright : (∫ ω, Φ' (Vlim ω) (fun z => g z ω) ∂Q) =
      ∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω => heq _ _ (hgnice ω))
  rw [hright] at hconv
  apply hconv.congr'
  filter_upwards [hfnice] with i hi
  exact integral_congr_ae (Eventually.of_forall fun ω => heq _ _ (hi ω))

end LatticeProb.Scaling.FddNiceFunctional
