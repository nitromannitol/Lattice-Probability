import LatticeProb.Prob.ScaleInvariantNestedExitTrial
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii

/-!
# Nested exit trials of whole-plane space-filling SLE after a first hit

Let `ηL` be the whole-plane space-filling SLE curve of a mating-of-trees coupling, parametrized
by Lebesgue measure. Its law is invariant under re-rooting at any point and rescaling. Assume
the integrated lower bound for balls in the trace between successive exits: for some
`δ, p ∈ (0, 1)`, uniformly in `ε ∈ (0, 1)` and in the measurable set `S` of exit windows, a ball
of radius `δ ε` lies in the trace of `ηL` between its exits from `ball 0 1` and from
`ball 0 (1 + ε)` with probability at least `p` on the event that the exit window of `ηL` at
radius `1` lies in `S`.

Then, with `C = 2 / δ > 1` and the radii `r k = (k + 1) C ε ρ`, for every point `z` and every
`ρ > 0`, each nested exit trial after the first hit of `z` (a ball of radius `ε ρ` in the trace
between the exits from `ball z (r k)` and from `ball z (r (k + 1))`) has conditional probability
at least `p` given the completed σ-algebra of the re-rooted forward window at radius `r k`; and
the event that no ball of radius `ε ρ` lies in the trace between the first hit of `z` and the
exit from `ball z ρ` has probability at most `exp (p ^ 2) exp (-(p ^ 2 / 2) (C ε)⁻¹)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

section Coupling

variable {γ : ℝ} {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The space-filling curve of a mating-of-trees coupling is almost surely proper. -/
theorem IsMatingOfTreesCoupling.ae_tendsto_cocompact_ηL
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) :=
  hC.spaceFilling.mono fun _ h => h.2.1

/-- **Nested exit trials after a first hit, per step.** Under the integrated lower bound for
balls in the trace between the exits from `ball 0 1` and `ball 0 (1 + ε)`, with constants
`δ, p ∈ (0, 1)`, there are `C > 1` and `p ∈ (0, 1)` such that, for all `ε ∈ (0, 1)`, every
point `z`, every `ρ > 0` and every `k`, the `k`-th nested exit trial after the first hit of `z`
with radii `(k + 1) C ε ρ` and ball radius `ε ρ` has conditional probability at least `p` given
the completed σ-algebra of the re-rooted forward window at radius `(k + 1) C ε ρ`. -/
theorem IsMatingOfTreesCoupling.exists_le_condExp_nestedExitTrial_rerootedExitWindow
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h31 : ∃ δ ∈ Ioo (0 : ℝ) 1, ∃ p ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
        ENNReal.ofReal p * P {ω | (exitTimeAfter (ηL ω) 0 0 1,
            realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ≤
          P ({ω | (exitTimeAfter (ηL ω) 0 0 1,
              realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ∩
            {ω | ∃ w, ball w (δ * ε) ⊆ ηL ω '' Icc (exitTimeAfter (ηL ω) 0 0 1)
              (exitTimeAfter (ηL ω) 0 0 (1 + ε))})) :
    ∃ C : ℝ, 1 < C ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (ρ : ℝ), 0 < ρ →
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        p ≤ P[(nestedExitTrialEvent (fun ω => ⇑(ηL ω)) (fun ω => firstHit (ηL ω) z) z
            (fun k : ℕ => ((k : ℝ) + 1) * C * ε * ρ) (ε * ρ) k).indicator (fun _ => (1 : ℝ)) |
          eventuallyMeasurableSpace (MeasurableSpace.comap
            (fun ω => rerootedExitWindow (ηL ω) z (((k : ℝ) + 1) * C * ε * ρ)) inferInstance)
              (ae P) ⊓ m] ω := by
  have := hC.isProbabilityMeasure
  obtain ⟨δ, hδ, p, hp, hD3⟩ := h31
  refine ⟨2 / δ, ?_, p, hp.1, hp.2, fun ε hε z ρ hρ k => ?_⟩
  · rw [lt_div_iff₀ hδ.1]
    linarith [hδ.2]
  exact le_condExp_nestedExitTrial_rerootedExitWindow_of_scaleInvariant
    hC.measurable_curves.1 (IsMatingOfTreesCoupling.ae_tendsto_cocompact_ηL hC) z
    (fun s hs => IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL hC z hs 0) hδ.1 hD3
    hε.1 hρ k

/-- **Failure of the nested exit trials after a first hit.** Under the same integrated lower
bound, there are `C > 1` and `p ∈ (0, 1)` such that, for all `ε ∈ (0, 1)`, every point `z` and
every `ρ > 0`, the probability that no ball of radius `ε ρ` lies in the trace of the curve
between the first hit of `z` and its exit from `ball z ρ` is at most
`exp (p ^ 2) exp (-(p ^ 2 / 2) (C ε)⁻¹)`. -/
theorem IsMatingOfTreesCoupling.exists_measureReal_firstExitTrace_failure_le
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h31 : ∃ δ ∈ Ioo (0 : ℝ) 1, ∃ p ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ S : Set (ℝ × C(ℝ, ℂ)), MeasurableSet S →
        ENNReal.ofReal p * P {ω | (exitTimeAfter (ηL ω) 0 0 1,
            realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ≤
          P ({ω | (exitTimeAfter (ηL ω) 0 0 1,
              realWindowCurve 0 (exitTimeAfter (ηL ω) 0 0 1) (ηL ω)) ∈ S} ∩
            {ω | ∃ w, ball w (δ * ε) ⊆ ηL ω '' Icc (exitTimeAfter (ηL ω) 0 0 1)
              (exitTimeAfter (ηL ω) 0 0 (1 + ε))})) :
    ∃ C : ℝ, 1 < C ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (ρ : ℝ), 0 < ρ →
      P.real {ω | ¬ ∃ w, ball w (ε * ρ) ⊆ ηL ω '' Icc (firstHit (ηL ω) z)
        (sInf {t : ℝ | firstHit (ηL ω) z ≤ t ∧ ηL ω t ∉ ball z ρ})} ≤
        Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  have := hC.isProbabilityMeasure
  obtain ⟨δ, hδ, p, hp, hD3⟩ := h31
  refine ⟨2 / δ, ?_, p, hp.1, hp.2, fun ε hε z ρ hρ => ?_⟩
  · rw [lt_div_iff₀ hδ.1]
    linarith [hδ.2]
  exact measureReal_firstExitTrace_failure_le_of_scaleInvariant
    hC.measurable_curves.1 (IsMatingOfTreesCoupling.ae_tendsto_cocompact_ηL hC) z
    (fun s hs => IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL hC z hs 0) hδ.1 hp.1.le
    hp.2.le hD3 hε.1 hρ

end Coupling

end LatticeProb.LQG
