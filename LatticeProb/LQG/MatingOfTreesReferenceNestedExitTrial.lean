import LatticeProb.LQG.MatingOfTreesNestedExitTrial
import LatticeProb.LQG.MatingOfTreesExitWindowReference

/-!
# Nested exit trials of whole-plane space-filling SLE from the conditional unit-exit bound

Let `ηL` be the whole-plane space-filling SLE curve of a mating-of-trees coupling, parametrized
by Lebesgue measure. Assume the conditional lower bound for its path after the first hit of the
origin: for every `q ∈ (0, 1)`, given the path stopped at its exit from the unit ball, a ball of
radius `a q` lies in the trace between the exits from `ball 0 1` and from `ball 0 (1 + q)` with
conditional probability at least `p > 0`. This is the conditional form of the estimate of
Gwynne, Holden and Miller (An almost sure KPZ relation for SLE and Brownian motion, Lemma 3.1).

Then there are `C > 1` and `p' ∈ (0, 1)` such that, for every point `z`, every `ρ > 0` and every
`ε ∈ (0, 1)`, each nested exit trial after the first hit of `z` with radii `(k + 1) C ε ρ` has
conditional probability at least `p'` given the re-rooted forward window, and no ball of radius
`ε ρ` lies in the trace between the first hit of `z` and the exit from `ball z ρ` with
probability at most `exp (p' ^ 2) exp (-(p' ^ 2 / 2) (C ε)⁻¹)` (the estimate of Lemma 3.6 there).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

variable {γ : ℝ} {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **Nested exit trials after a first hit, per step, from the conditional unit-exit bound.** -/
theorem IsMatingOfTreesCoupling.exists_le_condExp_nestedExitTrial_of_reference
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ηsize p : ℝ} (hη : 0 < ηsize) (hp : 0 < p)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let ν := P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) :
    ∃ C : ℝ, 1 < C ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (ρ : ℝ), 0 < ρ →
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        p ≤ P[(nestedExitTrialEvent (fun ω => ⇑(ηL ω)) (fun ω => firstHit (ηL ω) z) z
            (fun k : ℕ => ((k : ℝ) + 1) * C * ε * ρ) (ε * ρ) k).indicator (fun _ => (1 : ℝ)) |
          eventuallyMeasurableSpace (MeasurableSpace.comap
            (fun ω => rerootedExitWindow (ηL ω) z (((k : ℝ) + 1) * C * ε * ρ)) inferInstance)
              (ae P) ⊓ m] ω :=
  IsMatingOfTreesCoupling.exists_le_condExp_nestedExitTrial_rerootedExitWindow hC
    (IsMatingOfTreesCoupling.exitWindow_ball_bound_of_reference hC hη hp href)

/-- **Failure of the nested exit trials after a first hit, from the conditional unit-exit
bound.** For every point `z` and every `ρ > 0`, the trace of the curve between the first hit of
`z` and its exit from `ball z ρ` fails to contain a ball of radius `ε ρ` with probability at most
`exp (p ^ 2) exp (-(p ^ 2 / 2) (C ε)⁻¹)`. -/
theorem IsMatingOfTreesCoupling.exists_measureReal_firstExitTrace_failure_le_of_reference
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ηsize p : ℝ} (hη : 0 < ηsize) (hp : 0 < p)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let ν := P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) :
    ∃ C : ℝ, 1 < C ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (ρ : ℝ), 0 < ρ →
      P.real {ω | ¬ ∃ w, ball w (ε * ρ) ⊆ ηL ω '' Icc (firstHit (ηL ω) z)
        (sInf {t : ℝ | firstHit (ηL ω) z ≤ t ∧ ηL ω t ∉ ball z ρ})} ≤
        Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) :=
  IsMatingOfTreesCoupling.exists_measureReal_firstExitTrace_failure_le hC
    (IsMatingOfTreesCoupling.exitWindow_ball_bound_of_reference hC hη hp href)

end LatticeProb.LQG
