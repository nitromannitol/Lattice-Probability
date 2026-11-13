/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.ZeroConeL46 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TPrime
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Phase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimeReconstruction
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ConeDisk
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.FieldRecentre
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Data

/-!
# [18] Lemma 4.6 and Proposition 4.5 on the frozen zero-cone model, unconditionally

The measurable reconstruction (`GMS4c.bundle_l46tLocalReconstructionPrime_holds`, `GMS4c/PrimeReconstruction.lean`) produced the exact
`BundleSec4.L46TLocalReconstructionPrime` instance (measurable [18] Lemma 4.3 with the all-visit inner-degree event) on every
admissible disk. This file closes it into the zero-cone transfer theorems (`BundleSec4/L46TPrime.lean`):

* `zeroCone_primeReconstruction` — the instance in the exact shape of the `hlocal` hypothesis;
* **`l46t_zeroCone_innerDegreeBoundPolylogPrime_holds`**, **`l46t_zeroCone_innerDegreeBoundPolylog_holds`** — [18]
  Lemma 4.6 in the polylog form (`k(1+ζ)+1` power; all-visit and first-visit inner degrees) on the frozen zero-cone
  cell model `GMS4b.l46tZeroConeCellModel D hγ`, with no hypothesis;
* `l46t_zeroCone_prop45_holds` — [18] Proposition 4.5 on that model for ANY two circle-average processes with the
  sup bound `GMS4b.CircleAverageSupBound` (the event `GMS4b.prop45Event` takes the processes as parameters);
* `exists_zeroCone_circleAvgVersion` — the zero-cone circle averages have a jointly continuous version on circles in
  `𝔻` with the sup bound: the identification of `h₀|_𝔻` with a normalized whole-plane GFF `Xt|_𝔻`
  (`GMS4.prop48_exists_zeroCone_disk_wholePlaneGFF`), the GMCUpper version of `Xt` with [MS16b] Prop. 2.4
  (`GMCUpper.circleAverageSupBoundModel_holds`) and the locality argument's `L43O.circleAvg_eq_of_restrict_eq`;
* **`zeroCone_prop45_holds`** — fully unconditional: there are versions `H` (zero-cone field, on circles in `𝔻`)
  and `HIG` (IG field) such that, with the actual phase, `P[prop45Event(H, HIG + U)ᶜ] ≤ C ε^α` for every admissible
  `ρ, q, ζ`.

The version processes are NOT the literal pathwise `LQGMetric.circleAvg` processes (`GMS4.fieldCircleAverage`,
`GMS4.igCircleAverage`, used by the `GMS4.goodEvent`): a version agrees with the literal process a.s. at each
fixed `(r, z)` only (`DFGPS.IsCircleAvgVersion.ae_eq`), and the sup over `z ∈ B_ρ(0)` in the event needs simultaneous
identification, which neither the library nor the project provides.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic
open MatedCRTHarmonic.GMS4b

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **the measurable [18] Lemma 4.3 instance in the exact shape of the `hlocal` hypothesis.** -/
def zeroCone_primeReconstruction
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstructionPrime (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeFieldVersion D) hIG₀ T
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ :=
  fun _ hρ w hw k ζ ε hε => GMS4c.bundle_l46tLocalReconstructionPrime_holds D hγ hρ w hw k ζ ε hε

/-- **[18] Lemma 4.6 (polylog form, first visits) on the frozen zero-cone model, unconditionally.** -/
theorem l46t_zeroCone_innerDegreeBoundPolylog_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ k : ℕ, InnerDegreeBoundPolylog (l46tZeroConeCellModel D hγ) (2 * k) :=
  l46t_zeroCone_innerDegreeBoundPolylog_of_primeReconstruction D hγ
    (zeroCone_primeReconstruction D hγ)

/-- **[18] Proposition 4.5 on the frozen zero-cone model** for any two circle-average processes with the sup bound
(the reconstruction hypothesis is discharged by the measurable reconstruction). -/
theorem l46t_zeroCone_prop45_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : CircleAverageSupBound P H) (hHIG : CircleAverageSupBound P HIG)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 4)) :
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P (prop45Event (l46tZeroConeCellModel D hγ) H HIG ε ρ q ζ)ᶜ ≤
        ENNReal.ofReal (C * ε ^ α) :=
  l46t_zeroCone_prop45_of_primeReconstruction D hγ (zeroCone_primeReconstruction D hγ)
    hH hHIG hρ hq hζ

/-- **The zero-cone circle averages have a jointly continuous version with the sup bound.** `H` is continuous on
`(0, ∞) × ℂ` for every sample, agrees almost surely with the literal circle average of the zero-cone field
`(Canon.referenceSample D hγ ω).zeroConeField` on every circle `∂B_r(z)` with `B̄_r(z) ⊆ 𝔻`, and satisfies
`GMS4b.CircleAverageSupBound`. -/
theorem exists_zeroCone_circleAvgVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      (∀ r : ℝ, 0 < r → ∀ z : ℂ, closedBall z r ⊆ ball (0 : ℂ) 1 →
        (fun ω => H r z ω) =ᵐ[P]
          fun ω => LQGMetric.circleAvg (Canon.referenceSample D hγ ω).zeroConeField r z) ∧
      CircleAverageSupBound P H := by
  obtain ⟨Xt, hXt, hdisc⟩ := GMS4.prop48_exists_zeroCone_disk_wholePlaneGFF D hγ
  obtain ⟨H, hH, -⟩ := GMCUpper.exists_circleAvgVersion_normalized hXt
  refine ⟨H, hH.cont, fun r hr z hzr => ?_,
    GMCUpper.circleAverageSupBound_of_model hXt hH
      (GMCUpper.circleAverageSupBoundModel_holds hXt hH)⟩
  filter_upwards [hH.ae_eq r hr z, hdisc] with ω hω hres
  rw [hω]
  exact (L43O.circleAvg_eq_of_restrict_eq hres hr hzr).symm

/-- **[18] Proposition 4.5 on the frozen zero-cone model, fully unconditional.** There are jointly continuous
versions `H` of the zero-cone circle averages (on circles in `𝔻`) and `HIG` of the IG circle averages such that,
with the actual phase `T`, the Proposition 4.5 event fails with probability `O(ε^α)` for every admissible
`ρ, q, ζ`. -/
theorem zeroCone_prop45_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ H HIG : ℝ → ℂ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      (∀ r : ℝ, 0 < r → ∀ z : ℂ, closedBall z r ⊆ ball (0 : ℂ) 1 →
        (fun ω => H r z ω) =ᵐ[P]
          fun ω => LQGMetric.circleAvg (Canon.referenceSample D hγ ω).zeroConeField r z) ∧
      LQGMetric.DFGPS.IsCircleAvgVersion hIG₀ P HIG ∧
      ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2), ∀ ζ ∈ Ioo (0 : ℝ) (q / 4),
        ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
          P (prop45Event (l46tZeroConeCellModel D hγ) H (fun r z ω => HIG r z ω + T ω) ε ρ q ζ)ᶜ ≤
            ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨H, hcont, hver, hsup⟩ := exists_zeroCone_circleAvgVersion D hγ
  obtain ⟨HIG, hHIG, -, hHIGsup⟩ := exists_igCircleAvgVersion_withPhase D
  exact ⟨H, HIG, hcont, hver, hHIG, fun ρ hρ q hq ζ hζ =>
    l46t_zeroCone_prop45_holds D hγ hsup hHIGsup hρ hq hζ⟩

end Bundle

end MatedCRTHarmonic.BundleSec4
