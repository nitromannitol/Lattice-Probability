import LatticeProb.LQG.LGDDensityExponent
import LatticeProb.LQG.LQGMeasureUnitSquareDecomp
import LatticeProb.LQG.WholePlaneZeroBoundaryCircleMod
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence

/-!
# The Liouville graph distance exponent of the LQG measure of the whole-plane GFF

Let `h₀` be the whole-plane GFF of a white noise `W`, normalized by its unit-circle average, and
let `B` be a set whose points are at distance `≥ 1/10` from the boundary of the unit square `𝕍`.
For every dyadic `γ`-LQG limit `m` of `h₀ − h₀_1(0)` (`0 < γ < 2`) and every pair `u ≠ v` whose
segment lies in the interior of `B`, almost surely the Liouville graph distance exponent of `m`
between `u` and `v` is the Ding-Zeitouni-Zhang exponent:
`log D_δ(m)(u, v) / log δ⁻¹ → χ_γ` as `δ ↓ 0`.

The proof combines the domain Markov decomposition of the LQG measure on the unit square
(`m = e^{γ Y} μ_{h^𝕍}` on the interior of `B`, with `Y` continuous) with the exponent of a measure
with a continuous density against `μ_{h^𝕍}`. The continuous modification `Y` of
`h₀ − h₀_1(0) − h^𝕍` on a Fernique box is the circle-average modification of Ding-Gwynne
(arXiv:1807.01072, Lemma 3.1).

* `LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit_of_circleAvg`: the statement for a given
  continuous modification `Y`.
* `LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit`: the statement for a Fernique box, with `Y`
  supplied by Ding-Gwynne Lemma 3.1.
-/

open MeasureTheory Set Filter Topology

namespace LQGMetric

open QuantumZipper GMCIdent3 GMCIdent WhiteNoise DZZ GFFExist DG SupTail

/-- **Liouville graph distance exponent of a dyadic LQG limit, given the harmonic correction.**
Let `Y(·, ω)` be continuous with circle averages equal, almost surely, to those of
`h₀ − h₀_1(0) − h^𝕍` on discs inside `B`. Then for every dyadic `γ`-LQG limit `m` of
`h₀ − h₀_1(0)` and `u ≠ v` whose segment lies in the interior of `B`, almost surely
`log D_δ(m)(u, v) / log δ⁻¹ → χ_γ` as `δ ↓ 0`. -/
theorem _root_.LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit_of_circleAvg {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {h₀ : Ω → DistC} (hm : Measurable h₀)
    {B : Set ℂ} (hB : ∀ z ∈ B, Metric.ball z (1 / 10) ⊆ openSquare)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (hF : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ B →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω =>
        LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 -
          Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {hε : Ω → ℝ → ℂ → ℝ} {m : Ω → Measure ℂ}
    (hlim : ∀ᵐ ω ∂P, LatticeProb.LQG.IsLQGLimit γ (hε ω) (m ω))
    (hcirc : ∀ᵐ ω ∂P, ∀ k, hε ω (LatticeProb.LQG.dyadicScale k) =ᵐ[volume] fun z =>
      LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0)
    {u v : ℂ} (huv : u ≠ v)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → u + (t : ℂ) * (v - u) ∈ interior B) :
    ∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log (lgdDZZ (m ω) δ u v).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 (chiDZZ γ)) := by
  obtain ⟨Ω', _, P', X, _, hX⟩ := QuantumZipper.K3.exists_zeroGFFOn openSquare
  have hBsq : interior B ⊆ openSquare := fun z hz =>
    hB z (interior_subset hz) (Metric.mem_ball_self (by norm_num))
  exact LatticeProb.LQG.ae_tendsto_lgdRatio_of_restrict_eq_withDensity hW hγ hγ2 hYc
    isOpen_interior hBsq
    (LatticeProb.LQG.ae_restrict_eq_withDensity_of_isLQGLimit hX hW hm hB hYc hYm hF hγ hγ2
      hlim hcirc) huv hseg

/-- **Liouville graph distance exponent of a dyadic LQG limit of the whole-plane GFF.** Let `h₀`
be a whole-plane GFF whose pairings agree almost surely with those of the white noise `W`, and let
`K` be a Fernique box whose points are at distance `≥ 1/10` from the boundary of the unit square.
For every dyadic `γ`-LQG limit `m` of `h₀ − h₀_1(0)` (`0 < γ < 2`) and `u ≠ v` whose segment lies
in the interior of `K`, almost surely `log D_δ(m)(u, v) / log δ⁻¹ → χ_γ` as `δ ↓ 0`. -/
theorem _root_.LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {h₀ : Ω → DistC}
    (hh : LQGMetric.IsWholePlaneGFF h₀ P) (hm : Measurable h₀)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {hε : Ω → ℝ → ℂ → ℝ} {m : Ω → Measure ℂ}
    (hlim : ∀ᵐ ω ∂P, LatticeProb.LQG.IsLQGLimit γ (hε ω) (m ω))
    (hcirc : ∀ᵐ ω ∂P, ∀ k, hε ω (LatticeProb.LQG.dyadicScale k) =ᵐ[volume] fun z =>
      LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0)
    {u v : ℂ} (huv : u ≠ v)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → u + (t : ℂ) * (v - u) ∈ interior (ferniqueBox y b)) :
    ∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log (lgdDZZ (m ω) δ u v).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 (chiDZZ γ)) := by
  obtain ⟨Y, hYc, hYm, -, hF⟩ :=
    LatticeProb.LQG.dgCircMod_normalized_sub_zeroBoundary hW hh hae hb hK
  exact LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit_of_circleAvg hW hm hK hYc hYm hF hγ
    hγ2 hlim hcirc huv hseg

end LQGMetric
