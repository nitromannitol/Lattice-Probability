import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B2

/-!
# The normalized whole-plane GFF minus the zero-boundary GFF of the unit square

Let `W` be a space-time white noise and `h₀` the whole-plane GFF built from it, with pairings
`⟨h₀, φ⟩ = W(testL2 φ)` almost surely (Ding–Dubédat–Dunlap–Falconet heat-kernel representation).
The white-noise zero-boundary GFF `h^𝕍` of the open unit square `𝕍` has the circle averages
`h^𝕍_r(z) = √π W(K_{𝕍,(0,∞)} σ_{z,r})`.

`dgCircMod_normalized_sub_zeroBoundary`: on every box `K` all of whose points are at distance
at least `1/10` from `∂𝕍`, the difference of circle averages
`(h₀_r(z) − h₀_1(0)) − h^𝕍_r(z)` has a modification `Y` that is continuous on `K` for every
sample, whose maximum over `K` has a Gaussian tail, and whose circle averages
`∫ Y dσ_{z,r}` agree almost surely with this difference for every circle in `K`.
This is the circle-average form of the domain Markov decomposition
`h₀ − h₀_1(0) = h^𝕍 + 𝔥` on the square, with `𝔥` continuous on compact subsets.

Proof: Ding–Gwynne (arXiv:1807.01072) Lemma 3.1 for the pairs `(h₀, ĥ)` and `(h^𝕍, ĥ)`, where
`ĥ` is the white-noise field with the full heat kernel, and the random constant `h₀_1(0)`; the
three continuous modifications are combined linearly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric

open WhiteNoise GFFExist DZZ QuantumZipper SupTail CircleAvg KilledHeat GMCIdent DG

/-- **Domain Markov decomposition on the unit square, circle-average form.** For the whole-plane
GFF `h₀` of a white noise `W`, normalized by its unit-circle average, minus the white-noise
zero-boundary GFF of the open unit square: a continuous modification with a Gaussian tail of the
maximum on every box at distance `≥ 1/10` from the boundary of the square. -/
theorem _root_.LatticeProb.LQG.dgCircMod_normalized_sub_zeroBoundary
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC}
    (hW : IsWhiteNoise P W) (hh : LQGMetric.IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    DGCircMod P (ferniqueBox y b) fun z r ω =>
      LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 -
        Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω := by
  refine (((dgCircMod_h0_hat hW hh hae hb).sub (dg_lemma31_hU_hat_circ' hW hb hK)).sub
    (dgCircMod_const hW hh hae hb)).congr ?_
  intro z r ω
  simp only [dgHat]
  ring

/-- **The same for the normalized field** `h = h₀ − h₀_1(0)` (as a random distribution): its
circle averages minus those of the zero-boundary GFF of the unit square have a continuous
modification with a Gaussian tail of the maximum on every box at distance `≥ 1/10` from the
boundary of the square. -/
theorem _root_.LatticeProb.LQG.dgCircMod_normalizedWP_sub_zeroBoundary {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC}
    (hW : IsWhiteNoise P W) (hh : LQGMetric.IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    DGCircMod P (ferniqueBox y b) fun z r ω =>
      LQGMetric.circleAvg (addConst (h₀ ω) (-LQGMetric.circleAvg (h₀ ω) 1 0)) r z -
        Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω := by
  obtain ⟨Y, hc, hm, hT, hF⟩ :=
    LatticeProb.LQG.dgCircMod_normalized_sub_zeroBoundary hW hh hae hb hK
  refine ⟨Y, hc, hm, hT, fun z r hr hB => ?_⟩
  filter_upwards [hF z r hr hB, CircleAvg.ae_circleAvg_addConst hh z hr] with ω e1 e2
  rw [e1]
  simp only [e2]
  ring

end LQGMetric
