import LatticeProb.Prob.Kingman
import LatticeProb.Prob.AkcogluKrengel
import LatticeProb.Site

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Definitions for the almost-everywhere Akcoglu-Krengel theorem

Partial grids (`gridSet`, `natToSite`), grid averages (`gridAvg`) and grid boxes (`gridBox`) used to
iterate the one-parameter ergodic theorem one coordinate at a time; the volume-normalised value
`cubeRatio` on a cube; and the tail-deviation supremum `supDev` used in the moving-target Birkhoff
argument. Also restates the mean ergodic theorem `LatticeProb.akcoglu_krengel_mean` as a local
convergence statement for the volume-normalised mean along cubes.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The volume-normalised mean `∫ f(Q_n) / n^d` converges along the cubes `Q_n`, by the
multiparameter Fekete argument of `LatticeProb.akcoglu_krengel_mean`. -/
theorem exists_tendsto_mean_cubeRatio (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd :
    1 ≤ d)
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (∫ ω, f (latticeCube d n) ω ∂μ) / (n : ℝ) ^ d) atTop (𝓝 L) :=
  akcoglu_krengel_mean μ d hd τ hτ f hmeas hstat hbd hsub

/-- Coordinates in `s` range over `[0, n)`, the others are `0`. -/
def gridSet (d : ℕ) (s : Finset (Fin d)) (n : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.range n else {0}

/-- The site with coordinates `w i`. -/
def natToSite {d : ℕ} (w : Fin d → ℕ) : Site d := fun i => (w i : ℤ)

/-- Average of `h ∘ σ z` over the partial grid `gridSet d s n`. -/
noncomputable def gridAvg {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (s : Finset (Fin d))
    (n : ℕ) (ω : Ω) : ℝ :=
  (∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)) / (n : ℝ) ^ s.card

/-- The box with lower corner `m • w`, of side `m` in the coordinates of `s` and `k m` in
the others. -/
noncomputable def gridBox {d : ℕ} (m k : ℕ) (s : Finset (Fin d)) (w : Fin d → ℕ) :
    Finset (Site d) :=
  latticeBox (fun i => (m : ℤ) * (w i : ℤ))
    (fun i => (m : ℤ) * (w i : ℤ) + (if i ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)

/-- The normalised value on the cube `[0, n)^d`. -/
noncomputable def cubeRatio {d : ℕ} (f : Finset (Site d) → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  f (latticeCube d n) ω / (n : ℝ) ^ d

/-- The tail supremum of the deviation `|g (N + k) - G|`. -/
noncomputable def supDev (g : ℕ → Ω → ℝ) (G : Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  ⨆ k : ℕ, |g (N + k) x - G x|

end LatticeProb
