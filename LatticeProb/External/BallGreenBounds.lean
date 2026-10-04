import LatticeProb.Walk.BallGreenBounds

/-!
# The dimension-four ball-killed Green estimates, as a library proposition

The seven displays of `Sandpile.External.BallGreenBounds`, transcribed in the library's own
`LatticeProb.BallGreen` vocabulary. The proposition is stated here so that a formalization citing
it can carry it as an explicit hypothesis; it is proved in
`LatticeProb.External.BallGreenBoundsProved`.
-/

noncomputable section

namespace LatticeProb.External

/-- **The ball-killed Green estimates in dimension four**: the pointwise and square bounds, the
annular gradient bound, the cutoff field and its shifts, and the finite-time tail. -/
def BallGreenBounds : Prop :=
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      (∀ u : Site 4,
          0 ≤ LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 u ∧
            LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 u ≤ srwGreenInf 4 u ∧
            srwGreenInf 4 u ≤ C / (1 + euclidNorm u) ^ 2) ∧
      (∑' u : Site 4, LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 u ^ 2) ≤ C * Real.log (r : ℝ) ∧
      (∀ L : ℕ, 2 ≤ L →
          (∑' u : {u : Site 4 // euclidNorm u ≤ 2 * (L : ℝ)},
              LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 (u : Site 4) ^ 2) ≤
            C * Real.log (2 * (L : ℝ) + 2)) ∧
      (∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
          (∑' u : {u : Site 4 // (R : ℝ) ≤ euclidNorm u ∧ euclidNorm u ≤ 2 * (R : ℝ)},
              (LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 ((u : Site 4) + unit i) -
                LatticeProb.BallGreen.killedGreen (LatticeProb.BallGreen.box r) 0 (u : Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2) ∧
      (∀ L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, LatticeProb.BallGreen.IsCutoff φ →
          (∀ u : Site 4, |LatticeProb.BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
            (∑' u : Site 4, LatticeProb.BallGreen.cutField r L φ u ^ 3) ≤ C / (L : ℝ) ^ 2 ∧
            ∀ M : ℝ, 1 ≤ M → ∀ w : Site 4, euclidNorm w ≤ M * (L : ℝ) →
              (∑' u : Site 4, (LatticeProb.BallGreen.cutField r L φ u - LatticeProb.BallGreen.cutField r L φ (u - w)) ^ 2) ≤
                C * (1 + M) ^ 4) ∧
      (∀ A : ℝ, 1 ≤ A →
          (∀ u : Site 4, |LatticeProb.BallGreen.timeTail r A u| ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A)) ∧
            (∑' u : Site 4, LatticeProb.BallGreen.timeTail r A u ^ 2) ≤ C * Real.exp (-c * A))

end LatticeProb.External
