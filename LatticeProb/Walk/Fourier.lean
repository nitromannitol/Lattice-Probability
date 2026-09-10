/-
The Fourier representation of the simple random walk heat kernel, proved
without any Fourier theory: the right-hand side satisfies the same
nearest-neighbour recursion as the kernel, and the base case is the
orthogonality of characters (`LatticeProb.integral_cos_int_mul_eq`).

  `p_n(0, z) = (2π)^{-d} ∫_{[-π,π]^d} φ(θ)^n cos(θ · z) dθ`,
  `φ(θ) = d^{-1} ∑_j cos θ_j`.

This is the first half of the `d`-dimensional local central limit theorem
(`Sandpile.External.LocalCLT`); the three-region split of the θ-integral and
the uniformity are in `LatticeProb/Walk/LocalCLT.lean`.
-/
import LatticeProb.Walk.Character
import LatticeProb.Walk.SRW

noncomputable section

namespace LatticeProb

open MeasureTheory

/-! ### The torus, the character and the Fourier representation -/

/-- The inner product `θ · z` of a real vector with a lattice site. -/
def dotSite {d : ℕ} (θ : Fin d → ℝ) (z : Site d) : ℝ := ∑ i, θ i * (z i : ℝ)

/-- The characteristic function `φ(θ) = d^{-1} ∑_j cos θ_j` of one step of the
simple random walk on `ℤ^d`. -/
def charFn (d : ℕ) (θ : Fin d → ℝ) : ℝ := (∑ i, Real.cos (θ i)) / d

/-- Lebesgue measure on the torus `[-π, π]^d`, as a measure on `Fin d → ℝ`. -/
def torusMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (-Real.pi) Real.pi)

/-- The Fourier representation of the kernel: the integral of
`φ(θ)^n cos(θ · z)` over the torus. -/
def fourierHeat (d : ℕ) (n : ℕ) (z : Site d) : ℝ :=
  ∫ θ : Fin d → ℝ, charFn d θ ^ n * Real.cos (dotSite θ z) ∂torusMeasure d


theorem fourierHeat_zero_self (d : ℕ) : fourierHeat d 0 0 = (2 * Real.pi) ^ d := by
  simp only [fourierHeat, pow_zero, one_mul]
  have hdot : ∀ θ : Fin d → ℝ, dotSite θ 0 = 0 := by
    intro θ; unfold dotSite; simp
  simp only [hdot, Real.cos_zero]
  unfold torusMeasure
  have hpi : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have hfac : ∀ i : Fin d, (volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ
      = ENNReal.ofReal (2 * Real.pi) := by
    intro i
    rw [Measure.restrict_apply (s := Set.Icc (-Real.pi) Real.pi) (t := Set.univ),
      Set.univ_inter, Real.volume_Icc]
    · have h2 : (2:ℝ) * Real.pi = Real.pi + Real.pi := by ring
      rw [h2, ENNReal.ofReal_add hpi hpi]
      have h3 : Real.pi - -Real.pi = Real.pi + Real.pi := by ring
      rw [h3, ENNReal.ofReal_add hpi hpi]
    · exact MeasurableSet.univ
  have hmass : (Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (-Real.pi) Real.pi))
      Set.univ = ENNReal.ofReal ((2 * Real.pi) ^ d) := by
    rw [Measure.pi_univ, Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const]
    rw [show Finset.univ.card = d from Fintype.card_fin d]
    have hp2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
    exact (ENNReal.ofReal_pow hp2 d).symm
  have hint : Integrable (fun _ : Fin d → ℝ => (1:ℝ))
      (Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (-Real.pi) Real.pi)) :=
    integrable_const _
  have h1 : (∫ θ : Fin d → ℝ, (1:ℝ) ∂Measure.pi fun _ : Fin d =>
      volume.restrict (Set.Icc (-Real.pi) Real.pi))
      = ((Measure.pi fun _ : Fin d =>
        volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ).toReal :=
    by
      have h : ∫ (θ : Fin d → ℝ), (1:ℝ) ∂(Measure.pi fun _ : Fin d =>
          volume.restrict (Set.Icc (-Real.pi) Real.pi))
          = ((Measure.pi fun _ : Fin d =>
            volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ).toReal := by
        have h' := integral_const (1:ℝ) (μ := Measure.pi fun _ : Fin d =>
          volume.restrict (Set.Icc (-Real.pi) Real.pi))
        rw [h']
        simp [Measure.real]
      simpa using h
  rw [h1, hmass, ENNReal.toReal_ofReal]
  positivity

end LatticeProb