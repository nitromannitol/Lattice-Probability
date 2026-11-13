import LatticeProb.LQG.AnnulusEnergyBoundGMS
import LatticeProb.Analysis.GridAnnulusCountRpow
import LatticeProb.Probability.PolyHighProbUnionFamily

/-!
# The energy bound for the logarithmic annulus function on every annulus of a polynomial grid

Step 2 of the proof of Lemma 4.3 of Berestycki-Gwynne (*Random walks on mated-CRT maps and Liouville Brownian
motion*): the energy bound (4.7) for the discrete harmonic extension of `log(r/|· - c|)/log(r/s)` holds simultaneously
for all annuli `B_{q^j}(c) \ B̄_{q^k}(c)` of a grid with centres `ε^a (m + n i)` and radii in polynomially small ranges,
with polynomially high probability, provided the grid exponent satisfies `2a < α`, where `α` is the exponent of
Theorem 3.2 of Gwynne-Miller-Sheffield (*Harmonic functions on mated-CRT maps*).

The event attached to a grid annulus is the implication "the annulus satisfies the hypotheses of (4.7) ⟹ (4.7)
holds", so annuli outside the range of (4.7) cost nothing in the union bound
(`polyHighProb_forall_mem_finset`), and the number of grid annuli is at most `K ε^{-(2a + δ)}`
(`exists_card_gridAnnulusIndex_le_rpow`).
-/

noncomputable section

namespace LatticeProb.LQG

open MeasureTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal

/-- **The energy bound (4.7) on a polynomial grid of annuli** (Berestycki-Gwynne, proof of Lemma 4.3). For every
mating-of-trees coupling there are exponents `α, β > 0` and, for each `ρ ∈ (0, 1)`, a constant `A > 0` such that for
every grid (ratio `q > 1`, mesh `ε^a` with `2a < α`, centres in `[-ρg, ρg]²` up to one mesh, outer radii in
`[b₁ ε^{p₁}, Y₁]`, inner radii in `[b₂ ε^{p₂}, Y₂]`), with polynomially high probability as `ε → 0`, every grid annulus
`B_r(c) \ B̄_s(c)` with `s < r ≤ 1`, `B_r(c) ⊆ B_ρ(0)`, `(s log(r/s))⁻¹ ≤ ε^{-β}` and `(s² log(r/s))⁻¹ ≤ ε^{-β}` carries
a discrete harmonic extension of `log(r/|· - c|)/log(r/s)`, and every such extension has energy at most
`A · 2π / log(r/s) + ε^α` on the cells meeting the annulus. -/
theorem polyHighProb_grid_annulus_energyOn_le :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧
          ∀ (q a ρg b₁ p₁ Y₁ b₂ p₂ Y₂ : ℝ), 1 < q → 0 ≤ ρg → 0 ≤ a → 2 * a < α →
            0 < b₁ → 0 ≤ p₁ → b₁ ≤ Y₁ → 0 < b₂ → 0 ≤ p₂ → b₂ ≤ Y₂ →
            LatticeProb.Gauss.PolyHighProb P fun ε => {ω | ∀ i ∈ gridAnnulusIndex q (ε ^ a) ρg (b₁ * ε ^ p₁) Y₁
                (b₂ * ε ^ p₂) Y₂,
              q ^ i.2.2.2 < q ^ i.2.2.1 → q ^ i.2.2.1 ≤ 1 →
              ball (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball (0 : ℂ) ρ →
              (q ^ i.2.2.2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-β) →
              ((q ^ i.2.2.2) ^ 2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-β) →
              ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                (∃ g : ℤ → ℝ, (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω))
                  (ball (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
                    closedBall (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2))
                  (fun w : ℂ => Real.log (q ^ i.2.2.1 /
                      ‖w - ((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖) /
                    Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) g) ∧
                ∀ g : ℤ → ℝ, (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω))
                  (ball (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
                    closedBall (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2))
                  (fun w : ℂ => Real.log (q ^ i.2.2.1 /
                      ‖w - ((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖) /
                    Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) g →
                  (MatedCRT.graph ε (bm ω) h).energyOn
                      (verticesMeeting (MatedCRT.cell ε (η ω))
                        (ball (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
                          closedBall (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I))
                            (q ^ i.2.2.2))) g ≤
                    ENNReal.ofReal A * ENNReal.ofReal (2 * Real.pi / Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) +
                      ENNReal.ofReal (ε ^ α)} := by
  intro γ hγ hγ2 Ω _ _ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm hC
  obtain ⟨α, hα, β, hβ, hT⟩ := annulus_energyOn_le_of_matingOfTrees γ hγ hγ2 Ω P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm hC
  refine ⟨α, hα, β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A, hA, Cr, hT'⟩ := hT ρ hρ0 hρ1
  refine ⟨A, hA, fun q a ρg b₁ p₁ Y₁ b₂ p₂ Y₂ hq hρg ha haα hb₁ hp₁ hbY₁ hb₂ hp₂ hbY₂ => ?_⟩
  obtain ⟨K, hK, hcard⟩ := exists_card_gridAnnulusIndex_le_rpow (δ := (α - 2 * a) / 2) hq hρg ha hb₁ hp₁
    hbY₁ hb₂ hp₂ hbY₂ (by linarith)
  refine LatticeProb.Gauss.polyHighProb_forall_mem_finset P _ _ hK (le_max_right Cr 0)
    (by linarith : 2 * a + (α - 2 * a) / 2 < α) hcard ?_
  intro ε hε hε1 i _
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hyp : q ^ i.2.2.2 < q ^ i.2.2.1 ∧ q ^ i.2.2.1 ≤ 1 ∧
      ball (((ε ^ a : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball (0 : ℂ) ρ ∧
      (q ^ i.2.2.2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-β) ∧
      ((q ^ i.2.2.2) ^ 2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-β)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hyp
    calc _ ≤ _ := measure_mono fun ω hω => by
          simp only [Set.mem_ofPred_eq] at hω ⊢
          exact fun hgood => hω fun _ _ _ _ _ => hgood
      _ ≤ ENNReal.ofReal (Cr * ε ^ α) :=
          hT' ε hε hε1 _ (q ^ i.2.2.2) (q ^ i.2.2.1) (zpow_pos hq0 _) h1 h2 h3 h4 h5
      _ ≤ ENNReal.ofReal (max Cr 0 * ε ^ α) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left Cr 0) (Real.rpow_nonneg hε.le α))
  · refine (measure_mono_null (fun ω hω => ?_) measure_empty).le.trans zero_le
    exact absurd (fun h1 h2 h3 h4 h5 => (hyp ⟨h1, h2, h3, h4, h5⟩).elim) hω

end LatticeProb.LQG

end
