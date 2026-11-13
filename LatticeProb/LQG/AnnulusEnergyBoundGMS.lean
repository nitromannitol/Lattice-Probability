import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Theorem3_2
import LatticeProb.Analysis.AnnulusEnergyClass

/-!
# Energy of the discrete harmonic extension of the logarithmic annulus function

For every mating-of-trees coupling, Theorem 3.2 of Gwynne-Miller-Sheffield (*Harmonic functions on mated-CRT maps*)
applies to the annulus `D = B_r(c) \ B̄_s(c) ⊆ B_ρ(0)` and the function `f = log(r/|· - c|)/log(r/s)`, with the
constant `C = 16π` for the boundary-area and bounded-convexity hypotheses and `K = ε^{-β}` for the regularity of `f`.
Since the Dirichlet energy of `f` is `2π / log(r/s)`, this gives the bound (4.7) in the proof of Lemma 4.3 of
Berestycki-Gwynne (*Random walks on mated-CRT maps and Liouville Brownian motion*): outside an event of probability at
most `Cr ε^α`, the discrete harmonic extension of `f` on the mated-CRT map exists and every such extension has energy at
most `A · 2π / log(r/s) + ε^α` on the cells meeting the annulus, uniformly over annuli in `B_ρ(0)` with
`(s log(r/s))⁻¹ ≤ ε^{-β}` and `(s² log(r/s))⁻¹ ≤ ε^{-β}`.
-/

noncomputable section

namespace LatticeProb.LQG

open MeasureTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal

/-- The energy bound (4.7) of Berestycki-Gwynne for the logarithmic function of an annulus, from Theorem 3.2 of
Gwynne-Miller-Sheffield: for every mating-of-trees coupling there are exponents `α, β > 0` and, for each `ρ ∈ (0, 1)`,
constants `A > 0` and `Cr` such that for every `ε ∈ (0, 1)` and every annulus `B_r(c) \ B̄_s(c)` with `0 < s < r ≤ 1`,
`B_r(c) ⊆ B_ρ(0)`, `(s log(r/s))⁻¹ ≤ ε^{-β}` and `(s² log(r/s))⁻¹ ≤ ε^{-β}`, the probability that the discrete harmonic
extension of `log(r/|· - c|)/log(r/s)` fails to exist or has energy above `A · 2π / log(r/s) + ε^α` is at most
`Cr ε^α`. -/
theorem annulus_energyOn_le_of_matingOfTrees :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
          ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            ∀ (c : ℂ) (s r : ℝ), 0 < s → s < r → r ≤ 1 → ball c r ⊆ ball (0 : ℂ) ρ →
            (s * Real.log (r / s))⁻¹ ≤ ε ^ (-β) → (s ^ 2 * Real.log (r / s))⁻¹ ≤ ε ^ (-β) →
              P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                (∃ g : ℤ → ℝ, (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω))
                  (ball c r \ closedBall c s) (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) g) ∧
                ∀ g : ℤ → ℝ, (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω))
                  (ball c r \ closedBall c s) (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) g →
                  (MatedCRT.graph ε (bm ω) h).energyOn
                      (MatedCRTHarmonic.verticesMeeting (MatedCRT.cell ε (η ω)) (ball c r \ closedBall c s)) g ≤
                    ENNReal.ofReal A * ENNReal.ofReal (2 * Real.pi / Real.log (r / s)) +
                      ENNReal.ofReal (ε ^ α)} ≤ ENNReal.ofReal (Cr * ε ^ α) := by
  intro γ hγ hγ2 Ω _ _ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm hC
  obtain ⟨α, hα, β, hβ, hT⟩ := MatedCRTHarmonic.theorem3_2 γ hγ hγ2 Ω P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm hC
  refine ⟨α, hα, β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A, hA, Cr, hT'⟩ := hT ρ hρ0 hρ1 (16 * Real.pi) (by linarith [Real.pi_gt_three])
  refine ⟨A, hA, Cr, fun ε hε0 hε1 c s r hs hsr hr hρ hK1 hK2 => ?_⟩
  have hK : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
  obtain ⟨hf, hL, hsup, hgrad, hcont⟩ := LatticeProb.annulus_log_regular c hs hsr hK hK1 hK2
  have h := hT' ε hε0 hε1 (ball c r \ closedBall c s) (LatticeProb.isOpen_annulus c s r) (sdiff_subset.trans hρ)
    (LatticeProb.volume_thickening_frontier_annulus_le_mul c hs.le hsr.le hr le_rfl)
    (LatticeProb.hasBoundedConvexity_annulus c hs.le LatticeProb.one_add_two_mul_pi_le_sixteen_mul_pi)
    _ hf hL hsup hgrad hcont
  rwa [LatticeProb.dirichletEnergy_annulus_log c hs hsr] at h

end LatticeProb.LQG

end
