/-
# The corrected support-repair producer

`SupportRepair.lean` states the corrected residual `BandLimitedTestFnApproxOnDomain` and the sound
glue `rkLowFreqNet_of_domainSupportRepair`.  This module packages the two halves that produce it:

* `BandLimitedProjectionNet` — the **jet-net** half, the finite `H^{s₀}`-net of the
  low-frequency
  projections of the `H^s` unit ball of test functions on `D`, with integrable centres.  This is
  what the general-codomain Arzelà–Ascoli `exists_finite_supNet_of_uniformLip_of_proper`
  (`JetArzelaAscoli.lean`) produces once the band-limited `C^m` bound has made the projected family
  equicontinuous;
* `BandCentreSupportRepair` — the **support-repair** half, replacing a fixed net centre by a test
  function on `D` while keeping `H^{s₀}`-closeness.  This is the step the density input
  (`MollifierFourierTendsto`, `fourier_comp_smul`) feeds: cut the centre off with a test function
  `χ ∈ C_c^∞(D)`.

`bandLimitedTestFnApproxOnDomain_of_jetNet_and_supportRepair` composes them by the three-term
`sobolevNormSq` inequality, giving the producer `BandLimitedTestFnApproxOnDomain`.  The generator of
`BandLimitedProjectionNet` from `rkBandLimitedJetNet` + `rkResidual_holds` (the `C^m`-to-`H^{s₀}`
transfer for the non-compactly-supported band-limited centres) is the remaining named gap.
-/
import LatticeProb.Analysis.Sobolev.SupportRepair
import LatticeProb.Analysis.Sobolev.MollifierFourier
import LatticeProb.Analysis.Sobolev.JetArzelaAscoli

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The jet-net half.**  For every accuracy `η` there is a finite family `g i` of integrable
functions such that every low-frequency projection `P_Λ φ` of an `H^s`-unit test function on
`D` is
within `η` of some `g i` in `H^{s₀}`.  This is the finite-net input the general-codomain
Arzelà–Ascoli (`exists_finite_supNet_of_uniformLip_of_proper`) supplies. -/
def BandLimitedProjectionNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ) (η : ℝ), 0 < η →
      ∃ (N : ℕ) (g : Fin N → Space d → ℝ),
        (∀ i, Integrable (fun x => (g i x : ℂ))) ∧
        ∀ (φ : Space d → ℝ) (hφ : IsTestFn D φ), sobolevNormSq d s φ ≤ 1 →
          ∃ i, sobolevNormSq d s₀
              (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - g i x)
            ≤ ENNReal.ofReal η

/-- **The support-repair half.**  Every integrable net centre is within `η` of a test function on
`D` in the `H^{s₀}` norm.  This is the step `MollifierFourierTendsto` and the convolution theorem
feed. -/
def BandCentreSupportRepair : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ : ℝ) (g : Space d → ℝ),
    Integrable (fun x => (g x : ℂ)) → ∀ (η : ℝ), 0 < η →
      ∃ ψ : Space d → ℝ, IsTestFn D ψ ∧
        sobolevNormSq d s₀ (fun x => g x - ψ x) ≤ ENNReal.ofReal η

/-- The three-term triangle inequality for `sobolevNormSq`, splitting `φ - ψ` through a smooth
intermediate `P`. -/
private theorem sobolevNormSq_decomp_le'' {d : ℕ} (s : ℝ) {φ P ψ : Space d → ℝ}
    (hφ : Integrable (fun x => (φ x : ℂ))) (hP : Integrable (fun x => (P x : ℂ)))
    (hψ : Integrable (fun x => (ψ x : ℂ))) :
    sobolevNormSq d s (fun x => φ x - ψ x)
      ≤ 2 * sobolevNormSq d s (fun x => φ x - P x)
        + 2 * sobolevNormSq d s (fun x => P x - ψ x) := by
  have hφP : Integrable (fun x : Space d => ((φ x - P x : ℝ) : ℂ)) :=
    (hφ.sub hP).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have hPψ : Integrable (fun x : Space d => ((P x - ψ x : ℝ) : ℂ)) :=
    (hP.sub hψ).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Complex.ofReal_sub])
  have h := sobolevNormSq_add_le d s (fun x => φ x - P x) (fun x => P x - ψ x) hφP hPψ
  rwa [show (fun x => (φ x - P x) + (P x - ψ x)) = fun x => φ x - ψ x by
    funext x; ring] at h

/-- **The producer.**  The jet-net half and the per-centre support repair together give the
corrected residual `BandLimitedTestFnApproxOnDomain`: pick the finite net at accuracy `δ/4`,
repair each centre at accuracy `δ/4`, and split `P_Λ φ - ψ_i` through the centre `g_i`. -/
theorem bandLimitedTestFnApproxOnDomain_of_jetNet_and_supportRepair
    (hnet : BandLimitedProjectionNet) (hrep : BandCentreSupportRepair) :
    BandLimitedTestFnApproxOnDomain := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨N, g, hgint, hnet'⟩ := hnet d D hD s₀ s hss Λ hΛ (δ / 4) (by positivity)
  choose ψ hψ hψapprox using fun i => hrep d D hD s₀ (g i) (hgint i) (δ / 4) (by positivity)
  refine ⟨N, ψ, hψ, fun φ hφ hφs => ?_⟩
  obtain ⟨i, hi⟩ := hnet' φ hφ hφs
  refine ⟨i, ?_⟩
  have hP : Integrable (fun x : Space d => (bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x : ℂ)) :=
    (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hφ.1 hφ.2.1)).integrable.re.ofReal
  have hψi : Integrable (fun x : Space d => (ψ i x : ℂ)) :=
    ((hψ i).1.continuous.integrable_of_hasCompactSupport (hψ i).2.1).ofReal
  have hdec : sobolevNormSq d s₀ (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - ψ i x)
      ≤ 2 * sobolevNormSq d s₀ (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - g i x)
        + 2 * sobolevNormSq d s₀ (fun x => g i x - ψ i x) :=
    sobolevNormSq_decomp_le'' s₀ hP (hgint i) hψi
  have h2a : (2 : ℝ≥0∞) * ENNReal.ofReal (δ / 4) = ENNReal.ofReal (δ / 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsum : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ δ / 2)
      (by positivity : (0 : ℝ) ≤ δ / 2)]
    congr 1
    ring
  calc sobolevNormSq d s₀ (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - ψ i x)
      ≤ 2 * sobolevNormSq d s₀ (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - g i x)
        + 2 * sobolevNormSq d s₀ (fun x => g i x - ψ i x) := hdec
    _ ≤ 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
        add_le_add (mul_le_mul_right hi 2) (mul_le_mul_right (hψapprox i) 2)
    _ = ENNReal.ofReal δ := by rw [h2a, hsum]

/-- **The reduction of `rkLowFreqNet` to its two inputs.**  Composing the producer with the sound
glue `rkLowFreqNet_of_domainSupportRepair` (`SupportRepair.lean`): `rkLowFreqNet` now rests on the
jet net `BandLimitedProjectionNet` and the per-centre support repair `BandCentreSupportRepair`,
rather than on the (false) `BandLimitedTestFnApprox`. -/
theorem rkLowFreqNet_of_jetNet_and_supportRepair
    (hnet : BandLimitedProjectionNet) (hrep : BandCentreSupportRepair) : rkLowFreqNet :=
  rkLowFreqNet_of_domainSupportRepair
    (bandLimitedTestFnApproxOnDomain_of_jetNet_and_supportRepair hnet hrep)

/-- **The external, from the two inputs.**  Composing with
`rellichKondrachovNegSobolev_of_lowfreqNet` (`RellichLowFreqNet.lean`). -/
theorem rellichKondrachovNegSobolev_of_jetNet_and_supportRepair
    (hnet : BandLimitedProjectionNet) (hrep : BandCentreSupportRepair) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet (rkLowFreqNet_of_jetNet_and_supportRepair hnet hrep)

end LatticeProb.Sobolev
