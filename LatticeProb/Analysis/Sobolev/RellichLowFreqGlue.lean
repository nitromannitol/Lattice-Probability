/-
# The Rellich low-frequency glue: the sound truncation and support-repair inputs

`rellichKondrachovNegSobolev_of_lowfreqNet` (`RellichLowFreqNet.lean`) reduces the external
`RellichKondrachovNegSobolev` to the residual `rkLowFreqNet`.  The route to `rkLowFreqNet` that
does *not* go through the false `rkUniformCmNet` (`RellichCmNetReduction.lean`; it asks the rough
fields `φ` themselves to be `C^m`-close to test functions, which fails once `s < m`) runs through
the **low-frequency projection** `P_Λ φ = bandProj d Λ …`.

This module lands that route as two named inputs and their composition:

* `BandProjHighFreq` — the truncation identity
  `sobolevNormSq d s (φ - P_Λ φ) ≤ sobolevNormSqHigh d s Λ φ`, which follows from
  `fourier_bandProj` (`FejerLimit.lean`) and the support of `1 - bandCut`; it is named because the
  `L¹` Fourier linearity `𝓕 (φ - P_Λφ) = 𝓕φ - 𝓕 (P_Λφ)` is not packaged in this
  file;
* `BandLimitedTestFnApprox` — the support repair (cerw-ds1's packet): the real projections of the
  `H^s` unit ball are `H^{s₀}`-approximated by test functions on `D`;
* `rkLowFreqNet_of_truncation_and_supportRepair` — the composition, splitting `φ - ψ_i` through
  the projection and summing the high-frequency part and the repaired projection error.

No use is made of `rkUniformCmNet` / `BandLimitedCmNet`, which are false.
-/
import LatticeProb.Analysis.Sobolev.Additivity
import LatticeProb.Analysis.Sobolev.FejerLimit
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The truncation identity.**  The `H^s` error of the real projection `P_Λ φ` is controlled by
the high-frequency part of `φ`. -/
def BandProjHighFreq : Prop :=
  ∀ (d : ℕ) (s : ℝ) (Λ : ℝ) (hΛ : 0 < Λ),
    ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ),
      sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
        ≤ sobolevNormSqHigh d s Λ φ

/-- **The support-repair input.**  The real projections of the `H^s` unit ball are
`H^{s₀}`-approximated by test functions on `D`. -/
def BandLimitedTestFnApprox : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ) (δ : ℝ), 0 < δ →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
          (hcs : HasCompactSupport φ),
          sobolevNormSq d s φ ≤ 1 →
            ∃ i, sobolevNormSq d s₀
                (fun x => bandProj d Λ hΛ.ne' φ hcont hcs x - ψ i x)
              ≤ ENNReal.ofReal δ

/-- The high-frequency part is monotone decreasing in the cutoff radius. -/
private theorem sobolevNormSqHigh_mono_radius {d : ℕ} (s : ℝ) {Λ₁ Λ₂ : ℝ}
    (h : Λ₁ ≤ Λ₂) (φ : Space d → ℝ) :
    sobolevNormSqHigh d s Λ₂ φ ≤ sobolevNormSqHigh d s Λ₁ φ := by
  unfold sobolevNormSqHigh
  refine lintegral_mono_set (fun ξ hξ => ?_)
  simp only [Set.mem_setOf_eq] at hξ ⊢
  exact lt_of_le_of_lt h hξ

/-- The three-term triangle inequality for `sobolevNormSq`, splitting `φ - ψ` through a smooth
intermediate `P`. -/
private theorem sobolevNormSq_decomp_le {d : ℕ} (s : ℝ) {φ P ψ : Space d → ℝ}
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

/-- **The composition.**  The truncation identity and the support repair together discharge
`rkLowFreqNet`: choose the cutoff `Λ'` making the high-frequency part `≤ δ/4`, apply the support
repair at `Λ'` with accuracy `δ/4`, and split `φ - ψ_i` through the projection. -/
theorem rkLowFreqNet_of_truncation_and_supportRepair
    (htrunc : BandProjHighFreq) (hrep : BandLimitedTestFnApprox) : rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨Λ₀, _hΛ₀nonneg, htail₀⟩ := exists_sobolevNormSqHigh_le_truncation
    (d := d) (s₀ := s₀) (s := s) hss (Real.sqrt (δ / 4))
    (Real.sqrt_pos_of_pos (by positivity))
  set Λ' : ℝ := max Λ₀ 1 with _hΛ'def
  have hΛ'pos : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛ'ge : Λ₀ ≤ Λ' := le_max_left _ _
  obtain ⟨N, ψ, hψ, hnet⟩ := hrep d D hD s₀ s hss Λ' hΛ'pos (δ / 4) (by positivity)
  refine ⟨N, ψ, hψ, fun φ hφ hLow _hφn => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ.1 hφ.2.1 hLow
  refine ⟨i, ?_⟩
  have hP := htrunc d s₀ Λ' hΛ'pos φ hφ.1 hφ.2.1
  have htail' : sobolevNormSqHigh d s₀ Λ' φ ≤ ENNReal.ofReal (δ / 4) :=
    (sobolevNormSqHigh_mono_radius s₀ hΛ'ge φ).trans
      ((htail₀ φ hLow).trans (le_of_eq (by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 4)])))
  have hφi : Integrable (fun x : Space d => (φ x : ℂ)) :=
    (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).ofReal
  have hPi : Integrable
      (fun x : Space d => (bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x : ℂ)) :=
    (bandTrunc d Λ' hΛ'pos.ne' (realToComplexSchwartz d φ hφ.1 hφ.2.1)).integrable.re.ofReal
  have hψi : Integrable (fun x : Space d => (ψ i x : ℂ)) :=
    ((hψ i).1.continuous.integrable_of_hasCompactSupport (hψ i).2.1).ofReal
  have hdec := sobolevNormSq_decomp_le s₀ hφi hPi hψi
  have h1 : sobolevNormSq d s₀
      (fun x => φ x - bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x) ≤ ENNReal.ofReal (δ / 4) :=
    hP.trans htail'
  have h2 : sobolevNormSq d s₀
      (fun x => bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x - ψ i x)
        ≤ ENNReal.ofReal (δ / 4) :=
    hi
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
  calc sobolevNormSq d s₀ (fun x => φ x - ψ i x)
      ≤ 2 * sobolevNormSq d s₀ (fun x => φ x - bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x)
        + 2 * sobolevNormSq d s₀
            (fun x => bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x - ψ i x) := hdec
    _ ≤ 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
        add_le_add (mul_le_mul_right h1 2) (mul_le_mul_right h2 2)
    _ = ENNReal.ofReal δ := by rw [h2a, hsum]

/-- **The external, from the two inputs.**  Composing the sound composition with the glue
`rellichKondrachovNegSobolev_of_lowfreqNet` discharges `RellichKondrachovNegSobolev`. -/
theorem rellichKondrachovNegSobolev_of_truncation_and_supportRepair
    (htrunc : BandProjHighFreq) (hrep : BandLimitedTestFnApprox) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet
    (rkLowFreqNet_of_truncation_and_supportRepair htrunc hrep)

end LatticeProb.Sobolev
