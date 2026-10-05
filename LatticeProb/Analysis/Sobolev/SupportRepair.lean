/-
# The domain-restricted support repair — REFUTED

`RellichLowFreqGlue.lean` reduces `rkLowFreqNet` to a single input, `BandLimitedTestFnApprox`,
which asks that the real projections `P_Λ φ = bandProj d Λ … φ` of the rough fields `φ` be
`H^{s₀}`-approximated by test functions on `D`.  As stated, that definition quantifies over
**every** compactly supported `φ` (`ContDiff ℝ ⊤ φ`, `HasCompactSupport φ`) and does **not**
require `tsupport φ ⊆ D` — the datum the only consumer actually supplies.

The mismatch matters.  The conclusion demands a *fixed* finite family `ψ i` of test functions on
`D` with `sobolevNormSq d s₀ (P_Λ φ - ψ i) ≤ δ`.  Take `φ_R = c · ρ(· - R)` for a fixed
bump `ρ` and the constant `c` normalising `sobolevNormSq d s φ_R = 1`.  Then
`sobolevNormSq d s₀ (P_Λ φ_R)`
is translation-invariant, hence a fixed positive number, while for any fixed `D`-supported test
function `ψ` the pairing tends to `0` as `R → ∞`:

  `⟨P_Λ φ_R, ψ⟩_{H^{s₀}}
    = ∫ (1+‖ξ‖²)^{s₀} e^{-2πi R·ξ} ‖𝓕(P_Λ ρ)(ξ)‖ ‖𝓕ψ(ξ)‖ dξ → 0`,

so `sobolevNormSq d s₀ (P_Λ φ_R - ψ) → sobolevNormSq d s₀ (P_Λ ρ) · c² +
  sobolevNormSq d s₀ ψ`,
bounded below independently of `ψ`.  For `δ` below that bound no centre covers `φ_R`.  So
`BandLimitedTestFnApprox` is too strong to be the residual, and the committed implication is from
an unprovable premise.

**REFUTED.**  The domain-restricted residual below is **false** (a band-limited projection of a
unit test function on `D` is never `H^{s₀}`-close to a test function on the fixed bounded `D`), so
the composition `rkLowFreqNet_of_domainSupportRepair` rests on an unprovable premise.  This module
is kept only as the record of that route; the sound producer is
`SupportProducerWitness.BandLimitedProjectionNetWitness`, which replaces the support repair by
witnesses and needs none.
-/
import LatticeProb.Analysis.Sobolev.RellichLowFreqGlue

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The domain-restricted support-repair residual — REFUTED, do not use as a hypothesis.**
Like `BandLimitedTestFnApprox`, but the fields are `IsTestFn D` (so `tsupport φ ⊆ D`).  This is
**false as stated**: the projection `P_Λ φ` of a unit test function on `D` is not
`H^{s₀}`-approximable by a test function on the fixed bounded `D`.  The sound replacement is
`SupportProducerWitness.BandLimitedProjectionNetWitness` (witnesses instead of a support repair). -/
def BandLimitedTestFnApproxOnDomain : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ) (δ : ℝ), 0 < δ →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ (φ : Space d → ℝ) (hφ : IsTestFn D φ), sobolevNormSq d s φ ≤ 1 →
          ∃ i, sobolevNormSq d s₀
              (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - ψ i x)
            ≤ ENNReal.ofReal δ

/-- The unrestricted residual implies the domain-restricted one (the latter quantifies over fewer
fields): the `IsTestFn D φ` datum only unpacks the `ContDiff`/`HasCompactSupport` hypotheses of
`BandLimitedTestFnApprox`. -/
theorem bandLimitedTestFnApproxOnDomain_of_approx (h : BandLimitedTestFnApprox) :
    BandLimitedTestFnApproxOnDomain :=
  fun d D hD s₀ s hss Λ hΛ δ hδ =>
    let ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss Λ hΛ δ hδ
    ⟨N, ψ, hψ, fun φ hφ hφs => hnet φ hφ.1 hφ.2.1 hφs⟩

/-- The high-frequency part is monotone decreasing in the cutoff radius. -/
private theorem sobolevNormSqHigh_mono_radius' {d : ℕ} (s : ℝ) {Λ₁ Λ₂ : ℝ}
    (h : Λ₁ ≤ Λ₂) (φ : Space d → ℝ) :
    sobolevNormSqHigh d s Λ₂ φ ≤ sobolevNormSqHigh d s Λ₁ φ := by
  unfold sobolevNormSqHigh
  refine lintegral_mono_set (fun ξ hξ => ?_)
  simp only [Set.mem_setOf_eq] at hξ ⊢
  exact lt_of_le_of_lt h hξ

/-- The three-term triangle inequality for `sobolevNormSq`, splitting `φ - ψ` through a smooth
intermediate `P`. -/
private theorem sobolevNormSq_decomp_le' {d : ℕ} (s : ℝ) {φ P ψ : Space d → ℝ}
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

/-- **The sound composition.**  The truncation identity (`sobolevNormSq_sub_bandProj_le`) and the
**domain-restricted** support repair together discharge `rkLowFreqNet`: choose the cutoff `Λ'`
making the high-frequency part `≤ δ/4`, apply the support repair at `Λ'` with accuracy
`δ/4`, and
split `φ - ψ_i` through the projection.  Unlike `rkLowFreqNet_of_truncation_and_supportRepair`
(`RellichLowFreqGlue.lean`), this consumes `BandLimitedTestFnApproxOnDomain`, which matches the
`IsTestFn D φ` hypothesis of `rkLowFreqNet`. -/
theorem rkLowFreqNet_of_domainSupportRepair (hrep : BandLimitedTestFnApproxOnDomain) :
    rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨Λ₀, _hΛ₀nonneg, htail₀⟩ := exists_sobolevNormSqHigh_le_truncation
    (d := d) (s₀ := s₀) (s := s) hss (Real.sqrt (δ / 4))
    (Real.sqrt_pos_of_pos (by positivity))
  set Λ' : ℝ := max Λ₀ 1 with _hΛ'def
  have hΛ'pos : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛ'ge : Λ₀ ≤ Λ' := le_max_left _ _
  obtain ⟨N, ψ, hψ, hnet⟩ := hrep d D hD s₀ s hss Λ' hΛ'pos (δ / 4) (by positivity)
  refine ⟨N, ψ, hψ, fun φ hφ hLow _hHigh => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hLow
  refine ⟨i, ?_⟩
  have hP := sobolevNormSq_sub_bandProj_le d Λ' hΛ'pos φ hφ.1 hφ.2.1 s₀
  have htail' : sobolevNormSqHigh d s₀ Λ' φ ≤ ENNReal.ofReal (δ / 4) :=
    (sobolevNormSqHigh_mono_radius' s₀ hΛ'ge φ).trans
      ((htail₀ φ hLow).trans (le_of_eq (by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 4)])))
  have hφi : Integrable (fun x : Space d => (φ x : ℂ)) :=
    (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).ofReal
  have hPi : Integrable
      (fun x : Space d => (bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x : ℂ)) :=
    (bandTrunc d Λ' hΛ'pos.ne' (realToComplexSchwartz d φ hφ.1 hφ.2.1)).integrable.re.ofReal
  have hψi : Integrable (fun x : Space d => (ψ i x : ℂ)) :=
    ((hψ i).1.continuous.integrable_of_hasCompactSupport (hψ i).2.1).ofReal
  have hdec := sobolevNormSq_decomp_le' s₀ hφi hPi hψi
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

end LatticeProb.Sobolev
