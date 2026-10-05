/-
# The corrected low-frequency producer: witnesses instead of a support repair

The audit `LatticeProbAudit/RELLICH-LOWFREQ-SUPPORT-REPAIR.md` showed that
`BandLimitedTestFnApproxOnDomain` and its support-repair half `BandCentreSupportRepair` are false:
a band-limited projection is never `H^{s₀}`-close to a test function on a fixed bounded
domain `D`.
The correct architecture pairs each integrable net centre `g i` with a **witness** unit test
function `φ₀ i` whose projection is `H^{s₀}`-close to `g i`.  Then `rkLowFreqNet` follows by
comparing `φ` with `φ₀ i` through the centres and the truncation identity — no support
repair is ever needed, because the test-function centres are the witnesses `φ₀ i` themselves.

`BandLimitedProjectionNetWitness` is that corrected input; `rkLowFreqNet_of_projectionNetWitness`
discharges `rkLowFreqNet` (hence, with `rellichKondrachovNegSobolev_of_lowfreqNet`, the external
`RellichKondrachovNegSobolev`) from it.  What remains is the relative compactness of the projected
family (the first and third conjuncts of the input), which `rkBandLimitedJetNet`
(`RellichCmNetSupply.lean`) plus the `C^m`-to-`H^{s₀}` transfer supplies.
-/
import LatticeProb.Analysis.Sobolev.SupportRepair
import LatticeProb.Analysis.Sobolev.BandProjectionConsume

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The corrected jet-net input.**  For every accuracy `η` there is a finite family of integrable
centres `g i`, each paired with a unit test function `φ₀ i` on `D` whose projection is
`η`-close to `g i`, and such that every projection of a unit-ball test function on `D` is
`η`-close to some `g i`.  This is what the jet-net construction actually produces; unlike
`BandLimitedTestFnApproxOnDomain` it never asks a test function to approximate a band-limited
function. -/
def BandLimitedProjectionNetWitness : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ) (η : ℝ), 0 < η →
      ∃ (N : ℕ) (g : Fin N → Space d → ℝ),
        (∀ i, Integrable (fun x => (g i x : ℂ))) ∧
        (∀ i, ∃ (φ₀ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ₀)
            (hcs : HasCompactSupport φ₀),
          tsupport φ₀ ⊆ D ∧ (sobolevNormSq d s φ₀ ≤ 1 ∧
            sobolevNormSq d s₀ (fun x => bandProj d Λ hΛ.ne' φ₀ hcont hcs x - g i x)
              ≤ ENNReal.ofReal η)) ∧
        (∀ (φ : Space d → ℝ) (hφ : IsTestFn D φ), sobolevNormSq d s φ ≤ 1 →
          ∃ i, sobolevNormSq d s₀
            (fun x => bandProj d Λ hΛ.ne' φ hφ.1 hφ.2.1 x - g i x)
            ≤ ENNReal.ofReal η)

/-- The high-frequency part is monotone decreasing in the cutoff radius. -/
private theorem high_mono_radius {d : ℕ} (s : ℝ) {Λ₁ Λ₂ : ℝ}
    (h : Λ₁ ≤ Λ₂) (φ : Space d → ℝ) :
    sobolevNormSqHigh d s Λ₂ φ ≤ sobolevNormSqHigh d s Λ₁ φ := by
  unfold sobolevNormSqHigh
  refine lintegral_mono_set (fun ξ hξ => ?_)
  simp only [Set.mem_setOf_eq] at hξ ⊢
  exact lt_of_le_of_lt h hξ

/-- Negation does not change `sobolevNormSq`. -/
private theorem sobolevNormSq_negW {d : ℕ} (s : ℝ) (g : Space d → ℝ) :
    sobolevNormSq d s (fun x => -g x) = sobolevNormSq d s g := by
  rw [show (fun x => -g x) = fun x => (-1 : ℝ) * g x by funext x; ring,
    sobolevNormSq_const_mul]
  norm_num

/-- `sobolevNormSq` is symmetric in the difference. -/
private theorem sobolevNormSq_sub_commW {d : ℕ} (s : ℝ) (f g : Space d → ℝ) :
    sobolevNormSq d s (fun x => f x - g x) = sobolevNormSq d s (fun x => g x - f x) := by
  rw [show (fun x => g x - f x) = fun x => -(f x - g x) by funext x; ring, sobolevNormSq_negW]

/-- The three-term triangle inequality for `sobolevNormSq`, splitting `φ - ψ` through a smooth
intermediate `P`. -/
private theorem sobolevNormSq_decomp_leW {d : ℕ} (s : ℝ) {φ P ψ : Space d → ℝ}
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

/-- `2 * ofReal a = ofReal (2 * a)`. -/
private theorem two_mul_ofReal (a : ℝ) : (2 : ℝ≥0∞) * ENNReal.ofReal a
    = ENNReal.ofReal (2 * a) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- `2 * ofReal a + 2 * ofReal a = ofReal (4 * a)`. -/
private theorem two_mul_ofReal_add (a : ℝ) (ha : 0 ≤ a) :
    2 * ENNReal.ofReal a + 2 * ENNReal.ofReal a = ENNReal.ofReal (4 * a) := by
  rw [two_mul_ofReal a, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- **The corrected producer.**  The witness net discharges `rkLowFreqNet`: pick the truncation
`Λ'` making the high-frequency part `≤ δ/16` on the unit ball, run the witness net at `Λ'` with
accuracy `δ/16`, and compare `φ` with the witness `φ₀ i` through the centre `g i` in two
steps. -/
theorem rkLowFreqNet_of_projectionNetWitness (h : BandLimitedProjectionNetWitness) :
    rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨Λ₀, _hΛ₀nonneg, htail₀⟩ := exists_sobolevNormSqHigh_le_truncation
    (d := d) (s₀ := s₀) (s := s) hss (Real.sqrt (δ / 16))
    (Real.sqrt_pos_of_pos (by positivity))
  set Λ' : ℝ := max Λ₀ 1 with _hΛ'def
  have hΛ'pos : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛ'ge : Λ₀ ≤ Λ' := le_max_left _ _
  obtain ⟨N, g, hgint, hwit, hnet⟩ :=
    h d D hD s₀ s hss Λ' hΛ'pos (δ / 16) (by positivity)
  choose φ₀ hcont hcs htsupp hφ₀s hφ₀net using hwit
  have hφ₀test : ∀ i, IsTestFn D (φ₀ i) := fun i => ⟨hcont i, hcs i, htsupp i⟩
  have htail : ∀ (u : Space d → ℝ) (hu : IsTestFn D u), sobolevNormSq d s u ≤ 1 →
      sobolevNormSq d s₀ (fun x => u x - bandProj d Λ' hΛ'pos.ne' u hu.1 hu.2.1 x)
        ≤ ENNReal.ofReal (δ / 16) := by
    intro u hu hus
    refine (sobolevNormSq_sub_bandProj_le d Λ' hΛ'pos u hu.1 hu.2.1 s₀).trans ?_
    refine (high_mono_radius s₀ hΛ'ge u).trans ?_
    refine (htail₀ u hus).trans (le_of_eq ?_)
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 16)]
  refine ⟨N, φ₀, hφ₀test, fun φ hφ hLow _hHigh => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hLow
  refine ⟨i, ?_⟩
  have hφi : Integrable (fun x : Space d => (φ x : ℂ)) :=
    (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).ofReal
  have hφ₀i : Integrable (fun x : Space d => (φ₀ i x : ℂ)) :=
    ((hcont i).continuous.integrable_of_hasCompactSupport (hcs i)).ofReal
  have hPφ : Integrable
      (fun x : Space d => (bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x : ℂ)) :=
    (bandTrunc d Λ' hΛ'pos.ne' (realToComplexSchwartz d φ hφ.1 hφ.2.1)).integrable.re.ofReal
  have hPφ₀ : Integrable
      (fun x : Space d =>
        (bandProj d Λ' hΛ'pos.ne' (φ₀ i) (hcont i) (hcs i) x : ℂ)) :=
    (bandTrunc d Λ' hΛ'pos.ne'
      (realToComplexSchwartz d (φ₀ i) (hcont i) (hcs i))).integrable.re.ofReal
  have hφg : sobolevNormSq d s₀ (fun x => φ x - g i x) ≤ ENNReal.ofReal (δ / 4) := by
    refine (sobolevNormSq_decomp_leW s₀ hφi hPφ (hgint i)).trans ?_
    calc 2 * sobolevNormSq d s₀ (fun x => φ x - bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x)
          + 2 * sobolevNormSq d s₀
              (fun x => bandProj d Λ' hΛ'pos.ne' φ hφ.1 hφ.2.1 x - g i x)
        ≤ 2 * ENNReal.ofReal (δ / 16) + 2 * ENNReal.ofReal (δ / 16) :=
          add_le_add (mul_le_mul_right (htail φ hφ hLow) 2) (mul_le_mul_right hi 2)
      _ = ENNReal.ofReal (δ / 4) := by
          rw [two_mul_ofReal_add (δ / 16) (by positivity)]
          congr 1; ring
  have hφ₀g : sobolevNormSq d s₀ (fun x => φ₀ i x - g i x) ≤ ENNReal.ofReal (δ / 4) := by
    refine (sobolevNormSq_decomp_leW s₀ hφ₀i hPφ₀ (hgint i)).trans ?_
    calc 2 * sobolevNormSq d s₀
            (fun x => φ₀ i x - bandProj d Λ' hΛ'pos.ne' (φ₀ i) (hcont i) (hcs i) x)
          + 2 * sobolevNormSq d s₀
              (fun x => bandProj d Λ' hΛ'pos.ne' (φ₀ i) (hcont i) (hcs i) x - g i x)
        ≤ 2 * ENNReal.ofReal (δ / 16) + 2 * ENNReal.ofReal (δ / 16) :=
          add_le_add (mul_le_mul_right (htail (φ₀ i) (hφ₀test i) (hφ₀s i)) 2)
            (mul_le_mul_right (hφ₀net i) 2)
      _ = ENNReal.ofReal (δ / 4) := by
          rw [two_mul_ofReal_add (δ / 16) (by positivity)]
          congr 1; ring
  have hgφ₀ : sobolevNormSq d s₀ (fun x => g i x - φ₀ i x) ≤ ENNReal.ofReal (δ / 4) := by
    rw [sobolevNormSq_sub_commW]
    exact hφ₀g
  refine (sobolevNormSq_decomp_leW s₀ hφi (hgint i) hφ₀i).trans ?_
  calc 2 * sobolevNormSq d s₀ (fun x => φ x - g i x)
        + 2 * sobolevNormSq d s₀ (fun x => g i x - φ₀ i x)
      ≤ 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
        add_le_add (mul_le_mul_right hφg 2) (mul_le_mul_right hgφ₀ 2)
    _ = ENNReal.ofReal δ := by
        rw [two_mul_ofReal_add (δ / 4) (by positivity)]
        congr 1; ring

/-- **The external, from the corrected input.** -/
theorem rellichKondrachovNegSobolev_of_projectionNetWitness
    (h : BandLimitedProjectionNetWitness) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet (rkLowFreqNet_of_projectionNetWitness h)

end LatticeProb.Sobolev
