/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117E2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117E1

/-!
# D117, packet P-DIH, part 4: `DZZDihedralLaw` (exact invariance in law under the symmetries of `𝕍`)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-translation-invariant) l. 2271 and "by symmetry"
l. 2555, in the exact form decided in DEC-117 §1 (`DZZDihedralLaw`, S5D117): for every symmetry
`g` of `𝕍` (`IsDzzSym`: words in `dzzRefl`, `dzzRot`), the law of the rational ball masses of
`g_* M_{γ,η}` is that of `M_{γ,η}`. Proof:

* generators `dzzRefl`, `dzzSwap` (`IsDihGen`, S5D117D1; `dzzRot = dzzRefl ∘ dzzSwap`):
  `prob_ballMassQ_map_dih` from the pathwise covariance `ae_ballMassQ_dihNoise` (S5D117D2) for
  the noise `W ∘ dihL2 σ` and the noise-independence of the law `prob_ballMassQ_dzzMuIn_eq`
  (S5D117E1);
* words: `ballMassQ (σ_* ν)` is a measurable reindexing of `ballMassQ ν` (`ballMassQ_map_dih`),
  so the claim passes from `g` to `σ ∘ g`;
* **`dzzDihedralLaw_dzzMuIn`**: `DZZDihedralLaw P γ W` for every white noise `W`, `γ ∈ (0, 2)`.

Own elementary argument (DZZ state the invariance without proof); DV-D117-3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {σ : ℂ → ℂ}

/-- the reindexing of rational centres induced by `σ` -/
def IsDihGen.ratMap (hσ : IsDihGen σ) (c : ℚ × ℚ) : ℚ × ℚ := (hσ.rat c).choose

lemma IsDihGen.ratPt_ratMap (hσ : IsDihGen σ) (c : ℚ × ℚ) :
    ratPt (hσ.ratMap c) = σ (ratPt c) := (hσ.rat c).choose_spec

/-- the induced map on rational ball-mass functions -/
def IsDihGen.reidx (hσ : IsDihGen σ) (m : ℚ × ℚ → ℚ → ℝ≥0∞) : ℚ × ℚ → ℚ → ℝ≥0∞ :=
  fun c q => m (hσ.ratMap c) q

lemma IsDihGen.measurable_reidx (hσ : IsDihGen σ) : Measurable hσ.reidx :=
  measurable_pi_iff.2 fun c => measurable_pi_iff.2 fun q =>
    (measurable_pi_apply q).comp (measurable_pi_apply (hσ.ratMap c))

/-- `ballMassQ (σ_* ν)` is a reindexing of `ballMassQ ν` -/
lemma ballMassQ_map_dih (hσ : IsDihGen σ) (ν : Measure ℂ) :
    ballMassQ (ν.map σ) = hσ.reidx (ballMassQ ν) := by
  funext c q
  simp only [ballMassQ, IsDihGen.reidx]
  rw [Measure.map_apply hσ.continuous.measurable Metric.isOpen_ball.measurableSet,
    hσ.preimage_ball, hσ.ratPt_ratMap]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **invariance in law under one generator** -/
theorem prob_ballMassQ_map_dih (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hσ : IsDihGen σ) {S : Set (ℚ × ℚ → ℚ → ℝ≥0∞)} (hS : MeasurableSet S) :
    P {ω | ballMassQ ((dzzMuIn γ W ω).map σ) ∈ S} = P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S} := by
  have e : {ω | ballMassQ ((dzzMuIn γ W ω).map σ) ∈ S} =ᵐ[P]
      {ω | ballMassQ (dzzMuIn γ (dihNoise hσ W) ω) ∈ S} := by
    filter_upwards [ae_ballMassQ_dihNoise hW hγ hγ2 hσ] with ω hω
    rw [hω]
  rw [measure_congr e, prob_ballMassQ_dzzMuIn_eq (isWhiteNoise_dihNoise hW hσ) hW hγ hγ2 hS]

/-- the claim for a word `g` passes to `σ ∘ g` -/
theorem prob_ballMassQ_map_comp (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hσ : IsDihGen σ) {g : ℂ → ℂ} (hg : Measurable g)
    (h : ∀ S : Set (ℚ × ℚ → ℚ → ℝ≥0∞), MeasurableSet S →
      P {ω | ballMassQ ((dzzMuIn γ W ω).map g) ∈ S} = P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S})
    (S : Set (ℚ × ℚ → ℚ → ℝ≥0∞)) (hS : MeasurableSet S) :
    P {ω | ballMassQ ((dzzMuIn γ W ω).map (σ ∘ g)) ∈ S} =
      P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S} := by
  have e1 : ∀ ν : Measure ℂ, ballMassQ (ν.map (σ ∘ g)) = hσ.reidx (ballMassQ (ν.map g)) :=
    fun ν => by rw [← Measure.map_map hσ.continuous.measurable hg, ballMassQ_map_dih]
  have e2 : ∀ ν : Measure ℂ, ballMassQ (ν.map σ) = hσ.reidx (ballMassQ ν) :=
    ballMassQ_map_dih hσ
  have hS' : MeasurableSet (hσ.reidx ⁻¹' S) := hσ.measurable_reidx hS
  calc P {ω | ballMassQ ((dzzMuIn γ W ω).map (σ ∘ g)) ∈ S}
      = P {ω | ballMassQ ((dzzMuIn γ W ω).map g) ∈ hσ.reidx ⁻¹' S} := by
        congr 1; ext ω
        change _ ∈ S ↔ hσ.reidx _ ∈ S
        rw [e1]
    _ = P {ω | ballMassQ (dzzMuIn γ W ω) ∈ hσ.reidx ⁻¹' S} := h _ hS'
    _ = P {ω | ballMassQ ((dzzMuIn γ W ω).map σ) ∈ S} := by
        congr 1; ext ω
        change hσ.reidx _ ∈ S ↔ _ ∈ S
        rw [e2]
    _ = P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S} := prob_ballMassQ_map_dih hW hγ hγ2 hσ hS

/-- **DZZ (eq-translation-invariant), exact form** (l. 2271, "by symmetry" l. 2555; DEC-117 §1):
for every white noise `W` and `γ ∈ (0, 2)`, the law of the rational ball masses of `g_* M_{γ,η}`
is that of `M_{γ,η}` for every symmetry `g` of `𝕍`. -/
theorem dzzDihedralLaw_dzzMuIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    DZZDihedralLaw P γ W := by
  have key : ∀ g : ℂ → ℂ, IsDzzSym g → Measurable g ∧ ∀ S : Set (ℚ × ℚ → ℚ → ℝ≥0∞),
      MeasurableSet S →
      P {ω | ballMassQ ((dzzMuIn γ W ω).map g) ∈ S} = P {ω | ballMassQ (dzzMuIn γ W ω) ∈ S} := by
    intro g hg
    induction hg with
    | id => exact ⟨measurable_id, fun S _ => by simp only [Measure.map_id]⟩
    | @refl g _ ih =>
      exact ⟨isDihGen_dzzRefl.continuous.measurable.comp ih.1,
        prob_ballMassQ_map_comp hW hγ hγ2 isDihGen_dzzRefl ih.1 ih.2⟩
    | @rot g _ ih =>
      have e : dzzRot ∘ g = dzzRefl ∘ (dzzSwap ∘ g) := by
        funext z; simp only [Function.comp_apply, dzzRot_eq]
      have hm : Measurable (dzzSwap ∘ g) := isDihGen_dzzSwap.continuous.measurable.comp ih.1
      rw [e]
      exact ⟨isDihGen_dzzRefl.continuous.measurable.comp hm,
        prob_ballMassQ_map_comp hW hγ hγ2 isDihGen_dzzRefl hm
          (prob_ballMassQ_map_comp hW hγ hγ2 isDihGen_dzzSwap ih.1 ih.2)⟩
  exact fun g hg S hS => (key g hg).2 S hS

end DZZ
end LQGMetric
