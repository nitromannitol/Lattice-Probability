/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Prob at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_5
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Aux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3, Step 1: the regularity event `G^ε_𝕣` (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 1 (T:2685–2697): for `M̃ > 0`, `ζ ∈ (0,1)` there are `C, A > 1` such that the event
`G^ε_𝕣(M̃, ζ, C, A)` — (1) `B_{ε^{-M̃}𝕣}(0)` is covered by `C`-good balls with radii in
`[2ε𝕣, ε^{1−ζ}𝕣]`, (2) `D_h(z,w) ≥ ε^A sup_{u,v∈B_{ε^{-M̃}𝕣}(0)} D_h(u,v)` for
`|z − w| ≥ ε𝕣` — has probability `1 − O_ε(ε^{M̃})` uniformly in `𝕣` ("By Lemmas 4.4 and 4.5").
Condition (1) is taken in the sharpened form `CGoodCoverH` (`lem4_4_half`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint L45

/-- the regularity event `G^ε_𝕣` of Step 1 (T:2685–2693), with `CGoodCoverH` for condition 1 -/
def regG (D : DistC → ContMetric) (C A ζ M ε 𝕣 : ℝ) : Set DistC :=
  {g | CGoodCoverH (D g) C ζ M ε 𝕣 ∧ g ∈ ev45 D M A ε 𝕣}

/-- **Step 1 of the proof of Prop 4.3** (T:2694–2697), constants uniform in `𝕣` and the field -/
theorem prob_regG (h31a : LMLem3_1a) (hS : DFGPSScaling) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {ζ M : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (hM : 0 < M) :
    ∃ C A : ℝ, 1 < C ∧ 0 < A ∧ ∃ K ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
          P (h ⁻¹' regG D C A ζ M ε 𝕣)ᶜ ≤ ENNReal.ofReal (K * ε ^ M) := by
  obtain ⟨C, hC, K₁, ε₁, hε₁, H₁⟩ := lem4_4_half h31a hγ0 hγ2 hD hζ0 hζ1 hM
  obtain ⟨A, hA, K₂, ε₂, hε₂, H₂⟩ := lem4_5 h31a hS hγ0 hγ2 hD hM
  refine ⟨C, A, hC, hA, |K₁| + |K₂|, min ε₁ ε₂, lt_min hε₁ hε₂,
    fun P _ h hh ε hε 𝕣 h𝕣 => ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have h1 := H₁ P h hh.1 𝕣 h𝕣 ε ⟨hε0, hεm.trans_le (min_le_left _ _)⟩
  have h2 := H₂ P h hh ε ⟨hε0, hεm.trans_le (min_le_right _ _)⟩ 𝕣 h𝕣
  have hsub : (h ⁻¹' regG D C A ζ M ε 𝕣)ᶜ ⊆
      {ω | ¬ CGoodCoverH (D (h ω)) C ζ M ε 𝕣} ∪ (h ⁻¹' ev45 D M A ε 𝕣)ᶜ := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, mem_compl_iff, mem_preimage] at hn
    exact hω ⟨hn.1, hn.2⟩
  have hεM : 0 ≤ ε ^ M := by positivity
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
  have e1 := mul_le_mul_of_nonneg_right (le_abs_self K₁) hεM
  have e2 := mul_le_mul_of_nonneg_right (le_abs_self K₂) hεM
  calc ENNReal.ofReal (K₁ * ε ^ M) + ENNReal.ofReal (K₂ * ε ^ M)
      ≤ ENNReal.ofReal (|K₁| * ε ^ M) + ENNReal.ofReal (|K₂| * ε ^ M) :=
        add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal e2)
    _ = ENNReal.ofReal ((|K₁| + |K₂|) * ε ^ M) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

end P43
end LQGMetric.DFGPS
