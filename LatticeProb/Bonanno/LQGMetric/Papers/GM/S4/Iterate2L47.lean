/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L47 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ConditionalCount

/-!
# GM Lemma 4.7 per `k` in the form used by Proposition 4.17

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.7 (`lem-annulus-choose`),
(4.14) and its proof l. 1931–1940 ("`P[𝒵^𝔈_k ≠ ∅ | 𝓕_k] ≥ ε^{2ν+o(1)} P[𝒵^E_k ≠ ∅ | 𝓕_k] −
o^∞_ε(ε)`"), and its use in Lemma 4.21 (l. 2380–2390).

`gm_h47_of_fixed`: the conclusion of `gm_L4_7_fixed` (GM (4.17) at fixed `ε`:
`K P[⋃B | 𝓕] + C_p√δ < Λ⁻¹ P[⋃A | 𝓕]` only outside an event of probability `√δ`, on `W ∩ G`)
is the hypothesis `h47` of `gm_P4_17_abstract`/`gm_P4_17_ae`, with `κ = (ΛK)⁻¹`,
`e = C_p√δ/K`, for any σ-algebra `ℱ_k` whose conditional expectations agree a.s. with those
given `𝓕` (`gm_condExp_gmFilt` for the filtration `gmFilt`), provided `ℰ_𝕣 ⊂ W ∩ G` a.s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric.GM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **GM (4.14) in the form `h47`** from `gm_L4_7_fixed`'s conclusion -/
theorem gm_h47_of_fixed [IsFiniteMeasure μ] {F ℱk : MeasurableSpace Ω}
    (hcond : ∀ f : Ω → ℝ, μ[f | F] =ᵐ[μ] μ[f | ℱk]) {ZE ZF W G Reg : Set Ω}
    {Λ K Cp δ : ℝ} (hK : 0 < K) (hΛ : 0 < Λ) (hReg : ∀ᵐ ω ∂μ, ω ∈ Reg → ω ∈ W ∩ G)
    (hfix : μ.real {x | x ∈ W ∩ G ∧ K * (μ⟦ZF | F⟧) x + Cp * Real.sqrt δ <
      Λ⁻¹ * (μ⟦ZE | F⟧) x} ≤ Real.sqrt δ) :
    μ.real {ω | ω ∈ Reg ∧ μ[ZF.indicator (fun _ => (1 : ℝ)) | ℱk] ω <
      (Λ * K)⁻¹ * μ[ZE.indicator (fun _ => (1 : ℝ)) | ℱk] ω - Cp * Real.sqrt δ / K} ≤
        Real.sqrt δ := by
  refine le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae ?_)) hfix
  filter_upwards [hcond (ZF.indicator fun _ => (1 : ℝ)), hcond (ZE.indicator fun _ => (1 : ℝ)),
    hReg] with ω h1 h2 h3 hω
  obtain ⟨hR, hlt⟩ := hω
  refine ⟨h3 hR, ?_⟩
  show K * (μ[ZF.indicator fun _ => (1 : ℝ) | F]) ω + Cp * Real.sqrt δ <
    Λ⁻¹ * (μ[ZE.indicator fun _ => (1 : ℝ) | F]) ω
  rw [h1, h2]
  have e1 : (Λ * K)⁻¹ * μ[ZE.indicator (fun _ => (1 : ℝ)) | ℱk] ω - Cp * Real.sqrt δ / K =
      (Λ⁻¹ * μ[ZE.indicator (fun _ => (1 : ℝ)) | ℱk] ω - Cp * Real.sqrt δ) / K := by
    field_simp
  rw [e1, lt_div_iff₀ hK] at hlt
  linarith

end LQGMetric.GM
