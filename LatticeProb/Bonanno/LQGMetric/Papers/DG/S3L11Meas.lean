/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Sc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOscExp

/-!
# Measurability of DG's random factors `T_R`, `T_S` (P2-DG105g)

The first conjunct of `L311LevelInput` / `L319LevelInput` (S3L11Sc, S3L19Sc): the factors
`l311T` (DG:1305, `max ĥ_s` over `sℛ_n' + b`) and `l319X` (DG:1702, `min ĥ_s` over `s𝒜_n + b`)
are measurable, because `ĥ_s = phiVer W P s 1` is continuous in `z` for every `ω` and measurable
in `ω` for every `z` (`DDDF.IsPhiVersion`), so its supremum (infimum) over a compact set is a
supremum over a dense sequence (`DDDF.measurable_iSup_of_continuous`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma measurable_sSup_image_of_cont {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty)
    {X : ℂ → Ω → ℝ} (hc : ∀ ω, Continuous fun z => X z ω) (hm : ∀ z, Measurable (X z)) :
    Measurable fun ω => sSup ((fun z => X z ω) '' S) := by
  have := isCompact_iff_compactSpace.1 hS
  have : Nonempty S := hne.to_subtype
  have e : (fun ω => sSup ((fun z => X z ω) '' S)) = fun ω => ⨆ t : S, X t ω :=
    funext fun ω => sSup_image'
  rw [e]
  exact DDDF.measurable_iSup_of_continuous (X := fun (t : S) ω => X t ω)
    (fun ω => (hc ω).comp continuous_subtype_val) (fun t => hm t)

lemma measurable_sInf_image_of_cont {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty)
    {X : ℂ → Ω → ℝ} (hc : ∀ ω, Continuous fun z => X z ω) (hm : ∀ z, Measurable (X z)) :
    Measurable fun ω => sInf ((fun z => X z ω) '' S) := by
  have e : (fun ω => sInf ((fun z => X z ω) '' S)) =
      fun ω => -sSup ((fun z => -X z ω) '' S) := by
    funext ω
    rw [Real.sInf_def]
    congr 2
    ext x
    simp only [mem_neg, mem_image]
    constructor
    · rintro ⟨z, hz, h⟩; exact ⟨z, hz, by rw [h, neg_neg]⟩
    · rintro ⟨z, hz, h⟩; exact ⟨z, hz, by rw [← h, neg_neg]⟩
  rw [e]
  exact (measurable_sSup_image_of_cont hS hne (fun ω => (hc ω).neg)
    (fun z => (hm z).neg)).neg

lemma isCompact_l313Str (s : ℝ) (b : ℂ) (n : ℕ) : IsCompact (l313Str s b n) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma l313Str_nonempty {s : ℝ} (hs : 0 ≤ s) (b : ℂ) (n : ℕ) : (l313Str s b n).Nonempty := by
  refine ⟨b, ?_⟩
  have : 0 ≤ s * n := by positivity
  simp only [l313Str, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨by linarith, by linarith⟩, le_rfl, by linarith⟩

lemma isCompact_l321Out (s : ℝ) (b : ℂ) (n : ℕ) : IsCompact (l321Out s b n) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma l321Out_nonempty {s : ℝ} (hs : 0 ≤ s) (b : ℂ) (n : ℕ) : (l321Out s b n).Nonempty := by
  refine ⟨b, ?_⟩
  have : 0 ≤ s * n := by positivity
  simp only [l321Out, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- `T_R` is measurable (first conjunct of `L311LevelInput`) -/
theorem measurable_l311T (hW : IsWhiteNoise P W) (γ ε : ℝ) (j n : ℕ) (b : ℂ) :
    Measurable (l311T P W γ ε j n b) := by
  have hv := DDDF.isPhiVersion_phiVer hW (a := (2 : ℝ)⁻¹ ^ j) (b := 1) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))
  have hM := measurable_sSup_image_of_cont (isCompact_l313Str ((2 : ℝ)⁻¹ ^ j) b n)
    (l313Str_nonempty (by positivity) b n) hv.cont hv.meas
  unfold l311T
  exact measurable_const.mul (Real.measurable_exp.comp (hM.const_mul γ).neg)

/-- `T_S` is measurable (first conjunct of `L319LevelInput`) -/
theorem measurable_l319X (hW : IsWhiteNoise P W) (γ ε : ℝ) (j n : ℕ) (b : ℂ) :
    Measurable (l319X P W γ ε j n b) := by
  have hv := DDDF.isPhiVersion_phiVer hW (a := (2 : ℝ)⁻¹ ^ j) (b := 1) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))
  have hM := measurable_sInf_image_of_cont (isCompact_l321Out ((2 : ℝ)⁻¹ ^ j) b n)
    (l321Out_nonempty (by positivity) b n) hv.cont hv.meas
  unfold l319X
  exact measurable_const.mul (measurable_const.mul
    (Real.measurable_exp.comp (hM.const_mul γ).neg))

end DG
end LQGMetric
