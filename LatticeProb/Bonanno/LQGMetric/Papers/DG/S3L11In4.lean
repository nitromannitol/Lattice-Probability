/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11In4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Meas
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11V
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11In3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of the coarse factors `T_R`, `T_S` (node 2(c) of P2-DG105g, P2-DG105l)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1302–1305 (proof of L3.13):
`ĥ_{2^{-m-n_m}}` is a function of the white noise at times `≥ 2^{-2(m+n_m)}`, independent of the
fine field. The factors `l311T` (`T_R`, DG:1305), `l311TV` (vertical) and `l319X` (`T_S`, DG:1702)
are functions of `ĥ_s = phiVer W P s 1` (`s = 2^{-j}`), a continuous modification of
`φ_{s,1} = √π W(k_{s,1,z})` whose kernel lives at times in `[s², 1)` (`supportedIn_phiKernelL2`).
So each factor is a.s. equal to a `σ(W f : supp f ⊆ [s², ∞) × ℂ)`-measurable variable: the sup
(inf) over a compact set of a continuous field is a sup (inf) over a countable dense subset, where
the modification agrees a.s. with `φ_{s,1}` (`exists_ae_eq_sSup_image`).

* **`l311T_local`**, **`l311TV_local`**, **`l319X_local`**.

Own elementary glue.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise GMCIdent

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- the sup of a continuous function over a compact set is the sup over a dense subset -/
lemma sSup_image_eq_iSup_dense {S D : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty)
    (hDS : D ⊆ S) (hSD : S ⊆ closure D) {f : ℂ → ℝ} (hf : Continuous f) :
    sSup (f '' S) = ⨆ z : D, f z := by
  have hbdd : BddAbove (f '' S) := hS.bddAbove_image hf.continuousOn
  have hDne : Nonempty D := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw⟩ := mem_closure_iff.1 (hSD hz) univ isOpen_univ trivial
    exact ⟨⟨w, hw.2⟩⟩
  have hbddD : BddAbove (range fun z : D => f z) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM ⟨z, hDS z.2, rfl⟩⟩
  refine le_antisymm (csSup_le (hne.image f) ?_) (ciSup_le fun z => le_csSup hbdd ⟨z, hDS z.2, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  have hcl : IsClosed {w | f w ≤ ⨆ z : D, f z} := isClosed_le hf continuous_const
  exact (closure_minimal (fun w hw => le_ciSup hbddD (⟨w, hw⟩ : D)) hcl) (hSD hz)

/-- **The sup of a continuous modification is a.s. a functional of the original field**: if
`X z =ᵐ X' z` with `X' z` `m`-measurable, then `sup_S X` is a.s. an `m`-measurable variable. -/
lemma exists_ae_eq_sSup_image {m : MeasurableSpace Ω} {S : Set ℂ} (hS : IsCompact S)
    (hne : S.Nonempty) {X X' : ℂ → Ω → ℝ} (hc : ∀ ω, Continuous fun z => X z ω)
    (hX' : ∀ z, Measurable[m] (X' z)) (hXX : ∀ z, X z =ᵐ[P] X' z) :
    ∃ T' : Ω → ℝ, Measurable[m] T' ∧ (fun ω => sSup ((fun z => X z ω) '' S)) =ᵐ[P] T' := by
  obtain ⟨D, hDS, hDc, hSD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have : Countable D := hDc.to_subtype
  refine ⟨fun ω => ⨆ z : D, X' z ω, Measurable.iSup fun z => hX' z, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ z : D, X z ω = X' z ω := ae_all_iff.2 fun z => hXX z
  filter_upwards [hall] with ω hω
  rw [sSup_image_eq_iSup_dense hS hne hDS hSD (hc ω)]
  exact iSup_congr hω

lemma exists_ae_eq_sInf_image {m : MeasurableSpace Ω} {S : Set ℂ} (hS : IsCompact S)
    (hne : S.Nonempty) {X X' : ℂ → Ω → ℝ} (hc : ∀ ω, Continuous fun z => X z ω)
    (hX' : ∀ z, Measurable[m] (X' z)) (hXX : ∀ z, X z =ᵐ[P] X' z) :
    ∃ T' : Ω → ℝ, Measurable[m] T' ∧ (fun ω => sInf ((fun z => X z ω) '' S)) =ᵐ[P] T' := by
  obtain ⟨T', hT', h⟩ := exists_ae_eq_sSup_image (mΩ := mΩ) (m := m) (P := P) hS hne (X := fun z ω => -X z ω)
    (X' := fun z ω => -X' z ω) (fun ω => (hc ω).neg) (fun z => (hX' z).neg)
    (fun z => (hXX z).neg)
  refine ⟨fun ω => -T' ω, hT'.neg, ?_⟩
  filter_upwards [h] with ω hω
  rw [← hω, Real.sInf_def]
  congr 2
  ext x
  simp only [Set.mem_neg, mem_image]
  constructor
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, by have h' : X z ω = -x := h; show -X z ω = x; linarith⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, by have h' : -X z ω = x := h; show X z ω = -x; linarith⟩

/-- the coarse region `[s², ∞) × ℂ` of `ĥ_s` -/
def coarseReg (s : ℝ) : Set (ℝ × ℂ) := Ici (s ^ 2) ×ˢ univ

lemma phiVer_local {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (j : ℕ) :
    (∀ ω, Continuous fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ∧
    (∀ z, Measurable[wnSigma W (coarseReg ((2 : ℝ)⁻¹ ^ j))] (phi W ((2 : ℝ)⁻¹ ^ j) 1 z)) ∧
    ∀ z, DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z =ᵐ[P] phi W ((2 : ℝ)⁻¹ ^ j) 1 z := by
  have hv := DDDF.isPhiVersion_phiVer hW (a := (2 : ℝ)⁻¹ ^ j) (b := 1) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))
  refine ⟨hv.cont, fun z => ?_, hv.ae_eq⟩
  have hs : SupportedIn (coarseReg ((2 : ℝ)⁻¹ ^ j)) (phiKernelL2 ((2 : ℝ)⁻¹ ^ j) 1 z) :=
    supportedIn_mono (prod_mono Ico_subset_Ici_self (subset_univ _))
      (supportedIn_phiKernelL2 (by positivity) z)
  exact (measurable_wnSigma hs).const_mul _

/-- **`T_R` is a.s. a function of the coarse white noise** (DG:1305) -/
theorem l311T_local {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ ε : ℝ) (j n : ℕ) (b : ℂ) :
    ∃ T' : Ω → ℝ, Measurable[wnSigma W (coarseReg ((2 : ℝ)⁻¹ ^ j))] T' ∧
      l311T P W γ ε j n b =ᵐ[P] T' := by
  obtain ⟨hc, hm, he⟩ := phiVer_local hW j
  obtain ⟨T₀, hT₀, h⟩ := exists_ae_eq_sSup_image (P := P) (isCompact_l313Str ((2 : ℝ)⁻¹ ^ j) b n)
    (l313Str_nonempty (by positivity) b n) hc hm he
  refine ⟨fun ω => ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * T₀ ω)),
    measurable_const.mul (Real.measurable_exp.comp (hT₀.const_mul γ).neg), ?_⟩
  filter_upwards [h] with ω hω
  simp only [l311T, hω]

/-- **`T_R` for vertical rectangles** -/
theorem l311TV_local {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ ε : ℝ) (j n : ℕ) (b : ℂ) :
    ∃ T' : Ω → ℝ, Measurable[wnSigma W (coarseReg ((2 : ℝ)⁻¹ ^ j))] T' ∧
      l311TV P W γ ε j n b =ᵐ[P] T' := by
  obtain ⟨hc, hm, he⟩ := phiVer_local hW j
  have hS : l313StrV ((2 : ℝ)⁻¹ ^ j) b n = swapC '' l313Str ((2 : ℝ)⁻¹ ^ j) (swapC b) n :=
    (swapC_l313Str _ _ _).symm
  obtain ⟨T₀, hT₀, h⟩ := exists_ae_eq_sSup_image (P := P) (S := l313StrV ((2 : ℝ)⁻¹ ^ j) b n)
    (by rw [hS]; exact (isCompact_l313Str _ _ _).image continuous_swapC)
    (by rw [hS]; exact (l313Str_nonempty (by positivity) _ n).image _) hc hm he
  refine ⟨fun ω => ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * T₀ ω)),
    measurable_const.mul (Real.measurable_exp.comp (hT₀.const_mul γ).neg), ?_⟩
  filter_upwards [h] with ω hω
  simp only [l311TV, hω]

/-- **`T_S` is a.s. a function of the coarse white noise** (DG:1702) -/
theorem l319X_local {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ ε : ℝ) (j n : ℕ) (b : ℂ) :
    ∃ T' : Ω → ℝ, Measurable[wnSigma W (coarseReg ((2 : ℝ)⁻¹ ^ j))] T' ∧
      l319X P W γ ε j n b =ᵐ[P] T' := by
  obtain ⟨hc, hm, he⟩ := phiVer_local hW j
  obtain ⟨T₀, hT₀, h⟩ := exists_ae_eq_sInf_image (P := P) (isCompact_l321Out ((2 : ℝ)⁻¹ ^ j) b n)
    (l321Out_nonempty (by positivity) b n) hc hm he
  refine ⟨fun ω => ε * ((((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * T₀ ω))),
    measurable_const.mul (measurable_const.mul
      (Real.measurable_exp.comp (hT₀.const_mul γ).neg)), ?_⟩
  filter_upwards [h] with ω hω
  simp only [l319X, hω]

end DG
end LQGMetric
