/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.Lemma49Complete at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineAreaReader
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Canonical

/-! [18] Lemma 4.9: both local Borel factors and canonical conditional moments. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.L43O

theorem lemma49_zeroConeAreaLocality
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ZeroConeAreaLocality D fieldRegion excursionRegion := by
  let V : TopologicalSpace.Opens ℂ := excursionRegion
  let W : TopologicalSpace.Opens ℂ := fieldRegion
  let δ : ℝ := 1 / 8
  let J : ℂ ≃ₜ ℂ := Homeomorph.addRight (2 * Complex.I)
  have hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1 := Subset.rfl
  have hVb : Bornology.IsBounded (V : Set ℂ) := isBounded_excursionRegion
  have hVc : (V : Set ℂ)ᶜ.Nonempty := by
    refine ⟨(2 : ℂ), ?_⟩
    change (2 : ℂ) ∉ ball 0 (3 / 4)
    simp [mem_ball]
    norm_num
  have hδ : 0 < δ := by norm_num [δ]
  have hVW : GMS4c.thickOpen V δ ≤ W := thickOpen_excursionRegion_subset
  have hJb : Bornology.IsBounded (J '' (V : Set ℂ)) :=
    ((hVb.isCompact_closure.image J.continuous).isBounded).subset
      (image_mono subset_closure)
  have hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H := by
    rintro y ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ < 1 := by
      have hx' : x ∈ ball (0 : ℂ) (3 / 4) := hx
      have h : ‖x‖ < 3 / 4 := by simpa [mem_ball] using hx'
      linarith
    have him := (Complex.abs_im_le_norm x).trans_lt hnorm
    have hxlo : -1 < x.im := (abs_lt.mp him).1
    change 0 < (x + 2 * Complex.I).im
    norm_num [Complex.add_im, Complex.mul_im] at *
    linarith
  have hJc : (J '' (V : Set ℂ))ᶜ.Nonempty := by
    refine ⟨0, ?_⟩
    intro hz
    have hh := hJH hz
    exact (lt_irrefl (0 : ℝ)) hh
  exact zeroConeAreaLocality_of_localSelector D hγ W V hW hVb hVc hδ hVW J hJb hJH hJc

/-- Both clauses of (4.22): one Borel reader for all positive meshes at the root
and after every admissible recentering, for each masked observable. -/
theorem lemma49_zeroConeRescaledLocality_pair
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ZeroConeRescaledLocality D (maskedLocDA (1 / 2)) fieldRegion excursionRegion ∧
      ZeroConeRescaledLocality D (maskedLocUStar (1 / 2)) fieldRegion excursionRegion := by
  obtain ⟨hu, hda⟩ := zeroConeRescaledLocality_of_area D hγ (lemma49_zeroConeAreaLocality D hγ)
  exact ⟨hda, hu⟩

/-- Conditional moment bounds (4.24)–(4.25), in the canonical H1 statement. -/
def lemma49ConditionalMoments
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {q ζ ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    GMS4.Canonical.Lemma49ConditionalMoments D hγ q ζ ρ :=
  let hloc := lemma49_zeroConeRescaledLocality_pair D hγ
  L43O.lemma49ConditionalMoments_of_locality D hγ hloc.1 hloc.2 hρ hζ hζq

end MatedCRTHarmonic.GMS4cS

