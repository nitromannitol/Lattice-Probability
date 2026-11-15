import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Coverage of deterministic times by stationary window events -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Almost-every-time coverage in every window implies coverage of each fixed interior
point when coverage is monotone under window enlargement and almost-sure coverage is
invariant under translation. The joint event need only be measurable after completion. -/
theorem ae_fixedTime_of_stationary_window_coverage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SigmaFinite P]
    (E : ℝ → ℝ → ℝ → Ω → Prop)
    (hnull : ∀ r s : ℝ, r < s →
      NullMeasurableSet {p : Ω × ℝ | E r s p.2 p.1}
        (P.prod (volume.restrict (Ioo r s))))
    (hcoverage : ∀ r s : ℝ, r < s → ∀ᵐ ω ∂P,
      ∀ᵐ t ∂volume.restrict (Ioo r s), E r s t ω)
    (hshift : ∀ r s t d : ℝ, (∀ᵐ ω ∂P, E r s t ω) →
      ∀ᵐ ω ∂P, E (r + d) (s + d) (t + d) ω)
    (hmono : ∀ r s a b t : ℝ, a ≤ r → s ≤ b → ∀ ω,
      E r s t ω → E a b t ω)
    {a u b : ℝ} (hau : a < u) (hub : u < b) : ∀ᵐ ω ∂P, E a b u ω := by
  let h : ℝ := min (u - a) (b - u) / 4
  have hh : 0 < h := by dsimp [h]; positivity
  have hha : h ≤ (u - a) / 4 := by dsimp [h]; gcongr; exact min_le_left _ _
  have hhb : h ≤ (b - u) / 4 := by dsimp [h]; gcongr; exact min_le_right _ _
  let r := u - h
  let s := u + h
  have hrs : r < s := by dsimp [r, s]; linarith
  obtain ⟨T, hTsub, hTm, hTeq⟩ := (hnull r s hrs).exists_measurable_subset_ae_eq
  have heq : ∀ᵐ ω ∂P, ∀ᵐ t ∂volume.restrict (Ioo r s),
      ((ω, t) ∈ T ↔ E r s t ω) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hTeq] with ω hω
    filter_upwards [hω] with t ht
    exact Iff.of_eq ht
  have hT : ∀ᵐ ω ∂P, ∀ᵐ t ∂volume.restrict (Ioo r s), (ω, t) ∈ T := by
    filter_upwards [hcoverage r s hrs, heq] with ω hw he
    filter_upwards [hw, he] with t ht ht'
    exact ht'.2 ht
  have htgood : ∀ᵐ t ∂volume.restrict (Ioo r s), ∀ᵐ ω ∂P, E r s t ω := by
    have hflip := (Measure.ae_ae_comm (p := fun ω t => (ω, t) ∈ T) hTm).1 hT
    filter_upwards [hflip] with t ht
    filter_upwards [ht] with ω hω
    exact hTsub hω
  have hsmallsub : Ioo (u - h / 2) (u + h / 2) ⊆ Ioo r s := by
    intro t ht
    dsimp [r, s]
    constructor <;> linarith [ht.1, ht.2]
  have hsmall : ∀ᵐ t ∂volume.restrict (Ioo (u - h / 2) (u + h / 2)),
      ∀ᵐ ω ∂P, E r s t ω :=
    (Measure.restrict_mono hsmallsub le_rfl).absolutelyContinuous.ae_le htgood
  have hpos : volume (Ioo (u - h / 2) (u + h / 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨t, ht, hte⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hsmall
  have htranslated := hshift r s t (u - t) hte
  filter_upwards [htranslated] with ω hω
  have hleft : a ≤ r + (u - t) := by dsimp [r]; linarith [ht.2]
  have hright : s + (u - t) ≤ b := by dsimp [s]; linarith [ht.1]
  have hresult := hmono (r + (u - t)) (s + (u - t)) a b u hleft hright ω
  apply hresult
  convert hω using 1
  ring

end LatticeProb
