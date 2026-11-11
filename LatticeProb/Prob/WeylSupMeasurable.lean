import Mathlib

/-!
# Suprema over a set of a lower semicontinuous random field: countable reduction and a.e. measurability

General measure theory, with no Harmonic-balls object. Namespace `LatticeProb.Prob`; only Mathlib is imported.
For a supremum `⨆ x ∈ S, F ω x` in `ℝ≥0∞` over an uncountable set `S`:

* `iSup_mem_eq_iSup_mem_of_lowerSemicontinuousOn`: a function that is lower semicontinuous on `S` has the same
  supremum over `S` as over any `D ⊆ S` dense in `S`.
* `aemeasurable_iSup_mem_of_lowerSemicontinuousOn`: if `ω ↦ F ω x` is a.e. measurable for each `x` in a countable
  `D ⊆ S` dense in `S`, and `x ↦ F ω x` is lower semicontinuous on `S` for almost every `ω`, then
  `ω ↦ ⨆ x ∈ S, F ω x` is a.e. measurable.

These are the reduction step for the almost-everywhere measurability of the supremum over a closed dyadic square of the
internal metric of a Weyl-shifted LQG metric, as used in the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]. Their hypotheses on
`F` are not supplied here; the derivation that supplies them is in that formalization.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.Prob

variable {X : Type*} [TopologicalSpace X]

/-- A function lower semicontinuous on `S` has the same supremum over `S` as over any `D ⊆ S` dense in `S`. -/
theorem iSup_mem_eq_iSup_mem_of_lowerSemicontinuousOn {g : X → ℝ≥0∞} {S D : Set X}
    (hg : LowerSemicontinuousOn g S) (hDS : D ⊆ S) (hSD : S ⊆ closure D) :
    ⨆ x ∈ S, g x = ⨆ x ∈ D, g x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => le_iSup₂ (f := fun x _ => g x) x (hDS hx))
  by_contra hlt
  obtain ⟨y, hMy, hyg⟩ := exists_between (not_le.mp hlt)
  have hev : ∀ᶠ z in 𝓝[S] x, y < g z := hg x hx y hyg
  obtain ⟨t, ht, hts⟩ := Filter.eventually_iff_exists_mem.mp (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨d, hdt, hdD⟩ := mem_closure_iff_nhds.mp (hSD hx) t ht
  have hyd : y < g d := hts d hdt (hDS hdD)
  have hdM : g d ≤ ⨆ x ∈ D, g x := le_iSup₂ (f := fun x _ => g x) d hdD
  exact lt_irrefl _ (hMy.trans (hyd.trans_le hdM))

/-- Almost everywhere measurability of a supremum over `S` of a random field which is a.s. lower semicontinuous on
`S`, given a.e. measurability at the points of a countable `D ⊆ S` dense in `S`. -/
theorem aemeasurable_iSup_mem_of_lowerSemicontinuousOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → X → ℝ≥0∞} {S D : Set X} (hDc : D.Countable) (hDS : D ⊆ S) (hSD : S ⊆ closure D)
    (hmeas : ∀ x ∈ D, AEMeasurable (fun ω => F ω x) P)
    (hlsc : ∀ᵐ ω ∂P, LowerSemicontinuousOn (F ω) S) :
    AEMeasurable (fun ω => ⨆ x ∈ S, F ω x) P := by
  have : Countable D := hDc.to_subtype
  have hcount : AEMeasurable (fun ω => ⨆ x : D, F ω x) P :=
    AEMeasurable.iSup (f := fun (x : D) ω => F ω x.1) fun x => hmeas x.1 x.2
  refine hcount.congr ?_
  filter_upwards [hlsc] with ω hω
  rw [iSup_mem_eq_iSup_mem_of_lowerSemicontinuousOn hω hDS hSD]
  exact le_antisymm (iSup_le fun x => le_iSup₂ (f := fun y (_ : y ∈ D) => F ω y) x.1 x.2)
    (iSup₂_le fun x hx => le_iSup (fun y : D => F ω y) ⟨x, hx⟩)

end LatticeProb.Prob
