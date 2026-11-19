import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A function of a random element that is determined by a second function has the same law

Let `p : α → β` and `G : α → γ` be measurable maps on a standard Borel space and let `μ, ν` be two
measures carried by a set `N` on whose points `G` is a function of `p` (`p a = p a' → G a = G a'`).
If `p` has the same law under `μ` and `ν`, then so does `G`.  The proof separates, by a Borel set of `β`
(Lusin separation of disjoint analytic sets), the images under `p` of the two sets `N ∩ G⁻¹ A` and
`N ∩ G⁻¹ Aᶜ`.  Nothing is assumed about `γ`: `G` is not required to take values in a standard Borel space.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

variable {α β γ : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  [TopologicalSpace β] [T2Space β] [SecondCountableTopology β] [MeasurableSpace β]
  [OpensMeasurableSpace β] [MeasurableSpace γ]

/-- **A function that factors through `p` on a carrying set has the same law when `p` does.**
If `G a = G a'` whenever `a, a' ∈ N` and `p a = p a'`, both measures `μ, ν` are carried by `N`
(`N` need not be measurable), and `μ.map p = ν.map p`, then `μ.map G = ν.map G`. -/
theorem map_eq_map_of_eqOn_fibers {p : α → β} {G : α → γ} (hp : Measurable p) (hG : Measurable G)
    {N : Set α} (hfib : ∀ a ∈ N, ∀ a' ∈ N, p a = p a' → G a = G a')
    {μ ν : Measure α} (hμ : μ Nᶜ = 0) (hν : ν Nᶜ = 0) (hlaw : μ.map p = ν.map p) :
    μ.map G = ν.map G := by
  set M : Set α := (toMeasurable (μ + ν) Nᶜ)ᶜ with hM
  have hMm : MeasurableSet M := (measurableSet_toMeasurable _ _).compl
  have hMN : M ⊆ N := fun a ha => by
    by_contra haN
    exact ha (subset_toMeasurable (μ + ν) Nᶜ haN)
  have hnull : μ Mᶜ + ν Mᶜ = 0 := by
    rw [← Measure.add_apply, hM, compl_compl, measure_toMeasurable, Measure.add_apply, hμ, hν,
      add_zero]
  have hμM : ∀ᵐ a ∂μ, a ∈ M := ae_iff.2 (add_eq_zero.1 hnull).1
  have hνM : ∀ᵐ a ∂ν, a ∈ M := ae_iff.2 (add_eq_zero.1 hnull).2
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hG hA, Measure.map_apply hG hA]
  have hs : AnalyticSet (p '' (M ∩ G ⁻¹' A)) := (hMm.inter (hG hA)).analyticSet_image hp
  have ht : AnalyticSet (p '' (M ∩ G ⁻¹' Aᶜ)) := (hMm.inter (hG hA.compl)).analyticSet_image hp
  have hdisj : Disjoint (p '' (M ∩ G ⁻¹' A)) (p '' (M ∩ G ⁻¹' Aᶜ)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨haM, haA⟩, rfl⟩ ⟨a', ⟨ha'M, ha'A⟩, he⟩
    have h := hfib a (hMN haM) a' (hMN ha'M) he.symm
    have h1 : G a ∈ A := haA
    have h2 : G a' ∉ A := ha'A
    exact h2 (h ▸ h1)
  obtain ⟨u, hsu, htu, hu⟩ := hs.measurablySeparable ht hdisj
  have key : ∀ ρ : Measure α, (∀ᵐ a ∂ρ, a ∈ M) → ρ (G ⁻¹' A) = ρ (p ⁻¹' u) := by
    intro ρ hρ
    refine measure_congr ?_
    filter_upwards [hρ] with a ha
    refine propext ⟨fun h => hsu ⟨a, ⟨ha, h⟩, rfl⟩, fun h => ?_⟩
    by_contra hnot
    exact Set.disjoint_left.1 htu ⟨a, ⟨ha, hnot⟩, rfl⟩ h
  calc μ (G ⁻¹' A) = μ (p ⁻¹' u) := key μ hμM
    _ = (μ.map p) u := (Measure.map_apply hp hu).symm
    _ = (ν.map p) u := by rw [hlaw]
    _ = ν (p ⁻¹' u) := Measure.map_apply hp hu
    _ = ν (G ⁻¹' A) := (key ν hνM).symm

end LatticeProb
