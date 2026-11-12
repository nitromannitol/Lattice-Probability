import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Laws of functions measurable on a set of full outer measure

Let `Y₁, Y₂ : Ω → α` be random variables with the same law, and let `S ⊆ α` be a set, not necessarily
measurable, that contains `Y₁` and `Y₂` almost surely. If `G : α → β` is measurable on `S` for the subspace
σ-algebra (that is, `S.domRestrict G` is measurable), then `G ∘ Y₁` and `G ∘ Y₂` are almost everywhere measurable
and have the same law.

The typical use is a decoder `G` that is only defined in a meaningful way on the set `S` of inputs where some
limit exists (for instance a vague limit of random measures), where `S` itself need not be a measurable set.

The hypothesis that both `Y₁` and `Y₂` lie in `S` almost surely cannot be dropped: if `S` is a non-measurable set
of full outer measure whose complement also has full outer measure, the inclusions of `S` and of its complement
have the same law, while `G = 1_S` is measurable on both sets and separates them.

* `LatticeProb.map_val_injective_of_subtype`: two measures on a subtype with the same image measure coincide.
* `LatticeProb.aemeasurable_comp_of_ae_mem`: `G ∘ Y` is almost everywhere measurable.
* `LatticeProb.map_comp_eq_of_map_eq_of_ae_mem`: the laws of `G ∘ Y₁` and `G ∘ Y₂` agree.
-/

open MeasureTheory Set

namespace LatticeProb

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- Two measures on a subtype (with the subspace σ-algebra) with the same push-forward under the
inclusion are equal. -/
theorem map_val_injective_of_subtype {S : Set α} {μ ν : Measure S}
    (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext T hT
  obtain ⟨T', hT', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hT
  rw [← Measure.map_apply measurable_subtype_coe hT', h, Measure.map_apply measurable_subtype_coe hT']

/-- A measurable random variable that lies almost surely in a nonempty set `S` agrees almost
everywhere with a measurable random variable valued in the subtype `S`. -/
theorem exists_measurable_subtype_ae_eq {P : Measure Ω} {Y : Ω → α} (hY : Measurable Y)
    {S : Set α} (hS : S.Nonempty) (hYS : ∀ᵐ ω ∂P, Y ω ∈ S) :
    ∃ Z : Ω → S, Measurable Z ∧ ∀ᵐ ω ∂P, (Z ω : α) = Y ω := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hYS)
  let W : Ω → α := N.piecewise (fun _ => s₀) Y
  have hWm : Measurable W := Measurable.piecewise hNm measurable_const hY
  have hWS : ∀ ω, W ω ∈ S := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [W, Set.piecewise_eq_of_mem _ _ _ hω]
      exact hs₀
    · simp only [W, Set.piecewise_eq_of_notMem _ _ _ hω]
      by_contra hn
      exact hω (hNsub hn)
  refine ⟨fun ω => ⟨W ω, hWS ω⟩, hWm.subtype_mk, ?_⟩
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  filter_upwards [hNc] with ω hω
  simp only [W, Set.piecewise_eq_of_notMem _ _ _ hω]

/-- **Almost everywhere measurability through a function measurable on a full set.** If `Y` is almost
everywhere measurable, lies almost surely in `S`, and `G` is measurable on `S` for the subspace σ-algebra,
then `G ∘ Y` is almost everywhere measurable. -/
theorem aemeasurable_comp_of_ae_mem {P : Measure Ω} {Y : Ω → α} (hY : AEMeasurable Y P)
    {S : Set α} (hYS : ∀ᵐ ω ∂P, Y ω ∈ S) {G : α → β} (hG : Measurable (S.domRestrict G)) :
    AEMeasurable (fun ω => G (Y ω)) P := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hP : P = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      simpa using (ae_iff.1 hYS)
    rw [hP]
    exact aemeasurable_zero_measure
  have hmS : ∀ᵐ ω ∂P, hY.mk Y ω ∈ S := by
    filter_upwards [hYS, hY.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  obtain ⟨Z, hZm, hZ⟩ := exists_measurable_subtype_ae_eq hY.measurable_mk hS hmS
  refine ⟨fun ω => S.domRestrict G (Z ω), hG.comp hZm, ?_⟩
  filter_upwards [hZ, hY.ae_eq_mk] with ω h1 h2
  rw [Set.domRestrict_apply, h1, h2]

/-- **Equal laws pass through a function measurable on a set of full outer measure.** Let `Y₁, Y₂` be
almost everywhere measurable random variables with the same law that both lie almost surely in a set `S`
(not necessarily measurable). If `G` is measurable on `S` for the subspace σ-algebra, then `G ∘ Y₁` and
`G ∘ Y₂` have the same law. -/
theorem map_comp_eq_of_map_eq_of_ae_mem {P : Measure Ω} {Y₁ Y₂ : Ω → α}
    (hY₁ : AEMeasurable Y₁ P) (hY₂ : AEMeasurable Y₂ P) (hlaw : P.map Y₁ = P.map Y₂)
    {S : Set α} (h₁ : ∀ᵐ ω ∂P, Y₁ ω ∈ S) (h₂ : ∀ᵐ ω ∂P, Y₂ ω ∈ S)
    {G : α → β} (hG : Measurable (S.domRestrict G)) :
    P.map (fun ω => G (Y₁ ω)) = P.map (fun ω => G (Y₂ ω)) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hP : P = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      simpa using (ae_iff.1 h₁)
    simp [hP]
  have hm₁ : ∀ᵐ ω ∂P, hY₁.mk Y₁ ω ∈ S := by
    filter_upwards [h₁, hY₁.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  have hm₂ : ∀ᵐ ω ∂P, hY₂.mk Y₂ ω ∈ S := by
    filter_upwards [h₂, hY₂.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  obtain ⟨Z₁, hZ₁m, hZ₁⟩ := exists_measurable_subtype_ae_eq hY₁.measurable_mk hS hm₁
  obtain ⟨Z₂, hZ₂m, hZ₂⟩ := exists_measurable_subtype_ae_eq hY₂.measurable_mk hS hm₂
  have hZY₁ : (fun ω => (Z₁ ω : α)) =ᵐ[P] Y₁ := by
    filter_upwards [hZ₁, hY₁.ae_eq_mk] with ω h1 h2
    rw [h1, h2]
  have hZY₂ : (fun ω => (Z₂ ω : α)) =ᵐ[P] Y₂ := by
    filter_upwards [hZ₂, hY₂.ae_eq_mk] with ω h1 h2
    rw [h1, h2]
  have hZlaw : P.map Z₁ = P.map Z₂ := by
    refine map_val_injective_of_subtype ?_
    rw [Measure.map_map measurable_subtype_coe hZ₁m, Measure.map_map measurable_subtype_coe hZ₂m]
    change P.map (fun ω => (Z₁ ω : α)) = P.map (fun ω => (Z₂ ω : α))
    rw [Measure.map_congr hZY₁, Measure.map_congr hZY₂, hlaw]
  have hG₁ : (fun ω => G (Y₁ ω)) =ᵐ[P] (S.domRestrict G ∘ Z₁) := by
    filter_upwards [hZY₁] with ω h
    rw [Function.comp_apply, Set.domRestrict_apply, h]
  have hG₂ : (fun ω => G (Y₂ ω)) =ᵐ[P] (S.domRestrict G ∘ Z₂) := by
    filter_upwards [hZY₂] with ω h
    rw [Function.comp_apply, Set.domRestrict_apply, h]
  rw [Measure.map_congr hG₁, Measure.map_congr hG₂, ← Measure.map_map hG hZ₁m,
    ← Measure.map_map hG hZ₂m, hZlaw]

end LatticeProb
