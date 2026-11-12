import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.CompactOpen

/-!
# Independence through countably many almost sure coordinates

Let `e : β → (ι → ℝ)` be a measurable embedding with a countable index set `ι`. If every coordinate `e (Z ω) i` of a
random variable `Z` is almost surely a measurable function `g i` of a random variable `Y`, and `Y` is independent of
`ξ`, then `Z` is independent of `ξ`. No measurability of `Z` is assumed.

The typical embedding is the restriction of a continuous path to a countable dense set of times: for a Polish space
`C(T, ℝ)` with its Borel σ-algebra and `D : ι → T` of dense range, `f ↦ (f (D i))_i` is a measurable embedding
(Lusin-Souslin). This identifies the law of a continuous process with that of its values at countably many times, so
a continuous version of a process built from independent data inherits the independence.

* `measurableEmbedding_restrict_denseRange`
* `indepFun_of_measurableEmbedding_ae`
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Prob

/-- The restriction of a continuous real function to a dense countable family of points is a measurable embedding,
when the space of continuous functions is Polish with its Borel σ-algebra. -/
theorem measurableEmbedding_restrict_denseRange {T ι : Type*} [TopologicalSpace T] [Countable ι] {D : ι → T}
    (hD : DenseRange D) [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)] [PolishSpace C(T, ℝ)] :
    MeasurableEmbedding (fun f : C(T, ℝ) => fun i => f (D i)) := by
  refine Continuous.measurableEmbedding (continuous_pi fun i => continuous_eval_const (D i)) ?_
  intro f g hfg
  have h : ∀ i, f (D i) = g (D i) := fun i => congrFun hfg i
  ext x
  exact congrFun (Continuous.ext_on hD f.continuous g.continuous (by
    rintro _ ⟨i, rfl⟩
    exact h i)) x

/-- **Independence through countably many almost sure coordinates.** If `e` is a measurable embedding into `ι → ℝ`
(`ι` countable), each coordinate `e (Z ·) i` is almost surely `g i (Y ·)` with `g i` measurable, and `Y` is
independent of `ξ`, then `Z` is independent of `ξ`. -/
theorem indepFun_of_measurableEmbedding_ae {Ω β γ δ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] [Countable ι] {P : Measure Ω} {e : β → ι → ℝ}
    (he : MeasurableEmbedding e) {Z : Ω → β} {Y : Ω → γ} {ξ : Ω → δ} {g : ι → γ → ℝ}
    (hg : ∀ i, Measurable (g i)) (hZ : ∀ i, ∀ᵐ ω ∂P, e (Z ω) i = g i (Y ω)) (hind : IndepFun Y ξ P) :
    IndepFun Z ξ P := by
  have hG : Measurable fun y : γ => fun i => g i y := measurable_pi_iff.2 hg
  have h1 : IndepFun (fun ω => e (Z ω)) ξ P := by
    have h0 : IndepFun ((fun y : γ => fun i => g i y) ∘ Y) ξ P := hind.comp hG measurable_id
    refine h0.congr ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [ae_all_iff.2 hZ] with ω hω
    funext i
    exact (hω i).symm
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h1 ⊢
  intro S S' hS hS'
  have hpre : Z ⁻¹' S = (fun ω => e (Z ω)) ⁻¹' (e '' S) := by
    ext ω
    simp only [Set.mem_preimage, he.injective.mem_set_image]
  rw [hpre]
  exact h1 _ _ (he.measurableSet_image' hS) hS'

end LatticeProb.Prob
