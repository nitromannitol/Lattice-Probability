import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Distinct contacts of compact images -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- For two continuously varying compact images in a metric space, the event that
    their intersection contains two distinct points is Borel. -/
theorem measurableSet_compact_images_two_contact
    {Ω K E : Type} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [MetricSpace E]
    (f g : Ω × K → E) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {ω | ∃ x y x' y' : K,
      f (ω, x) = g (ω, y) ∧ f (ω, x') = g (ω, y') ∧
        f (ω, x) ≠ f (ω, x')} := by
  let F₀ : Ω × (K × K × K × K) → E := fun p => f (p.1, p.2.1)
  let G₀ : Ω × (K × K × K × K) → E := fun p => g (p.1, p.2.2.1)
  let F₁ : Ω × (K × K × K × K) → E := fun p => f (p.1, p.2.2.2.1)
  let G₁ : Ω × (K × K × K × K) → E := fun p => g (p.1, p.2.2.2.2)
  have hF₀ : Continuous F₀ := hf.comp (by fun_prop)
  have hG₀ : Continuous G₀ := hg.comp (by fun_prop)
  have hF₁ : Continuous F₁ := hf.comp (by fun_prop)
  have hG₁ : Continuous G₁ := hg.comp (by fun_prop)
  let A : ℕ → Set (Ω × (K × K × K × K)) := fun n =>
    {p | F₀ p = G₀ p ∧ F₁ p = G₁ p ∧
      1 / (n + 1 : ℝ) ≤ dist (F₀ p) (F₁ p)}
  have hA : ∀ n, IsClosed (A n) := by
    intro n
    exact (isClosed_eq hF₀ hG₀).inter
      ((isClosed_eq hF₁ hG₁).inter (isClosed_le continuous_const (hF₀.dist hF₁)))
  have hproj : ∀ n, MeasurableSet (Prod.fst '' A n) := fun n =>
    (isClosedMap_fst_of_compactSpace _ (hA n)).measurableSet
  have heq : {ω | ∃ x y x' y' : K,
      f (ω, x) = g (ω, y) ∧ f (ω, x') = g (ω, y') ∧
        f (ω, x) ≠ f (ω, x')} = ⋃ n, Prod.fst '' A n := by
    ext ω
    constructor
    · rintro ⟨x, y, x', y', h₀, h₁, hne⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hne)
      refine mem_iUnion.mpr ⟨n, ⟨(ω, (x, y, x', y')), ?_, rfl⟩⟩
      exact ⟨h₀, h₁, hn.le⟩
    · intro h
      obtain ⟨n, ⟨⟨ω', x, y, x', y'⟩, hw, he⟩⟩ := mem_iUnion.mp h
      change ω' = ω at he
      subst ω'
      change f (ω, x) = g (ω, y) ∧ f (ω, x') = g (ω, y') ∧
        1 / (n + 1 : ℝ) ≤ dist (f (ω, x)) (f (ω, x')) at hw
      refine ⟨x, y, x', y', hw.1, hw.2.1, ?_⟩
      exact dist_pos.mp (lt_of_lt_of_le (by positivity) hw.2.2)
  rw [heq]
  exact MeasurableSet.iUnion hproj

end LatticeProb
