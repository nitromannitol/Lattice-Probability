import LatticeProb.Topology.AreaCurveComponentTotalLength
import LatticeProb.Topology.PlaneTopology

/-! # Lengths of all component intervals -/

set_option autoImplicit false

open Set MeasureTheory Function LatticeProb.Topology

namespace LatticeProb

/-- If each interior component has an interval-image witness, the component
intervals can be indexed by the countable set of all components, and their
lengths sum to the length of the original segment. -/
theorem exists_all_component_interval_lengths
    (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t)
    (hwitness : ∀ x ∈ interior (η '' Icc s t), ∃ a b : ℝ,
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x)) :
    ∃ (x : {U // U ∈ connectedComponentsIn (interior (η '' Icc s t))} → ℂ)
      (a b : {U // U ∈ connectedComponentsIn (interior (η '' Icc s t))} → ℝ),
      (∀ i, connectedComponentIn (interior (η '' Icc s t)) (x i) = i.1) ∧
      (∀ i, η '' Icc (a i) (b i) = closure i.1) ∧
      (∑' i, ENNReal.ofReal (b i - a i)) = ENNReal.ofReal (t - s) := by
  classical
  let O := interior (η '' Icc s t)
  let C := connectedComponentsIn O
  have hdis : C.PairwiseDisjoint id := by
    intro U hU V hV hne
    apply disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨u, hu, rfl⟩ := hU
    obtain ⟨v, hv, rfl⟩ := hV
    exact hne ((connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm)
  have hcount : C.Countable := by
    apply hdis.countable_of_isOpen
    · rintro U ⟨u, hu, rfl⟩
      exact isOpen_interior.connectedComponentIn
    · rintro U ⟨u, hu, rfl⟩
      exact ⟨u, mem_connectedComponentIn hu⟩
  let : Countable C := hcount.to_subtype
  have hrep : ∀ i : C, ∃ x ∈ O, connectedComponentIn O x = i.1 := by
    intro i
    obtain ⟨x, hx, heq⟩ := i.2
    exact ⟨x, hx, heq⟩
  choose x hx hxeq using hrep
  have hw : ∀ i : C, ∃ a b : ℝ, η '' Icc a b = closure i.1 := by
    intro i
    obtain ⟨a, b, hab⟩ := hwitness (x i) (hx i)
    change η '' Icc a b = closure (connectedComponentIn O (x i)) at hab
    rw [hxeq i] at hab
    exact ⟨a, b, hab⟩
  choose a b hab using hw
  refine ⟨x, a, b, hxeq, hab, ?_⟩
  apply tsum_component_interval_lengths_eq η μ hp hs hmap harea hst x a b
  · intro i
    rw [hxeq i]
    exact ⟨x i, by rw [← hxeq i]; exact mem_connectedComponentIn (hx i)⟩
  · intro i
    rw [hxeq i]
    exact hab i
  · intro i j hij
    rw [hxeq i, hxeq j]
    exact fun h => hij (Subtype.ext h)
  · intro z hz
    let i : C := ⟨connectedComponentIn O z, ⟨z, hz, rfl⟩⟩
    exact ⟨i, by rw [hxeq i]; exact mem_connectedComponentIn hz⟩

end LatticeProb
