import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Measurability of injective compact curves -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Injectivity is a Borel property of continuous maps on a compact metric space. -/
theorem measurableSet_injective_continuousMap
    {K E : Type} [MetricSpace K] [CompactSpace K] [MetricSpace E] :
    MeasurableSet {f : C(K, E) | Function.Injective f} := by
  let A : ℕ → Set (C(K, E) × (K × K)) := fun n =>
    {p | p.1 p.2.1 = p.1 p.2.2 ∧ 1 / (n + 1 : ℝ) ≤ dist p.2.1 p.2.2}
  have hA : ∀ n, IsClosed (A n) := by
    intro n
    have hf : Continuous (fun p : C(K, E) × (K × K) => p.1 p.2.1) := by fun_prop
    have hg : Continuous (fun p : C(K, E) × (K × K) => p.1 p.2.2) := by fun_prop
    have hx : Continuous (fun p : C(K, E) × (K × K) => p.2.1) := by fun_prop
    have hy : Continuous (fun p : C(K, E) × (K × K) => p.2.2) := by fun_prop
    exact (isClosed_eq hf hg).inter (isClosed_le continuous_const (hx.dist hy))
  have hproj : ∀ n, MeasurableSet (Prod.fst '' A n) := fun n =>
    (isClosedMap_fst_of_compactSpace _ (hA n)).measurableSet
  have heq : {f : C(K, E) | Function.Injective f} = (⋃ n, Prod.fst '' A n)ᶜ := by
    ext f
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
    constructor
    · intro hinj n h
      obtain ⟨⟨g, x, y⟩, hxy, rfl⟩ := h
      have : x = y := hinj hxy.1
      subst y
      have := hxy.2
      simp only [dist_self] at this
      exact (not_le_of_gt (by positivity)) this
    · intro h x y hxy
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hne)
      apply h n
      exact ⟨(f, (x, y)), ⟨hxy, hn.le⟩, rfl⟩
  rw [heq]
  exact (MeasurableSet.iUnion hproj).compl

end LatticeProb
