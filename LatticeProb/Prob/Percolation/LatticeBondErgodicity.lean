import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Translation

/-!
# Ergodicity of canonical unordered-bond translations

Every nonzero lattice displacement moves each finite family of unordered bonds off itself
by moving its finite set of endpoints. The existing product-shift ergodicity theorem then
applies to the inverse pullback defining configuration translation, at every Bernoulli parameter.
-/

namespace LatticeProb.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- Iterating literal endpoint translation adds the natural multiple of its displacement. -/
theorem bondTranslation_iterate (z : Vertex d) (n : ℕ) (e : Bond d) :
    (bondTranslation z : Bond d → Bond d)^[n] e = bondTranslation (n • z) e := by
  induction n generalizing e with
  | zero => simp only [Function.iterate_zero, id_eq, zero_smul, bondTranslation_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, bondTranslation_add, succ_nsmul, add_comm z]

/-- A nonzero displacement eventually moves every bond in a finite family outside it. -/
theorem exists_bondTranslation_nsmul_notMem {z : Vertex d} (hz : z ≠ 0)
    (s : Finset (Bond d)) :
    ∃ n : ℕ, ∀ e ∈ s, bondTranslation (n • z) e ∉ s := by
  classical
  let t : Finset (Vertex d) := s.biUnion fun e => e.val.toFinset
  have endpoint_mem : ∀ e ∈ s, ∀ x ∈ e.val, x ∈ t := by
    intro e he x hx
    exact Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hx⟩
  obtain ⟨n, hn⟩ := exists_add_nsmul_notMem hz t
  refine ⟨n, fun e he htranslated => ?_⟩
  obtain ⟨x, y, hxy, _⟩ := e.property
  have hx : x ∈ e.val := hxy.symm ▸ Sym2.mem_mk_left x y
  have htranslated_x : x + n • z ∈ (bondTranslation (n • z) e).val := by
    rw [bondTranslation_val]
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  exact hn x (endpoint_mem e he x hx)
    (endpoint_mem _ htranslated _ htranslated_x)

/-- Every nonzero canonical configuration translation is ergodic for the actual bond law. -/
theorem ergodic_configurationTranslation (p : unitInterval) {z : Vertex d} (hz : z ≠ 0) :
    Ergodic (configurationTranslation z) (latticeBondLaw d p) := by
  change Ergodic (coordShift (bondTranslation (-z)))
    (Measure.infinitePi fun _ : Bond d => bernoulliMeasure true false p)
  refine ergodic_coordShift_infinitePi (fun _ : Bond d => bernoulliMeasure true false p)
    (bondTranslation (-z)).injective (fun _ => rfl) fun s => ?_
  obtain ⟨n, hn⟩ := exists_bondTranslation_nsmul_notMem (neg_ne_zero.mpr hz) s
  exact ⟨n, fun e he => by rw [bondTranslation_iterate]; exact hn e he⟩

/-- A measurable event invariant under one nonzero bond translation has probability zero or one. -/
theorem latticeBondLaw_zero_or_one_of_translationInvariant (p : unitInterval)
    {z : Vertex d} (hz : z ≠ 0) {A : Set (Configuration d)} (hA : MeasurableSet A)
    (hinv : configurationTranslation z ⁻¹' A = A) :
    latticeBondLaw d p A = 0 ∨ latticeBondLaw d p A = 1 := by
  rcases (ergodic_configurationTranslation p hz).ae_empty_or_univ hA hinv with h | h
  · left
    rw [measure_congr h, measure_empty]
  · right
    rw [measure_congr h, measure_univ]

end LatticeProb.Percolation
