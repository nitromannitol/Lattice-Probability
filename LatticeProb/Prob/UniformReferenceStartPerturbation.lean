import LatticeProb.Bonanno.BouRabeeGwynne.Section4UniformExitTopology

/-! # Uniform comparison at nearby starting points -/

set_option autoImplicit false

open Set Filter MeasureTheory BouRabeeGwynne
open scoped Topology

namespace LatticeProb

/-- Uniform convergence to a continuous probability kernel on a compact collar
persists when the argument is moved by a uniformly vanishing distance. -/
theorem uniform_reference_law_at_nearby_starts
    {d : ℕ} (K K' : Set (Euc d)) (hK' : IsCompact K')
    (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ x ∈ K, ∀ y, dist y x < r → y ∈ K')
    (V : ℕ → Type*) (p q : ∀ n, V n → Euc d)
    (μ : ∀ n, V n → ProbabilityMeasure (Euc d))
    (ν : K' → ProbabilityMeasure (Euc d)) (hν : Continuous ν)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v, dist (p n v) (q n v) < δ)
    (href : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v, ∀ hp : p n v ∈ K',
      levyProkhorovDist (μ n v : Measure (Euc d)) (ν ⟨p n v, hp⟩ : Measure (Euc d)) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v, ∀ hq : q n v ∈ K,
      levyProkhorovDist (μ n v : Measure (Euc d))
        (ν ⟨q n v, hcollar _ hq _ (by simpa using hr)⟩ : Measure (Euc d)) < ε := by
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have huc : UniformContinuous (fun x : K' => LevyProkhorov.ofMeasure (ν x)) :=
    CompactSpace.uniformContinuous_of_continuous
      (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hν)
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by linarith)
  filter_upwards [hclose (min δ r) (lt_min hδ hr), href (ε / 2) (by linarith)] with n hnclose hnref
  intro v hq
  have hdist := hnclose v
  have hp : p n v ∈ K' := hcollar _ hq _ (lt_of_lt_of_le hdist (min_le_right _ _))
  have hq' : q n v ∈ K' := hcollar _ hq _ (by simpa using hr)
  have hkernel := hmod (a := ⟨p n v, hp⟩) (b := ⟨q n v, hq'⟩)
    (by
      change dist (p n v) (q n v) < δ
      exact lt_of_lt_of_le hdist (min_le_left δ r))
  have hkernel' : levyProkhorovDist (ν ⟨p n v, hp⟩ : Measure (Euc d))
      (ν ⟨q n v, hq'⟩ : Measure (Euc d)) < ε / 2 := by
    simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hkernel
  have htriangle := levyProkhorovDist_triangle (μ n v : Measure (Euc d))
    (ν ⟨p n v, hp⟩ : Measure (Euc d)) (ν ⟨q n v, hq'⟩ : Measure (Euc d))
  have href' := hnref v hp
  linarith

end LatticeProb
