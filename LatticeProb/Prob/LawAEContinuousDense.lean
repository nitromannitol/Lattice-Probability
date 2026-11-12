import Mathlib

/-!
# Laws of almost surely continuous real processes from a dense set of coordinates

Let `X` and `Y` be real processes indexed by a first countable topological space `ι`, defined on two probability
spaces, with measurable coordinates and almost surely continuous paths.  If the finite dimensional distributions of
`X` and `Y` agree at all finite families of indices taken from a dense set `D ⊆ ι`, then `X` and `Y` have the same
law on `ι → ℝ` (product σ-algebra).

* `LatticeProb.map_eq_of_ae_continuous_of_dense_finite`: the finite dimensional distributions agree at all
  finite families of indices of `ι`: approximate every index by a sequence in `D` and pass to the limit in
  distribution (almost sure convergence implies convergence in distribution, and limits in distribution are unique).
* `LatticeProb.map_eq_of_ae_continuous_of_dense_coordinates`: equality of the laws, by the uniqueness of a
  projective limit.
-/

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace ι]
  [FirstCountableTopology ι] {μ : Measure Ω} {ν : Measure Ω'}

/-- **Finite dimensional distributions of almost surely continuous processes from a dense set of indices.**
If the vectors of values at all finite families of indices of a dense set `D` have the same law for `X` and `Y`,
and the paths are almost surely continuous, then the same holds for all finite families of indices of `ι`. -/
theorem map_eq_of_ae_continuous_of_dense_finite [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : ∀ i, Measurable fun ω => X ω i)
    (hY : ∀ i, Measurable fun ω => Y ω i) (hXc : ∀ᵐ ω ∂μ, Continuous (X ω))
    (hYc : ∀ᵐ ω ∂ν, Continuous (Y ω)) {D : Set ι} (hD : Dense D)
    (h : ∀ (k : ℕ) (a : Fin k → ι), (∀ j, a j ∈ D) →
      μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j)))
    (k : ℕ) (a : Fin k → ι) :
    μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j)) := by
  have hex : ∀ j, ∃ s : ℕ → ι, (∀ n, s n ∈ D) ∧ Tendsto s atTop (𝓝 (a j)) := fun j =>
    mem_closure_iff_seq_limit.1 (by rw [hD.closure_eq]; exact mem_univ _)
  choose s hsD hs using hex
  have hVXm : ∀ n, Measurable fun ω j => X ω (s j n) := fun n => measurable_pi_iff.2 fun j => hX (s j n)
  have hVYm : ∀ n, Measurable fun ω j => Y ω (s j n) := fun n => measurable_pi_iff.2 fun j => hY (s j n)
  have hZXm : Measurable fun ω j => X ω (a j) := measurable_pi_iff.2 fun j => hX (a j)
  have hZYm : Measurable fun ω j => Y ω (a j) := measurable_pi_iff.2 fun j => hY (a j)
  have hlimX : ∀ᵐ ω ∂μ, Tendsto (fun n => fun j => X ω (s j n)) atTop (𝓝 fun j => X ω (a j)) := by
    filter_upwards [hXc] with ω hω
    exact tendsto_pi_nhds.2 fun j => (hω.tendsto (a j)).comp (hs j)
  have hlimY : ∀ᵐ ω ∂ν, Tendsto (fun n => fun j => Y ω (s j n)) atTop (𝓝 fun j => Y ω (a j)) := by
    filter_upwards [hYc] with ω hω
    exact tendsto_pi_nhds.2 fun j => (hω.tendsto (a j)).comp (hs j)
  have h1 := tendstoInDistribution_of_ae_tendsto (fun n => (hVXm n).aemeasurable) hZXm.aemeasurable hlimX
  have h2 := tendstoInDistribution_of_ae_tendsto (fun n => (hVYm n).aemeasurable) hZYm.aemeasurable hlimY
  have hn : ∀ n, μ.map (fun ω j => X ω (s j n)) = ν.map (fun ω j => Y ω (s j n)) := fun n =>
    h k (fun j => s j n) (fun j => hsD j n)
  have h1t := h1.tendsto
  have h2t := h2.tendsto
  have hseq : (fun n => (⟨μ.map (fun ω j => X ω (s j n)), inferInstance⟩ : ProbabilityMeasure (Fin k → ℝ))) =
      fun n => ⟨ν.map (fun ω j => Y ω (s j n)), inferInstance⟩ := funext fun n => Subtype.ext (hn n)
  have h1t' := h1t
  simp only [hseq] at h1t'
  have h_eq := tendsto_nhds_unique h1t' h2t
  have h_eq' := congrArg (fun p : ProbabilityMeasure (Fin k → ℝ) => (p : Measure (Fin k → ℝ))) h_eq
  simpa using h_eq'

/-- **Equality of laws of almost surely continuous real processes from a dense set of indices.**
Let `X : Ω → ι → ℝ` and `Y : Ω' → ι → ℝ` have measurable coordinates and almost surely continuous paths on a first
countable space `ι`, and let `D ⊆ ι` be dense.  If for all finite families of indices of `D` the vectors of values of
`X` and `Y` have the same law, then `X` and `Y` have the same law. -/
theorem map_eq_of_ae_continuous_of_dense_coordinates [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : ∀ i, Measurable fun ω => X ω i)
    (hY : ∀ i, Measurable fun ω => Y ω i) (hXc : ∀ᵐ ω ∂μ, Continuous (X ω))
    (hYc : ∀ᵐ ω ∂ν, Continuous (Y ω)) {D : Set ι} (hD : Dense D)
    (h : ∀ (k : ℕ) (a : Fin k → ι), (∀ j, a j ∈ D) →
      μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j))) :
    μ.map X = ν.map Y := by
  have hA := map_eq_of_ae_continuous_of_dense_finite hX hY hXc hYc hD h
  have hXm : Measurable X := measurable_pi_iff.2 hX
  have hYm : Measurable Y := measurable_pi_iff.2 hY
  -- equality of the marginals on finite sets of indices
  have hfin : ∀ I : Finset ι, μ.map (fun ω (i : I) => X ω i) = ν.map (fun ω (i : I) => Y ω i) := by
    intro I
    classical
    let e : Fin I.card ≃ I := I.equivFin.symm
    let g : (Fin I.card → ℝ) → (I → ℝ) := fun w i => w (e.symm i)
    have hg : Measurable g := Measurable.of_eval fun i => measurable_pi_apply _
    have hXe : (fun ω (i : I) => X ω i) = g ∘ fun ω j => X ω ((e j : I) : ι) := by
      funext ω i
      simp [g]
    have hYe : (fun ω (i : I) => Y ω i) = g ∘ fun ω j => Y ω ((e j : I) : ι) := by
      funext ω i
      simp [g]
    have hXv : Measurable fun ω j => X ω ((e j : I) : ι) := measurable_pi_iff.2 fun j => hX _
    have hYv : Measurable fun ω j => Y ω ((e j : I) : ι) := measurable_pi_iff.2 fun j => hY _
    rw [hXe, hYe, ← Measure.map_map hg hXv, ← Measure.map_map hg hYv,
      hA I.card (fun j => ((e j : I) : ι))]
  have hP : IsProjectiveLimit (μ.map X) (fun I : Finset ι => μ.map fun ω (i : I) => X ω i) := by
    intro I
    have hg : Measurable (I.restrict : (ι → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : ι)
    rw [Measure.map_map hg hXm]
    rfl
  have hQ : IsProjectiveLimit (ν.map Y) (fun I : Finset ι => μ.map fun ω (i : I) => X ω i) := by
    intro I
    have hg : Measurable (I.restrict : (ι → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : ι)
    rw [Measure.map_map hg hYm]
    exact (hfin I).symm
  exact IsProjectiveLimit.unique hP hQ

end LatticeProb
