import Mathlib

/-!
# Laws of almost surely continuous real processes from a dense set of coordinates

Let `X` and `Y` be real processes indexed by a first countable topological space `ι`, defined on two probability
spaces, almost measurable as maps into `ι → ℝ` (product σ-algebra) and with almost surely continuous paths.  If the finite dimensional distributions of
`X` and `Y` agree at all finite families of indices taken from a dense set `D ⊆ ι`, then `X` and `Y` have the same
law on `ι → ℝ` (product σ-algebra).

* `LatticeProb.aemeasurable_apply_of_ae_continuous_of_dense` and `LatticeProb.aemeasurable_of_ae_continuous`: an
  almost surely continuous process whose coordinates at a dense set of indices are almost measurable has almost
  measurable coordinates, and, on a separable index space, is almost measurable as a map into `ι → ℝ`.
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

/-- **Coordinates of an almost surely continuous process from a dense set of indices.**  If the coordinates of
an almost surely continuous process at the indices of a dense set are almost measurable, so are all its
coordinates. -/
theorem aemeasurable_apply_of_ae_continuous_of_dense {X : Ω → ι → ℝ} (hXc : ∀ᵐ ω ∂μ, Continuous (X ω))
    {D : Set ι} (hD : Dense D) (hXD : ∀ d ∈ D, AEMeasurable (fun ω => X ω d) μ) (i : ι) :
    AEMeasurable (fun ω => X ω i) μ := by
  obtain ⟨s, hsD, hs⟩ : ∃ s : ℕ → ι, (∀ n, s n ∈ D) ∧ Tendsto s atTop (𝓝 i) :=
    mem_closure_iff_seq_limit.1 (by rw [hD.closure_eq]; exact mem_univ _)
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hXD (s n) (hsD n)) ?_
  filter_upwards [hXc] with ω hω
  exact (hω.tendsto i).comp hs

/-- **An almost surely continuous process with almost measurable coordinates on a separable space is almost
measurable.**  On a separable first countable index space `ι`, if the paths of `X` are almost surely continuous and
every coordinate is almost measurable, then `X : Ω → ι → ℝ` is almost measurable for the product σ-algebra: it agrees
almost surely with a process with measurable coordinates, built from measurable versions of the coordinates at
a countable dense set of indices. -/
theorem aemeasurable_of_ae_continuous [TopologicalSpace.SeparableSpace ι] {X : Ω → ι → ℝ} (hXc : ∀ᵐ ω ∂μ, Continuous (X ω))
    (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ) : AEMeasurable X μ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  have hex : ∀ i : ι, ∃ s : ℕ → ι, (∀ n, s n ∈ D) ∧ Tendsto s atTop (𝓝 i) := fun i =>
    mem_closure_iff_seq_limit.1 (by rw [hDd.closure_eq]; exact mem_univ _)
  choose s hsD hs using hex
  let Xt : ι → Ω → ℝ := fun d => (hX d).mk _
  have hXt : ∀ d, Measurable (Xt d) := fun d => (hX d).measurable_mk
  have hae : ∀ᵐ ω ∂μ, ∀ d ∈ D, X ω d = Xt d ω := by
    rw [ae_ball_iff hDc]
    exact fun d _ => (hX d).ae_eq_mk
  let G : Ω → ι → ℝ := fun ω i => (limsup (fun n => ((Xt (s i n) ω : ℝ) : EReal)) atTop).toReal
  have hG : Measurable G := by
    refine measurable_pi_iff.2 fun i => ?_
    exact Measurable.ereal_toReal (Measurable.limsup (f := fun n ω => ((Xt (s i n) ω : ℝ) : EReal))
      fun n => (hXt _).coe_real_ereal)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hXc, hae] with ω hc he
  funext i
  have h1 : Tendsto (fun n => Xt (s i n) ω) atTop (𝓝 (X ω i)) :=
    ((hc.tendsto i).comp (hs i)).congr fun n => he _ (hsD i n)
  have h2 := ((continuous_coe_real_ereal.tendsto _).comp h1).limsup_eq
  simp only [G, Function.comp_def] at h2 ⊢
  rw [h2, EReal.toReal_coe]

/-- **Finite dimensional distributions of almost surely continuous processes from a dense set of indices.**
If the vectors of values at all finite families of indices of a dense set `D` have the same law for `X` and `Y`,
and the paths are almost surely continuous, then the same holds for all finite families of indices of `ι`. -/
theorem map_eq_of_ae_continuous_of_dense_finite [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν) (hXc : ∀ᵐ ω ∂μ, Continuous (X ω))
    (hYc : ∀ᵐ ω ∂ν, Continuous (Y ω)) {D : Set ι} (hD : Dense D)
    (h : ∀ (k : ℕ) (a : Fin k → ι), (∀ j, a j ∈ D) →
      μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j)))
    (k : ℕ) (a : Fin k → ι) :
    μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j)) := by
  have hex : ∀ j, ∃ s : ℕ → ι, (∀ n, s n ∈ D) ∧ Tendsto s atTop (𝓝 (a j)) := fun j =>
    mem_closure_iff_seq_limit.1 (by rw [hD.closure_eq]; exact mem_univ _)
  choose s hsD hs using hex
  have hVXm : ∀ n, AEMeasurable (fun ω j => X ω (s j n)) μ := fun n => aemeasurable_pi_iff.2 fun j => hX (s j n)
  have hVYm : ∀ n, AEMeasurable (fun ω j => Y ω (s j n)) ν := fun n => aemeasurable_pi_iff.2 fun j => hY (s j n)
  have hZXm : AEMeasurable (fun ω j => X ω (a j)) μ := aemeasurable_pi_iff.2 fun j => hX (a j)
  have hZYm : AEMeasurable (fun ω j => Y ω (a j)) ν := aemeasurable_pi_iff.2 fun j => hY (a j)
  have hlimX : ∀ᵐ ω ∂μ, Tendsto (fun n => fun j => X ω (s j n)) atTop (𝓝 fun j => X ω (a j)) := by
    filter_upwards [hXc] with ω hω
    exact tendsto_pi_nhds.2 fun j => (hω.tendsto (a j)).comp (hs j)
  have hlimY : ∀ᵐ ω ∂ν, Tendsto (fun n => fun j => Y ω (s j n)) atTop (𝓝 fun j => Y ω (a j)) := by
    filter_upwards [hYc] with ω hω
    exact tendsto_pi_nhds.2 fun j => (hω.tendsto (a j)).comp (hs j)
  have h1 := tendstoInDistribution_of_ae_tendsto hVXm hZXm hlimX
  have h2 := tendstoInDistribution_of_ae_tendsto hVYm hZYm hlimY
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
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y ν)
    (hXc : ∀ᵐ ω ∂μ, Continuous (X ω)) (hYc : ∀ᵐ ω ∂ν, Continuous (Y ω)) {D : Set ι} (hD : Dense D)
    (h : ∀ (k : ℕ) (a : Fin k → ι), (∀ j, a j ∈ D) →
      μ.map (fun ω j => X ω (a j)) = ν.map (fun ω j => Y ω (a j))) :
    μ.map X = ν.map Y := by
  have hX : ∀ i, AEMeasurable (fun ω => X ω i) μ := fun i => (measurable_pi_apply i).comp_aemeasurable hXm
  have hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν := fun i => (measurable_pi_apply i).comp_aemeasurable hYm
  have hA := map_eq_of_ae_continuous_of_dense_finite hX hY hXc hYc hD h
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
    have hXv : AEMeasurable (fun ω j => X ω ((e j : I) : ι)) μ := aemeasurable_pi_iff.2 fun j => hX _
    have hYv : AEMeasurable (fun ω j => Y ω ((e j : I) : ι)) ν := aemeasurable_pi_iff.2 fun j => hY _
    rw [hXe, hYe, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hXv,
      ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hYv, hA I.card (fun j => ((e j : I) : ι))]
  have hP : IsProjectiveLimit (μ.map X) (fun I : Finset ι => μ.map fun ω (i : I) => X ω i) := by
    intro I
    have hg : Measurable (I.restrict : (ι → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : ι)
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hXm]
    rfl
  have hQ : IsProjectiveLimit (ν.map Y) (fun I : Finset ι => μ.map fun ω (i : I) => X ω i) := by
    intro I
    have hg : Measurable (I.restrict : (ι → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : ι)
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hYm]
    exact (hfin I).symm
  exact IsProjectiveLimit.unique hP hQ

end LatticeProb
