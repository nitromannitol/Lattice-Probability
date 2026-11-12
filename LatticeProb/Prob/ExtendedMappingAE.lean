import Mathlib

/-!
# The extended continuous mapping theorem with an exceptional null set

Let `ν n → ν` weakly on a pseudo-metric space `E`, let `T` be a pseudo-metric space and let
`g n, g : E → T` be Borel maps.  Suppose that for `ν`-almost every `x` the maps `g n` converge to the
constant `g x` uniformly on a small ball around `x`: for every `ε > 0` there are `δ > 0` and `N` such
that `dist (g n y) (g x) ≤ ε` whenever `n ≥ N` and `dist y x < δ`.  Then the image laws converge
weakly, `(ν n).map (g n) → ν.map g` (Billingsley, *Convergence of Probability Measures*, Theorem 5.5;
van der Vaart, *Asymptotic Statistics*, Theorem 18.11).  The proof is the closed-set half of the
portmanteau theorem: the exceptional null set only enlarges the limsup bound by a null set.

* `LatticeProb.limsup_measure_preimage_le_of_ae`: the closed-set bound
  `limsup (ν n) (g n ⁻¹' F) ≤ ν (g ⁻¹' F)`.
* `LatticeProb.tendsto_integral_comp_of_ae_locally_uniform`: convergence of the integrals of bounded
  continuous functions of `g n`.
* `LatticeProb.tendsto_integral_comp_prod_of_ae_locally_uniform`: the same for the pairs
  `(g n x, x)`, which gives joint convergence `(g n (X n), X n) → (g (X), X)` in law.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

namespace LatticeProb

variable {E T : Type*} [PseudoMetricSpace E] [PseudoMetricSpace T]

/-- **The closed-set half of the extended continuous mapping theorem, almost-everywhere form.**
If the laws `νs n` converge weakly to `ν` and, for `ν`-almost every `x`, the maps `fs n` converge to
the constant `f x` uniformly on a small ball about `x`, then the limsup of the image law of a closed
set is at most the limit image law of that set. -/
theorem limsup_measure_preimage_le_of_ae [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : E →ᵇ ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → T) (fs : ℕ → E → T)
    (hlu : ∀ᵐ x ∂ν, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → dist (fs n y) (f x) ≤ ε)
    {F : Set T} (hF : IsClosed F) :
    limsup (fun n => νs n (fs n ⁻¹' F)) atTop ≤ ν (f ⁻¹' F) := by
  classical
  let μ : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  let μs : ℕ → ProbabilityMeasure E := fun n => ⟨νs n, inferInstance⟩
  have hweak : Tendsto μs atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hlim
  set B : ℕ → Set E := fun k => closure (⋃ n ∈ Set.Ici k, fs n ⁻¹' F) with hB
  have hBclosed : ∀ k, IsClosed (B k) := fun k => isClosed_closure
  have hBanti : Antitone B := by
    intro k l hkl
    exact closure_mono (Set.iUnion₂_subset fun n hn => Set.subset_iUnion₂_of_subset n
      (le_trans hkl hn) le_rfl)
  have hstep : ∀ k, limsup (fun n => νs n (fs n ⁻¹' F)) atTop ≤ ν (B k) := by
    intro k
    have hev : ∀ᶠ n in atTop, νs n (fs n ⁻¹' F) ≤ νs n (B k) := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact measure_mono (le_trans (Set.subset_iUnion₂_of_subset n hn le_rfl) subset_closure)
    calc limsup (fun n => νs n (fs n ⁻¹' F)) atTop
        ≤ limsup (fun n => νs n (B k)) atTop := limsup_le_limsup hev
      _ ≤ ν (B k) :=
          ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak (hBclosed k)
  -- The exceptional set where the local uniform hypothesis fails.
  set Z : Set E := {x | ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → dist (fs n y) (f x) ≤ ε} with hZ
  have hZnull : ν Z = 0 := ae_iff.mp hlu
  have hinter : (⋂ k, B k) ⊆ f ⁻¹' F ∪ Z := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · left
      have hxZ' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ y : E, dist y x < δ → dist (fs n y) (f x) ≤ ε := by
        simpa [hZ] using hxZ
      by_contra hxF
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl (f x) hxF
      obtain ⟨δ, hδ, N, hN⟩ := hxZ' (ε / 2) (half_pos hε)
      have hxB : x ∈ B N := Set.mem_iInter.mp hx N
      obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hxB δ hδ
      obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.mp hy
      have h1 := hN n hn y (by rwa [dist_comm] at hyd)
      have hlt : dist (fs n y) (f x) < ε := lt_of_le_of_lt h1 (by linarith)
      have : fs n y ∈ Fᶜ := hball (by simpa [Metric.mem_ball] using hlt)
      exact this hyn
  have hmeas : ∀ k, NullMeasurableSet (B k) ν :=
    fun k => (hBclosed k).measurableSet.nullMeasurableSet
  have htend : Tendsto (fun k => ν (B k)) atTop (𝓝 (ν (⋂ k, B k))) :=
    tendsto_measure_iInter_atTop hmeas hBanti ⟨0, measure_ne_top _ _⟩
  have hle : ν (⋂ k, B k) ≤ ν (f ⁻¹' F) :=
    (measure_mono hinter).trans ((measure_union_le _ _).trans (by rw [hZnull, add_zero]))
  refine le_trans (ge_of_tendsto htend ?_) hle
  exact Eventually.of_forall hstep

/-- **The extended continuous mapping theorem, almost-everywhere local uniform form.**  If the laws
`νs n` converge weakly to `ν` on the pseudo-metric space `E`, the maps `fs n, f : E → T` are Borel,
and for `ν`-almost every `x` the maps `fs n` converge to the constant `f x` uniformly on a small ball
about `x`, then `∫ G (fs n x) d(νs n) → ∫ G (f x) dν` for every bounded continuous `G` on `T`. -/
theorem tendsto_integral_comp_of_ae_locally_uniform
    [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace T] [OpensMeasurableSpace T]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : E →ᵇ ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → T) (fs : ℕ → E → T)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hlu : ∀ᵐ x ∂ν, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → dist (fs n y) (f x) ≤ ε)
    (G : T →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, G (fs n x) ∂(νs n)) atTop (𝓝 (∫ x, G (f x) ∂ν)) := by
  classical
  let μ : ProbabilityMeasure T := ⟨ν.map f, inferInstance⟩
  let μs : ℕ → ProbabilityMeasure T := fun n => ⟨(νs n).map (fs n), inferInstance⟩
  have hcoe : ∀ (n : ℕ) (s : Set T), MeasurableSet s →
      (μs n : Measure T) s = νs n (fs n ⁻¹' s) := by
    intro n s hs
    exact Measure.map_apply (hfs n) hs
  have hcoe' : ∀ s : Set T, MeasurableSet s → (μ : Measure T) s = ν (f ⁻¹' s) := by
    intro s hs
    exact Measure.map_apply hf hs
  have hopen : ∀ U : Set T, IsOpen U →
      (μ : Measure T) U ≤ liminf (fun n => (μs n : Measure T) U) atTop := by
    intro U hU
    refine le_measure_liminf_of_limsup_measure_compl_le hU.measurableSet ?_
    have hkey := limsup_measure_preimage_le_of_ae ν νs hlim f fs hlu (isClosed_compl_iff.mpr hU)
    have hc : ∀ n, (μs n : Measure T) Uᶜ = νs n (fs n ⁻¹' Uᶜ) :=
      fun n => hcoe n Uᶜ hU.measurableSet.compl
    simp only [hc]
    exact hkey.trans_eq (hcoe' Uᶜ hU.measurableSet.compl).symm
  have hweak : Tendsto μs atTop (𝓝 μ) := tendsto_of_forall_isOpen_le_liminf' hopen
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak G
  have hL : ∀ n : ℕ, (∫ t, G t ∂((μs n : Measure T))) = ∫ x, G (fs n x) ∂(νs n) := by
    intro n
    exact integral_map (hfs n).aemeasurable G.continuous.measurable.aestronglyMeasurable
  have hR : (∫ t, G t ∂((μ : Measure T))) = ∫ x, G (f x) ∂ν :=
    integral_map hf.aemeasurable G.continuous.measurable.aestronglyMeasurable
  simpa only [hL, hR] using hint

/-- **Joint convergence with the argument.**  Under the hypotheses of the extended continuous mapping
theorem with a `ν`-null exceptional set, the pairs `(fs n x, x)` converge in law:
`∫ G (fs n x, x) d(νs n) → ∫ G (f x, x) dν` for every bounded continuous `G` on `T × E`.  In
particular, if `Y n → Y` in law and `g n → g` locally uniformly at `law(Y)`-almost every point, then
`(g n (Y n), Y n) → (g Y, Y)` in law. -/
theorem tendsto_integral_comp_prod_of_ae_locally_uniform
    [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace T] [OpensMeasurableSpace T]
    [SecondCountableTopology T]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : E →ᵇ ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → T) (fs : ℕ → E → T)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hlu : ∀ᵐ x ∂ν, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → dist (fs n y) (f x) ≤ ε)
    (G : (T × E) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, G (fs n x, x) ∂(νs n)) atTop (𝓝 (∫ x, G (f x, x) ∂ν)) := by
  refine tendsto_integral_comp_of_ae_locally_uniform ν νs hlim (fun x => (f x, x))
    (fun n x => (fs n x, x)) (fun n => (hfs n).prodMk measurable_id) (hf.prodMk measurable_id)
    ?_ G
  filter_upwards [hlu] with x hx ε hε
  obtain ⟨δ, hδ, N, hN⟩ := hx ε hε
  refine ⟨min δ ε, lt_min hδ hε, N, fun n hn y hy => ?_⟩
  rw [Prod.dist_eq]
  refine max_le (hN n hn y (lt_of_lt_of_le hy (min_le_left _ _))) ?_
  exact (lt_of_lt_of_le hy (min_le_right _ _)).le

end LatticeProb
