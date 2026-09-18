/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
The extended continuous mapping theorem.

Let `X_n → X` in law as random elements of a metric space `E`, and let
`f_n, f : E → ℝ` be Borel functions such that `f_n(x_n) → f(x)` whenever
`x_n → x` in `E`.  Then `f_n(X_n) → f(X)` in law.  This is van der Vaart,
*Asymptotic Statistics*, Theorem 18.11, and Billingsley, *Convergence of
Probability Measures*, Theorem 5.5.

The proof is the closed-set half of the portmanteau theorem and nothing else;
no coupling and no Skorokhod representation are used.  For `F ⊆ ℝ` closed put
`S_k = ⋃_{n ≥ k} f_n⁻¹(F)` and `B_k = closure(S_k)`.  Then
`limsup_n P(f_n(X_n) ∈ F) ≤ limsup_n P(X_n ∈ B_k) ≤ P(X ∈ B_k)` for every `k`,
the sets `B_k` decrease, and `⋂_k B_k ⊆ f⁻¹(F)`, so
`limsup_n P(f_n(X_n) ∈ F) ≤ P(f(X) ∈ F)`.

The last inclusion is where the hypothesis on `f_n` enters, and it uses only
its local uniform form: if `f(x) ∉ F` then an `ε`-ball about `f(x)` misses `F`,
and a `δ`-ball about `x` on which `|f_n − f(x)| ≤ ε/2` for all `n ≥ N` misses
`S_N`, so `x ∉ B_N`.  The local uniform form is proved here to follow from the
sequential one in any metric space.
-/
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.ExtendedMapping

variable {E : Type*} [PseudoMetricSpace E]

/-- **The sequential hypothesis of the extended continuous mapping theorem
implies its local uniform form.**  If `f_n(x_n) → f(x)` for every sequence
`x_n → x`, then for every `x` and every `ε > 0` there are a radius `δ > 0` and
a threshold `N` beyond which `f_n` stays within `ε` of `f(x)` on the whole
`δ`-ball about `x`.  No separability or completeness is used. -/
theorem locallyUniform_of_seq (fs : ℕ → E → ℝ) (f : E → ℝ)
    (hseq : ∀ (x : E) (z : ℕ → E), Tendsto z atTop (𝓝 x) →
      Tendsto (fun n => fs n (z n)) atTop (𝓝 (f x)))
    (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : E, dist y x < δ →
      |fs n y - f x| ≤ ε := by
  classical
  by_contra hcon
  push Not at hcon
  -- From the failure, extract for every radius and every threshold a bad index and a bad point.
  have hbad : ∀ (j : ℕ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ ∃ y : E,
      dist y x < 1 / (j + 1 : ℝ) ∧ ε < |fs n y - f x| := by
    intro j N
    have hpos : (0 : ℝ) < 1 / (j + 1 : ℝ) := by positivity
    obtain ⟨n, hn, y, hy, hy'⟩ := hcon (1 / (j + 1 : ℝ)) hpos N
    exact ⟨n, hn, y, hy, hy'⟩
  choose idx hidx pt hpt hpt' using hbad
  -- A strictly increasing sequence of bad indices, with the bad points approaching `x`.
  let n : ℕ → ℕ := fun j => Nat.rec (idx 0 0) (fun j m => idx (j + 1) (m + 1)) j
  have hn0 : n 0 = idx 0 0 := rfl
  have hnsucc : ∀ j, n (j + 1) = idx (j + 1) (n j + 1) := fun _ => rfl
  let w : ℕ → E := fun j => Nat.rec (pt 0 0) (fun j _ => pt (j + 1) (n j + 1)) j
  have hw0 : w 0 = pt 0 0 := rfl
  have hwsucc : ∀ j, w (j + 1) = pt (j + 1) (n j + 1) := fun _ => rfl
  have hmono : StrictMono n := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    have h := hidx (j + 1) (n j + 1)
    rw [hnsucc j]
    omega
  have hw : ∀ j : ℕ, dist (w j) x < 1 / (j + 1 : ℝ) := by
    intro j
    cases j with
    | zero => rw [hw0]; exact hpt 0 0
    | succ j => rw [hwsucc j]; exact hpt (j + 1) (n j + 1)
  have hwbad : ∀ j : ℕ, ε < |fs (n j) (w j) - f x| := by
    intro j
    cases j with
    | zero => rw [hw0, hn0]; exact hpt' 0 0
    | succ j => rw [hwsucc j, hnsucc j]; exact hpt' (j + 1) (n j + 1)
  -- Splice the bad points into a sequence converging to `x`.
  let z : ℕ → E := fun m => @dite E (∃ j, n j = m) (Classical.propDecidable _)
    (fun h => w (Classical.choose h)) (fun _ => x)
  have hzdef : ∀ m : ℕ, z m = @dite E (∃ j, n j = m) (Classical.propDecidable _)
      (fun h => w (Classical.choose h)) (fun _ => x) := fun _ => rfl
  have hzn : ∀ j, z (n j) = w j := by
    intro j
    have h : ∃ i, n i = n j := ⟨j, rfl⟩
    have hc : Classical.choose h = j := hmono.injective (Classical.choose_spec h)
    rw [hzdef, dif_pos h, hc]
  have hz : Tendsto z atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
    refine ⟨n J, fun m hm => ?_⟩
    rw [hzdef]
    rcases Classical.em (∃ j, n j = m) with h | h
    · rw [dif_pos h]
      set c : ℕ := Classical.choose h with hcdef
      have hj : n c = m := Classical.choose_spec h
      have hJle : J ≤ c := by
        by_contra hlt
        push Not at hlt
        have := hmono hlt
        omega
      have hle : 1 / ((c : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (J : ℝ) ≤ (c : ℝ) := by exact_mod_cast hJle
        linarith
      exact lt_of_lt_of_le (lt_of_lt_of_le (hw c) hle) hJ.le
    · rw [dif_neg h]
      simpa using hδ
  have hlim := hseq x z hz
  have hsub : Tendsto (fun j => fs (n j) (z (n j))) atTop (𝓝 (f x)) :=
    hlim.comp hmono.tendsto_atTop
  have hfin : ∀ᶠ j in atTop, |fs (n j) (z (n j)) - f x| < ε := by
    rw [Metric.tendsto_atTop] at hsub
    obtain ⟨J, hJ⟩ := hsub ε hε
    filter_upwards [eventually_ge_atTop J] with j hj
    simpa [Real.dist_eq] using hJ j hj
  obtain ⟨j, hj⟩ := hfin.exists
  rw [hzn j] at hj
  exact absurd hj (not_lt.mpr (hwbad j).le)

/-- **The closed-set half of the extended continuous mapping theorem.**  Under
the local uniform hypothesis the limsup of the image laws of a closed set is at
most its measure under the limit image law. -/
theorem limsup_measure_preimage_le [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : BoundedContinuousFunction E ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → ℝ) (fs : ℕ → E → ℝ)
    (hlu : ∀ (x : E) {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → |fs n y - f x| ≤ ε)
    {F : Set ℝ} (hF : IsClosed F) :
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
  -- Each `B k` swallows the preimages from `k` on.
  have hstep : ∀ k, limsup (fun n => νs n (fs n ⁻¹' F)) atTop ≤ ν (B k) := by
    intro k
    have hev : ∀ᶠ n in atTop, νs n (fs n ⁻¹' F) ≤ νs n (B k) := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact measure_mono (le_trans (Set.subset_iUnion₂_of_subset n hn le_rfl) subset_closure)
    calc limsup (fun n => νs n (fs n ⁻¹' F)) atTop
        ≤ limsup (fun n => νs n (B k)) atTop := limsup_le_limsup hev
      _ ≤ ν (B k) :=
          ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak (hBclosed k)
  -- The intersection of the `B k` lies inside the preimage of the closed set.
  have hinter : (⋂ k, B k) ⊆ f ⁻¹' F := by
    intro x hx
    by_contra hxF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl (f x) hxF
    obtain ⟨δ, hδ, N, hN⟩ := hlu x (half_pos hε)
    have hxB : x ∈ B N := Set.mem_iInter.mp hx N
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hxB δ hδ
    obtain ⟨n, hn, hyn⟩ := Set.mem_iUnion₂.mp hy
    have := hN n hn y (by rwa [dist_comm] at hyd)
    have hlt : |fs n y - f x| < ε := lt_of_le_of_lt this (by linarith)
    have : fs n y ∈ Fᶜ := hball (by simpa [Real.dist_eq] using hlt)
    exact this hyn
  have hmeas : ∀ k, NullMeasurableSet (B k) ν := fun k => (hBclosed k).measurableSet.nullMeasurableSet
  have htend : Tendsto (fun k => ν (B k)) atTop (𝓝 (ν (⋂ k, B k))) :=
    tendsto_measure_iInter_atTop hmeas hBanti ⟨0, measure_ne_top _ _⟩
  have hle : ν (⋂ k, B k) ≤ ν (f ⁻¹' F) := measure_mono hinter
  refine le_trans (ge_of_tendsto htend ?_) hle
  exact Eventually.of_forall hstep

/-- **The extended continuous mapping theorem, local uniform form.**  If the
laws `νs n` converge weakly to `ν` on the metric space `E` and the Borel
functions `fs n` converge to `f` uniformly on small balls and beyond a
threshold, then the image laws converge weakly on the line. -/
theorem tendsto_integral_comp_of_locally_uniform [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : BoundedContinuousFunction E ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → ℝ) (fs : ℕ → E → ℝ)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hlu : ∀ (x : E) {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y : E, dist y x < δ → |fs n y - f x| ≤ ε)
    (G : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ x, G (fs n x) ∂(νs n)) atTop (𝓝 (∫ x, G (f x) ∂ν)) := by
  classical
  let μ : ProbabilityMeasure ℝ := ⟨ν.map f, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(νs n).map (fs n), Measure.isProbabilityMeasure_map (hfs n).aemeasurable⟩
  have hcoe : ∀ (n : ℕ) (s : Set ℝ), MeasurableSet s →
      (μs n : Measure ℝ) s = νs n (fs n ⁻¹' s) := by
    intro n s hs
    exact Measure.map_apply (hfs n) hs
  have hcoe' : ∀ s : Set ℝ, MeasurableSet s → (μ : Measure ℝ) s = ν (f ⁻¹' s) := by
    intro s hs
    exact Measure.map_apply hf hs
  have hopen : ∀ U : Set ℝ, IsOpen U →
      (μ : Measure ℝ) U ≤ liminf (fun n => (μs n : Measure ℝ) U) atTop := by
    intro U hU
    refine le_measure_liminf_of_limsup_measure_compl_le hU.measurableSet ?_
    have hkey := limsup_measure_preimage_le ν νs hlim f fs hlu (isClosed_compl_iff.mpr hU)
    have hc : ∀ n, (μs n : Measure ℝ) Uᶜ = νs n (fs n ⁻¹' Uᶜ) :=
      fun n => hcoe n Uᶜ hU.measurableSet.compl
    simp only [hc]
    exact hkey.trans_eq (hcoe' Uᶜ hU.measurableSet.compl).symm
  have hweak : Tendsto μs atTop (𝓝 μ) := tendsto_of_forall_isOpen_le_liminf' hopen
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak G
  have hL : ∀ n : ℕ, (∫ t, G t ∂((μs n : Measure ℝ))) = ∫ x, G (fs n x) ∂(νs n) := by
    intro n
    exact integral_map (hfs n).aemeasurable G.continuous.measurable.aestronglyMeasurable
  have hR : (∫ t, G t ∂((μ : Measure ℝ))) = ∫ x, G (f x) ∂ν :=
    integral_map hf.aemeasurable G.continuous.measurable.aestronglyMeasurable
  simpa only [hL, hR] using hint

/-- **The extended continuous mapping theorem** (van der Vaart, Theorem 18.11;
Billingsley, Theorem 5.5).  If `νs n → ν` weakly on the metric space `E` and the
Borel functions `fs n, f : E → ℝ` satisfy `fs n (z n) → f x` for every sequence
`z n → x`, then the image laws converge weakly on the line. -/
theorem extended_continuous_mapping [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (νs : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (νs n)]
    (hlim : ∀ G : BoundedContinuousFunction E ℝ,
      Tendsto (fun n => ∫ x, G x ∂(νs n)) atTop (𝓝 (∫ x, G x ∂ν)))
    (f : E → ℝ) (fs : ℕ → E → ℝ)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hseq : ∀ (x : E) (z : ℕ → E), Tendsto z atTop (𝓝 x) →
      Tendsto (fun n => fs n (z n)) atTop (𝓝 (f x)))
    (G : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ x, G (fs n x) ∂(νs n)) atTop (𝓝 (∫ x, G (f x) ∂ν)) :=
  tendsto_integral_comp_of_locally_uniform ν νs hlim f fs hfs hf
    (fun x _ hε => locallyUniform_of_seq fs f hseq x hε) G

/-- **Uniformly Lipschitz functions converging pointwise converge locally
uniformly in the sense the extended theorem consumes**, with a radius that does
not depend on the point.  This is the form in which the hypothesis is
discharged for optimal-stopping values, which are `1`-Lipschitz in the reward
for the supremum norm. -/
theorem locallyUniform_of_lipschitz (fs : ℕ → E → ℝ) (f : E → ℝ)
    (hLip : ∀ (n : ℕ) (y x : E), |fs n y - fs n x| ≤ dist y x)
    (hpt : ∀ x : E, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : E, dist y x < δ →
      |fs n y - f x| ≤ ε := by
  refine ⟨ε / 2, by linarith, ?_⟩
  have hx := hpt x
  rw [Metric.tendsto_atTop] at hx
  obtain ⟨N, hN⟩ := hx (ε / 2) (by linarith)
  refine ⟨N, fun n hn y hy => ?_⟩
  have h1 : |fs n y - fs n x| ≤ dist y x := hLip n y x
  have h2 : |fs n x - f x| < ε / 2 := by simpa [Real.dist_eq] using hN n hn
  calc |fs n y - f x| ≤ |fs n y - fs n x| + |fs n x - f x| := by
        simpa using abs_sub_le (fs n y) (fs n x) (f x)
    _ ≤ ε := by linarith

/-- **The same, for a fixed Lipschitz constant `K`.**  Used when `fs n` is a sum of finitely
many `1`-Lipschitz pieces, so the combined map is `K`-Lipschitz for `K` the number of pieces. -/
theorem locallyUniform_of_lipschitz_const {K : ℝ} (hK : 0 < K) (fs : ℕ → E → ℝ) (f : E → ℝ)
    (hLip : ∀ (n : ℕ) (y x : E), |fs n y - fs n x| ≤ K * dist y x)
    (hpt : ∀ x : E, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : E, dist y x < δ →
      |fs n y - f x| ≤ ε := by
  refine ⟨ε / (2 * K), by positivity, ?_⟩
  have hx := hpt x
  rw [Metric.tendsto_atTop] at hx
  obtain ⟨N, hN⟩ := hx (ε / 2) (by linarith)
  refine ⟨N, fun n hn y hy => ?_⟩
  have h1 : |fs n y - fs n x| ≤ K * dist y x := hLip n y x
  have h2 : |fs n x - f x| < ε / 2 := by simpa [Real.dist_eq] using hN n hn
  have h3 : K * dist y x < ε / 2 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * K)).mp hy
    nlinarith
  calc |fs n y - f x| ≤ |fs n y - fs n x| + |fs n x - f x| := by
        simpa using abs_sub_le (fs n y) (fs n x) (f x)
    _ ≤ ε := by linarith

end LatticeProb.ExtendedMapping

end
