/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8LimF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, third conjunct: from a whole-plane GFF to a GFF plus a bounded function

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:897–898): "If `h` is a whole-plane
GFF and `f` is a bounded continuous function, then the metrics `D_{h+f}^ε` and `D_h^ε` are
bi-Lipschitz equivalent, with Lipschitz constants `e^{±ξ‖f‖_∞}`. Hence the case of a whole-plane
GFF implies the case of a whole-plane GFF plus a continuous function."

* `map_smallSet_le_of_le_mul`: a random bound `A ≤ K·B` gives the law domination of
  `ae_posOffDiag_of_dominated` up to `P(K > M)`;
* `ae_posOffDiag_of_le_mul`: positivity of limits transfers along `A ≤ K·B` with one a.s. finite
  measurable `K` (`ε`-independent random Lipschitz constant, T:887–888, T:897–898);
* `lem2_8_pos_of_gff`: positivity off the diagonal of subsequential limits for `h = g + f`
  from the whole-plane GFF case;
* `lem2_8_lim_of_gff`: the third conjunct of `Lem2_8` for `h = g + f` from the GFF case
  (tightness + positivity of limits for whole-plane GFFs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- **Random domination ⇒ law domination**: if a.s. `0 ≤ K` and `A ≤ K·B`, then
`law(B)(small δ η) ≤ law(A)(small δ (Mη)) + P(K > M)`. -/
theorem map_smallSet_le_of_le_mul {X : Type*} [MetricSpace X] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A B : Ω → C(X × X, ℝ)} (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    {K : Ω → ℝ} (hK : ∀ᵐ ω ∂P, 0 ≤ K ω ∧ ∀ p, A ω p ≤ K ω * B ω p) {M : ℝ} (hM : 0 < M)
    (δ : ℝ) {η : ℝ} (hη : 0 < η) :
    (P.map B) (smallSet δ η) ≤ (P.map A) (smallSet δ (M * η)) + P {ω | M < K ω} := by
  rw [Measure.map_apply_of_aemeasurable hB (isOpen_smallSet δ η).measurableSet,
    Measure.map_apply_of_aemeasurable hA (isOpen_smallSet δ (M * η)).measurableSet]
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hK] with ω hKω hω
  obtain ⟨hK0, hKle⟩ := hKω
  obtain ⟨x, y, hxy, hlt⟩ := hω
  by_cases hKM : M < K ω
  · exact Or.inr hKM
  · refine Or.inl ⟨x, y, hxy, ?_⟩
    have h1 := hKle (x, y)
    rcases le_or_gt 0 (B ω (x, y)) with hb | hb
    · calc A ω (x, y) ≤ K ω * B ω (x, y) := h1
        _ ≤ M * B ω (x, y) := mul_le_mul_of_nonneg_right (not_lt.1 hKM) hb
        _ < M * η := mul_lt_mul_of_pos_left hlt hM
    · have h2 : K ω * B ω (x, y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0 hb.le
      have h3 : 0 < M * η := mul_pos hM hη
      linarith

/-- **Positivity of limits along `A ≤ K·B`** with one a.s. finite measurable `K`. -/
theorem ae_posOffDiag_of_le_mul {X : Type*} [MetricSpace X] [CompactSpace X] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : ℕ → Ω → C(X × X, ℝ)} (hA : ∀ n, AEMeasurable (A n) P)
    (hB : ∀ n, AEMeasurable (B n) P) {K : Ω → ℝ} (hKm : Measurable K)
    (hK : ∀ n, ∀ᵐ ω ∂P, 0 ≤ K ω ∧ ∀ p, A n ω p ≤ K ω * B n ω p)
    {ν α : ℕ → ProbabilityMeasure C(X × X, ℝ)} {μ : ProbabilityMeasure C(X × X, ℝ)}
    (hνd : ∀ n, (ν n : Measure C(X × X, ℝ)) = P.map (B n))
    (hαd : ∀ n, (α n : Measure C(X × X, ℝ)) = P.map (A n))
    (hν : Tendsto ν atTop (𝓝 μ)) (hαc : IsCompact (closure (range α)))
    (hαlim : ∀ (ψ : ℕ → ℕ) (lam : ProbabilityMeasure C(X × X, ℝ)), StrictMono ψ →
      Tendsto (α ∘ ψ) atTop (𝓝 lam) → ∀ᵐ d ∂(lam : Measure C(X × X, ℝ)), IsPosOffDiag d) :
    ∀ᵐ d ∂(μ : Measure C(X × X, ℝ)), IsPosOffDiag d := by
  refine ae_posOffDiag_of_dominated hν hαc hαlim fun δ _ ζ hζ => ?_
  have hT : Tendsto (fun j : ℕ => P {ω | (j : ℝ) < K ω}) atTop
      (𝓝 (P (⋂ j : ℕ, {ω | (j : ℝ) < K ω}))) := by
    refine tendsto_measure_iInter_atTop
      (fun j => (measurableSet_lt measurable_const hKm).nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro i j hij ω (hω : (j : ℝ) < K ω)
    exact lt_of_le_of_lt (by exact_mod_cast hij) hω
  have he : (⋂ j : ℕ, {ω | (j : ℝ) < K ω}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact exists_nat_ge (K ω)
  rw [he, measure_empty] at hT
  obtain ⟨j, hj⟩ := (hT.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal ζ by
    simpa using hζ))).exists
  refine ⟨(j : ℝ) + 1, by positivity, fun η hη => Eventually.of_forall fun n => ?_⟩
  rw [hνd, hαd]
  refine (map_smallSet_le_of_le_mul (M := (j : ℝ) + 1) (hA n) (hB n) (hK n) (by positivity)
    δ hη).trans ?_
  exact add_le_add le_rfl ((measure_mono fun ω (hω : (j : ℝ) + 1 < K ω) =>
    (show (j : ℝ) < K ω by linarith)).trans hj.le)

/-- **DFGPS T:897–898, positivity part**: positivity off the diagonal of subsequential limits
for a whole-plane GFF plus a bounded continuous function, from the whole-plane GFF case. -/
theorem lem2_8_pos_of_gff {ξ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P)
    (hG : ∀ g : Ω → DistC, IsWholePlaneGFF g P → IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => lfppSqC ξ ε (g ω) (closedSq a s)})
    (hGpos : ∀ g : Ω → DistC, IsWholePlaneGFF g P → ∀ (εn : ℕ → ℝ)
      (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
      (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ)),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
        (ν n : Measure _) = P.map fun ω => lfppSqC ξ (εn n) (g ω) (closedSq a s)) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsPosOffDiag d)
    (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppSqC ξ (εn n) (h ω) (closedSq a s))
    (hε0 : Tendsto εn atTop (𝓝 0)) (hlim : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsPosOffDiag d := by
  obtain ⟨hhm, f, hf, hfb, hg⟩ := hh
  set S := closedSq a s
  set g : Ω → DistC := fun ω => h ω - ofCont (f ω)
  have : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  have hgm : Measurable g := hg.measurable
  have hhc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω)) := fun ε hε =>
    (IsGFFPlusBddCont.ae_tendstoLocallyUniformly_heatMollify ⟨hhm, f, hf, hfb, hg⟩ ε
      hε.1.ne').mono fun ω hω => hω.2
  have hgc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => g ω (heatTrunc (ε ^ 2 / 2) z n))
        (heatMollify ε (g ω)) atTop ∧ Continuous (heatMollify ε (g ω)) := fun ε hε =>
    hg.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'
  set c : ℝ → ℝ := fun ε => (aEpsDF ξ ε)⁻¹
  have hc0 : ∀ ε, 0 ≤ c ε := fun ε => inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
  set A : ℕ → Ω → C(S × S, ℝ) := fun n ω => lfppSqC ξ (εn n) (g ω) S
  set B : ℕ → Ω → C(S × S, ℝ) := fun n ω => lfppSqC ξ (εn n) (h ω) S
  have hA : ∀ n, AEMeasurable (A n) P := fun n =>
    aemeasurable_lfppSqC hgm ((hgc _ (hν n).1).mono fun ω hω => hω.2) hs
  have hB : ∀ n, AEMeasurable (B n) P := fun n => aemeasurable_lfppSqC hhm (hhc _ (hν n).1) hs
  let α : ℕ → ProbabilityMeasure C(S × S, ℝ) := fun n =>
    ⟨P.map (A n), inferInstance⟩
  have hαc : IsCompact (closure (range α)) := by
    refine isCompact_closure_of_isTightMeasureSet ((hG g hg).subset ?_)
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨εn n, (hν n).1, rfl⟩
  refine ae_posOffDiag_of_le_mul hA hB
    (Real.measurable_exp.comp ((measurable_supAbs hf).const_mul |ξ|)) ?_
    (fun n => (hν n).2) (fun n => rfl) hlim hαc
    (fun ψ lam hψ hl => hGpos g hg (εn ∘ ψ) (α ∘ ψ) lam (fun k => ⟨(hν (ψ k)).1, rfl⟩)
      (hε0.comp hψ.tendsto_atTop) hl)
  intro n
  have hε := (hν n).1
  filter_upwards [hgc _ hε, hhc _ hε] with ω hωg hωh
  refine ⟨(Real.exp_pos _).le, fun p => ?_⟩
  obtain ⟨M, hM⟩ := hfb ω
  have hMs := abs_le_supAbs hM
  have hdiff : ∀ x ∈ S, |heatMollify (εn n) (g ω) x - heatMollify (εn n) (h ω) x| ≤
      supAbs (f ω) := by
    intro x _
    have hadd := heatMollify_add_ofCont' (g ω) (f ω) M hM hε.1 x
      ((tendstoLocallyUniformlyOn_univ.2 hωg.1).tendsto_at (mem_univ x))
    have e : g ω + ofCont (f ω) = h ω := sub_add_cancel _ _
    rw [e] at hadd
    rw [hadd, abs_sub_comm, add_sub_cancel_left]
    exact abs_heatMollify_ofCont_le (f ω) hMs hε.1.ne' x
  obtain ⟨Bd, -, hBd⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hωh (convex_closedSq a s)
    (closedSq_subset_closedBall a hs.le)
  have hle := lfppDOn_toReal_le_of_abs_sub_le (ξ := ξ) hdiff
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hBd p.1 p.1.2 p.2 p.2.2))
  change lfppSqC ξ (εn n) (g ω) S p ≤ _ * lfppSqC ξ (εn n) (h ω) S p
  rw [lfppSqC_apply_of_continuous hωh hs p, lfppSqC_apply_of_continuous hωg.2 hs p]
  calc c (εn n) * (lfppDOn ξ (heatMollify (εn n) (g ω)) S p.1 p.2).toReal
      ≤ c (εn n) * (Real.exp (|ξ| * supAbs (f ω)) *
          (lfppDOn ξ (heatMollify (εn n) (h ω)) S p.1 p.2).toReal) :=
        mul_le_mul_of_nonneg_left hle (hc0 _)
    _ = _ := by simp only [Function.comp_apply, c, S]; ring

/-- **Third conjunct of DFGPS Lemma 2.8 from the whole-plane GFF case** (T:875, T:887–889,
T:897–898): tightness and positivity of limits for whole-plane GFFs give the length-metric
conclusion for a GFF plus a bounded continuous function. -/
theorem lem2_8_lim_of_gff {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P)
    (hG : ∀ g : Ω → DistC, IsWholePlaneGFF g P → IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)})
    (hGpos : ∀ g : Ω → DistC, IsWholePlaneGFF g P → ∀ (εn : ℕ → ℝ)
      (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
      (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ)),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
        (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (g ω) (closedSq a s)) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsPosOffDiag d) :
    ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
      (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ)),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
        (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closedSq a s)) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsSqLengthMetric d :=
  fun εn ν μ hν hε0 hlim => lem2_8_lim_of_pos hs hh εn ν μ hν hlim
    (lem2_8_pos_of_gff hs hh hG hGpos εn ν μ hν hε0 hlim)

end LQGMetric.DFGPS
