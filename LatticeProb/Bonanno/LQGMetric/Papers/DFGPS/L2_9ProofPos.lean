/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofPos at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofLim
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimF
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Prok

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9, positivity of subsequential limits, and `lem2_9`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:927–934 show that a subsequential
limit `D̃` of `𝔞_ε⁻¹ D_h^ε(·,·;W̄)` is positive off the diagonal using square annuli
`S_1 ⊂ S_2 ⊂ W̄` and Lemma 2.8 on `S_2`. We use instead one closed square `S ⊇ W̄` and the
domination `D_h^ε(·,·;S) ≤ D_h^ε(·,·;W̄)` on `W̄` (fewer paths): the laws of the restrictions to
`W̄ × W̄` of `𝔞_ε⁻¹ D_h^ε(·,·;S)` are relatively compact with positive limits (Lemma 2.8 on `S`),
so `ae_posOffDiag_of_le_mul` (L2_8LimF) applies with the constant `1`. (Own argument; it avoids
the annulus construction, which needs care at reentrant corners of `W̄`, where no square `S_2 ⊂ W̄`
has `S_1 ∋ x` at positive distance from `∂S_2 ∖ ∂W`. Proposed DEVIATIONS entry DF-L29-POS.)

`lem2_9 : Lem2_8 → Lem2_9`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

theorem exists_closedSq_superset {K : Set ℂ} (hK : IsCompact K) :
    ∃ a : ℂ, ∃ s : ℝ, 0 < s ∧ K ⊆ closedSq a s := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨⟨-(|R| + 1), -(|R| + 1)⟩, 2 * (|R| + 1), by positivity, fun x hx => ?_⟩
  have hx' := mem_closedBall_zero_iff.1 (hR hx)
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  rw [abs_le] at h1 h2
  have := le_abs_self R
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

theorem measurableSet_isPosOffDiag {X : Type*} [MetricSpace X] [CompactSpace X] :
    MeasurableSet {d : C(X × X, ℝ) | IsPosOffDiag d} := by
  have e : {d : C(X × X, ℝ) | IsPosOffDiag d} =
      ⋂ k : ℕ, (smallSetC (1 / ((k : ℝ) + 1)) 0)ᶜ := by
    ext d
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, smallSetC, IsPosOffDiag, not_exists,
      not_and, not_le]
    constructor
    · intro hd k x y hxy
      refine hd x y fun e => ?_
      rw [e, dist_self] at hxy
      exact absurd hxy (not_le.2 (by positivity))
    · intro hd x y hxy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hxy)
      exact hd k x y hk.le
  rw [e]
  exact MeasurableSet.iInter fun k => (isClosed_smallSetC _ _).isOpen_compl.measurableSet

/-- **positivity off the diagonal of subsequential limits** on a connected finite union `K` of
closed squares (DFGPS T:927–934, via a square `S ⊇ K`) -/
theorem lem2_9_pos_aux (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ}
    (𝒮 : Finset (Set ℂ)) (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s)
    (hKe : K = ⋃ S ∈ 𝒮, S) (hKc : IsConnected K) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(K × K, ℝ)) (μ : ProbabilityMeasure C(K × K, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) K)
    (hε0 : Tendsto εn atTop (𝓝 0)) (hlim : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure C(K × K, ℝ)), IsPosOffDiag d := by
  subst hKe
  haveI : CompactSpace ↥(⋃ S ∈ 𝒮, S) :=
    isCompact_iff_compactSpace.1 (isCompact_biUnion_closedSq 𝒮 h𝒮)
  obtain ⟨a, s, hs, hKS⟩ := exists_closedSq_superset (isCompact_biUnion_closedSq 𝒮 h𝒮)
  haveI : CompactSpace (closedSq a s) := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  obtain ⟨-, hT, hL⟩ := h28 γ hγ hγ2 a s hs P h hh
  set ξ := xiGamma γ
  let incl : C(↥(⋃ S ∈ 𝒮, S) × ↥(⋃ S ∈ 𝒮, S), closedSq a s × closedSq a s) :=
    (ContinuousMap.inclusion hKS).prodMap (ContinuousMap.inclusion hKS)
  let r := ContinuousMap.compRightContinuousMap ℝ incl
  have hr : Continuous r := r.continuous
  have hcS : ∀ n, ∀ᵐ ω ∂P, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => h ω (heatTrunc (εn n ^ 2 / 2) z k)) (heatMollify (εn n) (h ω))
        atTop ∧ Continuous (heatMollify (εn n) (h ω)) := fun n =>
    hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hν n).1.1.ne'
  have hFS : ∀ n, AEMeasurable (fun ω => lfppSqC ξ (εn n) (h ω) (closedSq a s)) P := fun n =>
    aemeasurable_lfppSqC hh.1 ((hcS n).mono fun ω hω => hω.2) hs
  have hFK : ∀ n, AEMeasurable (fun ω => lfppSqC ξ (εn n) (h ω) (⋃ S ∈ 𝒮, S)) P := fun n =>
    aemeasurable_lfppSqC_union hh.1 ((hcS n).mono fun ω hω => hω.2) 𝒮 h𝒮 hKc.isPreconnected
  let β : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ) := fun n =>
    ⟨P.map fun ω => lfppSqC ξ (εn n) (h ω) (closedSq a s),
      (Measure.isProbabilityMeasure_map_iff (hFS n)).2 inferInstance⟩
  let α : ℕ → ProbabilityMeasure C(↥(⋃ S ∈ 𝒮, S) × ↥(⋃ S ∈ 𝒮, S), ℝ) := fun n => (β n).map r
  have hαd : ∀ n, (α n : Measure _) =
      P.map fun ω => r (lfppSqC ξ (εn n) (h ω) (closedSq a s)) := fun n =>
    AEMeasurable.map_map_of_aemeasurable hr.aemeasurable (hFS n)
  have hβT : IsTightMeasureSet {((μ : ProbabilityMeasure _) : Measure _) | μ ∈ range β} :=
    hT.subset (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨εn n, (hν n).1, rfl⟩)
  have hαc : IsCompact (closure (range α)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hβT ⊢
    intro e he
    obtain ⟨C, hC, hCm⟩ := hβT e he
    refine ⟨r '' C, hC.image hr, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    show ((β n : Measure _).map r) (r '' C)ᶜ ≤ e
    rw [Measure.map_apply hr.measurable (hC.image hr).isClosed.isOpen_compl.measurableSet]
    exact (measure_mono (show r ⁻¹' (r '' C)ᶜ ⊆ Cᶜ from fun d hd hdC => hd ⟨d, hdC, rfl⟩)).trans
      (hCm _ ⟨β n, ⟨n, rfl⟩, rfl⟩)
  have hαlim : ∀ (ψ : ℕ → ℕ) (lam : ProbabilityMeasure C(↥(⋃ S ∈ 𝒮, S) × ↥(⋃ S ∈ 𝒮, S), ℝ)),
      StrictMono ψ → Tendsto (α ∘ ψ) atTop (𝓝 lam) →
        ∀ᵐ d ∂(lam : Measure C(↥(⋃ S ∈ 𝒮, S) × ↥(⋃ S ∈ 𝒮, S), ℝ)), IsPosOffDiag d := by
    intro ψ lam hψ hαψ
    obtain ⟨lS, -, φ, hφ, hβφ⟩ := (isCompact_closure_of_isTightMeasureSet hβT).tendsto_subseq
      (x := β ∘ ψ) fun n => subset_closure ⟨ψ n, rfl⟩
    have hLS := hL (εn ∘ ψ ∘ φ) ((β ∘ ψ) ∘ φ) lS (fun n => ⟨(hν _).1, rfl⟩)
      ((hε0.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop) hβφ
    have h1 : Tendsto ((α ∘ ψ) ∘ φ) atTop (𝓝 (lS.map r)) :=
      ((ProbabilityMeasure.continuous_map hr).tendsto lS).comp hβφ
    have h2 : Tendsto ((α ∘ ψ) ∘ φ) atTop (𝓝 lam) := hαψ.comp hφ.tendsto_atTop
    have hlam : lam = lS.map r := tendsto_nhds_unique h2 h1
    subst hlam
    rw [ProbabilityMeasure.toMeasure_map]
    refine (ae_map_iff hr.aemeasurable measurableSet_isPosOffDiag).2 ?_
    filter_upwards [hLS] with d hd x y hxy
    obtain ⟨hm, -⟩ := hd
    set u : closedSq a s := ⟨x.1, hKS x.2⟩
    set v : closedSq a s := ⟨y.1, hKS y.2⟩
    show 0 < d (u, v)
    have hne : u ≠ v := fun e => hxy (Subtype.ext (show x.1 = y.1 from congrArg (fun z : closedSq a s => (z : ℂ)) e))
    have h0 : 0 ≤ d (u, v) := by
      have := hm.triangle u v u
      rw [hm.self_eq_zero, hm.symm v u] at this
      linarith
    exact lt_of_le_of_ne h0 fun e => hne (hm.eq_of_eq_zero u v e.symm)
  refine ae_posOffDiag_of_le_mul (A := fun n ω => r (lfppSqC ξ (εn n) (h ω) (closedSq a s)))
    (B := fun n ω => lfppSqC ξ (εn n) (h ω) (⋃ S ∈ 𝒮, S))
    (fun n => hr.measurable.comp_aemeasurable (hFS n)) hFK (K := fun _ => 1) measurable_const
    ?_ (α := α) (fun n => (hν n).2) hαd hlim hαc hαlim
  intro n
  filter_upwards [hcS n] with ω hω
  refine ⟨zero_le_one, fun p => ?_⟩
  rw [one_mul]
  have hvK : lfppSqC ξ (εn n) (h ω) (⋃ S ∈ 𝒮, S) p = (aEpsDF ξ (εn n))⁻¹ *
      (lfppDOn ξ (heatMollify (εn n) (h ω)) (⋃ S ∈ 𝒮, S) p.1 p.2).toReal :=
    toCMap_apply_of_continuous
      (continuous_lfppDOn_union_toReal hω.2 𝒮 h𝒮 hKc.isPreconnected _) p
  show lfppSqC ξ (εn n) (h ω) (closedSq a s) (incl p) ≤ _
  rw [lfppSqC_apply_of_continuous hω.2 hs, hvK]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
    (lfppDOn_union_ne_top hω.2 𝒮 h𝒮 hKc.isPreconnected _ p.1.2 _ p.2.2)
    (lfppDOn_anti_set hKS _ _)) (inv_nonneg.2 (aEpsDF_nonneg_sq _ _))

/-- **DFGPS Lemma 2.9** (`lem-lfpp-tight-dyadic`, T:903–938), from Lemma 2.8. -/
theorem lem2_9 (h28 : Lem2_8) : Lem2_9 := by
  intro γ hγ hγ2 W hW hWc Ω _ P _ h hh
  refine ⟨lem2_9_continuous hW hWc hh, lem2_9_tight h28 hγ hγ2 hW hWc P h hh, ?_⟩
  intro εn ν μ hν hε0 hlim
  obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
  have hsq := dyadic_squares_closedSq h𝒮
  have he := closure_dyadicDomain_eq h𝒮
  exact lem2_9_lim_of_pos_aux 𝒮 hsq he hWc hh εn ν μ hν hlim
    (lem2_9_pos_aux h28 hγ hγ2 𝒮 hsq he hWc hh εn ν μ hν hε0 hlim)

end LQGMetric.DFGPS
