/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofLim at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofTightMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Lim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9, third conjunct: limits are length metrics, given positivity (T:926–936)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:926–936: a subsequential limit
`D̃` of `𝔞_ε⁻¹ D_h^ε(·,·;W̄)` is a metric (positivity off the diagonal, T:930–934), hence induces
the Euclidean topology on the compact `W̄`, and "By Lemma 2.7, `D̃` is a length metric". As for
squares (`L2_8Lim.lean`, BBI Lemma 2.4.10 / Theorem 2.4.16(2)): the approximating metrics have
`ε`-midpoints in `W̄` (`lfppDOn_approxMid_of_fin`, cutting near-optimal paths at half length),
so limit laws are supported on the closed set `lenPmetSet W̄` (portmanteau), and a member of it
positive off the diagonal is a length metric.

* `lem2_9_lim_of_pos`: the third conjunct of `Lem2_9` given a.s. positivity off the diagonal of
  the limit (the input T:930–934).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- `ε`-midpoints of `D_φ(·,·;S)` for any `S` on which the distance is finite and vanishes on the
diagonal (as `lfppDOn_approxMid`, without convexity) -/
theorem lfppDOn_approxMid_of_fin {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ}
    (hself : ∀ z ∈ S, lfppDOn ξ φ S z z = 0) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S)
    (hfin : lfppDOn ξ φ S x y ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ S, (lfppDOn ξ φ S x z).toReal ≤ (lfppDOn ξ φ S x y).toReal / 2 + ε ∧
      (lfppDOn ξ φ S z y).toReal ≤ (lfppDOn ξ φ S x y).toReal / 2 + ε := by
  have hlt : lfppDOn ξ φ S x y < lfppDOn ξ φ S x y + ENNReal.ofReal (2 * ε) :=
    ENNReal.lt_add_right hfin (by simp; positivity)
  obtain ⟨Q, hQ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, hP, hPS⟩ := Q
  simp only at hQ
  have hLfin : lfppLen ξ φ P ≠ ⊤ := ne_top_of_lt hQ
  set L := (lfppLen ξ φ P).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hLlt : L < (lfppDOn ξ φ S x y).toReal + 2 * ε := by
    have := (ENNReal.toReal_lt_toReal hLfin
      (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩)).2 hQ
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨t, ht, h1, h2⟩ := exists_half_lfppLen hφ hP hLfin
  have hzS : P t ∈ S := hPS t ht
  have b1 : lfppDOn ξ φ S x (P t) ≤ ENNReal.ofReal (L / 2) := by
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0, hP.source, hself x hx]; exact zero_le
    · have hpp := isPiecewiseC1Path_subPath hP le_rfl h0 ht.2
      rw [hP.source] at hpp
      refine (lfppDOn_le hpp fun u hu => hPS _ ⟨by nlinarith [hu.1, hu.2, ht.1, ht.2],
        by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩).trans (le_of_eq ?_)
      rw [lfppLen_subPath P h0, h1]
  have b2 : lfppDOn ξ φ S (P t) y ≤ ENNReal.ofReal (L / 2) := by
    rcases ht.2.eq_or_lt with h0 | h0
    · rw [h0, hP.target, hself y hy]; exact zero_le
    · have hpp := isPiecewiseC1Path_subPath hP ht.1 h0 le_rfl
      rw [hP.target] at hpp
      refine (lfppDOn_le hpp fun u hu => hPS _ ⟨by nlinarith [hu.1, hu.2, ht.1, ht.2],
        by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩).trans (le_of_eq ?_)
      rw [lfppLen_subPath P h0, h2]
  refine ⟨P t, hzS, ?_, ?_⟩
  · exact (ENNReal.toReal_le_of_le_ofReal (by positivity) b1).trans (by linarith)
  · exact (ENNReal.toReal_le_of_le_ofReal (by positivity) b2).trans (by linarith)

/-- the rescaled internal LFPP metric on a connected finite union of squares lies in
`lenPmetSet` (continuous `h*_ε`) -/
theorem lfppSqC_union_mem_lenPmetSet {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (𝒮 : Finset (Set ℂ)) (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s)
    (hK : IsPreconnected (⋃ S ∈ 𝒮, S)) :
    lfppSqC ξ ε g (⋃ S ∈ 𝒮, S) ∈ lenPmetSet (⋃ S ∈ 𝒮, S) := by
  set K := ⋃ S ∈ 𝒮, S
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_biUnion_closedSq 𝒮 h𝒮)
  set c := (aEpsDF ξ ε)⁻¹ with hcdef
  have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
  have hap : ∀ p : K × K, lfppSqC ξ ε g K p = c * (lfppDOn ξ (heatMollify ε g) K p.1 p.2).toReal :=
    fun p => toCMap_apply_of_continuous (continuous_lfppDOn_union_toReal hc 𝒮 h𝒮 hK _) p
  have hfin := lfppDOn_union_ne_top (ξ := ξ) hc 𝒮 h𝒮 hK
  obtain ⟨δ, hδ, B, hB0, hB⟩ := exists_lfppDOn_union_le (ξ := ξ) hc 𝒮 h𝒮
  have hself : ∀ z ∈ K, lfppDOn ξ (heatMollify ε g) K z z = 0 := fun z hz => by
    have := hB z hz z hz (by simpa using hδ)
    simpa using this
  refine ⟨⟨⟨fun x => ?_, fun x y z => ?_⟩, fun x y => ?_⟩,
    mem_midSet_of_approx _ fun x y ε' hε' => ?_⟩
  · rw [hap]; dsimp only; rw [hself x x.2, ENNReal.toReal_zero, mul_zero]
  · simp only [hap]
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [← ENNReal.toReal_add (hfin x x.2 y y.2) (hfin y y.2 z z.2)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x x.2 y y.2, hfin y y.2 z z.2⟩)
      (lfppDOn_triangle _ _ _)
  · simp only [hap]; rw [lfppDOn_comm]
  · simp only [hap]
    rcases hc0.eq_or_lt with h0 | h0
    · refine ⟨x, ?_, ?_⟩ <;> rw [← h0] <;> simp <;> linarith
    · obtain ⟨z, hz, h1, h2⟩ := lfppDOn_approxMid_of_fin (ξ := ξ) hc hself x.2 y.2
        (hfin x x.2 y y.2) (div_pos hε' h0)
      have key : c * ((lfppDOn ξ (heatMollify ε g) K x y).toReal / 2 + ε' / c) =
          c * (lfppDOn ξ (heatMollify ε g) K x y).toReal / 2 + ε' := by
        field_simp
      refine ⟨⟨z, hz⟩, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left h1 hc0).trans key.le
      · exact (mul_le_mul_of_nonneg_left h2 hc0).trans key.le

theorem lem2_9_lim_of_pos_aux {γ : ℝ} {K : Set ℂ} (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) (hKe : K = ⋃ S ∈ 𝒮, S)
    (hKc : IsConnected K) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(K × K, ℝ)) (μ : ProbabilityMeasure C(K × K, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) K)
    (hlim : Tendsto ν atTop (𝓝 μ))
    (hpos : ∀ᵐ d ∂(μ : Measure C(K × K, ℝ)), ∀ x y, x ≠ y → 0 < d (x, y)) :
    ∀ᵐ d ∂(μ : Measure C(K × K, ℝ)), IsSqLengthMetric d := by
  subst hKe
  haveI : CompactSpace ↥(⋃ S ∈ 𝒮, S) :=
    isCompact_iff_compactSpace.1 (isCompact_biUnion_closedSq 𝒮 h𝒮)
  have hF := isClosed_lenPmetSet (⋃ S ∈ 𝒮, S)
  have hνF : ∀ n, (ν n : Measure _) (lenPmetSet (⋃ S ∈ 𝒮, S)) = 1 := by
    intro n
    obtain ⟨hεn, hνn⟩ := hν n
    have hc := hh.ae_tendstoLocallyUniformly_heatMollify (εn n) hεn.1.ne'
    rw [hνn, Measure.map_apply_of_aemeasurable (aemeasurable_lfppSqC_union hh.1
      (hc.mono fun ω hω => hω.2) 𝒮 h𝒮 hKc.isPreconnected) hF.measurableSet]
    have hae : ∀ᵐ ω ∂P, ω ∈ (fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (⋃ S ∈ 𝒮, S)) ⁻¹'
        lenPmetSet (⋃ S ∈ 𝒮, S) :=
      hc.mono fun ω hω => lfppSqC_union_mem_lenPmetSet hω.2 𝒮 h𝒮 hKc.isPreconnected
    exact (measure_congr (eventuallyEqSet_univ.2 hae)).trans measure_univ
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simp only [hνF, limsup_const] at hle
  have h1 : (μ : Measure C((⋃ S ∈ 𝒮, S) × (⋃ S ∈ 𝒮, S), ℝ)) (lenPmetSet (⋃ S ∈ 𝒮, S)) =
      (μ : Measure C((⋃ S ∈ 𝒮, S) × (⋃ S ∈ 𝒮, S), ℝ)) univ := by
    rw [measure_univ]; exact le_antisymm prob_le_one hle
  filter_upwards [(ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).2 h1, hpos]
    with d hd hp
  exact isLengthMetric_of_mem_lenPmetSet hd hp

end LQGMetric.DFGPS
