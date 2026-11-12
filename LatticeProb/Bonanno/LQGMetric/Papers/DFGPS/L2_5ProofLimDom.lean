/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLimDom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Positivity of limits under domination with an error-dependent comparison family

Variant of `ae_posOffDiag_of_dominated` (`L2_8LimPos.lean`) in which the comparison laws `α` may
depend on the error `ζ`: this is the form needed in DFGPS Lemma 2.5 (arXiv:1905.00380,
`lqg-metric-estimates-final.tex`, T:997–1003), where the comparison square `S_{Rr}(0)` depends
on the probability `p` of the agreement event (2.10)/(eqn-square-metric-agree) through
`R = R(p)` of Lemma 2.10. The proof is that of `ae_posOffDiag_of_dominated`, with the
comparison limit chosen after `ζ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

variable {X : Type*} [MetricSpace X]

/-- **Positivity of limits under domination, `ζ`-dependent comparison laws.** -/
theorem ae_posOffDiag_of_dominated_family [CompactSpace X]
    {ν : ℕ → ProbabilityMeasure C(X × X, ℝ)} {μ : ProbabilityMeasure C(X × X, ℝ)}
    (hν : Tendsto ν atTop (𝓝 μ))
    (hfam : ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ α : ℕ → ProbabilityMeasure C(X × X, ℝ),
      IsCompact (closure (range α)) ∧
      (∀ (ψ : ℕ → ℕ) (lam : ProbabilityMeasure C(X × X, ℝ)), StrictMono ψ →
        Tendsto (α ∘ ψ) atTop (𝓝 lam) → ∀ᵐ d ∂(lam : Measure C(X × X, ℝ)), IsPosOffDiag d) ∧
      ∀ δ > 0, ∀ η > 0, ∀ᶠ n in atTop,
        (ν n : Measure C(X × X, ℝ)) (smallSet δ η) ≤
          (α n : Measure C(X × X, ℝ)) (smallSet δ η) + ENNReal.ofReal ζ) :
    ∀ᵐ d ∂(μ : Measure C(X × X, ℝ)), IsPosOffDiag d := by
  set N : ℝ → Set C(X × X, ℝ) := fun δ => {d | ∃ x y : X, δ ≤ dist x y ∧ d (x, y) ≤ 0}
  have hN : ∀ δ > 0, (μ : Measure C(X × X, ℝ)) (N δ) = 0 := by
    intro δ hδ
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ζ' hζ' _ => ?_) zero_le
    set ζ : ℝ := min ((ζ' : ℝ) / 2) (1 / 2) with hζdef
    have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
    have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨α, hαc, hαlim, hdom⟩ := hfam ζ ⟨hζ0, hζ1⟩
    obtain ⟨lam, -, ψ, hψ, hlimα⟩ :=
      hαc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
    have hpos := hαlim ψ lam hψ hlimα
    have hνψ : Tendsto (ν ∘ ψ) atTop (𝓝 μ) := hν.comp hψ.tendsto_atTop
    have key : ∀ η > 0, (μ : Measure C(X × X, ℝ)) (smallSet δ η) ≤
        (lam : Measure C(X × X, ℝ)) (smallSetC δ η) + ENNReal.ofReal ζ := by
      intro η hη
      have h1 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hνψ (isOpen_smallSet δ η)
      have h2 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlimα
        (isClosed_smallSetC δ η)
      refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
      have hlt : (lam : Measure C(X × X, ℝ)) (smallSetC δ η) <
          (lam : Measure C(X × X, ℝ)) (smallSetC δ η) + ε' :=
        ENNReal.lt_add_right (measure_ne_top _ _) (by simpa using hε'.ne')
      have hev := eventually_lt_of_limsup_lt (h2.trans_lt hlt)
      have hev2 := hψ.tendsto_atTop.eventually (hdom δ hδ η hη)
      refine h1.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
      filter_upwards [hev, hev2] with k hk1 hk2
      calc (ν (ψ k) : Measure C(X × X, ℝ)) (smallSet δ η)
          ≤ (α (ψ k) : Measure C(X × X, ℝ)) (smallSet δ η) + ENNReal.ofReal ζ := hk2
        _ ≤ (α (ψ k) : Measure C(X × X, ℝ)) (smallSetC δ η) + ENNReal.ofReal ζ := by
            gcongr; exact smallSet_subset_smallSetC _ _
        _ ≤ (lam : Measure C(X × X, ℝ)) (smallSetC δ η) + ε' + ENNReal.ofReal ζ := by
            gcongr; exact hk1.le
        _ = (lam : Measure C(X × X, ℝ)) (smallSetC δ η) + ENNReal.ofReal ζ + ε' := by
            ring
    have hC : Tendsto (fun j : ℕ => (lam : Measure C(X × X, ℝ))
        (smallSetC δ (1 / ((j : ℝ) + 1)))) atTop
        (𝓝 ((lam : Measure C(X × X, ℝ)) (⋂ j : ℕ, smallSetC δ (1 / ((j : ℝ) + 1))))) := by
      refine tendsto_measure_iInter_atTop
        (fun j => (isClosed_smallSetC δ _).measurableSet.nullMeasurableSet) ?_
        ⟨0, measure_ne_top _ _⟩
      intro i j hij d ⟨x, y, hxy, hle⟩
      refine ⟨x, y, hxy, hle.trans ?_⟩
      gcongr
    have h0 : (lam : Measure C(X × X, ℝ)) (⋂ j : ℕ, smallSetC δ (1 / ((j : ℝ) + 1))) = 0 := by
      refine measure_mono_null (t := {d | ¬ IsPosOffDiag d}) (fun d hd hp => ?_) (ae_iff.1 hpos)
      obtain ⟨m, hm, hmd⟩ := exists_not_mem_smallSetC hp hδ
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hm
      exact hmd _ hj (mem_iInter.1 hd j)
    rw [h0] at hC
    obtain ⟨j, hj⟩ := (hC.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < (ζ' : ℝ≥0∞) / 2 by
      simpa using hζ'.ne'))).exists
    have hη : (0 : ℝ) < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hsub : N δ ⊆ smallSet δ (1 / ((j : ℝ) + 1)) :=
      fun d ⟨x, y, hxy, hle⟩ => ⟨x, y, hxy, hle.trans_lt hη⟩
    calc (μ : Measure C(X × X, ℝ)) (N δ)
        ≤ (μ : Measure C(X × X, ℝ)) (smallSet δ (1 / ((j : ℝ) + 1))) := measure_mono hsub
      _ ≤ (lam : Measure C(X × X, ℝ)) (smallSetC δ (1 / ((j : ℝ) + 1))) +
            ENNReal.ofReal ζ := key _ hη
      _ ≤ (ζ' : ℝ≥0∞) / 2 + (ζ' : ℝ≥0∞) / 2 := by
          gcongr
          calc ENNReal.ofReal ζ ≤ ENNReal.ofReal ((ζ' : ℝ) / 2) :=
                ENNReal.ofReal_le_ofReal (min_le_left _ _)
            _ = (ζ' : ℝ≥0∞) / 2 := by
                rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal]; simp
      _ = 0 + ζ' := by rw [ENNReal.add_halves, zero_add]
  refine ae_iff.2 (measure_mono_null (fun d hd => ?_)
    (measure_iUnion_null fun k : ℕ => hN (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat))
  simp only [IsPosOffDiag, not_forall, not_lt, mem_ofPred_eq] at hd
  obtain ⟨x, y, hxy, hle⟩ := hd
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hxy)
  exact mem_iUnion.2 ⟨k, x, y, hk.le, hle⟩

end LQGMetric.DFGPS
