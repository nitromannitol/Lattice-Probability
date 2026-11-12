/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLimPos at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLimDom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofTightA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 A: positivity of subsequential limits on a square `S_r(0)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:997–1003: with `R = R(p)` of
Lemma 2.10 (`C = 2`), on the event (eqn-square-metric-agree), of probability `≥ p` for small `ε`,
`D_h^ε = D_h^ε(·,·;S_{Rr}(0))` on `S_r(0)`; "any subsequential limit in law of these metrics a.s.
induces the Euclidean topology on `S_r(0)`" by Lemma 2.8 on `S_{Rr}(0)`. Here: the positivity
off the diagonal on `S_r(0)` of every subsequential limit, via `ae_posOffDiag_of_dominated_family`
(the comparison laws are those of the restrictions to `S_r(0)²` of `𝔞_ε⁻¹ D_h^ε(·,·;S_{Rr}(0))`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- the restriction `C(ℂ × ℂ, ℝ) → C(S × S, ℝ)` -/
def restrSq (S : Set ℂ) : C(C(ℂ × ℂ, ℝ), C(S × S, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, ℂ)).prodMap ⟨Subtype.val, continuous_subtype_val⟩)

theorem restrSq_apply (S : Set ℂ) (f : C(ℂ × ℂ, ℝ)) (p : S × S) :
    restrSq S f p = f (p.1.1, p.2.1) := rfl

/-- **DFGPS T:997–1003**: subsequential limits of the laws of `𝔞_ε⁻¹ D_h^ε` are a.s. positive
off the diagonal on `S_r(0)`. -/
theorem lem2_5_pos_sq (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ))
    (μ : ProbabilityMeasure C(ℂ × ℂ, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppC (xiGamma γ) (εn n) (h ω))
    (hε0 : Tendsto εn atTop (𝓝 0)) (hlim : Tendsto ν atTop (𝓝 μ)) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), ∀ x ∈ sqC r 0, ∀ y ∈ sqC r 0, x ≠ y → 0 < d (x, y) := by
  set S := sqC r 0 with hSdef
  have : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_sqC hr.le)
  set ξ := xiGamma γ
  set ρ := restrSq S
  have hρ : Continuous ρ := ρ.continuous
  have hcS : ∀ n, ∀ᵐ ω ∂P, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => h ω (heatTrunc (εn n ^ 2 / 2) z k)) (heatMollify (εn n) (h ω))
        atTop ∧ Continuous (heatMollify (εn n) (h ω)) := fun n =>
    hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hν n).1.1.ne'
  have hFC : ∀ n, AEMeasurable (fun ω => lfppC ξ (εn n) (h ω)) P := fun n =>
    aemeasurable_lfppC hh (hν n).1.1.ne'
  have hεn' : Tendsto εn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun n => (hν n).1.1⟩
  have hmain : ∀ᵐ d ∂((μ.map ρ : ProbabilityMeasure C(S × S, ℝ)) :
      Measure C(S × S, ℝ)), IsPosOffDiag d := by
    refine ae_posOffDiag_of_dominated_family (ν := fun n => (ν n).map ρ)
      (((ProbabilityMeasure.continuous_map hρ).tendsto μ).comp hlim) ?_
    intro ζ hζ
    obtain ⟨R, hR1, hRp⟩ := lem2_10 h28 γ hγ hγ2 P h hh (1 - ζ / 2)
      ⟨by linarith [hζ.2], by linarith [hζ.1]⟩ 2 two_pos
    have hRr : 0 < R * r := mul_pos (by linarith) hr
    set a' : ℂ := 0 - ((R * r / 2 : ℝ) : ℂ) * (1 + Complex.I)
    set T := closedSq a' (R * r)
    have hTe : T = sqC (R * r) 0 := rfl
    have : CompactSpace T := isCompact_iff_compactSpace.1 (isCompact_closedSq a' hRr.le)
    have hST : S ⊆ T := sqC_mono (le_mul_of_one_le_left hr.le hR1.le)
    obtain ⟨-, hT, hL⟩ := h28 γ hγ hγ2 a' (R * r) hRr P h hh
    let incl : C(S × S, T × T) :=
      (ContinuousMap.inclusion hST).prodMap (ContinuousMap.inclusion hST)
    let ι := ContinuousMap.compRightContinuousMap ℝ incl
    have hι : Continuous ι := ι.continuous
    have hFS : ∀ n, AEMeasurable (fun ω => lfppSqC ξ (εn n) (h ω) T) P := fun n =>
      aemeasurable_lfppSqC hh.1 ((hcS n).mono fun ω hω => hω.2) hRr
    let β : ℕ → ProbabilityMeasure C(T × T, ℝ) := fun n =>
      ⟨P.map fun ω => lfppSqC ξ (εn n) (h ω) T,
        (Measure.isProbabilityMeasure_map_iff (hFS n)).2 inferInstance⟩
    let α : ℕ → ProbabilityMeasure C(S × S, ℝ) := fun n => (β n).map ι
    have hαd : ∀ n, (α n : Measure _) = P.map fun ω => ι (lfppSqC ξ (εn n) (h ω) T) := fun n =>
      AEMeasurable.map_map_of_aemeasurable hι.aemeasurable (hFS n)
    have hβT : IsTightMeasureSet {((μ : ProbabilityMeasure _) : Measure _) | μ ∈ range β} :=
      hT.subset (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨εn n, (hν n).1, rfl⟩)
    refine ⟨α, ?_, ?_, ?_⟩
    · refine isCompact_closure_of_isTightMeasureSet ?_
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hβT ⊢
      intro e he
      obtain ⟨C, hC, hCm⟩ := hβT e he
      refine ⟨ι '' C, hC.image hι, ?_⟩
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      show ((β n : Measure _).map ι) (ι '' C)ᶜ ≤ e
      rw [Measure.map_apply hι.measurable (hC.image hι).isClosed.isOpen_compl.measurableSet]
      exact (measure_mono (show ι ⁻¹' (ι '' C)ᶜ ⊆ Cᶜ from fun d hd hdC => hd ⟨d, hdC, rfl⟩)).trans
        (hCm _ ⟨β n, ⟨n, rfl⟩, rfl⟩)
    · intro ψ lam hψ hαψ
      obtain ⟨lS, -, φ, hφ, hβφ⟩ := (isCompact_closure_of_isTightMeasureSet hβT).tendsto_subseq
        (x := β ∘ ψ) fun n => subset_closure ⟨ψ n, rfl⟩
      have hLS := hL (εn ∘ ψ ∘ φ) ((β ∘ ψ) ∘ φ) lS (fun n => ⟨(hν _).1, rfl⟩)
        ((hε0.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop) hβφ
      have h1 : Tendsto ((α ∘ ψ) ∘ φ) atTop (𝓝 (lS.map ι)) :=
        ((ProbabilityMeasure.continuous_map hι).tendsto lS).comp hβφ
      have h2 : Tendsto ((α ∘ ψ) ∘ φ) atTop (𝓝 lam) := hαψ.comp hφ.tendsto_atTop
      have hlam : lam = lS.map ι := tendsto_nhds_unique h2 h1
      subst hlam
      rw [ProbabilityMeasure.toMeasure_map]
      refine (ae_map_iff hι.aemeasurable measurableSet_isPosOffDiag).2 ?_
      filter_upwards [hLS] with d hd x y hxy
      obtain ⟨hm, -⟩ := hd
      set u : T := ⟨x.1, hST x.2⟩
      set v : T := ⟨y.1, hST y.2⟩
      show 0 < d (u, v)
      have hne : u ≠ v := fun e => hxy (Subtype.ext
        (show x.1 = y.1 from congrArg (fun z : T => (z : ℂ)) e))
      have h0 : 0 ≤ d (u, v) := by
        have := hm.triangle u v u
        rw [hm.self_eq_zero, hm.symm v u] at this
        linarith
      exact lt_of_le_of_ne h0 fun e => hne (hm.eq_of_eq_zero u v e.symm)
    · intro δ _ η _
      have hq : ENNReal.ofReal (1 - ζ) <
          liminf (fun ε => P {ω | sqBdyEvent ξ ε 2 r R (h ω)}) (𝓝[>] 0) :=
        lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hζ.2])).2
          (by linarith [hζ.1])) (hRp r hr)
      filter_upwards [hεn'.eventually (eventually_lt_of_lt_liminf hq)] with n hn
      obtain ⟨E', hE'm, hE'⟩ := exists_measurableSet_sqBdyEvent ξ (εn n) 2 r R
      have hPE : P (h ⁻¹' E') = P {ω | sqBdyEvent ξ (εn n) 2 r R (h ω)} := by
        refine measure_congr ?_
        filter_upwards [hcS n] with ω hω
        exact propext (hE' (h ω) hω.2).symm
      have hcompl : P (h ⁻¹' E')ᶜ ≤ ENNReal.ofReal ζ := by
        rw [measure_compl (hh.1 hE'm) (measure_ne_top _ _), measure_univ, hPE]
        refine tsub_le_iff_right.2 ?_
        calc (1 : ℝ≥0∞) = ENNReal.ofReal ζ + ENNReal.ofReal (1 - ζ) := by
              rw [← ENNReal.ofReal_add hζ.1.le (by linarith [hζ.2])]; simp
          _ ≤ ENNReal.ofReal ζ + P {ω | sqBdyEvent ξ (εn n) 2 r R (h ω)} := by
              gcongr
      show ((ν n).map ρ : Measure C(S × S, ℝ)) (smallSet δ η) ≤ _
      rw [ProbabilityMeasure.toMeasure_map, (hν n).2, AEMeasurable.map_map_of_aemeasurable
        hρ.aemeasurable (hFC n),
        Measure.map_apply_of_aemeasurable (hρ.measurable.comp_aemeasurable (hFC n))
          (isOpen_smallSet δ η).measurableSet, hαd n,
        Measure.map_apply_of_aemeasurable (f := fun ω => ι (lfppSqC ξ (εn n) (h ω) T)) (hι.measurable.comp_aemeasurable (hFS n))
          (isOpen_smallSet δ η).measurableSet]
      refine (measure_mono_ae ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl hcompl))
      filter_upwards [hcS n] with ω hω hmem
      by_cases hE : h ω ∈ E'
      · left
        have hEv := (hE' (h ω) hω.2).2 hE
        have heq : ρ (lfppC ξ (εn n) (h ω)) = ι (lfppSqC ξ (εn n) (h ω) T) := by
          ext p
          show lfppC ξ (εn n) (h ω) (p.1.1, p.2.1) = lfppSqC ξ (εn n) (h ω) T (incl p)
          rw [lfppC_apply_of_continuous hω.2, lfppSqC_apply_of_continuous hω.2 hRr]
          congr 2
          exact lfppDistE_eq_lfppDOn_of_sqBdyEvent hr.le hR1.le hEv p.1.2 p.2.2
        show ι (lfppSqC ξ (εn n) (h ω) T) ∈ smallSet δ η
        rw [← heq]; exact hmem
      · right; exact hE
  rw [ProbabilityMeasure.toMeasure_map] at hmain
  have := (ae_map_iff hρ.aemeasurable measurableSet_isPosOffDiag).1 hmain
  filter_upwards [this] with d hd x hx y hy hxy
  exact hd ⟨x, hx⟩ ⟨y, hy⟩ fun e => hxy (congrArg Subtype.val e)

end LQGMetric.DFGPS
