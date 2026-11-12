/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLim at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLimZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 A, second conjunct: subsequential limits are continuous length metrics

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:993–1012. Let `D_h` be a
subsequential limit in law of `𝔞_ε⁻¹ D_h^ε` (law `μ`). We show that `μ`-a.s.
1. `D_h` is a continuous symmetric pseudo-metric (closed condition, portmanteau);
2. `D_h` is positive off the diagonal (`lem2_5_pos_sq`, T:997–1003, via Lemma 2.8 on
   `S_{Rr}(0)` and the agreement event (eqn-square-metric-agree));
3. for each `s`, `D_h` has midpoints in `S_s(0)` for pairs closer than the distance to
   `∂S_s(0)` (`zSetC`, closed; `𝔞_ε⁻¹ D_h^ε` is a length metric);
4. for each `r` there is `s` with `D_h(x,y) < D_h(x,w)` for `x,y ∈ S_r(0)`, `w ∈ ∂S_s(0)`: the
   first condition of (eqn-square-metric-agree'), "by passing to the (subsequential) limit in
   (eqn-square-metric-agree)" (T:1008), with probability `≥ p` for every `p < 1`;
and conclude by the deterministic `isContLengthMetric_of_local`.

Deviation (proposed DF-L25-LEN): DFGPS deduce the length property (T:1009–1012) from the joint
convergence with `D_h^ε(·,·;S_{Rr}(0))` and Lemma 2.11 on the agreement event; we instead pass the
local midpoint property of `𝔞_ε⁻¹ D_h^ε` to the limit (a closed condition) and build geodesics by
Menger's dyadic construction inside `S_s(0)`, which needs no coupling. The agreement event is used
as in the paper (items 2 and 4).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- portmanteau for closed sets of full measure -/
theorem ae_mem_of_isClosed_of_forall {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E] {ν : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto ν atTop (𝓝 μ)) {F : Set E} (hF : IsClosed F)
    (h : ∀ n, (ν n : Measure E) F = 1) : ∀ᵐ d ∂(μ : Measure E), d ∈ F := by
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simp only [h, limsup_const] at hle
  have h1 : (μ : Measure E) F = (μ : Measure E) univ := by
    rw [measure_univ]; exact le_antisymm prob_le_one hle
  exact (ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).2 h1

/-- portmanteau lower bound for closed sets -/
theorem le_measure_of_isClosed {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E] {ν : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto ν atTop (𝓝 μ)) {F : Set E} (hF : IsClosed F) {q : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, q ≤ (ν n : Measure E) F) : q ≤ (μ : Measure E) F :=
  (le_limsup_of_frequently_le h.frequently).trans
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF)

/-- the closed form of the first condition of (eqn-square-metric-agree) -/
def agreeSetC (r s : ℝ) : Set C(ℂ × ℂ, ℝ) :=
  {d | ∀ x ∈ sqC r 0, ∀ y ∈ sqC r 0, ∀ u ∈ sqC r 0, ∀ w ∈ frontier (sqC s 0),
    2 * d (x, y) ≤ d (u, w)}

theorem isClosed_agreeSetC (r s : ℝ) : IsClosed (agreeSetC r s) := by
  have e : agreeSetC r s = ⋂ x ∈ sqC r 0, ⋂ y ∈ sqC r 0, ⋂ u ∈ sqC r 0,
      ⋂ w ∈ frontier (sqC s 0), {d : C(ℂ × ℂ, ℝ) | 2 * d (x, y) ≤ d (u, w)} := by
    ext d; simp [agreeSetC]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_biInter fun u _ =>
    isClosed_biInter fun w _ =>
      isClosed_le (continuous_const.mul (continuous_eval_const _)) (continuous_eval_const _)

theorem lfppC_mem_agreeSetC {ξ ε r R : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (hE : sqBdyEvent ξ ε 2 r R g) : lfppC ξ ε g ∈ agreeSetC r (R * r) := by
  intro x hx y hy u hu w hw
  simp only [lfppC_apply_of_continuous hc]
  set c := (aEpsDF ξ ε)⁻¹
  have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
  unfold sqBdyEvent at hE
  have h1 : lfppDistE ξ ε g x y ≤ ⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v :=
    le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v) x hx
      (le_iSup₂_of_le (f := fun v _ => lfppDistE ξ ε g x v) y hy le_rfl)
  have h2 : (⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v) ≤
      lfppDistE ξ ε g u w :=
    iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v) u hu
      (iInf₂_le_of_le (f := fun v _ => lfppDistE ξ ε g u v) w hw le_rfl)
  have h3 : lfppDistE ξ ε g x y ≤ ENNReal.ofReal 2⁻¹ * lfppDistE ξ ε g u w :=
    (h1.trans hE.le).trans (by gcongr)
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lfppDistE_ne_top' hc u w)) h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h4
  nlinarith

theorem sqC_subset_interior {r s : ℝ} (hrs : r < s) : sqC r 0 ⊆ interior (sqC s 0) := by
  intro x hx
  rw [mem_sqC_iff] at hx
  have ho : IsOpen {z : ℂ | -(s / 2) < z.re ∧ z.re < s / 2 ∧ -(s / 2) < z.im ∧ z.im < s / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  refine interior_maximal (fun z hz => ?_) ho ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [mem_sqC_iff]
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- **DFGPS Lemma 2.5 A, second conjunct** (T:983–991 of the statement's proof, T:993–1012):
every subsequential limit law of `𝔞_ε⁻¹ D_h^ε` is supported on continuous length metrics. -/
theorem lem2_5_lim (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P) :
    ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ)) (μ : ProbabilityMeasure C(ℂ × ℂ, ℝ)),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
        (ν n : Measure _) = P.map fun ω => lfppC (xiGamma γ) (εn n) (h ω)) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContLengthMetric d := by
  intro εn ν μ hν hε0 hlim
  set ξ := xiGamma γ
  have hcS : ∀ n, ∀ᵐ ω ∂P, Continuous (heatMollify (εn n) (h ω)) := fun n =>
    (hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hν n).1.1.ne').mono fun ω hω => hω.2
  have hFC : ∀ n, AEMeasurable (fun ω => lfppC ξ (εn n) (h ω)) P := fun n =>
    aemeasurable_lfppC hh (hν n).1.1.ne'
  have hεn' : Tendsto εn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun n => (hν n).1.1⟩
  have hfull : ∀ F : Set C(ℂ × ℂ, ℝ), IsClosed F →
      (∀ (g : DistC) (ε : ℝ), Continuous (heatMollify ε g) → lfppC ξ ε g ∈ F) →
      ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), d ∈ F := by
    intro F hF hg
    refine ae_mem_of_isClosed_of_forall hlim hF fun n => ?_
    rw [(hν n).2, Measure.map_apply_of_aemeasurable (hFC n) hF.measurableSet]
    have hae : ∀ᵐ ω ∂P, ω ∈ (fun ω => lfppC ξ (εn n) (h ω)) ⁻¹' F :=
      (hcS n).mono fun ω hω => hg _ _ hω
    exact (measure_congr (eventuallyEqSet_univ.2 hae)).trans measure_univ
  have h1 : ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), d ∈ pmetSet ℂ :=
    hfull _ (isClosed_pmetSet ℂ) fun g ε hc => lfppC_mem_pmetSet hc
  have h2 : ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), d ∈ symmSet ℂ :=
    hfull _ (isClosed_symmSet ℂ) fun g ε hc => lfppC_mem_symmSet hc
  have h3 : ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), ∀ s : ℕ, d ∈ zSetC s :=
    ae_all_iff.2 fun s => hfull _ (isClosed_zSetC (Nat.cast_nonneg s)) fun g ε hc =>
      lfppC_mem_zSetC hc (Nat.cast_nonneg s)
  have h4 : ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), ∀ x y, x ≠ y → 0 < d (x, y) := by
    have := ae_all_iff.2 fun n : ℕ => lem2_5_pos_sq h28 hγ hγ2 hh εn ν μ hν hε0 hlim
      (r := (n : ℝ) + 1) (by positivity)
    filter_upwards [this] with d hd x y hxy
    set n : ℕ := max ⌈2 * ‖x‖⌉₊ ⌈2 * ‖y‖⌉₊
    have hr1 : 2 * ‖x‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    have hr2 : 2 * ‖y‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    exact hd n x (mem_sqC_of_norm_le (by linarith)) y (mem_sqC_of_norm_le (by linarith)) hxy
  have h5 : ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), ∀ r : ℕ, ∃ s : ℕ, d ∈ agreeSet r s := by
    refine ae_all_iff.2 fun r₀ => ?_
    have hNpos : (μ : Measure C(ℂ × ℂ, ℝ)) {d | ¬ ∀ x y, x ≠ y → 0 < d (x, y)} = 0 :=
      ae_iff.1 h4
    refine ae_iff.2 (le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_) zero_le)
    set ζ : ℝ := min ((ε' : ℝ) / 2) (1 / 2) with hζdef
    have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
    have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨R, hR1, hRp⟩ := lem2_10 h28 γ hγ hγ2 P h hh (1 - ζ / 2)
      ⟨by linarith, by linarith⟩ 2 two_pos
    have hR0 : 0 < R := by linarith
    set r₁ : ℝ := (r₀ : ℝ) + 1
    have hr₁ : 0 < r₁ := by positivity
    set s : ℕ := ⌈R * r₁⌉₊
    have hs1 : R * r₁ ≤ s := Nat.le_ceil _
    have hspos : (0 : ℝ) < s := lt_of_lt_of_le (mul_pos hR0 hr₁) hs1
    set r : ℝ := (s : ℝ) / R
    have hr1 : r₁ ≤ r := (le_div_iff₀ hR0).2 (by linarith [mul_comm R r₁])
    have hrpos : 0 < r := hr₁.trans_le hr1
    have hRr : R * r = s := mul_div_cancel₀ _ hR0.ne'
    have hrs : r < s := div_lt_self hspos hR1
    have hF := isClosed_agreeSetC r s
    have hμF : ENNReal.ofReal (1 - ζ) ≤ (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetC r s) := by
      refine le_measure_of_isClosed hlim hF ?_
      have hq : ENNReal.ofReal (1 - ζ) <
          liminf (fun ε => P {ω | sqBdyEvent ξ ε 2 r R (h ω)}) (𝓝[>] 0) :=
        lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
          (hRp r hrpos)
      filter_upwards [hεn'.eventually (eventually_lt_of_lt_liminf hq)] with n hn
      refine hn.le.trans ?_
      rw [(hν n).2, Measure.map_apply_of_aemeasurable (hFC n) hF.measurableSet]
      refine measure_mono_ae ?_
      filter_upwards [hcS n] with ω hω hE
      have := lfppC_mem_agreeSetC hω hE
      rwa [hRr] at this
    have hsub : {d : C(ℂ × ℂ, ℝ) | ¬ ∃ s : ℕ, d ∈ agreeSet r₀ s} ⊆
        (agreeSetC r s)ᶜ ∪ {d | ¬ ∀ x y, x ≠ y → 0 < d (x, y)} := by
      intro d hd
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq] at hcon
      apply hd
      refine ⟨s, fun x hx y hy w hw => ?_⟩
      have hx' : x ∈ sqC r 0 := sqC_mono (by linarith : (r₀ : ℝ) ≤ r) hx
      have hy' : y ∈ sqC r 0 := sqC_mono (by linarith : (r₀ : ℝ) ≤ r) hy
      have h2le := hcon.1 x hx' y hy' x hx' w hw
      have hxw : x ≠ w := fun e => hw.2 (e ▸ sqC_subset_interior hrs hx')
      have := hcon.2 x w hxw
      rcases le_or_gt (d (x, y)) 0 with h0 | h0 <;> linarith
    calc (μ : Measure C(ℂ × ℂ, ℝ)) {d | ¬ ∃ s : ℕ, d ∈ agreeSet r₀ s}
        ≤ (μ : Measure C(ℂ × ℂ, ℝ))
            ((agreeSetC r s)ᶜ ∪ {d | ¬ ∀ x y, x ≠ y → 0 < d (x, y)}) := measure_mono hsub
      _ ≤ (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetC r s)ᶜ +
            (μ : Measure C(ℂ × ℂ, ℝ)) {d | ¬ ∀ x y, x ≠ y → 0 < d (x, y)} :=
          measure_union_le _ _
      _ = (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetC r s)ᶜ := by rw [hNpos, add_zero]
      _ ≤ ENNReal.ofReal ζ := by
          rw [prob_compl_eq_one_sub hF.measurableSet]
          refine tsub_le_iff_right.2 ?_
          calc (1 : ℝ≥0∞) = ENNReal.ofReal ζ + ENNReal.ofReal (1 - ζ) := by
                rw [← ENNReal.ofReal_add hζ0.le (by linarith)]; simp
            _ ≤ ENNReal.ofReal ζ + (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetC r s) := by gcongr
      _ ≤ 0 + (ε' : ℝ≥0∞) := by
          rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by
            have := ε'.coe_nonneg; linarith))
  filter_upwards [h1, h2, h3, h4, h5] with d hd1 hd2 hd3 hd4 hd5
  exact isContLengthMetric_of_local hd1 hd2 hd4 hd3 hd5

end LQGMetric.DFGPS
