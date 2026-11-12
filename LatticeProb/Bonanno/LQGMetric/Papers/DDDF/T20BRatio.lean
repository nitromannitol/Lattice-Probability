/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BMom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

/-!
# DDDF (5.69): moments of `max L(R^L) / min L(R^S)` at scale `2^{-K}` (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1164–1167 ((5.69) = `eq:FirstIneq`):
`E[(max_{P,i} L^{(K,n)}(R_i^L(P), φ) / min_{P,i} L^{(K,n)}(R_i^S(P), φ))^{2β}]^{1/β}
  ≤ Λ_{n−K}(φ,p)² e^{CK^{1/2+ε₀}}`, "using our tail estimates ((4.48), (4.49)) and the scaling
property (2.30)".

`dddf_t20_ratio_moment`: for finite nonempty families `J` of long rectangles
`u_j 2^{-K} R_{3,1} + c_j` and `J'` of short rectangles `u'_j 2^{-K} R_{1,3} + c'_j`, with
`N = |J| + |J'|`,
`E[(max_J L / min_{J'} L)^q] ≤ Λ_{n−K}(φ,p)^q (e^{2q x₀} + 1)`, `x₀ = tailX0 (2q) N C c`,
which is `Λ^q e^{O((log N)^{2/3})}` (subexponential in `K` for `N = O(4^K)`; DDDF's
`e^{CK^{1/2+ε₀}}` is replaced by `e^{CK^{2/3}}`, equally sufficient for (5.70)).
Proof: `max L ≤ Λ ℓ 2^{-K} e^{X₁}`, `min L ≥ ℓ 2^{-K} e^{-X₂}` with `X₁, X₂ ≥ 0` whose tails are
the union bounds `t20_tail_max_long`, `t20_tail_min_short`; `e^{q(X₁+X₂)} ≤ (e^{2qX₁}+e^{2qX₂})/2`
and `lintegral_exp_le_of_tail_logsq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

namespace T20B

theorem measurable_mrectLen (hW : IsWhiteNoise P W) {K n : ℕ} (hKn : K ≤ n) (u : Circle)
    (c : ℂ) (a b : ℝ) : Measurable fun ω => mrectLen ξ (fun x => phiMN W P K n x ω) K u c a b := by
  have hφ := isPhiVersion_phiMN hW hKn
  exact (measurable_crossLenIn ((rectAB a b).isCompact_toSet.image (by unfold mot; fun_prop))
    hφ.cont hφ.meas).ennreal_toReal

theorem ae_mrectLen_pos (hW : IsWhiteNoise P W) {K n : ℕ} (hKn : K ≤ n) (u : Circle) (c : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᵐ ω ∂P, 0 < mrectLen ξ (fun x => phiMN W P K n x ω) K u c a b := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le (n - K))
  rw [ae_iff]
  have e : {ω | ¬ 0 < mrectLen ξ (fun x => phiMN W P K n x ω) K u c a b} =
      {ω | mrectLen ξ (fun x => phiMN W P K n x ω) K u c a b ∈ Iic 0} := by
    ext ω; simp
  rw [e, law_mrectLen hW hKn u c a b measurableSet_Iic]
  convert measure_empty (μ := P)
  ext ω
  simp only [mem_ofPred_eq, mem_Iic, mem_empty_iff_false, iff_false, not_le]
  exact mul_pos (by positivity) (lenObs_pos hφ.cont _ (by simp [rectAB] ; exact ha.le)
    (by simpa [rectAB] using hb) (by simpa [rectAB, MarkedRect.crossWidth] using ha) ω)

lemma LambdaN_pos (hW : IsWhiteNoise P W) {q : ℝ≥0∞} (hq0 : 0 < q) (hq : q ≤ 2⁻¹) (m : ℕ) :
    0 < LambdaN ξ W P m q := by
  have := hW.isProbabilityMeasure
  have hq1 : q < 1 := hq.trans_lt inv_two_lt_one'
  have h0 := ellN_pos (ξ := ξ) hW hq0 hq1 0
  have h1 : ellN ξ W P 0 q ≤ ellBarN ξ W P 0 q :=
    (ellN_le_lambdaN hq0 hq 0).trans (lambdaN_le_ellBarN hq0 hq 0)
  refine lt_of_lt_of_le (div_pos (h0.trans_le h1) h0) ?_
  exact Finset.le_sup' (fun k => ellBarN ξ W P k q / ellN ξ W P k q)
    (Finset.mem_range.2 (Nat.succ_pos m))

end T20B

open T20B in
/-- **DDDF (5.69)** (`tightness.tex` l. 1164–1167), with an explicit subexponential factor. -/
theorem dddf_t20_ratio_moment (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ q : ℝ, 0 < q → ∀ (K n : ℕ), K ≤ n → ∀ {ι : Type*} (J J' : Finset ι)
        (hJ : J.Nonempty) (hJ' : J'.Nonempty) (u u' : ι → Circle) (cc cc' : ι → ℂ),
        ∫⁻ ω, ENNReal.ofReal
          ((J.sup' hJ (fun j => mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 3 1) /
            J'.inf' hJ' (fun j => mrectLen ξ (fun x => phiMN W P K n x ω) K (u' j) (cc' j) 1 3))
            ^ q) ∂P ≤
          ENNReal.ofReal (LambdaN ξ W P (n - K) (ENNReal.ofReal p) ^ q *
            (Real.exp (2 * q * tailX0 (2 * q) (J.card + J'.card) C c) + 1)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, hL⟩ := t20_tail_max_long (P := P) hW hξ
  obtain ⟨p₂, hp₂, hS⟩ := t20_tail_min_short (P := P) hW hξ
  refine ⟨min (min p₁ p₂) (1 / 4), lt_min (lt_min hp₁ hp₂) (by norm_num), fun p hp hpp => ?_⟩
  have hpa : p ≤ p₁ := hpp.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hpb : p ≤ p₂ := hpp.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  obtain ⟨C₁, c₁, hC₁, hc₁, hL'⟩ := hL p hp hpa
  obtain ⟨C₂, c₂, hC₂, hc₂, hS'⟩ := hS p hp hpb
  refine ⟨max C₁ C₂, min c₁ (c₂ / 2), lt_max_of_lt_left hC₁, lt_min hc₁ (by positivity),
    fun q hq K n hKn ι J J' hJ hJ' u u' cc cc' => ?_⟩
  set Q : ℝ≥0∞ := ENNReal.ofReal p with hQdef
  have hQ0 : 0 < Q := ENNReal.ofReal_pos.2 hp
  have hQ2 : Q ≤ 2⁻¹ := by
    rw [hQdef, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set r : ℝ := (2 : ℝ)⁻¹ ^ K
  have hr : 0 < r := by positivity
  set Λ := LambdaN ξ W P (n - K) Q
  set ℓ := ellN ξ W P (n - K) Q
  have hΛ : 0 < Λ := LambdaN_pos hW hQ0 hQ2 _
  have hℓ : 0 < ℓ := ellN_pos hW hQ0 (hQ2.trans_lt inv_two_lt_one') _
  set N : ℝ := (J.card : ℝ) + J'.card
  have hN : 0 ≤ N := by positivity
  set C : ℝ := max C₁ C₂
  set c : ℝ := min c₁ (c₂ / 2)
  have hC : 0 < C := lt_max_of_lt_left hC₁
  have hc : 0 < c := lt_min hc₁ (by positivity)
  set Lj : ι → Ω → ℝ := fun j ω => mrectLen ξ (fun x => phiMN W P K n x ω) K (u j) (cc j) 3 1
  set Sj : ι → Ω → ℝ := fun j ω => mrectLen ξ (fun x => phiMN W P K n x ω) K (u' j) (cc' j) 1 3
  have hLm : ∀ j, Measurable (Lj j) := fun j => measurable_mrectLen hW hKn _ _ _ _
  have hSm : ∀ j, Measurable (Sj j) := fun j => measurable_mrectLen hW hKn _ _ _ _
  set X₁ : Ω → ℝ := fun ω => J.sup' hJ fun j => max 0 (Real.log (Lj j ω) - Real.log (Λ * ℓ * r))
  set X₂ : Ω → ℝ := fun ω => J'.sup' hJ' fun j => max 0 (Real.log (ℓ * r) - Real.log (Sj j ω))
  have hX₁0 : ∀ ω, 0 ≤ X₁ ω := fun ω => by
    obtain ⟨j, hj⟩ := hJ
    exact (le_max_left _ _).trans (Finset.le_sup' (fun j => max 0 (Real.log (Lj j ω) -
      Real.log (Λ * ℓ * r))) hj)
  have hX₂0 : ∀ ω, 0 ≤ X₂ ω := fun ω => by
    obtain ⟨j, hj⟩ := hJ'
    exact (le_max_left _ _).trans (Finset.le_sup' (fun j => max 0 (Real.log (ℓ * r) -
      Real.log (Sj j ω))) hj)
  have hX₁m : Measurable X₁ := by
    have h := Finset.measurable_sup' hJ (f := fun j ω => max 0 (Real.log (Lj j ω) -
      Real.log (Λ * ℓ * r))) fun j _ => measurable_const.max
        ((Real.measurable_log.comp (hLm j)).sub measurable_const)
    convert h using 1
    funext ω; rw [Finset.sup'_apply]
  have hX₂m : Measurable X₂ := by
    have h := Finset.measurable_sup' hJ' (f := fun j ω => max 0 (Real.log (ℓ * r) -
      Real.log (Sj j ω))) fun j _ => measurable_const.max
        (measurable_const.sub (Real.measurable_log.comp (hSm j)))
    convert h using 1
    funext ω; rw [Finset.sup'_apply]
  -- a.s. positivity of all crossing lengths
  have hpos : ∀ᵐ ω ∂P, (∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω := by
    have h1 : ∀ᵐ ω ∂P, ∀ j ∈ J, 0 < Lj j ω := (Filter.eventually_all_finset _).2 fun j _ =>
      ae_mrectLen_pos hW hKn _ _ (by norm_num) (by norm_num)
    have h2 : ∀ᵐ ω ∂P, ∀ j ∈ J', 0 < Sj j ω := (Filter.eventually_all_finset _).2 fun j _ =>
      ae_mrectLen_pos hW hKn _ _ (by norm_num) (by norm_num)
    filter_upwards [h1, h2] with ω a b using ⟨a, b⟩
  -- tails
  have hlog_t : ∀ t : ℝ, 2 < t → Real.exp (-c₁ * t ^ 2 / Real.log t) ≤
      Real.exp (-c * t ^ 2 / Real.log t) := fun t ht => by
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hl.le)
    nlinarith [min_le_left c₁ (c₂ / 2), sq_nonneg t]
  have hgauss : ∀ t : ℝ, 2 < t → Real.exp (-c₂ * t ^ 2) ≤
      Real.exp (-c * t ^ 2 / Real.log t) := fun t ht => by
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have hl2 : 1 / 2 ≤ Real.log t := by
      have := Real.add_one_le_exp (1 / 2 : ℝ)
      have h3 : Real.exp (1 / 2) ≤ t := by
        have : Real.exp (1 / 2) ≤ 2 := by
          have := Real.exp_one_lt_d9
          have h4 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos (1 / 2)]
        linarith
      rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; exact h3
    refine Real.exp_le_exp.2 ?_
    rw [le_div_iff₀ hl]
    have hc2 : c ≤ c₂ / 2 := min_le_right _ _
    nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left hl2 (sq_nonneg t)]
  have htail₁ : ∀ t, 2 < t → P {ω | t ≤ X₁ ω} ≤
      ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t)) := by
    intro t ht
    have hsub : {ω | t ≤ X₁ ω} ⊆ {ω | ∃ j ∈ J, Real.exp t * Λ * ℓ * r ≤ Lj j ω} ∪
        {ω | ¬ ((∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω)} := by
      intro ω hω
      by_cases hp : (∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω
      · left
        obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hJ fun j =>
          max 0 (Real.log (Lj j ω) - Real.log (Λ * ℓ * r))
        refine ⟨j, hj, ?_⟩
        have h1 : t ≤ max 0 (Real.log (Lj j ω) - Real.log (Λ * ℓ * r)) := by
          have : t ≤ X₁ ω := hω; rwa [show X₁ ω = _ from hjeq] at this
        have h2 : t ≤ Real.log (Lj j ω) - Real.log (Λ * ℓ * r) := by
          rcases le_total 0 (Real.log (Lj j ω) - Real.log (Λ * ℓ * r)) with h | h
          · rwa [max_eq_right h] at h1
          · rw [max_eq_left h] at h1; linarith
        have hpos := hp.1 j hj
        rw [← Real.exp_log hpos, show Real.exp t * Λ * ℓ * r = Real.exp t * (Λ * ℓ * r) by ring,
          ← Real.exp_log (show 0 < Λ * ℓ * r by positivity), ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      · right; exact hp
    have hnull : P {ω | ¬ ((∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω)} = 0 := by
      rw [← ae_iff]; exact hpos
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hnull, add_zero]
    have h := hL' K n hKn J u cc t ht
    refine le_trans h ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hJN : (J.card : ℝ) ≤ N := by simp only [N]; linarith [(Nat.cast_nonneg J'.card : (0 : ℝ) ≤ _)]
    calc (J.card : ℝ) * (C₁ * Real.exp (-c₁ * t ^ 2 / Real.log t))
        ≤ N * (C * Real.exp (-c * t ^ 2 / Real.log t)) :=
          mul_le_mul hJN (mul_le_mul (le_max_left _ _) (hlog_t t ht) (Real.exp_pos _).le hC.le)
            (by positivity) hN
      _ = N * C * Real.exp (-c * t ^ 2 / Real.log t) := by ring
  have htail₂ : ∀ t, 2 < t → P {ω | t ≤ X₂ ω} ≤
      ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t)) := by
    intro t ht
    have hsub : {ω | t ≤ X₂ ω} ⊆ {ω | ∃ j ∈ J', Sj j ω ≤ Real.exp (-t) * ℓ * r} ∪
        {ω | ¬ ((∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω)} := by
      intro ω hω
      by_cases hp : (∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω
      · left
        obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hJ' fun j =>
          max 0 (Real.log (ℓ * r) - Real.log (Sj j ω))
        refine ⟨j, hj, ?_⟩
        have h1 : t ≤ max 0 (Real.log (ℓ * r) - Real.log (Sj j ω)) := by
          have : t ≤ X₂ ω := hω; rwa [show X₂ ω = _ from hjeq] at this
        have h2 : t ≤ Real.log (ℓ * r) - Real.log (Sj j ω) := by
          rcases le_total 0 (Real.log (ℓ * r) - Real.log (Sj j ω)) with h | h
          · rwa [max_eq_right h] at h1
          · rw [max_eq_left h] at h1; linarith
        have hpos := hp.2 j hj
        rw [← Real.exp_log hpos, show Real.exp (-t) * ℓ * r = Real.exp (-t) * (ℓ * r) by ring,
          ← Real.exp_log (show 0 < ℓ * r by positivity), ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      · right; exact hp
    have hnull : P {ω | ¬ ((∀ j ∈ J, 0 < Lj j ω) ∧ ∀ j ∈ J', 0 < Sj j ω)} = 0 := by
      rw [← ae_iff]; exact hpos
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hnull, add_zero]
    have h := hS' K n hKn J' u' cc' t (by linarith)
    refine le_trans h ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hJN : (J'.card : ℝ) ≤ N := by simp only [N]; linarith [(Nat.cast_nonneg J.card : (0 : ℝ) ≤ _)]
    calc (J'.card : ℝ) * (C₂ * Real.exp (-c₂ * t ^ 2))
        ≤ N * (C * Real.exp (-c * t ^ 2 / Real.log t)) :=
          mul_le_mul hJN (mul_le_mul (le_max_right _ _) (hgauss t ht) (Real.exp_pos _).le hC.le)
            (by positivity) hN
      _ = N * C * Real.exp (-c * t ^ 2 / Real.log t) := by ring
  -- exponential moments
  have hq2 : 0 < 2 * q := by positivity
  have hE₁ := lintegral_exp_le_of_tail_logsq hX₁0 hX₁m.aemeasurable hq2 hN hC hc htail₁
  have hE₂ := lintegral_exp_le_of_tail_logsq hX₂0 hX₂m.aemeasurable hq2 hN hC hc htail₂
  set x₀ := tailX0 (2 * q) N C c
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal
      ((J.sup' hJ (fun j => Lj j ω) / J'.inf' hJ' (fun j => Sj j ω)) ^ q) ≤
      ENNReal.ofReal (Λ ^ q / 2) * (ENNReal.ofReal (Real.exp (2 * q * X₁ ω)) +
        ENNReal.ofReal (Real.exp (2 * q * X₂ ω))) := by
    filter_upwards [hpos] with ω hp
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨jA, hjA, hA⟩ := Finset.exists_mem_eq_sup' hJ fun j => Lj j ω
    obtain ⟨jB, hjB, hB⟩ := Finset.exists_mem_eq_inf' hJ' fun j => Sj j ω
    rw [hA, hB]
    have hLA := hp.1 jA hjA
    have hSB := hp.2 jB hjB
    have hA1 : Lj jA ω ≤ Λ * ℓ * r * Real.exp (X₁ ω) := by
      have h1 : Real.log (Lj jA ω) - Real.log (Λ * ℓ * r) ≤ X₁ ω :=
        (le_max_right _ _).trans (Finset.le_sup' (fun j => max 0 (Real.log (Lj j ω) -
          Real.log (Λ * ℓ * r))) hjA)
      rw [← Real.exp_log hLA, ← Real.exp_log (show 0 < Λ * ℓ * r by positivity),
        ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hB1 : ℓ * r * Real.exp (-X₂ ω) ≤ Sj jB ω := by
      have h1 : Real.log (ℓ * r) - Real.log (Sj jB ω) ≤ X₂ ω :=
        (le_max_right _ _).trans (Finset.le_sup' (fun j => max 0 (Real.log (ℓ * r) -
          Real.log (Sj j ω))) hjB)
      rw [← Real.exp_log hSB, ← Real.exp_log (show 0 < ℓ * r by positivity),
        ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hratio : Lj jA ω / Sj jB ω ≤ Λ * Real.exp (X₁ ω + X₂ ω) := by
      rw [div_le_iff₀ hSB]
      calc Lj jA ω ≤ Λ * ℓ * r * Real.exp (X₁ ω) := hA1
        _ = Λ * Real.exp (X₁ ω + X₂ ω) * (ℓ * r * Real.exp (-X₂ ω)) := by
          rw [Real.exp_add, Real.exp_neg]; field_simp
        _ ≤ Λ * Real.exp (X₁ ω + X₂ ω) * Sj jB ω :=
          mul_le_mul_of_nonneg_left hB1 (by positivity)
    have hpow : (Lj jA ω / Sj jB ω) ^ q ≤ Λ ^ q * Real.exp (q * (X₁ ω + X₂ ω)) := by
      calc (Lj jA ω / Sj jB ω) ^ q ≤ (Λ * Real.exp (X₁ ω + X₂ ω)) ^ q :=
            Real.rpow_le_rpow (by positivity) hratio hq.le
        _ = Λ ^ q * Real.exp (q * (X₁ ω + X₂ ω)) := by
            rw [Real.mul_rpow hΛ.le (Real.exp_pos _).le, ← Real.exp_mul, mul_comm (X₁ ω + X₂ ω)]
    have hamgm : Real.exp (q * (X₁ ω + X₂ ω)) ≤
        (Real.exp (2 * q * X₁ ω) + Real.exp (2 * q * X₂ ω)) / 2 := by
      have e1 : Real.exp (2 * q * X₁ ω) = Real.exp (q * X₁ ω) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : Real.exp (2 * q * X₂ ω) = Real.exp (q * X₂ ω) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [e1, e2, mul_add, Real.exp_add]
      nlinarith [sq_nonneg (Real.exp (q * X₁ ω) - Real.exp (q * X₂ ω))]
    calc (Lj jA ω / Sj jB ω) ^ q ≤ Λ ^ q * Real.exp (q * (X₁ ω + X₂ ω)) := hpow
      _ ≤ Λ ^ q * ((Real.exp (2 * q * X₁ ω) + Real.exp (2 * q * X₂ ω)) / 2) :=
          mul_le_mul_of_nonneg_left hamgm (by positivity)
      _ = Λ ^ q / 2 * (Real.exp (2 * q * X₁ ω) + Real.exp (2 * q * X₂ ω)) := by ring
  have hm1 : Measurable fun ω => ENNReal.ofReal (Real.exp (2 * q * X₁ ω)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hX₁m))
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Λ ^ q / 2) * (ENNReal.ofReal (Real.exp (2 * q * X₁ ω)) +
        ENNReal.ofReal (Real.exp (2 * q * X₂ ω))) ∂P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Λ ^ q / 2) * (∫⁻ ω, ENNReal.ofReal (Real.exp (2 * q * X₁ ω)) ∂P +
        ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * q * X₂ ω)) ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1]
    _ ≤ ENNReal.ofReal (Λ ^ q / 2) * (ENNReal.ofReal (Real.exp (2 * q * x₀) + 1) +
        ENNReal.ofReal (Real.exp (2 * q * x₀) + 1)) := by gcongr
    _ = ENNReal.ofReal (Λ ^ q * (Real.exp (2 * q * x₀) + 1)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring

end DDDF
end LQGMetric
