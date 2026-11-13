/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Quantile at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Concentration
import LatticeProb.Bonanno.LQGMetric.Prob.Quantile

/-!
# Quantiles of LFPP distances (packet P-X5, target T3: HA5 D3, DGZ (3.2) and Lemma 3.2)

Source: DGZ arXiv:2310.03996, (3.2) (the quantiles `a^{(p)}_n`) and Lemma 3.2
(`e^{-C√n} a^{(p₁)}_n ≤ a^{(p₂)}_n ≤ e^{C√n} a^{(p₁)}_n`); `source/higher-dimensional-lfpp-limit.pdf`,
App. A.1 (medians); planning audit HA5, Details D3 and findings A1-2, G6.

Quantiles are LQGMetric's lower quantiles of laws, `LQGMetric.lowerQuantile μ p =
inf {x | p ≤ μ(-∞, x]}` (HA5 §1 convention; only `μ(-∞, q_p] ≥ p` and `μ(-∞, q_p) ≤ p` are used,
never continuity of the law, G6).

* `Conc.abs_lowerQuantile_sub_le_of_tail` (HA5 Lemma D3): if
  `P[|Y - m| ≥ t] ≤ 2 exp(-t² / (2σ²))` for all `t ≥ 0` (`σ > 0`), then for `p ∈ (0,1)`,
  `|q_p(Y) - m| ≤ σ √(2 log(4 / min(p, 1 - p)))` (`= σ * quantileConst p`).
* `Conc.lowerQuantile_map_exp`, `Conc.lowerQuantile_map_eq_exp_lowerQuantile_map_log`,
  `Conc.log_lowerQuantile_map_eq`: for `D > 0` a.s., `q_p(D) = exp q_p(log D)`.
* LFPP (`X` a continuous version of `H_{a,b}`, `0 < a < b`, `v = log(b/a)`, `ξ > 0`,
  `D = D^ξ_V(x, y)(X)` for a bounded open convex `V` and `x ≠ y` in `V`; and the frozen
  distance, `d ≥ 1`):
  - `IsBandVersion.lowerQuantile_lfppDistOn_eq_exp`: `q_p(D) = exp q_p(log D)`;
  - `IsBandVersion.abs_log_lowerQuantile_lfppDistOn_sub_le` (DGZ, proof of Lemma 3.2):
    `|log q_p(D) - E log D| ≤ quantileConst p · ξ √v`;
  - `IsBandVersion.abs_log_lowerQuantile_lfppDistOn_sub_log_lowerQuantile_le` (DGZ Lemma 3.2):
    `|log q_{p₁}(D) - log q_{p₂}(D)| ≤ (quantileConst p₁ + quantileConst p₂) ξ √v`, and its
    multiplicative form `IsBandVersion.lowerQuantile_lfppDistOn_le_exp_mul`;
  - the same for the frozen distance (`…_lfppDistance_…`).

For DGZ's `D_n = D^ξ(h_n)`, `h_n = H_{2^{-n},1}`, one has `v = n log 2`, so the constant is
`C_{p₁,p₂} ξ √(n log 2)`: Lemma 3.2 with `C = (quantileConst p₁ + quantileConst p₂) ξ √(log 2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace HigherDimLFPP

namespace Conc

/-! ### The constant of Lemma D3 -/

/-- `√(2 log(4 / min(p, 1 - p)))`, the quantile constant of HA5 Lemma D3. -/
def quantileConst (p : ℝ) : ℝ := √(2 * Real.log (4 / min p (1 - p)))

theorem quantileConst_nonneg (p : ℝ) : 0 ≤ quantileConst p := Real.sqrt_nonneg _

/-- `2 exp(-(σ c_p)² / (2σ²)) = min(p, 1 - p) / 2`. -/
theorem two_mul_exp_neg_quantileConst {σ p : ℝ} (hσ : 0 < σ) (hp0 : 0 < p) (hp1 : p < 1) :
    2 * Real.exp (-(σ * quantileConst p) ^ 2 / (2 * σ ^ 2)) = min p (1 - p) / 2 := by
  have hm0 : 0 < min p (1 - p) := lt_min hp0 (by linarith)
  have hm1 : min p (1 - p) ≤ 1 := (min_le_left _ _).trans hp1.le
  have hlog : 0 ≤ Real.log (4 / min p (1 - p)) :=
    Real.log_nonneg ((one_le_div hm0).2 (by linarith))
  have hsq : quantileConst p ^ 2 = 2 * Real.log (4 / min p (1 - p)) :=
    Real.sq_sqrt (by positivity)
  have e : -(σ * quantileConst p) ^ 2 / (2 * σ ^ 2) = -Real.log (4 / min p (1 - p)) := by
    rw [mul_pow, hsq]
    field_simp
  rw [e, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  ring

/-! ### Lemma D3: quantiles under a two-sided Gaussian tail -/

section D3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- **HA5 Lemma D3**: if `P[|Y - m| ≥ t] ≤ 2 exp(-t² / (2σ²))` for all `t ≥ 0` (`σ > 0`), then
every lower quantile of level `p ∈ (0, 1)` satisfies `|q_p(Y) - m| ≤ σ √(2 log(4/min(p,1-p)))`. -/
theorem abs_lowerQuantile_sub_le_of_tail [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : AEMeasurable Y P) {m σ : ℝ} (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ |Y ω - m|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    |LQGMetric.lowerQuantile (P.map Y) p - m| ≤ σ * quantileConst p.toReal := by
  have hptop : p ≠ ⊤ := (hp1.trans ENNReal.one_lt_top).ne
  set r : ℝ := p.toReal with hr
  have hpr : p = ENNReal.ofReal r := (ENNReal.ofReal_toReal hptop).symm
  have hr0 : 0 < r := ENNReal.toReal_pos hp0.ne' hptop
  have hr1 : r < 1 := by
    have h := (ENNReal.toReal_lt_toReal hptop ENNReal.one_ne_top).2 hp1
    rwa [ENNReal.toReal_one] at h
  set mm : ℝ := min r (1 - r) with hmm
  have hmm0 : 0 < mm := lt_min hr0 (by linarith)
  have hmmr : mm ≤ r := min_le_left _ _
  have hmm1 : mm ≤ 1 - r := min_le_right _ _
  set T : ℝ := σ * quantileConst r with hT
  have hT0 : 0 ≤ T := mul_nonneg hσ.le (quantileConst_nonneg r)
  have hbad : P {ω | T ≤ |Y ω - m|} ≤ ENNReal.ofReal (mm / 2) := by
    have h := htail T hT0
    rwa [hT, two_mul_exp_neg_quantileConst hσ hr0 hr1] at h
  set μ : Measure ℝ := P.map Y with hμ
  -- upper bound `q ≤ m + T`
  have hup : LQGMetric.lowerQuantile μ p ≤ m + T := by
    refine (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 ?_
    have hIoi : μ (Ioi (m + T)) ≤ ENNReal.ofReal (mm / 2) := by
      rw [hμ, Measure.map_apply_of_aemeasurable hY measurableSet_Ioi]
      refine (measure_mono fun ω hω => ?_).trans hbad
      have h : m + T < Y ω := hω
      show T ≤ |Y ω - m|
      rw [abs_of_pos (by linarith)]
      linarith
    have hsum : μ (Iic (m + T)) + μ (Ioi (m + T)) = 1 := by
      rw [← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
    have h1 : ENNReal.ofReal r + ENNReal.ofReal (mm / 2) ≤ 1 := by
      rw [← ENNReal.ofReal_add hr0.le (by positivity), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [hpr]
    refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (mm / 2)) ENNReal.ofReal_ne_top ?_
    calc ENNReal.ofReal r + ENNReal.ofReal (mm / 2) ≤ 1 := h1
      _ = μ (Iic (m + T)) + μ (Ioi (m + T)) := hsum.symm
      _ ≤ μ (Iic (m + T)) + ENNReal.ofReal (mm / 2) := add_le_add le_rfl hIoi
  -- lower bound `m - T ≤ q`
  have hlow : m - T ≤ LQGMetric.lowerQuantile μ p := by
    by_contra hlt
    push Not at hlt
    set q := LQGMetric.lowerQuantile μ p with hq
    have hpq : p ≤ μ (Iic q) := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1).2 le_rfl
    have hIic : μ (Iic q) ≤ ENNReal.ofReal (mm / 2) := by
      rw [hμ, Measure.map_apply_of_aemeasurable hY measurableSet_Iic]
      refine (measure_mono fun ω hω => ?_).trans hbad
      have h : Y ω ≤ q := hω
      show T ≤ |Y ω - m|
      rw [abs_of_neg (by linarith)]
      linarith
    have hlt' : ENNReal.ofReal (mm / 2) < p := by
      rw [hpr]
      exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 (by linarith)
    exact absurd (hpq.trans hIic) (not_le.2 hlt')
  rw [abs_sub_le_iff]
  constructor <;> linarith

end D3

/-! ### Quantiles of `D` and of `log D` -/

section LogExp

/-- Lower quantiles commute with `exp`: `q_p(μ ∘ exp⁻¹) = exp q_p(μ)` for `p ∈ (0,1)`. -/
theorem lowerQuantile_map_exp {μ : Measure ℝ} [IsProbabilityMeasure μ] {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) :
    LQGMetric.lowerQuantile (μ.map Real.exp) p = Real.exp (LQGMetric.lowerQuantile μ p) := by
  set q := LQGMetric.lowerQuantile μ p with hq
  have hset : {x : ℝ | p ≤ (μ.map Real.exp) (Iic x)} = Ici (Real.exp q) := by
    ext x
    rw [mem_ofPred_eq, mem_Ici, Measure.map_apply Real.measurable_exp measurableSet_Iic]
    rcases le_or_gt x 0 with hx | hx
    · have hpre : Real.exp ⁻¹' Iic x = ∅ :=
        eq_empty_of_forall_notMem fun y hy => absurd (lt_of_lt_of_le (Real.exp_pos y) hy)
          (not_lt.2 hx)
      rw [hpre, measure_empty]
      constructor
      · intro h
        exact absurd (lt_of_lt_of_le hp0 h) (lt_irrefl 0)
      · intro h
        exact absurd (lt_of_lt_of_le (Real.exp_pos q) (h.trans hx)) (lt_irrefl 0)
    · have hpre : Real.exp ⁻¹' Iic x = Iic (Real.log x) := by
        ext y
        rw [mem_preimage, mem_Iic, mem_Iic, Real.le_log_iff_exp_le hx]
      rw [hpre, LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1,
        Real.le_log_iff_exp_le hx]
  show sInf {x : ℝ | p ≤ (μ.map Real.exp) (Iic x)} = Real.exp q
  rw [hset, csInf_Ici]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Quantiles of `D` versus quantiles of `log D`** (HA5 D3): for `D > 0` a.s.,
`q_p(D) = exp q_p(log D)`. -/
theorem lowerQuantile_map_eq_exp_lowerQuantile_map_log [IsProbabilityMeasure P] {D : Ω → ℝ}
    (hD : AEMeasurable D P) (hpos : ∀ᵐ ω ∂P, 0 < D ω) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    LQGMetric.lowerQuantile (P.map D) p =
      Real.exp (LQGMetric.lowerQuantile (P.map fun ω => Real.log (D ω)) p) := by
  have hlog : AEMeasurable (fun ω => Real.log (D ω)) P := hD.log
  have hmap : P.map D = (P.map fun ω => Real.log (D ω)).map Real.exp := by
    rw [AEMeasurable.map_map_of_aemeasurable Real.measurable_exp.aemeasurable hlog]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with ω hω
    exact (Real.exp_log hω).symm
  rw [hmap, lowerQuantile_map_exp hp0 hp1]

/-- `log q_p(D) = q_p(log D)` for `D > 0` a.s. -/
theorem log_lowerQuantile_map_eq [IsProbabilityMeasure P] {D : Ω → ℝ} (hD : AEMeasurable D P)
    (hpos : ∀ᵐ ω ∂P, 0 < D ω) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.log (LQGMetric.lowerQuantile (P.map D) p) =
      LQGMetric.lowerQuantile (P.map fun ω => Real.log (D ω)) p := by
  rw [lowerQuantile_map_eq_exp_lowerQuantile_map_log hD hpos hp0 hp1, Real.log_exp]

/-- Lower quantiles of a.s. positive variables are positive. -/
theorem lowerQuantile_map_pos [IsProbabilityMeasure P] {D : Ω → ℝ} (hD : AEMeasurable D P)
    (hpos : ∀ᵐ ω ∂P, 0 < D ω) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < LQGMetric.lowerQuantile (P.map D) p := by
  rw [lowerQuantile_map_eq_exp_lowerQuantile_map_log hD hpos hp0 hp1]
  exact Real.exp_pos _

end LogExp

end Conc

open Conc

/-! ### Quantiles of LFPP distances -/

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {κ : Rd d → ℝ} {a b : ℝ} {X : Rd d → Ω → ℝ}

section DistOn

variable {V : Set (Rd d)} {x y : Rd d}

/-- The internal distance between distinct points of a convex set is positive for every `ω`. -/
theorem IsBandVersion.lfppDistOn_pos (hX : IsBandVersion P W κ a b X) (ξ : ℝ)
    (hVc : Convex ℝ V) (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) (ω : Ω) :
    0 < lfppDistOn ξ (fun z => X z ω) V x y :=
  HigherDimLFPP.lfppDistOn_pos (hX.continuous ω) hxy (PcwJoined.of_convex hVc hx hy)

/-- **Quantiles of `log D` are close to `E log D`** (DGZ, proof of Lemma 3.2; HA5 D3): for
`0 < a < b`, `v = log(b/a)`, `ξ > 0`, a bounded open convex `V` and `x ≠ y` in `V`,
`|log q_p(D) - E log D| ≤ quantileConst p · ξ √v` with `D = D^ξ_V(x, y)(X)`. -/
theorem IsBandVersion.abs_log_lowerQuantile_lfppDistOn_sub_le (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X)
    {ξ : ℝ} (hξ : 0 < ξ) (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVc : Convex ℝ V)
    (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    |Real.log (LQGMetric.lowerQuantile (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p) -
        ∫ ω, Real.log (lfppDistOn ξ (fun z => X z ω) V x y) ∂P| ≤
      quantileConst p.toReal * ξ * √(Real.log (b / a)) := by
  have := hW.isProbabilityMeasure
  have hDm := measurable_lfppDistOn hX.continuous hX.measurable hV ξ x y
  rw [log_lowerQuantile_map_eq hDm.aemeasurable (ae_of_all _ (hX.lfppDistOn_pos ξ hVc hx hy hxy))
    hp0 hp1]
  have hv : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).2 hab)
  set σ : ℝ := ξ * √(Real.log (b / a)) with hσdef
  have hσ : 0 < σ := mul_pos hξ (Real.sqrt_pos.2 hv)
  have hσsq : 2 * σ ^ 2 = 2 * ξ ^ 2 * Real.log (b / a) := by
    rw [hσdef, mul_pow, Real.sq_sqrt hv.le]
    ring
  have h := abs_lowerQuantile_sub_le_of_tail hDm.log.aemeasurable hσ (fun t ht => by
    rw [hσsq]
    exact hX.measure_abs_log_lfppDistOn_sub_ge_le hκ hW ha hab.le ξ hVb hx y ht) hp0 hp1
  calc _ ≤ σ * quantileConst p.toReal := h
    _ = quantileConst p.toReal * ξ * √(Real.log (b / a)) := by rw [hσdef]; ring

/-- **DGZ Lemma 3.2** (HA5 D3): for two levels `p₁, p₂ ∈ (0,1)`,
`|log q_{p₁}(D) - log q_{p₂}(D)| ≤ (quantileConst p₁ + quantileConst p₂) ξ √(log(b/a))`. -/
theorem IsBandVersion.abs_log_lowerQuantile_lfppDistOn_sub_log_lowerQuantile_le
    (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b)
    (hX : IsBandVersion P W κ a b X) {ξ : ℝ} (hξ : 0 < ξ) (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hVc : Convex ℝ V) (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    {p₁ p₂ : ℝ≥0∞} (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1) :
    |Real.log (LQGMetric.lowerQuantile (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₁) -
        Real.log (LQGMetric.lowerQuantile
          (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₂)| ≤
      (quantileConst p₁.toReal + quantileConst p₂.toReal) * ξ * √(Real.log (b / a)) := by
  have h₁ := hX.abs_log_lowerQuantile_lfppDistOn_sub_le hκ hW ha hab hξ hV hVb hVc hx hy hxy
    hp₁0 hp₁1
  have h₂ := hX.abs_log_lowerQuantile_lfppDistOn_sub_le hκ hW ha hab hξ hV hVb hVc hx hy hxy
    hp₂0 hp₂1
  have e := abs_sub_le
    (Real.log (LQGMetric.lowerQuantile
      (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₁))
    (∫ ω, Real.log (lfppDistOn ξ (fun z => X z ω) V x y) ∂P)
    (Real.log (LQGMetric.lowerQuantile
      (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₂))
  rw [abs_sub_comm (∫ ω, Real.log (lfppDistOn ξ (fun z => X z ω) V x y) ∂P)] at e
  calc _ ≤ _ := e
    _ ≤ quantileConst p₁.toReal * ξ * √(Real.log (b / a)) +
          quantileConst p₂.toReal * ξ * √(Real.log (b / a)) := add_le_add h₁ h₂
    _ = (quantileConst p₁.toReal + quantileConst p₂.toReal) * ξ * √(Real.log (b / a)) := by
        ring

/-- **DGZ Lemma 3.2, multiplicative form**: `q_{p₂}(D) ≤ e^{C ξ √(log(b/a))} q_{p₁}(D)` with
`C = quantileConst p₁ + quantileConst p₂` (and symmetrically). -/
theorem IsBandVersion.lowerQuantile_lfppDistOn_le_exp_mul (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X)
    {ξ : ℝ} (hξ : 0 < ξ) (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVc : Convex ℝ V)
    (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) {p₁ p₂ : ℝ≥0∞} (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1)
    (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1) :
    LQGMetric.lowerQuantile (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₂ ≤
      Real.exp ((quantileConst p₁.toReal + quantileConst p₂.toReal) * ξ *
          √(Real.log (b / a))) *
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistOn ξ (fun z => X z ω) V x y) p₁ := by
  have := hW.isProbabilityMeasure
  have hDm := measurable_lfppDistOn hX.continuous hX.measurable hV ξ x y
  have hpos := ae_of_all P (hX.lfppDistOn_pos ξ hVc hx hy hxy)
  have hq₁ := lowerQuantile_map_pos hDm.aemeasurable hpos hp₁0 hp₁1
  have hq₂ := lowerQuantile_map_pos hDm.aemeasurable hpos hp₂0 hp₂1
  have h := hX.abs_log_lowerQuantile_lfppDistOn_sub_log_lowerQuantile_le hκ hW ha hab hξ hV hVb
    hVc hx hy hxy hp₁0 hp₁1 hp₂0 hp₂1
  rw [abs_sub_comm] at h
  have h2 := (abs_le.1 h).2
  rw [← Real.exp_le_exp, Real.exp_sub, Real.exp_log hq₂, Real.exp_log hq₁,
    div_le_iff₀ hq₁] at h2
  exact h2

end DistOn

/-! ### The frozen LFPP distance -/

section Frozen

/-- `|log q_p(D^ξ(X)) - E log D^ξ(X)| ≤ quantileConst p · ξ √(log(b/a))` (`d ≥ 1`). -/
theorem IsBandVersion.abs_log_lowerQuantile_lfppDistance_sub_le (hd : 0 < d)
    (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b)
    (hX : IsBandVersion P W κ a b X) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ≥0∞} (hp0 : 0 < p)
    (hp1 : p < 1) :
    |Real.log (LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => X z ω)) p) -
        ∫ ω, Real.log (lfppDistance d ξ (fun z => X z ω)) ∂P| ≤
      quantileConst p.toReal * ξ * √(Real.log (b / a)) := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact hX.abs_log_lowerQuantile_lfppDistOn_sub_le hκ hW ha hab hξ (isOpen_cube d)
    (isBounded_cube d) (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d) (e₁_ne_zero hd).symm
    hp0 hp1

/-- **DGZ Lemma 3.2 for the frozen distance, multiplicative form** (`d ≥ 1`). -/
theorem IsBandVersion.lowerQuantile_lfppDistance_le_exp_mul (hd : 0 < d) (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X)
    {ξ : ℝ} (hξ : 0 < ξ) {p₁ p₂ : ℝ≥0∞} (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂)
    (hp₂1 : p₂ < 1) :
    LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => X z ω)) p₂ ≤
      Real.exp ((quantileConst p₁.toReal + quantileConst p₂.toReal) * ξ *
          √(Real.log (b / a))) *
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => X z ω)) p₁ := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact hX.lowerQuantile_lfppDistOn_le_exp_mul hκ hW ha hab hξ (isOpen_cube d) (isBounded_cube d)
    (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d) (e₁_ne_zero hd).symm hp₁0 hp₁1 hp₂0 hp₂1

end Frozen

end HigherDimLFPP
