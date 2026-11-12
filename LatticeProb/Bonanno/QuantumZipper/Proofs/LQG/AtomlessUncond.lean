/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AtomlessUncond at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
* (1) `ae_noAtoms_free'`, `ae_noAtoms_zField'`, `ae_noAtoms_add_ofFun'`: the M4-P5 results of
  `Atomless.lean` with the hypothesis `LogSingNoAtom` discharged by `LogSing.logSingNoAtom`.
* (2) `ae_gamma0_logSingularity`: for `κ ∈ (0,4)`, `γ = √κ`, the field `ofFun (h0rev κ) + X` has
  a.s. a global vague limit of its boundary approximations, equal to `|t| · ν_X` (restricted to
  `ℝ \ {0}`), with no atom at `0` (strength `α = −2/γ < Q` at `s = 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AtomlessUncond

open LogSing GoodSample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### (1) Unconditional atomlessness -/

/-! ### (2) The `Γ⁰` field -/

/-! ### (3) Interior log singularities (area) -/

/-- The area density factor `max(2^{-k}, ‖w − z‖)^{−αγ}` (written with `2γ` to reuse `LogSing`). -/
def logFactorA (γ α : ℝ) (z : ℂ) (k : ℕ) (w : ℂ) : ℝ :=
  max (radius k) ‖w - z‖ ^ (-(α * (2 * γ) / 2))

theorem continuous_logFactorA (γ α : ℝ) (z : ℂ) (k : ℕ) : Continuous (logFactorA γ α z k) := by
  unfold logFactorA
  exact (continuous_const.max (continuous_id.sub continuous_const).norm).rpow_const
    fun w => Or.inl (lt_max_of_lt_left (radius_pos k)).ne'

/-! ### (3b) Global vague convergence on an open `U ∋ z` from `U \ {z}` and tightness at `z` -/

/-- Radial cut-off vanishing on `‖w − z‖ ≤ 1/(j+1)`, equal to `1` on `‖w − z‖ ≥ 2/(j+1)`. -/
def cutC (z : ℂ) (j : ℕ) (w : ℂ) : ℝ := max 0 (min 1 (((j : ℝ) + 1) * dist w z - 1))

/-- Radial trapezoid, `1` on `‖w − z‖ ≤ δ/2`, `0` on `‖w − z‖ ≥ δ`. -/
def trapC (z : ℂ) (δ : ℝ) (w : ℂ) : ℝ := max 0 (min 1 (2 * (δ - dist w z) / δ))

section CutC

variable {z : ℂ} {j : ℕ} {w : ℂ}

theorem continuous_cutC : Continuous (cutC z j) := by
  unfold cutC; exact continuous_const.max (continuous_const.min
    ((continuous_const.mul (continuous_id.dist continuous_const)).sub continuous_const))

theorem cutC_nonneg : 0 ≤ cutC z j w := le_max_left _ _

theorem cutC_le_one : cutC z j w ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutC_eq_zero (h : dist w z ≤ 1 / ((j : ℝ) + 1)) : cutC z j w = 0 := by
  unfold cutC
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left h hj.le
  rw [mul_one_div_cancel hj.ne'] at this
  exact max_eq_left (min_le_of_right_le (by linarith))

theorem cutC_eq_one (h : 2 / ((j : ℝ) + 1) ≤ dist w z) : cutC z j w = 1 := by
  unfold cutC
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have : 2 ≤ ((j : ℝ) + 1) * dist w z := by rw [div_le_iff₀ hj] at h; linarith
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutC_mono (z w : ℂ) : Monotone fun j => cutC z j w := by
  intro i j hij
  have h1 : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  have : ((i : ℝ) + 1) * dist w z ≤ ((j : ℝ) + 1) * dist w z :=
    mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

theorem tsupport_cutC_subset (z : ℂ) (j : ℕ) :
    tsupport (cutC z j) ⊆ {w | 1 / ((j : ℝ) + 1) ≤ dist w z} :=
  closure_minimal (fun w hw => by
    by_contra h
    exact hw (cutC_eq_zero (not_le.1 h).le))
    (isClosed_le continuous_const (continuous_id.dist continuous_const))

theorem continuous_trapC (z : ℂ) (δ : ℝ) : Continuous (trapC z δ) := by
  unfold trapC
  exact continuous_const.max (continuous_const.min
    ((continuous_const.mul (continuous_const.sub (continuous_id.dist continuous_const))).div_const
      _))

theorem trapC_nonneg {δ : ℝ} : 0 ≤ trapC z δ w := le_max_left _ _

theorem trapC_le_one {δ : ℝ} : trapC z δ w ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem trapC_eq_one {δ : ℝ} (hδ : 0 < δ) (h : dist w z ≤ δ / 2) : trapC z δ w = 1 := by
  unfold trapC
  have : 1 ≤ 2 * (δ - dist w z) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem trapC_eq_zero {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ dist w z) : trapC z δ w = 0 := by
  unfold trapC
  have : 2 * (δ - dist w z) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left (min_le_of_right_le this)

theorem tsupport_trapC_subset {δ : ℝ} (hδ : 0 < δ) :
    tsupport (trapC z δ) ⊆ Metric.closedBall z δ :=
  closure_minimal (fun w hw => by
    by_contra h
    exact hw (trapC_eq_zero hδ (le_of_lt (not_le.1 h))))
    Metric.isClosed_closedBall

end CutC

theorem integrable_of_finite_tsupport {μ : Measure ℂ} {h : ℂ → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) (hfin : μ (tsupport h) < ⊤) : Integrable h μ :=
  integrable_of_tsupport (U := tsupport h)
    (fun K _ hK => (measure_mono hK).trans_lt hfin) hh hhc subset_rfl

/-- The limit has mass at most `ε` near `z` if the approximations eventually do. -/
theorem measure_closedBall_le_of_tight {U : Set ℂ} {z : ℂ} {νs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hloc : IsVagueLimitOn (U \ {z}) νs μ)
    (hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, νs k K < ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδU : Metric.closedBall z δ ⊆ U) {ε : ℝ≥0∞}
    (hε : ∀ᶠ k in atTop, νs k (Metric.ball z δ) ≤ ε) :
    μ (Metric.closedBall z (δ / 2)) ≤ ε := by
  have hs0 : μ {z} = 0 := measure_mono_null (by intro w hw hw'; exact hw'.2 hw) hloc.1
  set h : ℕ → ℂ → ℝ := fun j w => trapC z δ w * cutC z j w with hhdef
  have hhc : ∀ j, Continuous (h j) := fun j => (continuous_trapC z δ).mul continuous_cutC
  have hts : ∀ j, tsupport (h j) ⊆ Metric.closedBall z δ ∩ {w | 1 / ((j : ℝ) + 1) ≤ dist w z} :=
    fun j => subset_inter ((tsupport_mul_subset_left).trans (tsupport_trapC_subset hδ))
      ((tsupport_mul_subset_right).trans (tsupport_cutC_subset z j))
  have hhcs : ∀ j, HasCompactSupport (h j) := fun j =>
    (isCompact_closedBall z δ).of_isClosed_subset (isClosed_tsupport _)
      ((hts j).trans inter_subset_left)
  have hhU : ∀ j, tsupport (h j) ⊆ U \ {z} := fun j w hw => by
    have h1 := hts j hw
    refine ⟨hδU h1.1, fun hwz => ?_⟩
    have h2 := h1.2
    rw [mem_setOf_eq, mem_singleton_iff.1 hwz, dist_self] at h2
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hh0 : ∀ j w, 0 ≤ h j w := fun j w => mul_nonneg trapC_nonneg cutC_nonneg
  have hball : ∀ j w, ENNReal.ofReal (h j w) ≤ (Metric.ball z δ).indicator 1 w := by
    intro j w
    by_cases hw : dist w z < δ
    · rw [indicator_of_mem (Metric.mem_ball.2 hw), Pi.one_apply, ENNReal.ofReal_le_one]
      exact mul_le_one₀ trapC_le_one cutC_nonneg cutC_le_one
    · simp only [hhdef, trapC_eq_zero hδ (not_lt.1 hw), zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  have hj : ∀ j, ∫⁻ w, ENNReal.ofReal (h j w) ∂μ ≤ ε := by
    intro j
    have hint : Integrable (h j) μ := integrable_of_tsupport hloc.2.1 (hhc j) (hhcs j) (hhU j)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hh0 j))]
    have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (hloc.2.2 _ (hhc j) (hhcs j) (hhU j))
    refine le_of_tendsto hlim ?_
    filter_upwards [hε, hfin _ (hhcs j) ((hhU j).trans diff_subset)] with k hk hkf
    simp only [Function.comp]
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_of_finite_tsupport (hhc j) (hhcs j) hkf)
      (ae_of_all _ (hh0 j))]
    calc ∫⁻ w, ENNReal.ofReal (h j w) ∂νs k
        ≤ ∫⁻ w, (Metric.ball z δ).indicator 1 w ∂νs k := lintegral_mono (hball j)
      _ = νs k (Metric.ball z δ) := lintegral_indicator_one Metric.isOpen_ball.measurableSet
      _ ≤ ε := hk
  have hmono : Monotone fun j w => ENNReal.ofReal (h j w) := by
    intro i j hij w
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (cutC_mono z w hij) trapC_nonneg)
  have htrap : ∫⁻ w, ENNReal.ofReal (trapC z δ w) ∂μ ≤ ε := by
    calc ∫⁻ w, ENNReal.ofReal (trapC z δ w) ∂μ
        ≤ ∫⁻ w, ⨆ j, ENNReal.ofReal (h j w) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0] with w hw
          have hwz : 0 < dist w z := dist_pos.2 hw
          obtain ⟨j, hj⟩ := LogSing.exists_cutS_lt hwz
          refine le_iSup_of_le j (le_of_eq ?_)
          simp only [hhdef, cutC_eq_one hj.le, mul_one]
      _ = ⨆ j, ∫⁻ w, ENNReal.ofReal (h j w) ∂μ :=
          lintegral_iSup (fun j => ((hhc j).measurable).ennreal_ofReal) hmono
      _ ≤ ε := iSup_le hj
  calc μ (Metric.closedBall z (δ / 2))
      = ∫⁻ w, (Metric.closedBall z (δ / 2)).indicator 1 w ∂μ :=
        (lintegral_indicator_one Metric.isClosed_closedBall.measurableSet).symm
    _ ≤ ∫⁻ w, ENNReal.ofReal (trapC z δ w) ∂μ := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ Metric.closedBall z (δ / 2)
        · rw [indicator_of_mem hw, Pi.one_apply, trapC_eq_one hδ (Metric.mem_closedBall.1 hw),
            ENNReal.ofReal_one]
        · rw [indicator_of_notMem hw]; exact zero_le
    _ ≤ ε := htrap

theorem abs_integral_sub_mul_cutC_le {μ : Measure ℂ} {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfin : μ (tsupport f) < ⊤) {M : ℝ} (hM : ∀ w, ‖f w‖ ≤ M)
    {z : ℂ} {δ : ℝ} {j : ℕ} (hj : 2 / ((j : ℝ) + 1) < δ / 2) {ε' : ℝ} (hε' : 0 ≤ ε')
    (hμ : μ (Metric.closedBall z (δ / 2)) ≤ ENNReal.ofReal ε') :
    |∫ w, f w ∂μ - ∫ w, f w * cutC z j w ∂μ| ≤ |M| * ε' := by
  have hfi := integrable_of_finite_tsupport hf hfc hfin
  have hgi : Integrable (fun w => f w * cutC z j w) μ :=
    integrable_of_finite_tsupport (hf.mul continuous_cutC) hfc.mul_right
      ((measure_mono (tsupport_mul_subset_left)).trans_lt hfin)
  rw [← integral_sub (f := f) (g := fun w => f w * cutC z j w) hfi hgi]
  set A := Metric.closedBall z (δ / 2) with hA
  have hAf : μ A < ⊤ := hμ.trans_lt ENNReal.ofReal_lt_top
  have hpt : ∀ w, ‖f w - f w * cutC z j w‖ ≤ A.indicator (fun _ => |M|) w := by
    intro w
    have hfM : |f w| ≤ |M| := (by simpa using hM w : |f w| ≤ M).trans (le_abs_self M)
    by_cases hw : w ∈ A
    · rw [indicator_of_mem hw, Real.norm_eq_abs,
        show f w - f w * cutC z j w = f w * (1 - cutC z j w) by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.2 cutC_le_one)]
      calc |f w| * (1 - cutC z j w) ≤ |f w| * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [(cutC_nonneg : 0 ≤ cutC z j w)])
              (abs_nonneg _)
        _ ≤ |M| := by rw [mul_one]; exact hfM
    · rw [indicator_of_notMem hw]
      have h2 : 2 / ((j : ℝ) + 1) ≤ dist w z := by
        have := not_le.1 (fun h => hw (Metric.mem_closedBall.2 h))
        linarith
      rw [cutC_eq_one h2]; simp
  have hint : Integrable (A.indicator fun _ => |M|) μ :=
    (integrableOn_const hAf.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  calc |∫ w, (f w - f w * cutC z j w) ∂μ| = ‖∫ w, (f w - f w * cutC z j w) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ w, A.indicator (fun _ => |M|) w ∂μ := norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
    _ = μ.real A * |M| := by
        rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, smul_eq_mul]
    _ ≤ ε' * |M| := mul_le_mul_of_nonneg_right
        (by rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hε' hμ) (abs_nonneg _)
    _ = |M| * ε' := mul_comm _ _

/-- **Global vague convergence on `U`** from vague convergence on `U \ {z}` and eventual
uniform smallness of the approximations near `z`. -/
theorem isVagueLimitOn_of_local_of_tight {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (hloc : IsVagueLimitOn (U \ {z}) νs μ)
    (hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, νs k K < ⊤)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop,
      νs k (Metric.ball z δ) ≤ ENNReal.ofReal ε) :
    IsVagueLimitOn U νs μ := by
  obtain ⟨δ0, hδ0, hδ0U⟩ := Metric.isOpen_iff.1 hU z hz
  have hsm : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, Metric.closedBall z δ ⊆ U ∧
      (∀ᶠ k in atTop, νs k (Metric.ball z δ) ≤ ENNReal.ofReal ε) ∧
      μ (Metric.closedBall z (δ / 2)) ≤ ENNReal.ofReal ε := fun ε hε => by
    obtain ⟨δ1, hδ1, h⟩ := htight ε hε
    set δ := min δ1 (δ0 / 2) with hδdef
    have hδ : 0 < δ := lt_min hδ1 (by linarith)
    have hδU : Metric.closedBall z δ ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith [min_le_right δ1 (δ0 / 2)])).trans hδ0U
    have h' : ∀ᶠ k in atTop, νs k (Metric.ball z δ) ≤ ENNReal.ofReal ε :=
      h.mono fun k hk => (measure_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hk
    exact ⟨δ, hδ, hδU, h', measure_closedBall_le_of_tight hloc hfin hδ hδU h'⟩
  refine ⟨measure_mono_null (compl_subset_compl.2 diff_subset) hloc.1, fun K hK hKU => ?_,
    fun f hf hfc hfU => ?_⟩
  · obtain ⟨δ, hδ, -, -, hμ⟩ := hsm 1 one_pos
    have h1 : K ⊆ (K \ Metric.ball z (δ / 2)) ∪ Metric.closedBall z (δ / 2) := fun w hw => by
      by_cases h : w ∈ Metric.ball z (δ / 2)
      · exact Or.inr (Metric.ball_subset_closedBall h)
      · exact Or.inl ⟨hw, h⟩
    refine (measure_mono h1).trans_lt ((measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨?_, hμ.trans_lt ENNReal.ofReal_lt_top⟩))
    refine hloc.2.1 _ (hK.diff Metric.isOpen_ball) fun w hw => ⟨hKU hw.1, fun hwz => hw.2 ?_⟩
    rw [mem_singleton_iff.1 hwz]; exact Metric.mem_ball_self (by linarith)
  · have hKf : μ (tsupport f) < ⊤ := by
      obtain ⟨δ, hδ, -, -, hμ⟩ := hsm 1 one_pos
      have h1 : tsupport f ⊆ (tsupport f \ Metric.ball z (δ / 2)) ∪ Metric.closedBall z (δ / 2) :=
        fun w hw => by
          by_cases h : w ∈ Metric.ball z (δ / 2)
          · exact Or.inr (Metric.ball_subset_closedBall h)
          · exact Or.inl ⟨hw, h⟩
      refine (measure_mono h1).trans_lt ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.2 ⟨?_, hμ.trans_lt ENNReal.ofReal_lt_top⟩))
      refine hloc.2.1 _ (hfc.diff Metric.isOpen_ball) fun w hw => ⟨hfU hw.1, fun hwz => hw.2 ?_⟩
      rw [mem_singleton_iff.1 hwz]; exact Metric.mem_ball_self (by linarith)
    obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' := ε / (4 * (|M| + 1)) with hε'def
    have hε' : 0 < ε' := by positivity
    have hMε : |M| * ε' ≤ ε / 4 := by
      rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg M]
    obtain ⟨δ, hδ, hδU, hk, hμ⟩ := hsm ε' hε'
    obtain ⟨j, hj⟩ := LogSing.exists_cutS_lt (by linarith : 0 < δ / 2)
    have hgU : tsupport (fun w => f w * cutC z j w) ⊆ U \ {z} := by
      intro w hw
      refine ⟨hfU (tsupport_mul_subset_left hw), fun hwz => ?_⟩
      have := tsupport_cutC_subset z j (tsupport_mul_subset_right hw)
      rw [mem_setOf_eq, mem_singleton_iff.1 hwz, dist_self] at this
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    have hconv := hloc.2.2 (fun w => f w * cutC z j w) (hf.mul continuous_cutC) hfc.mul_right hgU
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconv (ε / 2) (by positivity)
    obtain ⟨N', hN'⟩ := (hk.and (hfin _ hfc hfU)).exists_forall_of_atTop
    refine ⟨max N N', fun k hkN => ?_⟩
    obtain ⟨hk1, hk2⟩ := hN' k ((le_max_right _ _).trans hkN)
    have e1 := abs_integral_sub_mul_cutC_le (μ := νs k) hf hfc hk2 hM hj hε'.le
      ((measure_mono (Metric.closedBall_subset_ball (by linarith))).trans hk1)
    have e2 := abs_integral_sub_mul_cutC_le (μ := μ) hf hfc hKf hM hj hε'.le hμ
    have e3 := hN k ((le_max_left _ _).trans hkN)
    rw [Real.dist_eq] at e3 ⊢
    calc |∫ w, f w ∂νs k - ∫ w, f w ∂μ|
        ≤ |∫ w, f w ∂νs k - ∫ w, f w * cutC z j w ∂νs k| +
          |∫ w, f w * cutC z j w ∂νs k - ∫ w, f w * cutC z j w ∂μ| +
          |∫ w, f w * cutC z j w ∂μ - ∫ w, f w ∂μ| := by
          have := abs_sub_le (∫ w, f w ∂νs k) (∫ w, f w * cutC z j w ∂νs k) (∫ w, f w ∂μ)
          have := abs_sub_le (∫ w, f w * cutC z j w ∂νs k) (∫ w, f w * cutC z j w ∂μ)
            (∫ w, f w ∂μ)
          linarith
      _ < ε / 4 + ε / 2 + ε / 4 := by
          rw [abs_sub_comm (∫ w, f w * cutC z j w ∂μ)]
          linarith
      _ = ε := by ring

/-! ### (3c) Eventual smallness near `z` from dyadic ball bounds -/

/-- The dyadic ball `B̄(z, 2^{-n})`. -/
def annIC (z : ℂ) (n : ℕ) : Set ℂ := Metric.closedBall z (radius n)

/-- `T_n = sup_{k ≥ n} μ_k(B̄(z, 2^{-n}))`. -/
def annTC (νX : ℕ → Measure ℂ) (z : ℂ) (n : ℕ) : ℝ≥0∞ := ⨆ j, νX (j + n) (annIC z n)

theorem le_annTC (νX : ℕ → Measure ℂ) (z : ℂ) {n k : ℕ} (h : n ≤ k) :
    νX k (annIC z n) ≤ annTC νX z n :=
  le_iSup_of_le (k - n) (by rw [Nat.sub_add_cancel h])

theorem mem_annIC {z w : ℂ} {n : ℕ} (h : ‖w - z‖ ≤ radius n) : w ∈ annIC z n := by
  rw [annIC, Metric.mem_closedBall, dist_eq_norm]; exact h

theorem logFactorA_le_of_near {γ α : ℝ} (hγ : 0 < γ) {z w : ℂ} {k : ℕ}
    (h : ‖w - z‖ ≤ radius k) : logFactorA γ α z k w ≤ radius k ^ (-expB (2 * γ) α) := by
  unfold logFactorA
  rw [max_eq_left h]
  exact rpow_neg_le_of_le (by linarith) (radius_pos k) le_rfl (BdryExist.radius_le_one k)

theorem withDensity_logFactorA_le_near {γ α : ℝ} (hγ : 0 < γ) (z : ℂ) (μ : Measure ℂ) {k m : ℕ}
    (hkm : k ≤ m) :
    μ.withDensity (fun w => ENNReal.ofReal (logFactorA γ α z k w)) (Metric.ball z (radius m)) ≤
      ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * μ (Metric.ball z (radius m)) := by
  rw [withDensity_apply _ Metric.isOpen_ball.measurableSet, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun w hw =>
    ENNReal.ofReal_le_ofReal (logFactorA_le_of_near hγ ?_)
  rw [Metric.mem_ball, dist_eq_norm] at hw
  exact hw.le.trans (AreaExist.aradius_anti hkm)

theorem logFactorA_le_sum {γ α : ℝ} (hγ : 0 < γ) {z w : ℂ} {k m : ℕ} (hmk : m < k)
    (hw : ‖w - z‖ < radius m) :
    ENNReal.ofReal (logFactorA γ α z k w) ≤
      (∑ n ∈ Finset.Ico m k, annW (2 * γ) α n * (annIC z n).indicator 1 w) +
        ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * (annIC z k).indicator 1 w := by
  classical
  by_cases hd : ‖w - z‖ ≤ radius k
  · rw [indicator_of_mem (mem_annIC hd), Pi.one_apply, mul_one]
    exact le_add_left (ENNReal.ofReal_le_ofReal (logFactorA_le_of_near hγ hd))
  · push_neg at hd
    have hk1 : radius (k - 1 + 1) ≤ ‖w - z‖ := by
      rw [Nat.sub_add_cancel (by omega)]; exact hd.le
    have hex : ∃ n, radius (n + 1) ≤ ‖w - z‖ := ⟨k - 1, hk1⟩
    set n := Nat.find hex with hn
    have hn1 : radius (n + 1) ≤ ‖w - z‖ := Nat.find_spec hex
    have hnk : n < k := by
      have := Nat.find_min' hex hk1
      omega
    have hmn : m ≤ n := by
      by_contra h
      push_neg at h
      have := AreaExist.aradius_anti (show n + 1 ≤ m by omega)
      linarith
    have hdn : ‖w - z‖ ≤ radius n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, radius_zero']; linarith [BdryExist.radius_le_one m]
      · have := Nat.find_min hex (show n - 1 < n by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact (not_le.1 this).le
    refine le_add_right (le_trans ?_ (Finset.single_le_sum (f := fun i =>
      annW (2 * γ) α i * (annIC z i).indicator 1 w) (fun i _ => zero_le)
      (Finset.mem_Ico.2 ⟨hmn, hnk⟩)))
    rw [indicator_of_mem (mem_annIC hdn), Pi.one_apply, mul_one]
    unfold annW logFactorA
    rw [max_eq_right hd.le]
    exact ENNReal.ofReal_le_ofReal (rpow_neg_le_of_le (by linarith) (radius_pos _) hn1
      (by linarith [BdryExist.radius_le_one m]))

theorem withDensity_logFactorA_le_far {γ α : ℝ} (hγ : 0 < γ) (z : ℂ) (μ : Measure ℂ) {k m : ℕ}
    (hmk : m < k) :
    μ.withDensity (fun w => ENNReal.ofReal (logFactorA γ α z k w)) (Metric.ball z (radius m)) ≤
      (∑ n ∈ Finset.Ico m k, annW (2 * γ) α n * μ (annIC z n)) +
        ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * μ (annIC z k) := by
  have hmeas : ∀ n, MeasurableSet (annIC z n) := fun n =>
    Metric.isClosed_closedBall.measurableSet
  have hg : Measurable fun w =>
      (∑ n ∈ Finset.Ico m k, annW (2 * γ) α n * (annIC z n).indicator 1 w) +
        ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * (annIC z k).indicator 1 w :=
    (Finset.measurable_sum _ fun n _ => (measurable_one.indicator (hmeas n)).const_mul _).add
      ((measurable_one.indicator (hmeas k)).const_mul _)
  rw [withDensity_apply _ Metric.isOpen_ball.measurableSet]
  calc ∫⁻ w in Metric.ball z (radius m), ENNReal.ofReal (logFactorA γ α z k w) ∂μ
      ≤ ∫⁻ w in Metric.ball z (radius m),
          ((∑ n ∈ Finset.Ico m k, annW (2 * γ) α n * (annIC z n).indicator 1 w) +
            ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * (annIC z k).indicator 1 w) ∂μ :=
        setLIntegral_mono hg fun w hw => logFactorA_le_sum hγ hmk
          (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw)
    _ ≤ ∫⁻ w, ((∑ n ∈ Finset.Ico m k, annW (2 * γ) α n * (annIC z n).indicator 1 w) +
            ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) * (annIC z k).indicator 1 w) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = _ := by
        rw [lintegral_add_left (Finset.measurable_sum _ fun n _ =>
            (measurable_one.indicator (hmeas n)).const_mul _),
          lintegral_finset_sum _ fun n _ => (measurable_one.indicator (hmeas n)).const_mul _,
          lintegral_const_mul _ (measurable_one.indicator (hmeas k)),
          lintegral_indicator_one (hmeas k)]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hmeas n)),
          lintegral_indicator_one (hmeas n)]

/-- **Eventual uniform smallness near `z`.** -/
theorem tight_of_balls {γ α : ℝ} (hγ : 0 < γ) {z : ℂ} {νX νY : ℕ → Measure ℂ} {K1 M1 : ℕ}
    (hid : ∀ k, K1 ≤ k → ∀ m, M1 ≤ m → νY k (Metric.ball z (radius m)) =
      (νX k).withDensity (fun w => ENNReal.ofReal (logFactorA γ α z k w))
        (Metric.ball z (radius m)))
    {N : ℕ} (hsum : ∑' n, annW (2 * γ) α (n + N) * annTC νX z (n + N) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop,
      νY k (Metric.ball z δ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  set a : ℕ → ℝ≥0∞ := fun n => annW (2 * γ) α n * annTC νX z n with ha
  set tail : ℕ → ℝ≥0∞ := fun i => ∑' j, a (j + i + N) with htail
  have hF1 : Tendsto tail atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun n => a (n + N)) hsum
    simpa only [htail] using this
  have hF2 : ∀ i k, i + N ≤ k → a k ≤ tail i := fun i k hik => by
    have := ENNReal.le_tsum (f := fun j => a (j + i + N)) (k - i - N)
    simpa only [show k - i - N + i + N = k by omega] using this
  have hF3 : ∀ i k, ∑ n ∈ Finset.Ico (i + N) k, a n ≤ tail i := fun i k => by
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (k - (i + N))))
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha]
    congr 2 <;> omega
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (radius k ^ (-expB (2 * γ) α)) with hc
  have hck : ∀ k, c k * νX k (annIC z k) ≤ a k := fun k =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (radius_rpow_mono (by linarith) α (Nat.le_succ k)))
      (le_annTC νX z le_rfl)
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by linarith)
  have hee : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
  have he : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  have hev1 : ∀ᶠ i in atTop, tail i ≤ ENNReal.ofReal (ε / 2) :=
    hF1.eventually (eventually_le_nhds hε2)
  obtain ⟨i0, hi0⟩ := hev1.exists
  obtain ⟨i1, hi1, hi1M, hi1'⟩ :=
    ((eventually_ge_atTop i0).and ((eventually_ge_atTop M1).and hev1)).exists
  refine ⟨radius (i1 + N), radius_pos _, ?_⟩
  filter_upwards [eventually_ge_atTop (max K1 (i0 + N))] with k hk
  have hkK : K1 ≤ k := (le_max_left _ _).trans hk
  have hk0 : i0 + N ≤ k := (le_max_right _ _).trans hk
  rw [hid k hkK (i1 + N) (by omega)]
  rcases lt_or_ge (i1 + N) k with hmk | hkm
  · calc (νX k).withDensity (fun w => ENNReal.ofReal (logFactorA γ α z k w))
          (Metric.ball z (radius (i1 + N)))
        ≤ (∑ n ∈ Finset.Ico (i1 + N) k, annW (2 * γ) α n * νX k (annIC z n)) +
            c k * νX k (annIC z k) := withDensity_logFactorA_le_far hγ z _ hmk
      _ ≤ (∑ n ∈ Finset.Ico (i1 + N) k, a n) + a k := by
          refine add_le_add (Finset.sum_le_sum fun n hn => ?_) (hck k)
          exact mul_le_mul_of_nonneg_left (le_annTC νX z (Finset.mem_Ico.1 hn).2.le) zero_le
      _ ≤ tail i1 + tail i1 := add_le_add (hF3 i1 k) (hF2 i1 k hmk.le)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hi1' hi1'
      _ = ENNReal.ofReal ε := hee
  · calc _ ≤ c k * νX k (Metric.ball z (radius (i1 + N))) :=
          withDensity_logFactorA_le_near (α := α) hγ z (νX k) hkm
      _ ≤ c k * νX k (annIC z k) := by
          refine mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le
          exact Metric.ball_subset_closedBall.trans
            (Metric.closedBall_subset_closedBall (AreaExist.aradius_anti hkm))
      _ ≤ a k := hck k
      _ ≤ tail i0 := hF2 i0 k hk0
      _ ≤ ENNReal.ofReal (ε / 2) := hi0
      _ ≤ ENNReal.ofReal ε := he

/-! ### (3d) The almost sure interior statement, under an area fractional-moment bound -/

/-- Generic Borel–Cantelli step: moment bounds with a geometric rate give a.s. a summable tail of
the weighted masses. -/
theorem ae_tsum_ne_top_of_moments [IsProbabilityMeasure P] {T : ℕ → Ω → ℝ≥0∞}
    (hT : ∀ n, Measurable (T n)) {b e p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hneg : b * p + e < 0)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {n₀ : ℕ}
    (hbd : ∀ n, n₀ ≤ n → ∫⁻ ω, T n ω ^ p ∂P ≤ C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * e))) :
    ∀ᵐ ω ∂P, ∃ N : ℕ,
      ∑' n, ENNReal.ofReal (radius (n + N + 1) ^ (-b)) * T (n + N) ω ≠ ⊤ := by
  set w : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (radius (n + 1) ^ (-b)) with hw
  set u : ℕ → ℝ := fun n => (radius (n + 1) ^ (-b)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _) (by positivity)
  have husum : Summable u := summable_annuli hp0.le hneg
  have hmeas : ∀ n, Measurable fun ω => (w (n + n₀) * T (n + n₀) ω) ^ p := fun n =>
    (measurable_const.mul (hT _)).pow_const p
  have hterm : ∀ n, ∫⁻ ω, (w (n + n₀) * T (n + n₀) ω) ^ p ∂P ≤
      C * ENNReal.ofReal (u (n + n₀)) := by
    intro n'
    set n := n' + n₀ with hn
    have hwp : w n ^ p = ENNReal.ofReal ((radius (n + 1) ^ (-b)) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (radius_pos _).le _) hp0.le
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hwp]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((radius (n + 1) ^ (-b)) ^ p) * ∫⁻ ω, T n ω ^ p ∂P
        ≤ ENNReal.ofReal ((radius (n + 1) ^ (-b)) ^ p) *
            (C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * e))) := by
          gcongr; exact hbd n (Nat.le_add_left _ _)
      _ = C * ENNReal.ofReal (u n) := by
          rw [hu, ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _)]
          ring
  have hsumE : ∑' n, ∫⁻ ω, (w (n + n₀) * T (n + n₀) ω) ^ p ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => hu0 _)
      ((summable_nat_add_iff n₀).2 husum)]
    exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂P, ∑' n, (w (n + n₀) * T (n + n₀) ω) ^ p < ⊤ := by
    refine ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (hmeas n).aemeasurable) ?_
    rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
    exact hsumE
  filter_upwards [hlt] with ω hω
  set bb : ℕ → ℝ≥0∞ := fun n => (w (n + n₀) * T (n + n₀) ω) ^ p with hbb
  have hb0 : Tendsto bb atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  obtain ⟨N, hN⟩ := (hb0.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
  refine ⟨N + n₀, ne_top_of_le_ne_top hω.ne ?_⟩
  calc ∑' n, ENNReal.ofReal (radius (n + (N + n₀) + 1) ^ (-b)) * T (n + (N + n₀)) ω
      ≤ ∑' n, bb (n + N) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← Nat.add_assoc]
        have h1 : bb (n + N) ≤ 1 := hN (n + N) (Nat.le_add_left _ _)
        have ha1 : w (n + N + n₀) * T (n + N + n₀) ω ≤ 1 := by
          by_contra h
          push_neg at h
          exact absurd h1 (not_le.2 (ENNReal.one_lt_rpow h hp0))
        calc w (n + N + n₀) * T (n + N + n₀) ω =
              (w (n + N + n₀) * T (n + N + n₀) ω) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
          _ ≤ bb (n + N) := ENNReal.rpow_le_rpow_of_exponent_ge ha1 hp1
    _ ≤ ∑' n, bb n := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N) bb

open AreaExist (aZ)

end AtomlessUncond
end QuantumZipper
