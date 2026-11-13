/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.MartingaleL2MaximalEnvelope at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleMaximal
import LatticeProb.Bonanno.ReflectedGMS.Limit.FiniteTimeMaximal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace ReflectedGMS

private noncomputable def finiteAbsMax
    {Ω : Type*} (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (range (n + 1)).sup' nonempty_range_add_one fun k => |M k ω|

private theorem finiteAbsMax_measurable
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {M : ℕ → Ω → ℝ} (hM : ∀ n, StronglyMeasurable (M n)) (n : ℕ) :
    Measurable (finiteAbsMax M n) := by
  apply measurable_range_sup''
  intro k _
  simpa only [Real.norm_eq_abs] using (hM k).norm.measurable

private theorem finiteAbsMax_nonneg
    {Ω : Type*} (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ finiteAbsMax M n ω := by
  apply le_trans (abs_nonneg (M 0 ω))
  exact le_sup' (fun k => |M k ω|) (mem_range.mpr (Nat.zero_lt_succ n))

private theorem finiteAbsMax_memLp_two
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {M : ℕ → Ω → ℝ} (hM : ∀ n, StronglyMeasurable (M n))
    (h2 : ∀ n, MemLp (M n) 2 P) (n : ℕ) :
    MemLp (finiteAbsMax M n) 2 P := by
  have hsum : MemLp (fun ω => ∑ k ∈ range (n + 1), |M k ω|) 2 P :=
    memLp_finsetSum (range (n + 1)) fun k _ => by
      simpa only [Real.norm_eq_abs] using (h2 k).norm
  refine MemLp.mono' (μ := P) hsum
    (finiteAbsMax_measurable hM n).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (finiteAbsMax_nonneg M n ω)]
  apply (sup'_le_iff nonempty_range_add_one (fun k => |M k ω|)).2
  intro k hk
  exact single_le_sum (fun i _ => abs_nonneg (M i ω)) hk

private theorem martingale_abs_submartingale
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) :
    Submartingale (fun t ω => |M t ω|) F P := by
  refine ⟨fun t => by simpa only [Real.norm_eq_abs] using
      (hM.stronglyMeasurable t).norm, ?_, fun t => by
        simpa only [Real.norm_eq_abs] using ((h2 t).integrable (by norm_num)).norm⟩
  intro i j hij
  filter_upwards [abs_condExp_ae_le_condExp_abs (m := F i) (M j),
    hM.condExp_ae_eq hij] with ω habs hm
  dsimp at habs hm ⊢
  rw [hm] at habs
  exact habs

theorem martingale_abs_discrete_maximal_integral_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℕ mΩ}
    {M : ℕ → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (n : ℕ) :
    ∫ ω, (finiteAbsMax M n ω) ^ 2 ∂P ≤
      4 * ∫ ω, (M n ω) ^ 2 ∂P := by
  let Y := finiteAbsMax M n
  let X := fun ω => |M n ω|
  have hMsm : ∀ k, StronglyMeasurable (M k) := fun k =>
    (hM.stronglyMeasurable k).mono (F.le k)
  have hYm : Measurable Y := finiteAbsMax_measurable hMsm n
  have hY0 : 0 ≤ Y := fun ω => finiteAbsMax_nonneg M n ω
  have hY2 : MemLp Y 2 P := finiteAbsMax_memLp_two hMsm h2 n
  have hXi : Integrable X P := by
    simpa only [X, Real.norm_eq_abs] using ((h2 n).integrable (by norm_num)).norm
  let ν : Measure Ω := P.withDensity fun ω => ENNReal.ofReal (X ω)
  have hν (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal t * P {ω | t ≤ Y ω} ≤ ν {ω | t ≤ Y ω} := by
    let ε : ℝ≥0 := t.toNNReal
    have he : (ε : ℝ) = t := Real.coe_toNNReal t ht.le
    have hb := maximal_ineq (martingale_abs_submartingale hM h2)
      (fun _ _ => abs_nonneg _) (ε := ε) n
    change (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ Y ω} ≤ _ at hb
    rw [he] at hb
    rw [show (ε : ℝ≥0∞) = ENNReal.ofReal t by rfl] at hb
    refine hb.trans_eq ?_
    rw [withDensity_apply _ (measurableSet_le measurable_const hYm)]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hXi.integrableOn) (Eventually.of_forall fun _ => abs_nonneg _)]
    rfl
  have htail :
      ∫⁻ t in Ioi (0 : ℝ), P {ω | t ≤ Y ω} * ENNReal.ofReal t ≤
        ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ Y ω} := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simpa only [mul_comm] using hν t ht
  have hlayerY := lintegral_rpow_eq_lintegral_meas_le_mul P
    (Eventually.of_forall hY0) hYm.aemeasurable
      (p_pos := (by norm_num : (0 : ℝ) < 2))
  have hlayerν := lintegral_rpow_eq_lintegral_meas_le_mul ν
    (Eventually.of_forall hY0) hYm.aemeasurable
      (p_pos := (by norm_num : (0 : ℝ) < 1))
  have hlin :
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ (2 : ℝ)) ∂P ≤
        ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂P := by
    rw [hlayerY]
    calc
      ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ), P {ω | t ≤ Y ω} *
          ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) ≤
          ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ Y ω} := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
          (mul_le_mul le_rfl htail (by positivity) (by positivity))
      _ = _ := by
        congr 1
        have htν : (∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ Y ω}) =
            ∫⁻ ω, ENNReal.ofReal (Y ω ^ (1 : ℝ)) ∂ν := by
          rw [hlayerν]
          norm_num
        rw [htν]
        simp only [Real.rpow_one]
        rw [lintegral_withDensity_eq_lintegral_mul₀
          hXi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          hYm.aemeasurable.ennreal_ofReal]
        congr 1
        funext ω
        rw [Pi.mul_apply, ← ENNReal.ofReal_mul (abs_nonneg (M n ω))]
  have hYsq_int : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
  have hX2 : MemLp X 2 P := by
    simpa only [X, Real.norm_eq_abs] using (h2 n).norm
  have hXsq_int : Integrable (fun ω => X ω ^ 2) P := hX2.integrable_sq
  have hXY_int : Integrable (fun ω => X ω * Y ω) P := by
    change Integrable (X * Y) P
    exact hX2.integrable_mul hY2
  have hreal : ∫ ω, Y ω ^ 2 ∂P ≤ 2 * ∫ ω, X ω * Y ω ∂P := by
    have hR0 : 0 ≤ 2 * ∫ ω, X ω * Y ω ∂P :=
      mul_nonneg (by norm_num) (integral_nonneg_of_ae
        (Eventually.of_forall fun ω => mul_nonneg (abs_nonneg _) (hY0 ω)))
    rw [← ENNReal.ofReal_le_ofReal_iff hR0]
    rw [ofReal_integral_eq_lintegral_ofReal hYsq_int
      (Eventually.of_forall fun ω => sq_nonneg (Y ω))]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [ofReal_integral_eq_lintegral_ofReal hXY_int
      (Eventually.of_forall fun ω => mul_nonneg (abs_nonneg _) (hY0 ω))]
    simpa only [Real.rpow_two] using hlin
  have hyoung : ∀ ω, 2 * (X ω * Y ω) ≤ (Y ω) ^ 2 / 2 + 2 * (X ω) ^ 2 := by
    intro ω
    nlinarith [sq_nonneg (Y ω - 2 * X ω)]
  have hint : 2 * ∫ ω, X ω * Y ω ∂P ≤
      (∫ ω, Y ω ^ 2 ∂P) / 2 + 2 * ∫ ω, X ω ^ 2 ∂P := by
    rw [← integral_const_mul]
    calc
      ∫ ω, 2 * (X ω * Y ω) ∂P ≤
          ∫ ω, (Y ω) ^ 2 / 2 + 2 * (X ω) ^ 2 ∂P :=
        integral_mono (hXY_int.const_mul 2)
          (hYsq_int.div_const 2 |>.add (hXsq_int.const_mul 2)) hyoung
      _ = _ := by
        rw [integral_add (hYsq_int.div_const 2) (hXsq_int.const_mul 2),
          integral_div, integral_const_mul]
  dsimp only [Y, X] at hreal hint ⊢
  have hx : (fun ω => |M n ω| ^ 2) = fun ω => (M n ω) ^ 2 := by
    funext ω
    exact sq_abs (M n ω)
  rw [hx] at hint
  linarith

/-- Strong Doob L² inequality along a finite monotone grid. -/
theorem martingale_abs_grid_maximal_integral_le
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (τ : ℕ → ι) (hτ : Monotone τ) (n : ℕ) :
    ∫ ω, ((range (n + 1)).sup' nonempty_range_add_one
      (fun k => |M (τ k) ω|)) ^ 2 ∂P ≤
      4 * ∫ ω, (M (τ n) ω) ^ 2 ∂P := by
  let G : Filtration ℕ mΩ := ReflectedGMS.MartingaleLimit.sampledFiltration F τ hτ
  have hMs : Martingale (fun k => M (τ k)) G P :=
    ⟨fun k => hM.1 (τ k), fun i j hij => hM.2 _ _ (hτ hij)⟩
  simpa only [finiteAbsMax] using
    martingale_abs_discrete_maximal_integral_le hMs (fun k => h2 (τ k)) n

/-- Strong Doob L² inequality on an unordered finite set of observation times. -/
theorem martingale_abs_finset_maximal_integral_le
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [LinearOrder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (s : Finset ι) (T : ι)
    (hsT : ∀ t ∈ s, t ≤ T) :
    ∫ ω, ((insert T s).sup' (insert_nonempty T s) (fun t => |M t ω|)) ^ 2 ∂P ≤
      4 * ∫ ω, (M T ω) ^ 2 ∂P := by
  classical
  let S := insert T s
  have hS : S.Nonempty := insert_nonempty T s
  have hc : 0 < S.card := card_pos.mpr hS
  let τ : ℕ → ι := fun n => S.orderEmbOfFin rfl ⟨min n (S.card - 1), by omega⟩
  have hτ : Monotone τ := by
    intro i j hij
    exact (S.orderEmbOfFin rfl).monotone (min_le_min_right _ hij)
  have hτT : τ (S.card - 1) = T := by
    have he : τ (S.card - 1) = S.max' hS := by
      simpa only [τ, min_self] using S.orderEmbOfFin_last rfl hc
    rw [he]
    apply le_antisymm
    · apply max'_le
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact le_rfl
      · exact hsT t ht
    · exact le_max' _ _ (mem_insert_self T s)
  have hb := martingale_abs_grid_maximal_integral_le hM h2 τ hτ (S.card - 1)
  rw [hτT] at hb
  have heq : (fun ω => (range (S.card - 1 + 1)).sup' nonempty_range_add_one
      (fun k => |M (τ k) ω|)) =
      fun ω => S.sup' hS (fun t => |M t ω|) := by
    funext ω
    apply le_antisymm
    · apply (sup'_le_iff nonempty_range_add_one _).2
      intro k hk
      have hmem : τ k ∈ S :=
        S.orderEmbOfFin_mem rfl ⟨min k (S.card - 1), by omega⟩
      exact le_sup' (fun t => |M t ω|) hmem
    · apply (sup'_le_iff hS _).2
      intro t ht
      let i := (S.orderIsoOfFin rfl).symm ⟨t, ht⟩
      have hi : i.val < S.card := i.isLt
      have hτi : τ i.val = t := by
        have hmin : min i.val (S.card - 1) = i.val := min_eq_left (by omega)
        simp only [τ, hmin]
        exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨t, ht⟩)
      rw [← hτi]
      exact le_sup' (fun k => |M (τ k) ω|)
        (by simpa only [Nat.sub_add_cancel hc] using mem_range.mpr hi)
  change ∫ ω, ((fun ω => S.sup' hS (fun t => |M t ω|)) ω) ^ 2 ∂P ≤ _
  rw [← heq]
  exact hb

private theorem finsetAbsMax_memLp_two
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {M : ι → Ω → ℝ} (hM : ∀ t, StronglyMeasurable (M t))
    (h2 : ∀ t, MemLp (M t) 2 P) (s : Finset ι) (hs : s.Nonempty) :
    MemLp (fun ω => s.sup' hs (fun t => |M t ω|)) 2 P := by
  classical
  have hsum : MemLp (fun ω => ∑ t ∈ s, |M t ω|) 2 P :=
    memLp_finsetSum s fun t _ => by
      simpa only [Real.norm_eq_abs] using (h2 t).norm
  have hm : Measurable (fun ω => s.sup' hs (fun t => |M t ω|)) := by
    convert measurable_sup' hs (fun t _ => by simpa only [Real.norm_eq_abs] using
      (hM t).norm.measurable) using 1
    ext ω
    simp
  refine MemLp.mono' (μ := P) hsum
    hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have hnonneg : 0 ≤ s.sup' hs (fun t => |M t ω|) := by
    obtain ⟨t, ht⟩ := hs
    exact (abs_nonneg (M t ω)).trans (le_sup' (fun t => |M t ω|) ht)
  rw [Real.norm_of_nonneg hnonneg]
  apply (sup'_le_iff hs _).2
  intro t ht
  exact single_le_sum (fun i _ => abs_nonneg (M i ω)) ht

end ReflectedGMS
