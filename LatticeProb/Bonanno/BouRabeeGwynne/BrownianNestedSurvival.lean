/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianNestedSurvival at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianBoundaryExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.SkeletonSurvival

/-! Finite multiplicative collar survival for the genuine concentric-ball
excursions extracted from one Brownian path. Endpoint guards are proved almost
surely from the actual excursion kernels, and removed from the final event. -/

open MeasureTheory ProbabilityTheory Set Metric Preorder
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne

def nestedBrownianBall {d : ℕ} (p : Euc d) (r R : ℝ) (i : ℕ) : Set (Euc d) :=
  ball p (R * (r * R ^ i))

private def nestedExcursionValid {d : ℕ} (p : Euc d) (r R : ℝ) (i : ℕ) :
    Set (Bool × C(unitInterval, Euc d)) :=
  {e | e.1 = false ∧ e.2 1 ∈ closedBall p (R * (r * R ^ i))}

private lemma measurableSet_nestedExcursionValid {d : ℕ} (p : Euc d) (r R : ℝ)
    (i : ℕ) : MeasurableSet (nestedExcursionValid p r R i) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    (isClosed_closedBall.measurableSet.preimage
      ((ContinuousMap.measurable_eval 1).comp measurable_snd))

private noncomputable def nestedMarkedExcursionLaw {d : ℕ} (p : Euc d) (r R : ℝ)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (i : ℕ) (x : Euc d) :
    Measure (Bool × C(unitInterval, Euc d)) :=
  (brownianExcursionKernel (U := nestedBrownianBall p r R i) isOpen_ball μ x).map
    (fun f => (false, f))

private lemma nestedMarkedExcursionLaw_valid_compl {d : ℕ} (hd : 1 ≤ d)
    (p : Euc d) (r R : ℝ) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) (i : ℕ) {x : Euc d}
    (hx : x ∈ nestedBrownianBall p r R i) :
    nestedMarkedExcursionLaw p r R μ i x (nestedExcursionValid p r R i)ᶜ = 0 := by
  have hflag : Measurable (fun f : C(unitInterval, Euc d) => (false, f)) :=
    measurable_const.prodMk measurable_id
  have hAE : ∀ᵐ f ∂brownianExcursionKernel (U := nestedBrownianBall p r R i)
      isOpen_ball μ x, (false, f) ∈ nestedExcursionValid p r R i := by
    filter_upwards [brownianExcursionKernel_ae_mem_closure hd isOpen_ball isBounded_ball
      μ hμ hx] with f hf
    exact ⟨rfl, closure_ball_subset_closedBall (hf 1)⟩
  rw [nestedMarkedExcursionLaw, Measure.map_apply hflag
    (measurableSet_nestedExcursionValid p r R i).compl]
  exact ae_iff.mp hAE

private lemma nestedMarkedExcursionLaw_range {d : ℕ} (p : Euc d) (r R : ℝ)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (i : ℕ) (x : Euc d)
    {K : Set (Euc d)} (hK : IsClosed K) :
    nestedMarkedExcursionLaw p r R μ i x (Prod.snd ⁻¹' curveRangeEvent K) =
      brownianExcursionKernel (U := nestedBrownianBall p r R i) isOpen_ball μ x
        (curveRangeEvent K) := by
  have hflag : Measurable (fun f : C(unitInterval, Euc d) => (false, f)) :=
    measurable_const.prodMk measurable_id
  rw [nestedMarkedExcursionLaw, Measure.map_apply hflag
    ((isClosed_curveRangeEvent hK).measurableSet.preimage measurable_snd)]
  rfl

/-- The finite probability assembly uses only the actual one-step excursion
bound. All spatial endpoint guards are derived from genuine kernel support. -/
theorem brownian_nested_survival_le_of_step {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (p : Euc d) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    {x : Euc d} (hx : dist x p ≤ r) {K : Set (Euc d)} (hK : IsClosed K)
    (q : ℝ≥0∞) (N : ℕ)
    (hstep : ∀ i < N, ∀ y : Euc d, dist y p ≤ r * R ^ i →
      brownianExcursionKernel (U := nestedBrownianBall p r R i) isOpen_ball μ y
        (curveRangeEvent K) ≤ q) :
    μ {ω | ∀ i < N,
      (brownianSkeletonExcursion (nestedBrownianBall p r R) x 0
        (fun n _ => some n) i ω).2 ∈ curveRangeEvent K} ≤ q ^ N := by
  let : MeasurableSpace (Option ℕ) := ⊤
  let Z := Bool × C(unitInterval, Euc d)
  let V := nestedBrownianBall p r R
  let selector : ℕ → Euc d → Option ℕ := fun n _ => some n
  let μ₀ := brownianSkeletonInitialLaw V (fun _ => isOpen_ball) μ x 0
  let : IsProbabilityMeasure μ₀ := brownianSkeletonInitialLaw_isProbability
    (d := d) (J := ℕ) V (fun _ => isOpen_ball) μ x 0
  let κ := brownianSkeletonKernel V (fun _ => isOpen_ball) μ selector
    (fun _ => measurable_const)
  let : ∀ n, IsMarkovKernel (κ n) := fun n => brownianSkeletonKernel_isMarkov
    (d := d) (J := ℕ) V (fun _ => isOpen_ball) μ selector (fun _ => measurable_const) n
  let P := Kernel.trajMeasure (X := fun _ => Z) μ₀ κ
  let : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let valid : ℕ → Set Z := nestedExcursionValid p r R
  let C : Set Z := Prod.snd ⁻¹' curveRangeEvent K
  have hC : MeasurableSet C :=
    (isClosed_curveRangeEvent hK).measurableSet.preimage measurable_snd
  have hvalid (i : ℕ) : MeasurableSet (valid i) :=
    measurableSet_nestedExcursionValid p r R i
  have hscale (i : ℕ) : 0 < r * R ^ i := mul_pos hr (pow_pos (by linarith) i)
  have hinner (i : ℕ) {y : Euc d} (hy : dist y p ≤ r * R ^ i) : y ∈ V i := by
    change dist y p < R * (r * R ^ i)
    exact hy.trans_lt (by nlinarith [hscale i])
  have hinit : μ₀ = nestedMarkedExcursionLaw p r R μ 0 x := rfl
  have hkernel (n : ℕ) (h : Finset.Iic n → Z) (hh : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ valid n) :
      κ n h = nestedMarkedExcursionLaw p r R μ (n + 1)
        ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 1) := by
    change (if (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 then _ else _) = _
    rw [hh.1]
    rfl
  have hendpoint (n : ℕ) (h : Finset.Iic n → Z)
      (hh : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ valid n) :
      dist ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 1) p ≤ r * R ^ (n + 1) := by
    have hb := hh.2
    change dist _ p ≤ R * (r * R ^ n) at hb
    convert hb using 1; rw [pow_succ]; ring
  have hinit_bad : μ₀ (valid 0)ᶜ = 0 := by
    rw [hinit]
    apply nestedMarkedExcursionLaw_valid_compl hd p r R μ hμ 0
    exact hinner 0 (by simpa only [pow_zero, mul_one] using hx)
  have hvalid_bad (k : ℕ) : P (SkeletonCoupling.badUpTo (fun i => (valid i)ᶜ) k) = 0 := by
    have hbadstep : ∀ n h, h ∈ SkeletonCoupling.goodHistory (fun i => (valid i)ᶜ) n →
        κ n h (valid (n + 1))ᶜ ≤ 0 := by
      intro n h hh
      have hv : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ valid n :=
        not_not.mp (hh ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      rw [hkernel n h hv]
      exact (nestedMarkedExcursionLaw_valid_compl hd p r R μ hμ (n + 1)
        (hinner (n + 1) (hendpoint n h hv))).le
    have hb := SkeletonCoupling.badUpTo_le μ₀ κ (fun i => (valid i)ᶜ)
      (fun i => (hvalid i).compl) (fun _ => 0) hbadstep k
    apply le_antisymm
    · simpa only [P, hinit_bad, Finset.sum_const_zero, zero_add] using hb
    · exact bot_le
  have hvalidAE (k : ℕ) : ∀ᵐ ω ∂P, ∀ i ≤ k, ω i ∈ valid i := by
    have hAE : ∀ᵐ ω ∂P, ω ∉ SkeletonCoupling.badUpTo (fun i => (valid i)ᶜ) k := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hvalid_bad k
    filter_upwards [hAE] with ω hω
    intro i hi
    exact not_not.mp (fun hnot => hω ⟨i, hi, hnot⟩)
  have hbound : P {ω | ∀ i < N, ω i ∈ C} ≤ q ^ N := by
    cases N with
    | zero => simp only [Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
        Set.ofPred_true, measure_univ, pow_zero, le_refl]
    | succ k =>
      let S : ℕ → Set Z := fun i => if i ≤ k then valid i ∩ C else ∅
      have hS (i : ℕ) : MeasurableSet (S i) := by
        by_cases hi : i ≤ k
        · simpa only [S, ite_eq_left hi] using (hvalid i).inter hC
        · simp only [S, ite_eq_right hi, MeasurableSet.empty]
      have hS0 : μ₀ (S 0) ≤ q := by
        calc
          μ₀ (S 0) ≤ μ₀ C := measure_mono (by simp only [S, Nat.zero_le, ite_true]; exact inter_subset_right)
          _ = brownianExcursionKernel (U := V 0) isOpen_ball μ x (curveRangeEvent K) := by
            rw [hinit, nestedMarkedExcursionLaw_range p r R μ 0 x hK]
          _ ≤ q := hstep 0 (Nat.zero_lt_succ k) x (by simpa only [pow_zero, mul_one] using hx)
      have hSstep : ∀ n h, h ∈ SkeletonCoupling.goodHistory (fun i => (S i)ᶜ) n →
          κ n h (S (n + 1)) ≤ q := by
        intro n h hh
        by_cases hn : n + 1 ≤ k
        · have hs : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ S n :=
            not_not.mp (hh ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          have hv : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ valid n := by
            exact (show h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ valid n ∩ C by
              simpa only [S, ite_eq_left (by omega : n ≤ k)] using hs).1
          rw [hkernel n h hv]
          calc
            nestedMarkedExcursionLaw p r R μ (n + 1) _ (S (n + 1)) ≤
                nestedMarkedExcursionLaw p r R μ (n + 1) _ C :=
              measure_mono (by simp only [S, ite_eq_left hn]; exact inter_subset_right)
            _ = brownianExcursionKernel (U := V (n + 1)) isOpen_ball μ
                ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 1) (curveRangeEvent K) :=
              nestedMarkedExcursionLaw_range p r R μ (n + 1) _ hK
            _ ≤ q := hstep (n + 1) (by omega) _ (hendpoint n h hv)
        · simp only [S, ite_eq_right hn, measure_empty, zero_le]
      have heq : {ω : ℕ → Z | ∀ i < k + 1, ω i ∈ C} =ᵐ[P]
          SkeletonCoupling.survivalUpTo S k := by
        filter_upwards [hvalidAE k] with ω hω
        apply propext
        constructor
        · intro hc i hi
          simpa only [S, ite_eq_left hi, mem_inter_iff] using And.intro (hω i hi) (hc i (by omega))
        · intro hs i hi
          exact (show ω i ∈ valid i ∩ C by
            simpa only [S, ite_eq_left (by omega : i ≤ k)] using hs i (by omega)).2
      calc
        _ = P (SkeletonCoupling.survivalUpTo S k) := measure_congr heq
        _ ≤ μ₀ (S 0) * q ^ k := SkeletonCoupling.survivalUpTo_le μ₀ κ S hS q hSstep k
        _ ≤ q * q ^ k := mul_le_mul_left hS0 _
        _ = q ^ (k + 1) := (pow_succ' q k).symm
  have hevent : MeasurableSet {ω : ℕ → Z | ∀ i < N, ω i ∈ C} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      hC.preimage (measurable_pi_apply i)
  have hm : Measurable (fun ω n => brownianSkeletonExcursion V x 0 selector n ω) :=
    Measurable.of_eval (fun n => measurable_brownianSkeletonExcursion V
      (fun _ => isOpen_ball) x 0 (fun _ => measurable_const) n)
  calc
    _ = (μ.map (fun ω n => brownianSkeletonExcursion V x 0 selector n ω))
        {ω : ℕ → Z | ∀ i < N, ω i ∈ C} := (Measure.map_apply hm hevent).symm
    _ = P {ω | ∀ i < N, ω i ∈ C} := by
      rw [standardBrownianLaw_skeleton_map hd hμ V (fun _ => isOpen_ball)
        (fun _ => isBounded_ball) x 0 selector (fun _ => measurable_const)]
    _ ≤ q ^ N := hbound

/-- A bounded Lipschitz domain has a uniform geometric finite-stage survival
bound for its actual nested Brownian ball excursions. -/
theorem HasLipschitzBoundary.uniform_brownian_nested_survival {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hL : HasLipschitzBoundary U) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) :
    ∃ s > 0, ∃ κ > 0, ∃ q R : ℝ, 0 ≤ q ∧ q < 1 ∧ 1 < R ∧
      ∀ p ∈ frontier U, ∀ r : ℝ≥0, 0 < r → ∀ N : ℕ,
        (∀ i < N, (r : ℝ) * R ^ i < s) →
        ∀ x : Euc d, dist x p ≤ (r : ℝ) → ∀ δ : ℝ, δ < κ * (r : ℝ) / 2 →
          μ {ω | ∀ i < N,
            (brownianSkeletonExcursion (nestedBrownianBall p (r : ℝ) R) x 0
              (fun n _ => some n) i ω).2 ∈ curveRangeEvent (cthickening δ U)} ≤
            ENNReal.ofReal q ^ N := by
  obtain ⟨s, hs, κ, hκ, q, R, hq, hqone, hR, hsurvive⟩ :=
    hL.uniform_brownian_excursion_survival hd hU hUb μ hμ
  refine ⟨s, hs, κ, hκ, q, R, hq, hqone, hR, ?_⟩
  intro p hp r hr N hsmall x hx δ hδ
  apply brownian_nested_survival_le_of_step hd μ hμ p hr hR hx isClosed_cthickening
    (ENNReal.ofReal q) N
  intro i hi y hy
  have hrR : 0 < (r : ℝ) := hr
  have hscale : 0 < (r : ℝ) * R ^ i := mul_pos hrR (pow_pos (by linarith) i)
  have hbase : (r : ℝ) ≤ (r : ℝ) * R ^ i :=
    le_mul_of_one_le_right hrR.le (one_le_pow₀ hR.le)
  apply hsurvive p hp ⟨(r : ℝ) * R ^ i, hscale.le⟩ hscale (hsmall i hi) y δ hy
  change δ < κ * ((r : ℝ) * R ^ i) / 2
  exact hδ.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbase hκ.le) (by norm_num))

end BouRabeeGwynne
