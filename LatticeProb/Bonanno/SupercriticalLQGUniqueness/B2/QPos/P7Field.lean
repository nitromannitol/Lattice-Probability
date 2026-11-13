/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Field at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Kernel
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

 













set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Real Finset
open scoped RealInnerProductSpace Matrix
open LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 

 
def cell1 (N : ℕ) (c : ℤ) : Set ℝ := Set.Ico (((c : ℝ) - 1 / 2) / N) (((c : ℝ) + 1 / 2) / N)

lemma measurableSet_cell1 (N : ℕ) (c : ℤ) : MeasurableSet (cell1 N c) := measurableSet_Ico

lemma mem_cell1 {N : ℕ} (hN : 0 < N) {c : ℤ} {r : ℝ} :
    r ∈ cell1 N c ↔ (c : ℝ) - 1 / 2 ≤ N * r ∧ N * r < c + 1 / 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [cell1, Set.mem_Ico]
  rw [div_le_iff₀ hN', lt_div_iff₀ hN']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma volume_cell1 {N : ℕ} (hN : 0 < N) (c : ℤ) :
    volume.real (cell1 N c) = (N : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [measureReal_def, cell1, Real.volume_Ico, ENNReal.toReal_ofReal (by
    rw [sub_nonneg]; exact div_le_div_of_nonneg_right (by linarith) hN'.le)]
  field_simp; ring

lemma cell1_eq_of_mem {N : ℕ} (hN : 0 < N) {c c' : ℤ} {r : ℝ} (h : r ∈ cell1 N c)
    (h' : r ∈ cell1 N c') : c = c' := by
  rw [mem_cell1 hN] at h h'
  have h1 : (c : ℝ) < c' + 1 := by linarith
  have h2 : (c' : ℝ) < c + 1 := by linarith
  have h1' : c < c' + 1 := by exact_mod_cast h1
  have h2' : c' < c + 1 := by exact_mod_cast h2
  omega

lemma indicator_cell1_mul {N : ℕ} (hN : 0 < N) (c c' : ℤ) (r : ℝ) :
    (cell1 N c).indicator (1 : ℝ → ℝ) r * (cell1 N c').indicator (1 : ℝ → ℝ) r =
      if c = c' then (cell1 N c).indicator (1 : ℝ → ℝ) r else 0 := by
  by_cases hc : c = c'
  · subst hc
    by_cases hr : r ∈ cell1 N c <;> simp [hr]
  · rw [if_neg hc]
    by_cases hr : r ∈ cell1 N c
    · have hr' : r ∉ cell1 N c' := fun hr' => hc (cell1_eq_of_mem hN hr hr')
      simp [hr, hr']
    · simp [hr]

lemma integrable_indicator_cell1 (N : ℕ) (c : ℤ) (C : ℝ) :
    Integrable (fun r => C * (cell1 N c).indicator (1 : ℝ → ℝ) r) := by
  have h : Integrable ((cell1 N c).indicator (1 : ℝ → ℝ)) := by
    refine (integrableOn_const ?_).integrable_indicator (measurableSet_cell1 N c)
    rw [cell1, Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  exact h.const_mul C

 

 
def prof (N : ℕ) (s : ℝ) (a : ℤ) (r : ℝ) : ℝ :=
  ∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c) * (cell1 N c).indicator (1 : ℝ → ℝ) r

theorem integral_prof_mul (N : ℕ) (hN : 0 < N) (s s' : ℝ) (a b : ℤ) :
    ∫ r, prof N s a r * prof N s' b r = N * qker N (s + s') a b := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hprod : ∀ r, prof N s a r * prof N s' b r =
      ∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c * ((N : ℝ) * qker N s' b c)) *
        (cell1 N c).indicator (1 : ℝ → ℝ) r := by
    intro r
    unfold prof
    rw [sum_mul_sum]
    refine sum_congr rfl fun c _ => ?_
    have : ∀ c' ∈ sites1 N, ((N : ℝ) * qker N s a c) * (cell1 N c).indicator (1 : ℝ → ℝ) r *
        (((N : ℝ) * qker N s' b c') * (cell1 N c').indicator (1 : ℝ → ℝ) r) =
        ((N : ℝ) * qker N s a c * ((N : ℝ) * qker N s' b c')) *
          (if c = c' then (cell1 N c).indicator (1 : ℝ → ℝ) r else 0) := by
      intro c' _
      rw [← indicator_cell1_mul hN]; ring
    rw [sum_congr rfl this]
    simp only [mul_ite, mul_zero, sum_ite_eq, if_pos (show c ∈ sites1 N from ‹_›)]
  simp_rw [hprod]
  rw [integral_finset_sum _ fun c _ => integrable_indicator_cell1 N c _]
  simp_rw [integral_const_mul]
  rw [sum_congr rfl fun c _ => by
    rw [integral_indicator_one (measurableSet_cell1 N c), volume_cell1 hN]]
  rw [← qker_semigroup N hN s s' a b, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [qker_symm N s' b c]
  field_simp

 
lemma abs_mul_qker_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (a c : ℤ) :
    |(N : ℝ) * qker N s a c| ≤ (2 * N - 1 : ℝ) * Real.exp (-s / 2) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold qker
  rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  calc |∑ k ∈ modes N, Real.exp (-s * mu N k) * dsin N k a * dsin N k c|
      ≤ ∑ k ∈ modes N, |Real.exp (-s * mu N k) * dsin N k a * dsin N k c| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ modes N, Real.exp (-s / 2) := by
        refine sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 := abs_dsin_le N k a
        have h2 := abs_dsin_le N k c
        have hmu := mu_ge N hk
        have hk1 : (1 : ℝ) ≤ k := by simp only [modes, mem_Icc] at hk; exact_mod_cast hk.1
        have hμ : 1 / 2 ≤ mu N k := by nlinarith
        have he : Real.exp (-s * mu N k) ≤ Real.exp (-s / 2) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hμ hs])
        calc Real.exp (-s * mu N k) * |dsin N k a| * |dsin N k c|
            ≤ Real.exp (-s * mu N k) * 1 * 1 := by gcongr
          _ ≤ _ := by rw [mul_one, mul_one]; exact he
    _ = (2 * N - 1 : ℝ) * Real.exp (-s / 2) := by
        rw [sum_const, nsmul_eq_mul]
        congr 1
        simp only [modes, Int.card_Icc]
        rw [show (2 * (N : ℤ) - 1 + 1 - 1) = ((2 * N - 1 : ℕ) : ℤ) by omega]
        simp only [Int.toNat_natCast]
        rw [Nat.cast_sub (by omega)]; push_cast; ring

 
lemma cell1_subset {N : ℕ} (hN : 0 < N) {c : ℤ} (hc : c ∈ sites1 N) :
    cell1 N c ⊆ Set.Icc (-1) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro r hr
  rw [mem_cell1 hN] at hr
  simp only [sites1, mem_Icc] at hc
  have h1 : (-((N : ℤ) - 1) : ℝ) ≤ c := by exact_mod_cast hc.1
  have h2 : (c : ℝ) ≤ (N : ℤ) - 1 := by exact_mod_cast hc.2
  push_cast at h1 h2
  constructor
  · by_contra h; push_neg at h; nlinarith
  · by_contra h; push_neg at h; nlinarith

lemma abs_prof_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (a : ℤ) (r : ℝ) :
    |prof N s a r| ≤ (2 * N - 1 : ℝ) ^ 2 * Real.exp (-s / 2) *
      (Set.Icc (-1 : ℝ) 1).indicator 1 r := by
  unfold prof
  by_cases hr : r ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hr, Pi.one_apply, mul_one]
    calc |∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c) * (cell1 N c).indicator 1 r|
        ≤ ∑ c ∈ sites1 N, |((N : ℝ) * qker N s a c) * (cell1 N c).indicator 1 r| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ sites1 N, (2 * N - 1 : ℝ) * Real.exp (-s / 2) := by
          refine sum_le_sum fun c _ => ?_
          rw [abs_mul]
          have h1 := abs_mul_qker_le N hN hs a c
          have h2 : |(cell1 N c).indicator (1 : ℝ → ℝ) r| ≤ 1 := by
            by_cases h : r ∈ cell1 N c <;> simp [h]
          calc |(N : ℝ) * qker N s a c| * |(cell1 N c).indicator 1 r|
              ≤ ((2 * N - 1 : ℝ) * Real.exp (-s / 2)) * 1 :=
                mul_le_mul h1 h2 (abs_nonneg _) (by
                  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                  exact mul_nonneg (by linarith) (Real.exp_pos _).le)
            _ = _ := mul_one _
      _ = (2 * N - 1 : ℝ) ^ 2 * Real.exp (-s / 2) := by
          rw [sum_const, nsmul_eq_mul]
          simp only [sites1, Int.card_Icc]
          rw [show (N : ℤ) - 1 + 1 - -((N : ℤ) - 1) = ((2 * N - 1 : ℕ) : ℤ) by omega]
          simp only [Int.toNat_natCast]
          rw [Nat.cast_sub (by omega)]; push_cast; ring
  · rw [Set.indicator_of_notMem hr, mul_zero]
    have : ∀ c ∈ sites1 N, ((N : ℝ) * qker N s a c) * (cell1 N c).indicator (1 : ℝ → ℝ) r = 0 := by
      intro c hc
      have : r ∉ cell1 N c := fun h => hr (cell1_subset hN hc h)
      simp [this]
    rw [sum_congr rfl this, sum_const_zero, abs_zero]

lemma continuous_qker (N : ℕ) (a c : ℤ) : Continuous (fun s => qker N s a c) := by
  unfold qker
  exact continuous_const.mul (continuous_finset_sum _ fun k _ =>
    ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
      continuous_const).mul continuous_const)

lemma measurable_prof_comp (N : ℕ) (a : ℤ) {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => prof N (f x) a (g x)) := by
  unfold prof
  refine Finset.measurable_sum _ fun c _ => ?_
  have h1 : Measurable (fun x => (N : ℝ) * qker N (f x) a c) :=
    ((continuous_const.mul (continuous_qker N a c)).measurable).comp hf
  have h2 : Measurable (fun x => (cell1 N c).indicator (1 : ℝ → ℝ) (g x)) :=
    (measurable_one.indicator (measurableSet_cell1 N c)).comp hg
  exact h1.mul h2

 

 
def fKer (n : ℕ) (v : DGFFSite n) : ℝ × ℂ → ℝ :=
  {q : ℝ × ℂ | 0 < q.1}.indicator fun p =>
    Real.sqrt π * (prof (Nn n) (p.1 / 2) v.1.1 p.2.re * prof (Nn n) (p.1 / 2) v.1.2 p.2.im)

lemma measurable_fKer (n : ℕ) (v : DGFFSite n) : Measurable (fKer n v) := by
  have h1 : Measurable (fun p : ℝ × ℂ => prof (Nn n) (p.1 / 2) v.1.1 p.2.re) :=
    measurable_prof_comp (Nn n) v.1.1 (measurable_fst.div_const 2)
      (Complex.measurable_re.comp measurable_snd)
  have h2 : Measurable (fun p : ℝ × ℂ => prof (Nn n) (p.1 / 2) v.1.2 p.2.im) :=
    measurable_prof_comp (Nn n) v.1.2 (measurable_fst.div_const 2)
      (Complex.measurable_im.comp measurable_snd)
  have hS : MeasurableSet {q : ℝ × ℂ | 0 < q.1} := measurableSet_lt measurable_const measurable_fst
  exact ((h1.mul h2).const_mul _).indicator hS

 
def fDom (C : ℝ) (p : ℝ × ℂ) : ℝ :=
  C * ((Set.Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t / 2)) p.1 *
    ((Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2.re *
      (Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2.im))

lemma memLp_fDom (C : ℝ) : MemLp (fDom C) 2 (volume : Measure (ℝ × ℂ)) := by
  have hmeas : Measurable (fDom C) := by
    unfold fDom
    refine Measurable.const_mul (Measurable.mul ?_ (Measurable.mul ?_ ?_)) _
    · exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).indicator
        measurableSet_Ioi |>.comp measurable_fst
    · exact (measurable_one.indicator measurableSet_Icc).comp
        (Complex.measurable_re.comp measurable_snd)
    · exact (measurable_one.indicator measurableSet_Icc).comp
        (Complex.measurable_im.comp measurable_snd)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  have h1 : Integrable (fun t : ℝ => ((Set.Ioi (0 : ℝ)).indicator
      (fun t => Real.exp (-t / 2)) t) ^ 2) := by
    have : (fun t : ℝ => ((Set.Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t / 2)) t) ^ 2) =
        (Set.Ioi (0 : ℝ)).indicator (fun t => Real.exp (-1 * t)) := by
      funext t
      by_cases ht : t ∈ Set.Ioi (0 : ℝ)
      · simp only [Set.indicator_of_mem ht]
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      · simp [Set.indicator_of_notMem ht]
    rw [this]
    exact (integrableOn_exp_mul_Ioi (by norm_num) 0).integrable_indicator measurableSet_Ioi
  have h2 : Integrable (fun y : ℂ => ((Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y.re *
      (Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y.im) ^ 2) := by
    have hS : MeasurableSet {y : ℂ | y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1} :=
      (measurableSet_Icc.preimage Complex.measurable_re).inter
        (measurableSet_Icc.preimage Complex.measurable_im)
    have hfin : volume {y : ℂ | y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1} ≠ ⊤ := by
      refine (Bornology.IsBounded.measure_lt_top ?_).ne
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun y hy => ?_
      simp only [Metric.mem_closedBall, dist_zero_right]
      have h1 := abs_le.mpr hy.1
      have h2 := abs_le.mpr hy.2
      linarith [Complex.norm_le_abs_re_add_abs_im y]
    have : (fun y : ℂ => ((Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y.re *
        (Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y.im) ^ 2) =
        {y : ℂ | y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1}.indicator
          (1 : ℂ → ℝ) := by
      funext y
      by_cases h1 : y.re ∈ Set.Icc (-1 : ℝ) 1 <;> by_cases h2 : y.im ∈ Set.Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem (show y ∈ {y : ℂ | y.re ∈ Set.Icc (-1 : ℝ) 1 ∧
            y.im ∈ Set.Icc (-1 : ℝ) 1} from ⟨h1, h2⟩)]
        simp
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem (show y ∉ {y : ℂ |
          y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1} from fun h => h2 h.2)]
        simp
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show y ∉ {y : ℂ |
          y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1} from fun h => h1 h.1)]
        simp
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show y ∉ {y : ℂ |
          y.re ∈ Set.Icc (-1 : ℝ) 1 ∧ y.im ∈ Set.Icc (-1 : ℝ) 1} from fun h => h1 h.1)]
        simp
    rw [this]
    exact (integrableOn_const hfin).integrable_indicator hS
  have h3 := (h1.mul_prod h2).const_mul (C ^ 2)
  rw [← Measure.volume_eq_prod] at h3
  refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [fDom]; ring

lemma abs_fKer_le (n : ℕ) (v : DGFFSite n) (p : ℝ × ℂ) :
    |fKer n v p| ≤ |fDom (Real.sqrt π * (2 * Nn n - 1 : ℝ) ^ 4) p| := by
  set N := Nn n
  have hN : 0 < N := Nn_pos n
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine le_trans ?_ (le_abs_self _)
  unfold fKer fDom
  by_cases ht : 0 < p.1
  · rw [Set.indicator_of_mem (show p ∈ {q : ℝ × ℂ | 0 < q.1} from ht),
      Set.indicator_of_mem (show p.1 ∈ Set.Ioi (0 : ℝ) from ht)]
    have h1 := abs_prof_le N hN (show 0 ≤ p.1 / 2 by positivity) v.1.1 p.2.re
    have h2 := abs_prof_le N hN (show 0 ≤ p.1 / 2 by positivity) v.1.2 p.2.im
    have hI1 : 0 ≤ (Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2.re := by
      apply Set.indicator_nonneg; intro _ _; norm_num
    have hI2 : 0 ≤ (Set.Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2.im := by
      apply Set.indicator_nonneg; intro _ _; norm_num
    have he : Real.exp (-(p.1 / 2) / 2) * Real.exp (-(p.1 / 2) / 2) = Real.exp (-p.1 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg π), abs_mul]
    calc Real.sqrt π * (|prof N (p.1 / 2) v.1.1 p.2.re| * |prof N (p.1 / 2) v.1.2 p.2.im|)
        ≤ Real.sqrt π * (((2 * N - 1 : ℝ) ^ 2 * Real.exp (-(p.1 / 2) / 2) *
            (Set.Icc (-1 : ℝ) 1).indicator 1 p.2.re) *
            ((2 * N - 1 : ℝ) ^ 2 * Real.exp (-(p.1 / 2) / 2) *
            (Set.Icc (-1 : ℝ) 1).indicator 1 p.2.im)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hI1))
            (Real.sqrt_nonneg _)
      _ = Real.sqrt π * (2 * N - 1 : ℝ) ^ 4 * (Real.exp (-p.1 / 2) *
            ((Set.Icc (-1 : ℝ) 1).indicator 1 p.2.re *
              (Set.Icc (-1 : ℝ) 1).indicator 1 p.2.im)) := by
          rw [← he]; ring
  · rw [Set.indicator_of_notMem (show p ∉ {q : ℝ × ℂ | 0 < q.1} from ht), abs_zero,
      Set.indicator_of_notMem (show p.1 ∉ Set.Ioi (0 : ℝ) from ht)]
    simp

theorem memLp_fKer (n : ℕ) (v : DGFFSite n) : MemLp (fKer n v) 2 (volume : Measure (ℝ × ℂ)) :=
  (memLp_fDom _).of_le (measurable_fKer n v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_fKer_le n v p)

 
def fKerL2 (n : ℕ) (v : DGFFSite n) : WNSpace := (memLp_fKer n v).toLp

 

 
lemma integral_complex_re_mul_im (f g : ℝ → ℝ) :
    ∫ y : ℂ, f y.re * g y.im = (∫ x, f x) * ∫ x, g x := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun y : ℂ => f y.re * g y.im)
  rw [← h, Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma integral_fKer_mul_slice (n : ℕ) (v u : DGFFSite n) (t : ℝ) :
    ∫ y : ℂ, fKer n v (t, y) * fKer n u (t, y) =
      if 0 < t then π * (((Nn n : ℝ) * qker (Nn n) t v.1.1 u.1.1) *
        ((Nn n : ℝ) * qker (Nn n) t v.1.2 u.1.2)) else 0 := by
  have hN : 0 < Nn n := Nn_pos n
  unfold fKer
  by_cases ht : 0 < t
  · have hmem : ∀ y : ℂ, ((t, y) : ℝ × ℂ) ∈ {q : ℝ × ℂ | 0 < q.1} := fun _ => ht
    simp only [Set.indicator_of_mem (hmem _), if_pos ht]
    have e : ∀ y : ℂ, Real.sqrt π * (prof (Nn n) (t / 2) v.1.1 y.re *
        prof (Nn n) (t / 2) v.1.2 y.im) *
        (Real.sqrt π * (prof (Nn n) (t / 2) u.1.1 y.re * prof (Nn n) (t / 2) u.1.2 y.im)) =
        π * ((prof (Nn n) (t / 2) v.1.1 y.re * prof (Nn n) (t / 2) u.1.1 y.re) *
          (prof (Nn n) (t / 2) v.1.2 y.im * prof (Nn n) (t / 2) u.1.2 y.im)) := by
      intro y
      have := Real.mul_self_sqrt Real.pi_pos.le
      linear_combination (prof (Nn n) (t / 2) v.1.1 y.re * prof (Nn n) (t / 2) v.1.2 y.im *
        (prof (Nn n) (t / 2) u.1.1 y.re * prof (Nn n) (t / 2) u.1.2 y.im)) * this
    simp_rw [e]
    rw [integral_const_mul, integral_complex_re_mul_im
      (fun r => prof (Nn n) (t / 2) v.1.1 r * prof (Nn n) (t / 2) u.1.1 r)
      (fun r => prof (Nn n) (t / 2) v.1.2 r * prof (Nn n) (t / 2) u.1.2 r),
      integral_prof_mul (Nn n) hN, integral_prof_mul (Nn n) hN, add_halves]
  · have hmem : ∀ y : ℂ, ((t, y) : ℝ × ℂ) ∉ {q : ℝ × ℂ | 0 < q.1} := fun _ => ht
    simp only [Set.indicator_of_notMem (hmem _), if_neg ht, zero_mul, integral_zero]

 
lemma mul_qker_eq (N : ℕ) (hN : 0 < N) (t : ℝ) (a b : ℤ) :
    (N : ℝ) * qker N t a b = ∑ k ∈ modes N, Real.exp (-t * mu N k) * dsin N k a * dsin N k b := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold qker; rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]

lemma integral_slice_eq_Gmat (n : ℕ) (v u : DGFFSite n) :
    ∫ t in Set.Ioi (0 : ℝ), π * (((Nn n : ℝ) * qker (Nn n) t v.1.1 u.1.1) *
      ((Nn n : ℝ) * qker (Nn n) t v.1.2 u.1.2)) = Gmat n v u := by
  set N := Nn n
  have hN : 0 < N := Nn_pos n
  have e : ∀ t : ℝ, π * (((N : ℝ) * qker N t v.1.1 u.1.1) * ((N : ℝ) * qker N t v.1.2 u.1.2)) =
      ∑ k ∈ modes N, ∑ l ∈ modes N, (π * (dsin N k v.1.1 * dsin N k u.1.1 *
        dsin N l v.1.2 * dsin N l u.1.2)) * Real.exp (-(mu N k + mu N l) * t) := by
    intro t
    rw [mul_qker_eq N hN, mul_qker_eq N hN, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [show -(mu N k + mu N l) * t = -t * mu N k + -t * mu N l by ring, Real.exp_add]
    ring
  simp_rw [e]
  have hint : ∀ k ∈ modes N, ∀ l ∈ modes N, IntegrableOn
      (fun t => Real.exp (-(mu N k + mu N l) * t)) (Set.Ioi 0) := fun k hk l hl =>
    integrableOn_exp_mul_Ioi (by linarith [mu_pos N hk, mu_pos N hl]) 0
  rw [integral_finset_sum _ fun k hk => integrable_finset_sum _ fun l hl =>
    (hint k hk l hl).const_mul _]
  unfold Gmat
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [integral_finset_sum _ fun l hl => (hint k hk l hl).const_mul _, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [mu_pos N hk, mu_pos N hl])]
  have hpos : 0 < mu N k + mu N l := add_pos (mu_pos N hk) (mu_pos N hl)
  rw [mul_zero, Real.exp_zero]
  simp only [N] at hpos ⊢
  field_simp

 
theorem inner_fKerL2 (n : ℕ) (v u : DGFFSite n) :
    ⟪fKerL2 n v, fKerL2 n u⟫ = (boxConductances n).precision⁻¹ v u := by
  rw [← Gmat_eq_inv]
  have hf := memLp_fKer n v
  have hg := memLp_fKer n u
  rw [L2.inner_def]
  have h1 : ∫ q, ⟪(fKerL2 n v : ℝ × ℂ → ℝ) q, (fKerL2 n u : ℝ × ℂ → ℝ) q⟫ =
      ∫ q, fKer n v q * fKer n u q := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with q h1 h2
    simp only [fKerL2, h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real]
    ring
  rw [h1, Measure.volume_eq_prod, integral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact hf.integrable_mul hg)]
  simp_rw [integral_fKer_mul_slice]
  rw [← integral_slice_eq_Gmat n v u, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  by_cases ht : 0 < t
  · rw [if_pos ht, Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)]
  · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]

 

variable {Ω : Type*} [MeasurableSpace Ω]

 
def dgffVec (n : ℕ) (W : WNSpace → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ (DGFFSite n) :=
  WithLp.toLp 2 fun v => W (fKerL2 n v) ω

lemma measurable_dgffVec (n : ℕ) {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : Measurable (dgffVec n W) := by
  have : Measurable fun ω => fun v : DGFFSite n => W (fKerL2 n v) ω :=
    measurable_pi_iff.mpr fun v => hW.measurable _
  exact (WithLp.measurable_toLp 2 _).comp this

 
theorem map_dgffVec (n : ℕ) {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : P.map (dgffVec n W) = boxDGFF n := by
  letI := hW.isProbabilityMeasure
  have hm := measurable_dgffVec n hW
  haveI : IsProbabilityMeasure (P.map (dgffVec n W)) := inferInstance
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [boxDGFF, WiredConductances.gaussianOfPrecision,
    charFun_multivariateGaussian (box_precision_posDef n).inv.posSemidef]
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  
  set c : DGFFSite n → ℝ := fun v => x v
  have hinner : ∀ ω, ⟪dgffVec n W ω, x⟫ = ∑ v, c v * W (fKerL2 n v) ω := by
    intro ω
    simp only [dgffVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, c]
  simp_rw [hinner]
  have hlaw := hW.hasLaw (fun v => fKerL2 n v) c
  set σ2 := ‖∑ v, c v • fKerL2 n v‖ ^ 2
  have hY : Measurable fun ω => ∑ v, c v * W (fKerL2 n v) ω :=
    Finset.measurable_sum _ fun v _ => (hW.measurable _).const_mul _
  have hcf : ∫ ω, Complex.exp (((∑ v, c v * W (fKerL2 n v) ω : ℝ) : ℂ) * Complex.I) ∂P =
      charFun (gaussianReal 0 σ2.toNNReal) 1 := by
    rw [← hlaw.map_eq, charFun_apply_real, integral_map hY.aemeasurable (by fun_prop)]
    simp
  rw [hcf, charFun_gaussianReal]
  have hσ : σ2 = x.ofLp ⬝ᵥ (boxConductances n).precision⁻¹ *ᵥ x.ofLp := by
    simp only [σ2, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, inner_fKerL2]
    simp only [dotProduct, Matrix.mulVec, c, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => by ring
  have hσ0 : 0 ≤ σ2 := sq_nonneg _
  rw [Real.coe_toNNReal _ hσ0, hσ]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, mul_zero,
    Complex.ofReal_one, one_pow, mul_one]

 
def dgffCoupling (n : ℕ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) :
    Measure (EuclideanSpace ℝ (DGFFSite n) × Ω) :=
  P.map fun ω => (dgffVec n W ω, ω)

theorem dgffCoupling_isProbability (n : ℕ) {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : IsProbabilityMeasure (dgffCoupling n P W) := by
  letI := hW.isProbabilityMeasure
  unfold dgffCoupling
  infer_instance

theorem dgffCoupling_fst (n : ℕ) {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : (dgffCoupling n P W).map Prod.fst = boxDGFF n := by
  have hm : Measurable (fun ω => (dgffVec n W ω, ω)) :=
    (measurable_dgffVec n hW).prodMk measurable_id
  rw [dgffCoupling, Measure.map_map measurable_fst hm]
  exact map_dgffVec n hW

theorem dgffCoupling_snd (n : ℕ) {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : (dgffCoupling n P W).map Prod.snd = P := by
  have hm : Measurable (fun ω => (dgffVec n W ω, ω)) :=
    (measurable_dgffVec n hW).prodMk measurable_id
  rw [dgffCoupling, Measure.map_map measurable_snd hm]
  exact Measure.map_id

end SupercriticalLQGUniqueness.B2.QPos.P7
