import LatticeProb.Prob.Freedman

/-!
# Conditional exponential estimates for bounded martingales

The exponential process associated with the predictable quadratic variation satisfies
its one-step supermartingale inequality on every finite interval of bounded increments.
-/

open MeasureTheory ProbabilityTheory Filter

namespace LatticeProb

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The conditional exponential process is a supermartingale at each bounded step. -/
theorem condExp_exp_sub_condQvar_le {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {lam : ℝ} (hlam : 0 < lam) (hlb : lam * b < 3) {k : ℕ} (hk1 : k + 1 ≤ n) :
    P[fun ω => Real.exp (lam * M (k + 1) ω -
        lam ^ 2 / (2 * (1 - lam * b / 3)) * condQvar P ℱ M (k + 1) ω) | ℱ k]
      ≤ᵐ[P] fun ω => Real.exp (lam * M k ω -
        lam ^ 2 / (2 * (1 - lam * b / 3)) * condQvar P ℱ M k ω) := by
  have hθpos : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  set c : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3)) with hcdef
  have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hMmeas : ∀ j, Measurable[m0] (M j) := fun j =>
    ((hmart.stronglyMeasurable j).mono (ℱ.le j)).measurable
  have hMb : ∀ j, j ≤ n → ∀ ω, |M j ω| ≤ j * b := abs_le_of_increments hM0 hinc
  have hZmeas : ∀ j, Measurable[m0]
      (fun ω => Real.exp (lam * M j ω - c * condQvar P ℱ M j ω)) := fun j =>
    Real.measurable_exp.comp (((hMmeas j).const_mul lam).sub
      ((measurable_condQvar P ℱ M j).const_mul c))
  have hZint : ∀ j, j ≤ n → Integrable
      (fun ω => Real.exp (lam * M j ω - c * condQvar P ℱ M j ω)) P := by
    intro j hj
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((j : ℝ) * b))))
      (hZmeas j).aestronglyMeasurable ?_
    filter_upwards [condQvar_nonneg P ℱ M j] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : M j ω ≤ (j : ℝ) * b := (abs_le.mp (hMb j hj ω)).2
    have h2 : 0 ≤ c * condQvar P ℱ M j ω := mul_nonneg hcnn hω
    nlinarith [hlam]
  have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk1
  set X : Ω → ℝ := fun ω => M (k + 1) ω - M k ω with hXdef
  have hXmeas : Measurable[m0] X := (hMmeas (k + 1)).sub (hMmeas k)
  have hXb : ∀ ω, |X ω| ≤ b := hinc k hkn
  have hXmean : P[X | ℱ k] =ᵐ[P] 0 := by
    have h3 := condExp_sub (μ := P) (hmart.integrable (k + 1)) (hmart.integrable k) (ℱ k)
    have h1 : P[M (k + 1) | ℱ k] =ᵐ[P] M k := hmart.condExp_ae_eq (Nat.le_succ k)
    have h2 : P[M k | ℱ k] = M k :=
      condExp_of_stronglyMeasurable (ℱ.le k) (hmart.stronglyMeasurable k)
        (hmart.integrable k)
    filter_upwards [h3, h1] with ω e3 e1
    show P[M (k + 1) - M k | ℱ k] ω = 0
    rw [e3]
    simp only [Pi.sub_apply]
    rw [e1, h2, sub_self]
  have hcond := condExp_exp_le (ℱ.le k) hXmeas hXb hXmean hlam hlb
  rw [← hcdef] at hcond
  set g : Ω → ℝ := fun ω => Real.exp (lam * M k ω - c * condQvar P ℱ M (k + 1) ω)
    with hgdef
  have hgSM : StronglyMeasurable[ℱ k] g := by
    refine Measurable.stronglyMeasurable ?_
    exact Real.measurable_exp.comp
      (((hmart.stronglyMeasurable k).measurable.const_mul lam).sub
        ((stronglyMeasurable_condQvar P ℱ M (k + 1) k le_rfl).measurable.const_mul c))
  have hEmeas : Measurable[m0] fun ω => Real.exp (lam * X ω) :=
    Real.measurable_exp.comp (hXmeas.const_mul lam)
  have hEint : Integrable (fun ω => Real.exp (lam * X ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * b)))
      hEmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [(abs_le.mp (hXb ω)).2, hlam]
  have hprodeq : (fun ω => Real.exp (lam * M (k + 1) ω - c * condQvar P ℱ M (k + 1) ω))
      = g * fun ω => Real.exp (lam * X ω) := by
    funext ω
    show Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    rw [hXdef]
    ring
  have hprodint : Integrable (g * fun ω => Real.exp (lam * X ω)) P := by
    rw [← hprodeq]; exact hZint (k + 1) hk1
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ k) hgSM hprodint hEint
  have hstep : P[fun ω => Real.exp (lam * M (k + 1) ω - c * condQvar P ℱ M (k + 1) ω) | ℱ k]
      ≤ᵐ[P] fun ω => Real.exp (lam * M k ω - c * condQvar P ℱ M k ω) := by
    rw [hprodeq]
    filter_upwards [hpull, hcond] with ω e1 e2
    rw [e1]
    simp only [Pi.mul_apply]
    have hgpos : 0 < g ω := Real.exp_pos _
    calc g ω * P[fun ω => Real.exp (lam * X ω) | ℱ k] ω
        ≤ g ω * Real.exp (c * P[fun ω => X ω ^ 2 | ℱ k] ω) := by nlinarith [e2, hgpos]
      _ = Real.exp (lam * M k ω - c * condQvar P ℱ M k ω) := by
          rw [hgdef, ← Real.exp_add, condQvar_succ]
          congr 1
          ring
  exact hstep

/-- The exponential process stopped at a deterministic horizon is a supermartingale. -/
theorem supermartingale_exp_sub_condQvar {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {lam : ℝ} (hlam : 0 < lam) (hlb : lam * b < 3) :
    Supermartingale (fun i ω => Real.exp (lam * M (min i n) ω -
      lam ^ 2 / (2 * (1 - lam * b / 3)) * condQvar P ℱ M (min i n) ω)) ℱ P := by
  have hθpos : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  let c : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let Z : ℕ → Ω → ℝ := fun i ω =>
    Real.exp (lam * M (min i n) ω - c * condQvar P ℱ M (min i n) ω)
  have hZsm : StronglyAdapted ℱ Z := by
    intro i
    apply Measurable.stronglyMeasurable
    exact Real.measurable_exp.comp
      ((((hmart.stronglyMeasurable (min i n)).mono (ℱ.mono (min_le_left _ _))).measurable.const_mul lam).sub
        (((stronglyMeasurable_condQvar P ℱ M (min i n) i
          (le_trans (min_le_left _ _) (Nat.le_succ i))).measurable).const_mul c))
  have hZint : ∀ i, Integrable (Z i) P := by
    intro i
    refine Integrable.mono' (integrable_const (Real.exp (lam * ((min i n : ℕ) : ℝ) * b)))
      ((hZsm i).mono (ℱ.le i)).aestronglyMeasurable ?_
    filter_upwards [condQvar_nonneg P ℱ M (min i n)] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hbound := (abs_le.mp (abs_le_of_increments hM0 hinc (min i n) (min_le_right _ _) ω)).2
    have hnonneg : 0 ≤ c * condQvar P ℱ M (min i n) ω := mul_nonneg hc hω
    nlinarith [hlam]
  change Supermartingale Z ℱ P
  refine supermartingale_nat hZsm hZint ?_
  intro i
  by_cases hi : i < n
  · have hi' : i + 1 ≤ n := hi
    simpa only [Z, c, min_eq_left (le_of_lt hi), min_eq_left hi'] using
      (condExp_exp_sub_condQvar_le hmart hM0 hinc hlam hlb hi')
  · have hn : n ≤ i := Nat.le_of_not_gt hi
    have hn' : n ≤ i + 1 := hn.trans (Nat.le_succ i)
    have heq : Z (i + 1) = Z i := by
      simp only [Z, min_eq_right hn, min_eq_right hn']
    rw [heq, condExp_of_stronglyMeasurable (ℱ.le i) (hZsm i) (hZint i)]

/-- A supermartingale loses no expectation on an event known before a bounded stopping time. -/
theorem setIntegral_stoppedValue_le {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ P) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) {j k : ℕ} (hτj : ∀ ω, (j : WithTop ℕ) ≤ τ ω)
    (hτk : ∀ ω, τ ω ≤ k) {B : Set Ω} (hB : MeasurableSet[ℱ j] B) :
    ∫ ω in B, stoppedValue Z τ ω ∂P ≤ ∫ ω in B, Z j ω ∂P := by
  classical
  let σ : Ω → WithTop ℕ := B.piecewise τ (fun _ => j)
  have hσ : IsStoppingTime ℱ σ :=
    hτ.piecewise_of_le (isStoppingTime_const ℱ j) hτj (fun _ => le_rfl) hB
  have hσj : (fun _ : Ω => (j : WithTop ℕ)) ≤ σ := by
    intro ω
    dsimp [σ, Set.piecewise]
    split_ifs with hω
    · exact hτj ω
    · rfl
  have hσk : ∀ ω, σ ω ≤ k := by
    intro ω
    dsimp [σ, Set.piecewise]
    split_ifs with hω
    · exact hτk ω
    · exact (hτj ω).trans (hτk ω)
  have hopt := hZ.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ j) hσ hσj hσk
  have hwhole : (∫ ω, stoppedValue Z σ ω ∂P) ≤ ∫ ω, Z j ω ∂P := by
    have hneg : stoppedValue (-Z) σ = -stoppedValue Z σ := rfl
    rw [stoppedValue_const, hneg] at hopt
    change (∫ ω, -Z j ω ∂P) ≤ ∫ ω, -stoppedValue Z σ ω ∂P at hopt
    rw [integral_neg, integral_neg, neg_le_neg_iff] at hopt
    exact hopt
  have hstop : stoppedValue Z σ = B.piecewise (stoppedValue Z τ) (Z j) := by
    funext ω
    by_cases hω : ω ∈ B
    · have he : σ ω = τ ω := by simp [σ, hω]
      simp only [Set.piecewise_eq_of_mem B _ _ hω, stoppedValue, he]
    · have he : σ ω = (j : WithTop ℕ) := by simp [σ, hω]
      rw [Set.piecewise_eq_of_notMem B _ _ hω]
      change Z (σ ω).untopA ω = Z j ω
      rw [he]
      rfl
  have hτint : Integrable (stoppedValue Z τ) P :=
    integrable_stoppedValue ℕ hτ hZ.integrable hτk
  rw [hstop, integral_piecewise (ℱ.le j _ hB) hτint.integrableOn
    (hZ.integrable j).integrableOn] at hwhole
  rw [← integral_add_compl (ℱ.le j _ hB) (hZ.integrable j)] at hwhole
  linarith

/-- The predictable quadratic variation is almost surely nondecreasing. -/
theorem condQvar_monotone_ae (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) : ∀ᵐ ω ∂P, Monotone (fun k => condQvar P ℱ M k ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ,
      0 ≤ (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω := by
    refine ae_all_iff.mpr fun i => ?_
    have h := condExp_nonneg (μ := P) (m := ℱ i)
      (f := fun ω' => (M (i + 1) ω' - M i ω') ^ 2)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [h] with ω hω
    simpa using hω
  filter_upwards [hall] with ω hω
  intro j k hjk
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) fun i _ _ => hω i


/-- An eventwise stopped-value lower bound yields a probability bound. -/
theorem measureReal_le_of_stoppedValue {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ P) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) {j k : ℕ} (hτj : ∀ ω, (j : WithTop ℕ) ≤ τ ω)
    (hτk : ∀ ω, τ ω ≤ k) {B C : Set Ω} (hB : MeasurableSet[ℱ j] B)
    (hC : MeasurableSet C) (hCB : C ⊆ B) {c : ℝ}
    (hpos : ∀ i ω, 0 ≤ Z i ω) (hZ0 : ∀ ω, Z j ω = 1)
    (hbound : ∀ᵐ ω ∂P, ω ∈ C → c ≤ stoppedValue Z τ ω) :
    c * P.real C ≤ P.real B := by
  have hτint : Integrable (stoppedValue Z τ) P :=
    integrable_stoppedValue ℕ hτ hZ.integrable hτk
  have hnonneg : 0 ≤ᵐ[P] stoppedValue Z τ :=
    Filter.Eventually.of_forall fun ω => hpos _ ω
  calc
    c * P.real C = ∫ _ in C, c ∂P := by simp [measureReal_def, mul_comm]
    _ ≤ ∫ ω in C, stoppedValue Z τ ω ∂P :=
      setIntegral_mono_on_ae (integrableOn_const (measure_ne_top _ _))
        hτint.integrableOn hC hbound
    _ ≤ ∫ ω in B, stoppedValue Z τ ω ∂P :=
      setIntegral_mono_set hτint.integrableOn (ae_restrict_of_ae hnonneg)
        (Filter.Eventually.of_forall hCB)
    _ ≤ ∫ ω in B, Z j ω ∂P := setIntegral_stoppedValue_le hZ hτ hτj hτk hB
    _ = P.real B := by simp [hZ0, measureReal_def]

/-- A filtration with its origin shifted by a deterministic time. -/
def shiftedFiltration (ℱ : Filtration ℕ m0) (j : ℕ) : Filtration ℕ m0 where
  seq i := ℱ (j + i)
  mono' := fun _ _ h => ℱ.mono (Nat.add_le_add_left h j)
  le' := fun i => ℱ.le (j + i)

/-- Shifting the starting time and subtracting the initial value preserves a martingale. -/
theorem martingale_shift_sub {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ P) (j : ℕ) :
    Martingale (fun i ω => M (j + i) ω - M j ω) (shiftedFiltration ℱ j) P := by
  have hshift : Martingale (fun i => M (j + i)) (shiftedFiltration ℱ j) P := by
    refine ⟨fun i => hM.stronglyMeasurable (j + i), fun i k hik => ?_⟩
    exact hM.condExp_ae_eq (Nat.add_le_add_left hik j)
  have hconst : Martingale (fun _ => M j) (shiftedFiltration ℱ j) P := by
    apply martingale_const_fun
    · change StronglyMeasurable[ℱ (j + 0)] (M j)
      simpa only [Nat.add_zero] using hM.stronglyMeasurable j
    · exact hM.integrable j
  exact hshift.sub hconst


/-- Shifting a martingale shifts its predictable quadratic variation by the same interval. -/
theorem condQvar_shift_sub (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (j n : ℕ) (ω : Ω) :
    condQvar P (shiftedFiltration ℱ j) (fun i ω => M (j + i) ω - M j ω) n ω =
      condQvar P ℱ M (j + n) ω - condQvar P ℱ M j ω := by
  have hterm : ∀ i : ℕ,
      (fun ω => ((M (j + (i + 1)) ω - M j ω) - (M (j + i) ω - M j ω)) ^ 2) =
      (fun ω => (M ((j + i) + 1) ω - M (j + i) ω) ^ 2) := by
    intro i
    funext ω
    simp only [Nat.add_assoc]
    ring
  simp only [condQvar, shiftedFiltration, hterm, Finset.sum_range_add]
  ring

/-- A one-sided eventwise exponential maximal bound. -/
theorem measureReal_max_condQvar_le_exp {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {lam t v : ℝ} (hlam : 0 < lam) (hlb : lam * b < 3)
    {B : Set Ω} (hB : MeasurableSet[ℱ 0] B) :
    P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ M i ω) ∧ condQvar P ℱ M n ω ≤ v} ≤
      Real.exp (-lam * t + lam ^ 2 / (2 * (1 - lam * b / 3)) * v) * P.real B := by
  let c : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3))
  have hθpos : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let Z : ℕ → Ω → ℝ := fun i ω =>
    Real.exp (lam * M (min i n) ω - c * condQvar P ℱ M (min i n) ω)
  let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn M (Set.Ici t) 0 n ω : ℕ)
  let C : Set Ω := {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ M i ω) ∧ condQvar P ℱ M n ω ≤ v}
  have hZ : Supermartingale Z ℱ P :=
    supermartingale_exp_sub_condQvar hmart hM0 hinc hlam hlb
  have hτ : IsStoppingTime ℱ τ :=
    hmart.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ0 : ∀ ω, (0 : WithTop ℕ) ≤ τ ω := fun _ => bot_le
  have hτn : ∀ ω, τ ω ≤ n := by
    intro ω
    change (↑(hittingBtwn M (Set.Ici t) 0 n ω) : WithTop ℕ) ≤ n
    exact_mod_cast (hittingBtwn_le (u := M) (s := Set.Ici t) (n := 0) ω)
  have hC : MeasurableSet C := by
    have hmax : MeasurableSet {ω | ∃ i ≤ n, t ≤ M i ω} := by
      simp only [show {ω | ∃ i ≤ n, t ≤ M i ω} =
        ⋃ i, ⋃ (_ : i ≤ n), {ω | t ≤ M i ω} by ext ω; simp]
      exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
        measurableSet_le measurable_const (((hmart.stronglyMeasurable i).mono (ℱ.le i)).measurable)
    change MeasurableSet (B ∩ ({ω | ∃ i ≤ n, t ≤ M i ω} ∩
      {ω | condQvar P ℱ M n ω ≤ v}))
    exact (ℱ.le 0 _ hB).inter (hmax.inter
      (measurableSet_le (measurable_condQvar P ℱ M n) measurable_const))
  have hbound : ∀ᵐ ω ∂P, ω ∈ C →
      Real.exp (lam * t - c * v) ≤ stoppedValue Z τ ω := by
    filter_upwards [condQvar_monotone_ae P ℱ M] with ω hmono hω
    obtain ⟨_, ⟨i, hi, hMi⟩, hv⟩ := hω
    have hhit : t ≤ M (hittingBtwn M (Set.Ici t) 0 n ω) ω :=
      hittingBtwn_mem_set ⟨i, ⟨Nat.zero_le i, hi⟩, hMi⟩
    have hvar : condQvar P ℱ M (hittingBtwn M (Set.Ici t) 0 n ω) ω ≤
        condQvar P ℱ M n ω := hmono (hittingBtwn_le ω)
    have htime : hittingBtwn M (Set.Ici t) 0 n ω ≤ n := hittingBtwn_le ω
    change Real.exp (lam * t - c * v) ≤
      Z (hittingBtwn M (Set.Ici t) 0 n ω) ω
    simp only [Z, min_eq_left htime]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprob := measureReal_le_of_stoppedValue hZ hτ hτ0 hτn hB hC
    (show C ⊆ B from fun _ h => h.1) (c := Real.exp (lam * t - c * v))
    (fun i ω => (Real.exp_pos _).le) (by
      intro ω
      change Real.exp (lam * M 0 ω - c * condQvar P ℱ M 0 ω) = 1
      simp [hM0, condQvar]) hbound
  have hcancel : Real.exp (-lam * t + c * v) * Real.exp (lam * t - c * v) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring
  have hp : 0 ≤ Real.exp (-lam * t + c * v) := (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_left hprob hp
  rw [← mul_assoc, hcancel, one_mul] at hm
  exact hm


/-- The one-sided eventwise Freedman bound with optimized exponent. -/
theorem measureReal_max_condQvar_le {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {t v : ℝ} (hb : 0 < b) (ht : 0 < t) (hv : 0 < v)
    {B : Set Ω} (hB : MeasurableSet[ℱ 0] B) :
    P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ M i ω) ∧ condQvar P ℱ M n ω ≤ v} ≤
      Real.exp (-(t ^ 2 / (2 * (v + b * t / 3)))) * P.real B := by
  set D : ℝ := v + b * t / 3 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  set lam : ℝ := t / D with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlb : lam * b < 3 := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ hD, hDdef]
    nlinarith
  have hone : 1 - lam * b / 3 = v / D := by
    rw [hlamdef, hDdef]
    field_simp
    ring
  have hcv : lam ^ 2 / (2 * (1 - lam * b / 3)) * v = t ^ 2 / (2 * D) := by
    rw [hone, hlamdef]
    field_simp
  have hexp : -lam * t + lam ^ 2 / (2 * (1 - lam * b / 3)) * v = -(t ^ 2 / (2 * D)) := by
    rw [hcv, hlamdef]
    field_simp
    ring
  have h := measureReal_max_condQvar_le_exp hmart hM0 hinc hlam hlb hB (t := t) (v := v)
  rw [hexp] at h
  exact h

/-- Negating a martingale does not change its predictable quadratic variation. -/
theorem condQvar_neg (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    condQvar P ℱ (-M) n ω = condQvar P ℱ M n ω := by
  unfold condQvar
  apply Finset.sum_congr rfl
  intro i _
  have hfun : (fun ω' => ((-M) (i + 1) ω' - (-M) i ω') ^ 2) =
      (fun ω' => (M (i + 1) ω' - M i ω') ^ 2) := by
    funext ω'
    simp only [Pi.neg_apply]
    ring
  rw [hfun]

/-- The two-sided eventwise Freedman bound from time zero. -/
theorem measureReal_max_abs_condQvar_le {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    {b : ℝ} {n : ℕ} (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {t v : ℝ} (hb : 0 < b) (ht : 0 < t) (hv : 0 < v)
    {B : Set Ω} (hB : MeasurableSet[ℱ 0] B) :
    P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ |M i ω|) ∧ condQvar P ℱ M n ω ≤ v} ≤
      2 * Real.exp (-(t ^ 2 / (2 * (v + b * t / 3)))) * P.real B := by
  have hM0' : ∀ ω, (-M) 0 ω = 0 := by
    intro ω
    simp [hM0]
  have hinc' : ∀ i, i < n → ∀ ω, |(-M) (i + 1) ω - (-M) i ω| ≤ b := by
    intro i hi ω
    convert hinc i hi ω using 1; simp only [Pi.neg_apply]
    rw [show -M (i + 1) ω - -M i ω = -(M (i + 1) ω - M i ω) by ring, abs_neg]
  have h1 := measureReal_max_condQvar_le hmart hM0 hinc hb ht hv hB
  have h2 := measureReal_max_condQvar_le hmart.neg hM0' hinc' hb ht hv hB
  simp only [condQvar_neg, Pi.neg_apply] at h2
  calc
    P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ |M i ω|) ∧ condQvar P ℱ M n ω ≤ v} ≤
        P.real ({ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ M i ω) ∧ condQvar P ℱ M n ω ≤ v} ∪
          {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ -M i ω) ∧ condQvar P ℱ M n ω ≤ v}) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro ω ⟨hBω, ⟨i, hi, hMi⟩, hvω⟩
      rcases le_abs'.1 hMi with h | h
      · exact Or.inr ⟨hBω, ⟨i, hi, by linarith⟩, hvω⟩
      · exact Or.inl ⟨hBω, ⟨i, hi, h⟩, hvω⟩
    _ ≤ P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ M i ω) ∧ condQvar P ℱ M n ω ≤ v} +
        P.real {ω | ω ∈ B ∧ (∃ i ≤ n, t ≤ -M i ω) ∧ condQvar P ℱ M n ω ≤ v} :=
      measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- The two-sided eventwise Freedman bound over an arbitrary finite time interval. -/
theorem measureReal_max_abs_sub_condQvar_le {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) {j k : ℕ} (hjk : j ≤ k)
    {b : ℝ} (hinc : ∀ i, i < k → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {t v : ℝ} (hb : 0 < b) (ht : 0 < t) (hv : 0 < v)
    {B : Set Ω} (hB : MeasurableSet[ℱ j] B) :
    P.real {ω | ω ∈ B ∧ (∃ i, j ≤ i ∧ i ≤ k ∧ t ≤ |M i ω - M j ω|) ∧
      condQvar P ℱ M k ω - condQvar P ℱ M j ω ≤ v} ≤
      2 * Real.exp (-(t ^ 2 / (2 * (v + b * t / 3)))) * P.real B := by
  let N : ℕ → Ω → ℝ := fun i ω => M (j + i) ω - M j ω
  let G : Filtration ℕ m0 := shiftedFiltration ℱ j
  have hN : Martingale N G P := martingale_shift_sub hmart j
  have hN0 : ∀ ω, N 0 ω = 0 := by intro ω; simp [N]
  have hNinc : ∀ i, i < k - j → ∀ ω, |N (i + 1) ω - N i ω| ≤ b := by
    intro i hi ω
    have hi' : j + i < k := by omega
    have h := hinc (j + i) hi' ω
    convert h using 1
    dsimp [N]
    congr 1
    simp only [Nat.add_assoc]
    ring
  have hBG : MeasurableSet[G 0] B := by
    change MeasurableSet[ℱ (j + 0)] B
    simpa only [Nat.add_zero] using hB
  have h := measureReal_max_abs_condQvar_le hN hN0 hNinc hb ht hv hBG
  have hvar : ∀ ω, condQvar P G N (k - j) ω =
      condQvar P ℱ M k ω - condQvar P ℱ M j ω := by
    intro ω
    change condQvar P (shiftedFiltration ℱ j) (fun i ω => M (j + i) ω - M j ω) (k - j) ω = _
    rw [condQvar_shift_sub, Nat.add_sub_of_le hjk]
  have hevent : {ω | ω ∈ B ∧ (∃ i ≤ k - j, t ≤ |N i ω|) ∧ condQvar P G N (k - j) ω ≤ v} =
      {ω | ω ∈ B ∧ (∃ i, j ≤ i ∧ i ≤ k ∧ t ≤ |M i ω - M j ω|) ∧
        condQvar P ℱ M k ω - condQvar P ℱ M j ω ≤ v} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hvar]
    constructor
    · rintro ⟨hBω, ⟨i, hi, hMi⟩, hvω⟩
      exact ⟨hBω, ⟨j + i, by omega, by omega, hMi⟩, hvω⟩
    · rintro ⟨hBω, ⟨i, hji, hik, hMi⟩, hvω⟩
      refine ⟨hBω, ⟨i - j, by omega, ?_⟩, hvω⟩
      simpa [N, Nat.add_sub_of_le hji] using hMi
  rw [hevent] at h
  exact h

/-- The partial sums of increments, kept constant after the finite horizon. -/
noncomputable def boundedDifferenceSum (ξ : ℕ → Ω → ℝ) (k i : ℕ) : Ω → ℝ :=
  fun ω => ∑ l ∈ Finset.Icc 1 (min i k), ξ l ω

/-- Before the horizon, the next difference of the partial sums is the next increment. -/
theorem boundedDifferenceSum_succ {ξ : ℕ → Ω → ℝ} {k i : ℕ} (hi : i < k) :
    boundedDifferenceSum ξ k (i + 1) = boundedDifferenceSum ξ k i + ξ (i + 1) := by
  funext ω
  simp only [boundedDifferenceSum, min_eq_left (le_of_lt hi), min_eq_left (Nat.succ_le_of_lt hi), Pi.add_apply]
  rw [Finset.sum_Icc_succ_top (by omega) (fun j => ξ j ω)]

/-- The bounded partial sums form a martingale when the increments have conditional mean zero. -/
theorem martingale_boundedDifferenceSum {ℱ : Filtration ℕ m0} [IsFiniteMeasure P]
    {ξ : ℕ → Ω → ℝ} {k : ℕ}
    (hξ : ∀ i, Measurable[ℱ i] (ξ i)) (hint : ∀ i, Integrable (ξ i) P)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → P[ξ i | ℱ (i - 1)] =ᵐ[P] 0) :
    Martingale (boundedDifferenceSum ξ k) ℱ P := by
  have hadapted : StronglyAdapted ℱ (boundedDifferenceSum ξ k) := by
    intro i
    unfold boundedDifferenceSum
    have h := Finset.stronglyMeasurable_sum (M := ℝ) (f := fun j : ℕ => ξ j)
      (Finset.Icc 1 (min i k)) fun j hj => by
        exact (hξ j).stronglyMeasurable.mono (ℱ.mono (le_trans (Finset.mem_Icc.mp hj).2 (min_le_left _ _)))
    rw [show (∑ j ∈ Finset.Icc 1 (min i k), ξ j) =
      (fun ω => ∑ j ∈ Finset.Icc 1 (min i k), ξ j ω) by
        funext ω
        rw [Finset.sum_apply]] at h
    exact h
  have hintsum : ∀ i, Integrable (boundedDifferenceSum ξ k i) P := by
    intro i
    exact integrable_finsetSum (Finset.Icc 1 (min i k)) fun j _ => hint j
  refine martingale_of_condExp_sub_eq_zero_nat hadapted hintsum ?_
  intro i
  by_cases hi : i < k
  · have heq : boundedDifferenceSum ξ k (i + 1) - boundedDifferenceSum ξ k i = ξ (i + 1) := by
      rw [boundedDifferenceSum_succ hi]
      abel
    rw [heq]
    simpa only [Nat.add_sub_cancel] using hmean (i + 1) (by omega) (by omega)
  · have hk : k ≤ i := Nat.le_of_not_gt hi
    have heq : boundedDifferenceSum ξ k (i + 1) - boundedDifferenceSum ξ k i = 0 := by
      funext ω
      simp [boundedDifferenceSum, min_eq_right hk, min_eq_right (hk.trans (Nat.le_succ i))]
    rw [heq]
    simp

/-- Bounded increments give the required increment bound for the stopped partial sums. -/
theorem boundedDifferenceSum_increment_le {ξ : ℕ → Ω → ℝ} {k : ℕ} {a : ℝ}
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) :
    ∀ i, i < k → ∀ ω,
      |boundedDifferenceSum ξ k (i + 1) ω - boundedDifferenceSum ξ k i ω| ≤ a := by
  intro i hi ω
  have hs := congrFun (boundedDifferenceSum_succ (ξ := ξ) hi) ω
  simp only [Pi.add_apply] at hs
  have hb := hbound (i + 1) (by omega) (by omega) ω
  convert hb using 1
  rw [hs]
  congr 1
  ring

/-- The predictable quadratic variation of the stopped sum is the sum of the conditional variances. -/
theorem condQvar_boundedDifferenceSum (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (ξ : ℕ → Ω → ℝ) (k n : ℕ) (hn : n ≤ k) (ω : Ω) :
    condQvar P ℱ (boundedDifferenceSum ξ k) n ω =
      ∑ i ∈ Finset.Icc 1 n, (P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω := by
  induction n with
  | zero => simp [condQvar]
  | succ n ih =>
      have hn' : n < k := by omega
      rw [condQvar_succ, ih (by omega), Finset.sum_Icc_succ_top (by omega)]
      have heq : (fun ω' =>
          (boundedDifferenceSum ξ k (n + 1) ω' - boundedDifferenceSum ξ k n ω') ^ 2) =
          (fun ω' => ξ (n + 1) ω' ^ 2) := by
        funext ω'
        have hs := congrFun (boundedDifferenceSum_succ (ξ := ξ) hn') ω'
        simp only [Pi.add_apply] at hs
        rw [hs]
        congr 1
        ring
      rw [heq]
      simp only [Nat.add_sub_cancel]

/-- The bounded representative of the sum of conditional variances. -/
noncomputable def clippedDifferenceVariance (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (ξ : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    min (a ^ 2) (max 0 ((P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω))

/-- The clipped variance and predictable quadratic variation agree almost surely. -/
theorem clippedDifferenceVariance_ae_eq_condQvar {ℱ : Filtration ℕ m0}
    [IsFiniteMeasure P] {ξ : ℕ → Ω → ℝ} {k : ℕ} {a : ℝ}
    (hξ : ∀ i, Measurable[ℱ i] (ξ i))
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a)
    {n : ℕ} (hn : n ≤ k) :
    clippedDifferenceVariance P ℱ ξ a n =ᵐ[P] condQvar P ℱ (boundedDifferenceSum ξ k) n := by
  have hclip : ∀ i, 1 ≤ i → i ≤ k → ∀ᵐ ω ∂P,
      min (a ^ 2) (max 0 ((P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω)) =
        ((P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω) := by
    intro i hi hik
    have hsqint : Integrable (fun ω => ξ i ω ^ 2) P := by
      refine Integrable.mono' (integrable_const (a ^ 2))
        (((hξ i).mono (ℱ.le i) le_rfl).pow_const 2).aestronglyMeasurable ?_
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hbound i hi hik ω, abs_nonneg (ξ i ω), sq_abs (ξ i ω)]
    have hnonneg := condExp_nonneg (μ := P) (m := ℱ (i - 1))
      (f := fun ω => ξ i ω ^ 2) (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    have hupper := condExp_mono (m := ℱ (i - 1)) hsqint (integrable_const (a ^ 2))
      (Filter.Eventually.of_forall fun ω => by
        nlinarith [hbound i hi hik ω, abs_nonneg (ξ i ω), sq_abs (ξ i ω)])
    rw [condExp_const (ℱ.le (i - 1))] at hupper
    filter_upwards [hnonneg, hupper] with ω h0 h1
    simp only [Pi.zero_apply] at h0
    simp only [max_eq_right h0, min_eq_right h1]
  have hall : ∀ᵐ ω ∂P, ∀ i, 1 ≤ i → i ≤ k →
      min (a ^ 2) (max 0 ((P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω)) =
        ((P[fun ω' => ξ i ω' ^ 2 | ℱ (i - 1)]) ω) := by
    refine ae_all_iff.mpr fun i => ?_
    by_cases hi : 1 ≤ i ∧ i ≤ k
    · filter_upwards [hclip i hi.1 hi.2] with ω hω _ _
      exact hω
    · exact Filter.Eventually.of_forall fun ω h1 h2 => (hi ⟨h1, h2⟩).elim
  filter_upwards [hall] with ω hω
  rw [condQvar_boundedDifferenceSum P ℱ ξ k n hn ω]
  apply Finset.sum_congr rfl
  intro i hi
  exact hω i (Finset.mem_Icc.mp hi).1 (le_trans (Finset.mem_Icc.mp hi).2 hn)

/-- Eventwise maximal Freedman inequality for finite bounded martingale differences. -/
theorem measureReal_max_abs_partialSum_le {ℱ : Filtration ℕ m0} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {j k : ℕ} (hjk : j ≤ k)
    (hξ : ∀ i, Measurable[ℱ i] (ξ i)) (hint : ∀ i, Integrable (ξ i) P)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → P[ξ i | ℱ (i - 1)] =ᵐ[P] 0)
    {a : ℝ} (ha : 0 < a)
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a)
    {t v : ℝ} (ht : 0 < t) (hv : 0 < v)
    {B : Set Ω} (hB : MeasurableSet[ℱ j] B) :
    P.real {ω | ω ∈ B ∧ (∃ n, j ≤ n ∧ n ≤ k ∧
      t ≤ |(∑ i ∈ Finset.Icc 1 n, ξ i ω) - (∑ i ∈ Finset.Icc 1 j, ξ i ω)|) ∧
      clippedDifferenceVariance P ℱ ξ a k ω - clippedDifferenceVariance P ℱ ξ a j ω ≤ v} ≤
      2 * Real.exp (-(t ^ 2 / (2 * (v + a * t / 3)))) * P.real B := by
  have hmart := martingale_boundedDifferenceSum hξ hint hmean
  have hinc := boundedDifferenceSum_increment_le hbound
  have h := measureReal_max_abs_sub_condQvar_le hmart hjk hinc ha ht hv hB
  have hqj := clippedDifferenceVariance_ae_eq_condQvar (P := P) hξ hbound hjk
  have hqk := clippedDifferenceVariance_ae_eq_condQvar (P := P) hξ hbound (le_refl k)
  have hevent :
      {ω | ω ∈ B ∧ (∃ n, j ≤ n ∧ n ≤ k ∧
        t ≤ |boundedDifferenceSum ξ k n ω - boundedDifferenceSum ξ k j ω|) ∧
        condQvar P ℱ (boundedDifferenceSum ξ k) k ω -
          condQvar P ℱ (boundedDifferenceSum ξ k) j ω ≤ v} =ᵐ[P]
      {ω | ω ∈ B ∧ (∃ n, j ≤ n ∧ n ≤ k ∧
        t ≤ |(∑ i ∈ Finset.Icc 1 n, ξ i ω) - (∑ i ∈ Finset.Icc 1 j, ξ i ω)|) ∧
        clippedDifferenceVariance P ℱ ξ a k ω - clippedDifferenceVariance P ℱ ξ a j ω ≤ v} := by
    filter_upwards [hqj, hqk] with ω hj hk
    apply propext
    constructor
    · rintro ⟨hBω, ⟨n, hjn, hnk, hsum⟩, hvar⟩
      refine ⟨hBω, ⟨n, hjn, hnk, ?_⟩, ?_⟩
      · simpa [boundedDifferenceSum, min_eq_left hnk, min_eq_left hjk] using hsum
      · simpa [hj, hk] using hvar
    · rintro ⟨hBω, ⟨n, hjn, hnk, hsum⟩, hvar⟩
      refine ⟨hBω, ⟨n, hjn, hnk, ?_⟩, ?_⟩
      · simpa [boundedDifferenceSum, min_eq_left hnk, min_eq_left hjk] using hsum
      · simpa [hj, hk] using hvar
  have hmeasure := measure_congr hevent
  change P.real _ ≤ _ at h
  unfold Measure.real at h ⊢
  rw [← hmeasure]
  exact h

end LatticeProb
