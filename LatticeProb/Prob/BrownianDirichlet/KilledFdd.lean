import LatticeProb.Prob.BrownianDirichlet.KilledKernel
import LatticeProb.Prob.BrownianDirichlet.KilledLp
import LatticeProb.Prob.BrownianDirichlet.KilledStrongContinuity
import LatticeProb.Prob.BrownianWeakMarkovPath

/-!
# Products of killed Brownian observations

Observation schedules use successive nonnegative time increments. The empty schedule
has payoff one. Nonempty schedules include survival through their last observation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb

noncomputable section

variable {d : ℕ}

/-- Integrating a bounded future payoff after a surviving deterministic past gives
one application of the killed kernel. -/
lemma integral_killed_shift {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (s : ℝ≥0)
    {F : Euc d × BrownianPath d → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ p, |F p| ≤ C) (x : Euc d) :
    (∫ ω, if (s : ℝ≥0∞) < scaledExit B σ x ω
      then F (x + σ • ω s, shiftedBrownianPath s ω) else 0 ∂μ) =
      killed B σ μ s (fun y ↦ ∫ η, F (y, η) ∂μ) x := by
  letI : IsProbabilityMeasure μ := hμ.1
  let past := fun ω : BrownianPath d ↦
    ((if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0 : ℝ), x + σ • ω s)
  let G := fun p : (ℝ × Euc d) × BrownianPath d ↦ p.1.1 * F (p.1.2, p.2)
  have hpast : Measurable past :=
    (measurable_killed_past hB σ x s).mono ((brownianNaturalFiltration d).le s) le_rfl
  have hG : Measurable G := measurable_fst.fst.mul
    (hF.comp (measurable_fst.snd.prodMk measurable_snd))
  have hprod := (indepFun_killed_past_shift hB σ hμ x s).map_prod_eq_prod_map_map
    hpast.aemeasurable (measurable_shiftedBrownianPath s).aemeasurable
  rw [standardBrownianLaw_map_shift hμ s] at hprod
  have hpastbound : ∀ᵐ a ∂μ.map past, |a.1| ≤ (1 : ℝ) := by
    apply (ae_map_iff hpast.aemeasurable
      (measurableSet_le measurable_fst.abs measurable_const)).mpr
    exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp [past]
      split_ifs <;> norm_num
  have hi : Integrable G ((μ.map past).prod μ) := by
    apply Integrable.of_bound hG.aestronglyMeasurable C
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hG.norm measurable_const)).mpr
    filter_upwards [hpastbound] with a ha
    exact Filter.Eventually.of_forall fun η ↦ by
      change ‖a.1 * F (a.2, η)‖ ≤ C
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans
        ((one_mul _).le.trans (hFC _))
  calc
    _ = ∫ ω, G (past ω, shiftedBrownianPath s ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        dsimp [G, past]
        split_ifs <;> simp only [one_mul, zero_mul]
    _ = ∫ p, G p ∂((μ.map past).prod μ) := by
      rw [← hprod]
      exact (integral_map (hpast.prodMk
        (measurable_shiftedBrownianPath s)).aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ a, ∫ η, G (a, η) ∂μ ∂(μ.map past) := integral_prod G hi
    _ = ∫ ω, ∫ η, G (past ω, η) ∂μ ∂μ :=
      integral_map hpast.aemeasurable
        hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        change (∫ η, (past ω).1 * F ((past ω).2, η) ∂μ) = _
        rw [integral_const_mul]
        dsimp [past]
        split_ifs <;> simp only [one_mul, zero_mul]

/-- The path payoff for a finite schedule of time increments and spatial marks. -/
def killedProduct (B : Set (Euc d)) (σ : ℝ) :
    List (ℝ≥0 × (Euc d → ℝ)) → Euc d → BrownianPath d → ℝ
  | [], _, _ => 1
  | (s, b) :: rest, x, ω =>
      if (s : ℝ≥0∞) < scaledExit B σ x ω then
        b (x + σ • ω s) *
          killedProduct B σ rest (x + σ • ω s) (shiftedBrownianPath s ω)
      else 0

/-- Backward iteration of killed kernels for a finite observation schedule. -/
def killedProductKernel (B : Set (Euc d)) (σ : ℝ) (μ : Measure (BrownianPath d)) :
    List (ℝ≥0 × (Euc d → ℝ)) → Euc d → ℝ
  | [] => fun _ ↦ 1
  | (s, b) :: rest => killed B σ μ s (fun y ↦ b y * killedProductKernel B σ μ rest y)

/-- Borel marks make the entire finite path payoff jointly measurable. -/
lemma measurable_killedProduct {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2) :
    Measurable (fun p : Euc d × BrownianPath d ↦ killedProduct B σ schedule p.1 p.2) := by
  induction schedule with
  | nil => exact measurable_const
  | cons a rest ih =>
    rcases a with ⟨s, b⟩
    have hrest := ih (fun a ha ↦ hb a (List.mem_cons_of_mem _ ha))
    have hpos : Measurable (fun p : Euc d × BrownianPath d ↦ p.1 + σ • p.2 s) := by
      fun_prop
    have hfuture := hrest.comp
      (hpos.prodMk ((measurable_shiftedBrownianPath s).comp measurable_snd))
    have hmark := (hb (s, b) (List.mem_cons_self)).comp hpos
    exact Measurable.ite
      (measurableSet_lt measurable_const (measurable_scaledExit_joint hB σ))
      (hmark.mul hfuture) measurable_const

/-- The product of uniform bounds controls the finite path payoff. -/
lemma abs_killedProduct_le (B : Set (Euc d)) (σ : ℝ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ω, |killedProduct B σ schedule x ω| ≤ C := by
  induction schedule with
  | nil => exact ⟨1, zero_le_one, fun _ _ ↦ by simp [killedProduct]⟩
  | cons a rest ih =>
    rcases a with ⟨s, b⟩
    obtain ⟨C, hC, hbC⟩ := hb (s, b) List.mem_cons_self
    obtain ⟨D, hD, hrD⟩ := ih (fun a ha ↦ hb a (List.mem_cons_of_mem _ ha))
    refine ⟨C * D, mul_nonneg hC hD, fun x ω ↦ ?_⟩
    dsimp only [killedProduct]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hbC _) (hrD _ _) (abs_nonneg _) hC
    · simpa only [abs_zero] using mul_nonneg hC hD

/-- Every finite killed product expectation is the backward kernel recursion. -/
lemma killed_product_recursion {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C)
    (x : Euc d) :
    (∫ ω, killedProduct B σ schedule x ω ∂μ) =
      killedProductKernel B σ μ schedule x := by
  letI : IsProbabilityMeasure μ := hμ.1
  induction schedule generalizing x with
  | nil => simp only [killedProduct, killedProductKernel, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
  | cons a rest ih =>
    rcases a with ⟨s, b⟩
    have hbr := fun a ha ↦ hb a (List.mem_cons_of_mem _ ha)
    have hbdr := fun a ha ↦ hbound a (List.mem_cons_of_mem _ ha)
    obtain ⟨C, hC, hbC⟩ := hbound (s, b) List.mem_cons_self
    obtain ⟨D, hD, hrD⟩ := abs_killedProduct_le B σ rest hbdr
    let F := fun p : Euc d × BrownianPath d ↦ b p.1 * killedProduct B σ rest p.1 p.2
    have hF : Measurable F := ((hb (s, b) List.mem_cons_self).comp measurable_fst).mul
      (measurable_killedProduct hB σ rest hbr)
    have hFC : ∀ p, |F p| ≤ C * D := fun p ↦ by
      exact (abs_mul _ _).trans_le (mul_le_mul (hbC _) (hrD _ _) (abs_nonneg _) hC)
    change (∫ ω, if (s : ℝ≥0∞) < scaledExit B σ x ω
      then F (x + σ • ω s, shiftedBrownianPath s ω) else 0 ∂μ) = _
    rw [integral_killed_shift hB σ hμ s hF hFC]
    congr 1
    funext y
    change (∫ η, b y * killedProduct B σ rest y η ∂μ) = _
    rw [integral_const_mul, ih hbr hbdr]

/-- The un-killed product of spatial marks at successive observation increments. -/
def observationProduct (σ : ℝ) :
    List (ℝ≥0 × (Euc d → ℝ)) → Euc d → BrownianPath d → ℝ
  | [], _, _ => 1
  | (s, b) :: rest, x, ω => b (x + σ • ω s) *
      observationProduct σ rest (x + σ • ω s) (shiftedBrownianPath s ω)

/-- Convert successive increments to absolute observation times, starting at `u`. -/
def cumulativeObservations (u : ℝ≥0) :
    List (ℝ≥0 × (Euc d → ℝ)) → List (ℝ≥0 × (Euc d → ℝ))
  | [] => []
  | (s, b) :: rest => (u + s, b) :: cumulativeObservations (u + s) rest

/-- The restarted-path product is the product of marks on the original path at
cumulative observation times. -/
lemma observationProduct_eq_prod (σ : ℝ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ))) (x : Euc d) (ω : BrownianPath d) :
    observationProduct σ schedule x ω =
      ((cumulativeObservations 0 schedule).map (fun a ↦ a.2 (x + σ • ω a.1))).prod := by
  have htransfer : ∀ schedule : List (ℝ≥0 × (Euc d → ℝ)),
      ∀ (y : Euc d) (η : BrownianPath d) (u : ℝ≥0),
      (∀ t, y + σ • η t = x + σ • ω (u + t)) →
      observationProduct σ schedule y η =
        ((cumulativeObservations u schedule).map
          (fun a ↦ a.2 (x + σ • ω a.1))).prod := by
    intro schedule
    induction schedule with
    | nil => intros; rfl
    | cons a rest ih =>
      rcases a with ⟨s, b⟩
      intro y η u hpos
      dsimp only [observationProduct, cumulativeObservations, List.map_cons, List.prod_cons]
      refine congrArg₂ (· * ·) (congrArg b (hpos s)) ?_
      apply ih
      intro t
      rw [shiftedBrownianPath_position, hpos (s + t), add_assoc]
  exact htransfer schedule x ω 0 (fun t ↦ by rw [zero_add])

/-- A nonempty schedule has exactly one killing condition, at its final time. -/
lemma killedProduct_eq_final_survival {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ))) (hne : schedule ≠ [])
    (x : Euc d) (ω : BrownianPath d) :
    killedProduct B σ schedule x ω =
      if ((schedule.map Prod.fst).sum : ℝ≥0∞) < scaledExit B σ x ω
      then observationProduct σ schedule x ω else 0 := by
  induction schedule generalizing x ω with
  | nil => exact (hne rfl).elim
  | cons a rest ih =>
    rcases a with ⟨s, b⟩
    cases rest with
    | nil => simp only [killedProduct, observationProduct, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, mul_one]
    | cons a rest =>
      rw [killedProduct, ih (List.cons_ne_nil _ _)]
      simp only [List.map_cons, List.sum_cons, survival_split hB σ, observationProduct]
      split_ifs <;> simp_all only [mul_zero, and_self, and_false, false_and,
        not_true_eq_false]

/-- The ordinary finite product, killed only at the last cumulative time, equals
the backward iteration of the killed kernels. -/
lemma killed_product_expectation {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ))) (hne : schedule ≠ [])
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C)
    (x : Euc d) :
    (∫ ω, if ((schedule.map Prod.fst).sum : ℝ≥0∞) < scaledExit B σ x ω
      then ((cumulativeObservations 0 schedule).map
        (fun a ↦ a.2 (x + σ • ω a.1))).prod else 0 ∂μ) =
      killedProductKernel B σ μ schedule x := by
  convert killed_product_recursion hB σ hμ schedule hb hbound x using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [killedProduct_eq_final_survival hB σ schedule hne, observationProduct_eq_prod]

/-- A single observation is the usual killed evaluation, without extra killing factors. -/
lemma killedProduct_singleton (B : Set (Euc d)) (σ : ℝ) (s : ℝ≥0)
    (b : Euc d → ℝ) (x : Euc d) (ω : BrownianPath d) :
    killedProduct B σ [(s, b)] x ω =
      if (s : ℝ≥0∞) < scaledExit B σ x ω then b (x + σ • ω s) else 0 := by
  simp only [killedProduct, mul_one]

/-- Two observations occur at `s` and `s + t` in the original path coordinates. -/
lemma killedProduct_pair {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (s t : ℝ≥0) (b c : Euc d → ℝ) (x : Euc d) (ω : BrownianPath d) :
    killedProduct B σ [(s, b), (t, c)] x ω =
      if ((s + t : ℝ≥0) : ℝ≥0∞) < scaledExit B σ x ω
      then b (x + σ • ω s) * c (x + σ • ω (s + t)) else 0 := by
  rw [killedProduct_eq_final_survival hB σ _ (List.cons_ne_nil _ _)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    observationProduct, mul_one, shiftedBrownianPath_position]

/-- Backward iteration preserves Borel measurability and a finite uniform bound. -/
lemma killedProductKernel_bounded {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C) :
    Measurable (killedProductKernel B σ μ schedule) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |killedProductKernel B σ μ schedule y| ≤ C := by
  letI : IsProbabilityMeasure μ := hμ.1
  induction schedule with
  | nil => exact ⟨measurable_const, 1, zero_le_one, fun _ ↦ by simp [killedProductKernel]⟩
  | cons a rest ih =>
    rcases a with ⟨s, b⟩
    obtain ⟨hr, D, hD, hrD⟩ := ih
      (fun a ha ↦ hb a (List.mem_cons_of_mem _ ha))
      (fun a ha ↦ hbound a (List.mem_cons_of_mem _ ha))
    obtain ⟨C, hC, hbC⟩ := hbound (s, b) List.mem_cons_self
    have hm := (hb (s, b) List.mem_cons_self).mul hr
    have hbd : ∀ y, |b y * killedProductKernel B σ μ rest y| ≤ C * D := fun y ↦
      (abs_mul _ _).trans_le (mul_le_mul (hbC y) (hrD y) (abs_nonneg _) hC)
    exact ⟨measurable_killed hB σ s hm, C * D, mul_nonneg hC hD,
      abs_killed_le σ s (mul_nonneg hC hD) hbd⟩

variable {B : Set (Euc d)} [IsFiniteMeasure (volume.restrict B)]

/-- The backward finite-observation kernel belongs to L² on a finite-volume domain. -/
lemma memLp_killedProductKernel (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C) :
    MemLp (killedProductKernel B σ μ schedule) 2 (volume.restrict B) := by
  obtain ⟨hm, C, _, hC⟩ := killedProductKernel_bounded hB σ hμ schedule hb hbound
  exact MemLp.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y ↦ (Real.norm_eq_abs _).trans_le (hC y))

/-- A finite product expectation paired against any L² initial density is its
L² inner product with the backward kernel. -/
lemma killed_product_inner (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C)
    {g : Euc d → ℝ} (hg : MemLp g 2 (volume.restrict B)) :
    (∫ x, g x * (∫ ω, killedProduct B σ schedule x ω ∂μ) ∂(volume.restrict B)) =
      inner ℝ (hg.toLp g)
        ((memLp_killedProductKernel hB σ hμ schedule hb hbound).toLp
          (killedProductKernel B σ μ schedule)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp,
    (memLp_killedProductKernel hB σ hμ schedule hb hbound).coeFn_toLp] with x hgx hkx
  rw [hgx, hkx, killed_product_recursion hB σ hμ schedule hb hbound]
  simp only [Real.inner_apply]

/-- Each nonempty backward L² kernel is one application of the killed semigroup
to the current mark times the remaining backward kernel. -/
lemma killedProductKernel_toLp_cons (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (s : ℝ≥0) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C)
    (rest : List (ℝ≥0 × (Euc d → ℝ)))
    (hr : ∀ a ∈ rest, Measurable a.2)
    (hrbound : ∀ a ∈ rest, ∃ D : ℝ, 0 ≤ D ∧ ∀ y, |a.2 y| ≤ D) :
    ∃ hdata : MemLp (fun y ↦ b y * killedProductKernel B σ μ rest y)
        2 (volume.restrict B),
      ∃ hout : MemLp (killedProductKernel B σ μ ((s, b) :: rest))
          2 (volume.restrict B),
        hout.toLp (killedProductKernel B σ μ ((s, b) :: rest)) =
          (killedSemigroup hB σ hμ).operator s (hdata.toLp _) := by
  obtain ⟨hm, D, hD, hrD⟩ := killedProductKernel_bounded hB σ hμ rest hr hrbound
  have hmeas := hb.mul hm
  have hbd : ∀ y, |b y * killedProductKernel B σ μ rest y| ≤ C * D := fun y ↦
    (abs_mul _ _).trans_le (mul_le_mul (hbC y) (hrD y) (abs_nonneg _) hC)
  have hdata : MemLp (fun y ↦ b y * killedProductKernel B σ μ rest y)
      2 (volume.restrict B) := MemLp.of_bound hmeas.aestronglyMeasurable (C * D)
        (Filter.Eventually.of_forall fun y ↦ (Real.norm_eq_abs _).trans_le (hbd y))
  refine ⟨hdata, memLp_killed hB σ hμ s hmeas (mul_nonneg hC hD) hbd, ?_⟩
  exact (killedLp_toLp hB σ hμ s hmeas (mul_nonneg hC hD) hbd hdata).symm

omit [IsFiniteMeasure (volume.restrict B)] in
/-- Fubini converts expectation under any finite initial law and Brownian law
into the integral of the backward kernel. -/
lemma integral_prod_killedProduct (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C)
    (ρ : Measure (Euc d)) [IsFiniteMeasure ρ] :
    (∫ p, killedProduct B σ schedule p.1 p.2 ∂(ρ.prod μ)) =
      ∫ x, killedProductKernel B σ μ schedule x ∂ρ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨C, _, hC⟩ := abs_killedProduct_le B σ schedule hbound
  have hi : Integrable (fun p : Euc d × BrownianPath d ↦
      killedProduct B σ schedule p.1 p.2) (ρ.prod μ) :=
    Integrable.of_bound (measurable_killedProduct hB σ schedule hb).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p ↦ (Real.norm_eq_abs _).trans_le (hC p.1 p.2))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (killed_product_recursion hB σ hμ schedule hb hbound)

/-- A probability density against restricted volume gives the same L² pairing
when the starting point and Brownian path are sampled under the product measure. -/
lemma killed_product_density_inner (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (schedule : List (ℝ≥0 × (Euc d → ℝ)))
    (hb : ∀ a ∈ schedule, Measurable a.2)
    (hbound : ∀ a ∈ schedule, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C)
    {g : Euc d → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgLp : MemLp g 2 (volume.restrict B))
    (hprob : ∫⁻ x, ENNReal.ofReal (g x) ∂(volume.restrict B) = 1) :
    (∫ p, killedProduct B σ schedule p.1 p.2
      ∂(((volume.restrict B).withDensity (fun x ↦ ENNReal.ofReal (g x))).prod μ)) =
      inner ℝ (hgLp.toLp g)
        ((memLp_killedProductKernel hB σ hμ schedule hb hbound).toLp
          (killedProductKernel B σ μ schedule)) := by
  letI : IsFiniteMeasure
      ((volume.restrict B).withDensity (fun x ↦ ENNReal.ofReal (g x))) :=
    isFiniteMeasure_withDensity (by rw [hprob]; exact ENNReal.one_ne_top)
  rw [integral_prod_killedProduct hB σ hμ schedule hb hbound,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
  convert killed_product_inner hB σ hμ schedule hb hbound hgLp using 1
  congr 1
  funext x
  rw [killed_product_recursion hB σ hμ schedule hb hbound]

end

end LatticeProb
