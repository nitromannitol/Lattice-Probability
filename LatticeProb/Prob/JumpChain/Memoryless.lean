import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Residual exponential clocks

Partial sums and residual clock sequences are measurable. Translation of a restricted
exponential law gives the exponential survival factor. Splitting the infinite product law
and applying Fubini proves that the residual sequence is independent of a measurable prefix
event and the event specifying the current ring count at a deterministic time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.JumpChain

noncomputable section

open Classical

/-- The time of the `n`-th ring is the sum of the preceding clocks. -/
def clockSum (e : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, e k

/-- The residual clock and subsequent untouched clocks at time `s` after ring `n`. -/
def clockShift (n : ℕ) (s : ℝ) (e : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if k = 0 then clockSum e (n + 1) - s else e (n + k)

/-- Finite clock sums are measurable. -/
@[fun_prop]
theorem measurable_clockSum (n : ℕ) : Measurable (fun e ↦ clockSum e n) := by
  unfold clockSum
  fun_prop

/-- The residual clock sequence is measurable at each deterministic ring and time. -/
@[fun_prop]
theorem measurable_clockShift (n : ℕ) (s : ℝ) : Measurable (clockShift n s) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = 0
  · simp only [clockShift, if_pos hk]
    exact (measurable_clockSum (n + 1)).sub_const s
  · simp only [clockShift, if_neg hk]
    exact measurable_pi_apply (n + k)

/-- Adding one clock gives the next ring time. -/
theorem clockSum_succ (e : ℕ → ℝ) (n : ℕ) :
    clockSum e (n + 1) = clockSum e n + e n := by
  exact Finset.sum_range_succ e n

/-- The exponential density factors under a nonnegative translation. -/
theorem exponentialPDF_add {R c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) :
    exponentialPDF R (y + c) =
      ENNReal.ofReal (Real.exp (-(R * c))) * exponentialPDF R y := by
  rw [exponentialPDF_of_nonneg (add_nonneg hy hc), exponentialPDF_of_nonneg hy]
  have hexp : -(R * (y + c)) = -(R * c) + -(R * y) := by ring
  rw [hexp, Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  ring

/-- Translating Lebesgue measure with density translates its density in the opposite direction. -/
theorem map_sub_withDensity (f : ℝ → ℝ≥0∞) (c : ℝ) :
    (volume.withDensity f).map (fun x ↦ x - c) =
      volume.withDensity (fun y ↦ f (y + c)) := by
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA,
    withDensity_apply _ ((show Measurable (fun x : ℝ ↦ x - c) from by fun_prop) hA),
    withDensity_apply _ hA,
    ← lintegral_indicator ((show Measurable (fun x : ℝ ↦ x - c) from by fun_prop) hA),
    ← lintegral_indicator hA]
  rw [← lintegral_add_right_eq_self
    (((fun x ↦ x - c) ⁻¹' A).indicator f) c]
  apply lintegral_congr
  intro y
  simp only [Set.indicator_apply, Set.mem_preimage, add_sub_cancel_right]

/-- Memorylessness of the exponential law, including its unnormalized survival mass. -/
theorem expMeasure_shift {R c : ℝ} (_hR : 0 < R) (hc : 0 ≤ c) :
    ((expMeasure R).restrict (Set.Ioi c)).map (fun x ↦ x - c) =
      ENNReal.ofReal (Real.exp (-(R * c))) • expMeasure R := by
  change ((volume.withDensity (exponentialPDF R)).restrict (Ioi c)).map _ =
    _ • volume.withDensity (exponentialPDF R)
  rw [restrict_withDensity measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi, map_sub_withDensity,
    ← withDensity_smul' _ (exponentialPDF R) ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
  change (Ioi c).indicator (exponentialPDF R) (y + c) =
    ENNReal.ofReal (Real.exp (-(R * c))) * exponentialPDF R y
  by_cases hypos : 0 < y
  · rw [Set.indicator_of_mem (by exact show c < y + c by linarith)]
    exact exponentialPDF_add hc hypos.le
  · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
    rw [Set.indicator_of_notMem (by exact show ¬c < y + c by linarith),
      exponentialPDF_of_neg hyneg, mul_zero]

/-- Splitting off a finite prefix preserves the product clock law. -/
theorem infinitePi_split {R : ℝ} (hR : 0 < R) (n : ℕ) :
    MeasurePreserving
      (fun e : ℕ → ℝ ↦ ((fun i : Fin n ↦ e i), fun k ↦ e (n + k)))
      (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      ((Measure.pi (fun _ : Fin n ↦ expMeasure R)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))) := by
  letI := isProbabilityMeasure_expMeasure hR
  let κ : Bool → Type := fun b ↦ bif b then ℕ else Fin n
  let q : (b : Bool) → κ b → Measure ℝ := fun _ _ ↦ expMeasure R
  let e : (Σ b, κ b) ≃ ℕ :=
    (Equiv.sumEquivSigmaBool (Fin n) ℕ).symm.trans (finSumNatEquiv n)
  have hreindex := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ expMeasure R) e.injective
  have hcurry := Measure.infinitePi_map_piCurry q
  have hpair := Measure.infinitePi_map_eval_prod
    (P := fun b ↦ Measure.infinitePi (q b)) (i := false) (j := true) (by decide)
  refine ⟨by fun_prop, ?_⟩
  have hcomp := congrArg (fun μ ↦ μ.map
    (fun f : (b : Bool) → κ b → ℝ ↦ (f false, f true))) hcurry
  rw [Measure.map_map (by fun_prop) (by fun_prop), hpair] at hcomp
  rw [← hreindex, Measure.map_map (by fun_prop) (by fun_prop)] at hcomp
  change (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)).map
      (fun e ↦ ((fun i : Fin n ↦ e i), fun k ↦ e (n + k))) =
      (Measure.infinitePi (fun _ : Fin n ↦ expMeasure R)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) at hcomp
  simpa only [Measure.infinitePi_eq_pi] using hcomp

/-- Prepending one clock to a sequence. -/
def clockCons (x : ℝ) (e : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if k = 0 then x else e (k - 1)

/-- Prepending a clock is jointly measurable. -/
@[fun_prop]
theorem measurable_clockCons :
    Measurable (fun p : ℝ × (ℕ → ℝ) ↦ clockCons p.1 p.2) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = 0
  · simp only [clockCons, if_pos hk]
    exact measurable_fst
  · simp only [clockCons, if_neg hk]
    exact (measurable_pi_apply (k - 1)).comp measurable_snd

/-- An independent exponential clock prepended to the clock law has the same clock law. -/
theorem infinitePi_cons {R : ℝ} (hR : 0 < R) :
    MeasurePreserving (fun p : ℝ × (ℕ → ℝ) ↦ clockCons p.1 p.2)
      ((expMeasure R).prod (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)))
      (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) := by
  letI := isProbabilityMeasure_expMeasure hR
  have hs := ((measurePreserving_piUnique (fun _ : Fin 1 ↦ expMeasure R)).prod
    (MeasurePreserving.id (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)))).comp
      (infinitePi_split hR 1)
  have hsplit : (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)).map
      (fun e ↦ (e 0, fun k ↦ e (1 + k))) =
      (expMeasure R).prod (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) :=
    hs.map_eq
  refine ⟨measurable_clockCons, ?_⟩
  rw [← hsplit, Measure.map_map measurable_clockCons (by fun_prop)]
  have hid : (fun p : ℝ × (ℕ → ℝ) ↦ clockCons p.1 p.2) ∘
      (fun e : ℕ → ℝ ↦ (e 0, fun k ↦ e (1 + k))) = id := by
    funext e k
    cases k with
    | zero => rfl
    | succ k => simp only [Function.comp_apply, clockCons, Nat.succ_ne_zero,
        if_false, Nat.add_sub_cancel, Nat.add_comm, id_eq]
  rw [hid, Measure.map_id]

/-- The residual sequence under survival has the original law times the survival mass. -/
theorem expMeasure_prod_clockCons_shift {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    (((expMeasure R).restrict (Ioi c)).prod
      (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))).map
        (fun p : ℝ × (ℕ → ℝ) ↦ clockCons (p.1 - c) p.2) =
      ENNReal.ofReal (Real.exp (-(R * c))) •
        Measure.infinitePi (fun _ : ℕ ↦ expMeasure R) := by
  letI := isProbabilityMeasure_expMeasure hR
  have hcomp : (fun p : ℝ × (ℕ → ℝ) ↦ clockCons (p.1 - c) p.2) =
      (fun p ↦ clockCons p.1 p.2) ∘ Prod.map (fun x ↦ x - c) id := rfl
  rw [hcomp, ← Measure.map_map measurable_clockCons (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    Measure.map_id, expMeasure_shift hR hc, Measure.prod_smul_left,
    Measure.map_smul, (infinitePi_cons hR).map_eq]

/-- Survival and an event for the shifted sequence factor on the canonical clock space. -/
theorem infinitePi_residual_event {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    {C : Set (ℕ → ℝ)} (hC : MeasurableSet C) :
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | c < e 0 ∧ clockCons (e 0 - c) (fun k ↦ e (1 + k)) ∈ C} =
      ENNReal.ofReal (Real.exp (-(R * c))) *
        (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) C := by
  letI := isProbabilityMeasure_expMeasure hR
  have hs := ((measurePreserving_piUnique (fun _ : Fin 1 ↦ expMeasure R)).prod
    (MeasurePreserving.id (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)))).comp
      (infinitePi_split hR 1)
  have hsplit : (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)).map
      (fun e ↦ (e 0, fun k ↦ e (1 + k))) =
      (expMeasure R).prod (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) :=
    hs.map_eq
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) ↦ clockCons (p.1 - c) p.2) := by
    exact measurable_clockCons.comp ((measurable_fst.sub_const c).prodMk measurable_snd)
  have hA : MeasurableSet
      {p : ℝ × (ℕ → ℝ) | c < p.1 ∧ clockCons (p.1 - c) p.2 ∈ C} :=
    (measurableSet_lt measurable_const measurable_fst).inter (hm hC)
  change (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
    ((fun e ↦ (e 0, fun k ↦ e (1 + k))) ⁻¹'
      {p : ℝ × (ℕ → ℝ) | c < p.1 ∧ clockCons (p.1 - c) p.2 ∈ C}) = _
  rw [← Measure.map_apply (by fun_prop) hA, hsplit]
  have heq := congrArg (fun μ : Measure (ℕ → ℝ) ↦ μ C)
    (expMeasure_prod_clockCons_shift hR hc)
  rw [Measure.map_apply hm hC, Measure.smul_apply, smul_eq_mul] at heq
  rw [Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (hm hC)] at heq
  convert heq using 1
  congr 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
  exact and_comm

/-- Finite-coordinate and range presentations of the ring time agree. -/
theorem clockSum_eq_sum_fin (e : ℕ → ℝ) (n : ℕ) :
    clockSum e n = ∑ i : Fin n, e i := by
  simpa only [clockSum] using (Fin.sum_univ_eq_sum_range (fun k ↦ e k) n).symm

/-- The residual sequence is a prepended residual clock and the untouched tail. -/
theorem clockShift_eq_clockCons (n : ℕ) (s : ℝ) (e : ℕ → ℝ) :
    clockShift n s e = clockCons (clockSum e n + e n - s)
      (fun k ↦ e (n + (1 + k))) := by
  funext k
  cases k with
  | zero => simp only [clockShift, clockCons, ite_true, clockSum_succ]
  | succ k => simp [clockShift, clockCons, Nat.add_comm]

/-- Fubini identifies the residual-event mass with a weighted prefix integral. -/
theorem infinitePi_clockShift_integral {R : ℝ} (hR : 0 < R) (n : ℕ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B)
    {C : Set (ℕ → ℝ)} (hC : MeasurableSet C) (s : ℝ) :
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | (fun i : Fin n ↦ e i) ∈ B ∧ clockSum e n ≤ s ∧
        s < clockSum e (n + 1) ∧ clockShift n s e ∈ C} =
    (∫⁻ p : Fin n → ℝ,
      if p ∈ B ∧ ∑ i, p i ≤ s then
        ENNReal.ofReal (Real.exp (-(R * (s - ∑ i, p i)))) else 0
      ∂Measure.pi (fun _ : Fin n ↦ expMeasure R)) *
        (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) C := by
  letI := isProbabilityMeasure_expMeasure hR
  let A : Set ((Fin n → ℝ) × (ℕ → ℝ)) :=
    {p | p.1 ∈ B ∧ ∑ i, p.1 i ≤ s ∧ s - ∑ i, p.1 i < p.2 0 ∧
      clockCons (p.2 0 - (s - ∑ i, p.1 i)) (fun k ↦ p.2 (1 + k)) ∈ C}
  have hA : MeasurableSet A := by
    change MeasurableSet {p : (Fin n → ℝ) × (ℕ → ℝ) |
      p.1 ∈ B ∧ ∑ i, p.1 i ≤ s ∧ s - ∑ i, p.1 i < p.2 0 ∧
        clockCons (p.2 0 - (s - ∑ i, p.1 i)) (fun k ↦ p.2 (1 + k)) ∈ C}
    exact (hB.preimage measurable_fst).inter
      ((measurableSet_le
        (show Measurable (fun p : (Fin n → ℝ) × (ℕ → ℝ) ↦ ∑ i, p.1 i) from
          by fun_prop) measurable_const).inter
        ((measurableSet_lt
          (show Measurable (fun p : (Fin n → ℝ) × (ℕ → ℝ) ↦ s - ∑ i, p.1 i) from
            by fun_prop)
          (show Measurable (fun p : (Fin n → ℝ) × (ℕ → ℝ) ↦ p.2 0) from
            by fun_prop)).inter
          (hC.preimage (measurable_clockCons.comp
            (show Measurable (fun p : (Fin n → ℝ) × (ℕ → ℝ) ↦
              (p.2 0 - (s - ∑ i, p.1 i), fun k ↦ p.2 (1 + k))) from by fun_prop)))))
  have hpre : {e | (fun i : Fin n ↦ e i) ∈ B ∧ clockSum e n ≤ s ∧
      s < clockSum e (n + 1) ∧ clockShift n s e ∈ C} =
      (fun e : ℕ → ℝ ↦ ((fun i : Fin n ↦ e i), fun k ↦ e (n + k))) ⁻¹' A := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_preimage, A, Nat.add_zero,
      clockShift_eq_clockCons, clockSum_succ, clockSum_eq_sum_fin]
    have heq : e n - (s - ∑ i : Fin n, e i) = (∑ i : Fin n, e i) + e n - s := by
      ring
    rw [heq]
    exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
      and_congr_left fun _ ↦ by constructor <;> intro h <;> linarith
  rw [hpre, ← Measure.map_apply (by fun_prop) hA,
    (infinitePi_split hR n).map_eq, Measure.prod_apply hA]
  have hw : Measurable (fun p : Fin n → ℝ ↦
      if p ∈ B ∧ ∑ i, p i ≤ s then
        ENNReal.ofReal (Real.exp (-(R * (s - ∑ i, p i)))) else 0) := by
    have hcond : MeasurableSet {p : Fin n → ℝ | p ∈ B ∧ ∑ i, p i ≤ s} :=
      hB.inter (measurableSet_le
        (show Measurable (fun p : Fin n → ℝ ↦ ∑ i, p i) from by fun_prop)
        measurable_const)
    apply Measurable.ite hcond
    · fun_prop
    · exact measurable_const
  rw [← lintegral_mul_const _ hw]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ B ∧ ∑ i, p i ≤ s
  · simp only [if_pos hp]
    have hsection : Prod.mk p ⁻¹' A =
        {e | s - ∑ i, p i < e 0 ∧
          clockCons (e 0 - (s - ∑ i, p i)) (fun k ↦ e (1 + k)) ∈ C} := by
      ext e
      simp only [A, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hp.1, hp.2, h⟩⟩
    rw [hsection]
    exact infinitePi_residual_event hR (sub_nonneg.mpr hp.2) hC
  · have hsection : Prod.mk p ⁻¹' A = ∅ := by
      ext e
      simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hpB hpSum
      exact (hp ⟨hpB, hpSum⟩).elim
    rw [hsection, measure_empty, if_neg hp, zero_mul]

/-- At a deterministic time, the residual exponential sequence is independent of the prefix
and the event specifying its current ring count. -/
theorem infinitePi_clockShift {R : ℝ} (hR : 0 < R) (n : ℕ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B)
    {C : Set (ℕ → ℝ)} (hC : MeasurableSet C) (s : ℝ) :
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | (fun i : Fin n ↦ e i) ∈ B ∧ clockSum e n ≤ s ∧
        s < clockSum e (n + 1) ∧ clockShift n s e ∈ C} =
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | (fun i : Fin n ↦ e i) ∈ B ∧ clockSum e n ≤ s ∧
        s < clockSum e (n + 1)} *
      (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) C := by
  letI := isProbabilityMeasure_expMeasure hR
  have hmass := infinitePi_clockShift_integral hR n hB MeasurableSet.univ s
  simp only [Set.mem_univ, and_true, measure_univ, mul_one] at hmass
  rw [infinitePi_clockShift_integral hR n hB hC s, hmass]

end

end LatticeProb.JumpChain
