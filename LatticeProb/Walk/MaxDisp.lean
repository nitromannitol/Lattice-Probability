/-
The maximal displacement of simple random walk.

`P_x(max_{k ≤ n} |X_k - x| ≥ a) ≤ C exp(-c a^2 / n)`.  Two ingredients, neither
of which needs a local limit theorem.

The first is **Lévy's inequality**: for a walk with symmetric independent
increments, the maximum of the norm up to time `n` is at most twice as likely
to be large as the norm at time `n` itself.  The proof reflects the increments
after the first time the norm is large: the reflected path has the same law,
the reflection does not change the path up to that time, and the two paths sum
to twice the position at that time, so at least one of them is large at time
`n`.  Nothing but the invariance of the law under reflecting a tail of the
increments enters.

The second is the **Chernoff bound at a fixed time**.  Each coordinate of one
increment is `+1` and `-1` with probability `1/(2d)` each and `0` otherwise, so
its moment generating function is `1 + (cosh θ - 1)/d ≤ exp(θ^2/d)` for
`|θ| ≤ 1`, and the coordinates of the position at time `n` are exponentially
concentrated.  The `ℓ¹` norm is at least `a` only when some coordinate is at
least `a/d`, so a union bound over the `2d` signed coordinates finishes.  Every
integral is a lower integral, so no integrability hypothesis is needed.
-/
import LatticeProb.Walk.Markov
import LatticeProb.Walk.SRW
import LatticeProb.Prob.InfinitePiSplit

noncomputable section

namespace LatticeProb

open MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-! ### The displacement -/

/-- The displacement of the walk after `k` steps. -/
def incSum (k : ℕ) (ξ : ℕ → Site d) : Site d := ∑ j ∈ Finset.range k, ξ j

theorem sitePath_eq_add_incSum (x : Site d) (ξ : ℕ → Site d) (k : ℕ) :
    sitePath x ξ k = x + incSum k ξ := rfl

theorem measurable_incSum (k : ℕ) : Measurable (incSum (d := d) k) :=
  Finset.measurable_sum _ fun j _ => measurable_pi_apply j

theorem incSum_consNat (n : ℕ) (u : Site d) (ω : ℕ → Site d) :
    incSum (n + 1) (consNat u ω) = u + incSum n ω := by
  rw [incSum, Finset.sum_range_succ']
  simp only [consNat_zero, consNat_succ]
  rw [incSum, add_comm]

/-- The displacement moves by at most one in the `ℓ¹` norm at each step whose
increment is a unit vector. -/
theorem graphNorm_incSum_le {k : ℕ} {ξ : ℕ → Site d} (h : ∀ j < k, graphNorm (ξ j) = 1) :
    graphNorm (incSum k ξ) ≤ k := by
  induction k with
  | zero => simp [incSum]
  | succ k ih =>
      have hk : graphNorm (incSum k ξ) ≤ k := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
      have : incSum (k + 1) ξ = incSum k ξ + ξ k := by
        rw [incSum, incSum, Finset.sum_range_succ]
      rw [this]
      calc graphNorm (incSum k ξ + ξ k) ≤ graphNorm (incSum k ξ) + graphNorm (ξ k) :=
            graphNorm_add_le _ _
        _ ≤ k + 1 := by rw [h k (Nat.lt_succ_self k)]; omega

/-! ### Reflecting a tail of the increments -/

/-- The increments after time `j`, reflected. -/
def reflectAt (j : ℕ) (ξ : ℕ → Site d) : ℕ → Site d := fun k => if k < j then ξ k else -(ξ k)

theorem reflectAt_apply (j k : ℕ) (ξ : ℕ → Site d) :
    reflectAt j ξ k = (if k < j then (id : Site d → Site d) else fun v => -v) (ξ k) := by
  rw [reflectAt]
  by_cases h : k < j <;> simp [h]

theorem measurable_reflectAt (j : ℕ) : Measurable (reflectAt (d := d) j) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases h : k < j
  · simp only [reflectAt, if_pos h]
    exact measurable_pi_apply k
  · simp only [reflectAt, if_neg h]
    exact (measurable_pi_apply k).neg

theorem reflectAt_involutive (j : ℕ) (ξ : ℕ → Site d) :
    reflectAt j (reflectAt j ξ) = ξ := by
  funext k
  by_cases h : k < j <;> simp [reflectAt, h]

theorem incSum_reflectAt_of_le {j k : ℕ} (h : k ≤ j) (ξ : ℕ → Site d) :
    incSum k (reflectAt j ξ) = incSum k ξ := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m < j := lt_of_lt_of_le (Finset.mem_range.mp hm) h
  simp [reflectAt, this]

theorem incSum_reflectAt_of_ge {j k : ℕ} (h : j ≤ k) (ξ : ℕ → Site d) :
    incSum k (reflectAt j ξ) = incSum j ξ + (incSum j ξ - incSum k ξ) := by
  have hsplit : ∀ η : ℕ → Site d, incSum k η = incSum j η + ∑ m ∈ Finset.Ico j k, η m := by
    intro η
    rw [incSum, incSum, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) h]
  rw [hsplit (reflectAt j ξ), hsplit ξ, incSum_reflectAt_of_le le_rfl]
  have : ∑ m ∈ Finset.Ico j k, reflectAt j ξ m = -∑ m ∈ Finset.Ico j k, ξ m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have : ¬ m < j := by
      rw [Finset.mem_Ico] at hm
      omega
    simp [reflectAt, this]
  rw [this]
  abel

/-! ### The law is invariant under reflecting a tail -/

/-- The one-step law, evaluated on a set. -/
theorem incLaw_apply {T : Set (Site d)} (hT : MeasurableSet T) :
    incLaw d T = (2 * (d : ℝ≥0∞))⁻¹
      * ∑ i : Fin d, (T.indicator 1 (unit i) + T.indicator 1 (-unit i)) := by
  rw [incLaw, instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.coe_add, Pi.add_apply, Measure.dirac_apply' _ hT, Measure.dirac_apply' _ hT]
  simp [sub_eq_add_neg]

/-- The one-step law is symmetric. -/
theorem incLaw_map_neg (d : ℕ) : (incLaw d).map (fun v : Site d => -v) = incLaw d := by
  refine Measure.ext fun T hT => ?_
  rw [Measure.map_apply measurable_neg hT, incLaw_apply (measurable_neg hT), incLaw_apply hT]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ((fun v : Site d => -v) ⁻¹' T).indicator (1 : Site d → ℝ≥0∞) (unit i)
      = T.indicator 1 (-unit i) := by
    by_cases h : (-unit i : Site d) ∈ T
    · rw [Set.indicator_of_mem (by simpa using h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem h]
  have h2 : ((fun v : Site d => -v) ⁻¹' T).indicator (1 : Site d → ℝ≥0∞) (-unit i)
      = T.indicator 1 (unit i) := by
    by_cases h : (unit i : Site d) ∈ T
    · rw [Set.indicator_of_mem (by simpa using h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem h]
  rw [h1, h2, add_comm]

/-- Reflecting the increments from time `j` on preserves the law of the walk. -/
theorem incPathLaw_map_reflectAt (d : ℕ) [NeZero d] (j : ℕ) :
    (incPathLaw d).map (reflectAt (d := d) j) = incPathLaw d := by
  have hf : ∀ k : ℕ,
      Measurable (if k < j then (id : Site d → Site d) else fun v : Site d => -v) := by
    intro k
    by_cases h : k < j
    · simpa [h] using (measurable_id : Measurable (id : Site d → Site d))
    · simpa [h] using (measurable_neg : Measurable fun v : Site d => -v)
  have hre : (reflectAt (d := d) j)
      = fun ξ k => (if k < j then (id : Site d → Site d) else fun v : Site d => -v) (ξ k) := by
    funext ξ k
    exact reflectAt_apply j k ξ
  rw [incPathLaw, hre, Measure.infinitePi_map_pi (μ := fun _ : ℕ => incLaw d)
    (f := fun k : ℕ => if k < j then (id : Site d → Site d) else fun v : Site d => -v) hf]
  congr 1
  funext k
  by_cases h : k < j
  · simp only [h, if_pos]
    exact Measure.map_id
  · simp only [h, if_neg, not_false_iff]
    exact incLaw_map_neg d

/-! ### Lévy's inequality -/

theorem graphNorm_add_self (u : Site d) : graphNorm (u + u) = 2 * graphNorm u := by
  simp only [graphNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (u + u) i = 2 * u i := by simp [two_mul]
  rw [this]
  omega

/-- The event that the displacement is at least `a` at some time up to `n`. -/
def bigSome (a : ℝ) (n : ℕ) : Set (ℕ → Site d) :=
  {ξ | ∃ k ≤ n, a ≤ (graphNorm (incSum k ξ) : ℝ)}

/-- The event that time `j` is the first at which the displacement is at least `a`. -/
def firstBig (a : ℝ) (j : ℕ) : Set (ℕ → Site d) :=
  {ξ | a ≤ (graphNorm (incSum j ξ) : ℝ) ∧ ∀ k < j, ¬ (a ≤ (graphNorm (incSum k ξ) : ℝ))}

theorem measurable_graphNorm_incSum (k : ℕ) :
    Measurable fun ξ : ℕ → Site d => ((graphNorm (incSum k ξ) : ℕ) : ℝ) := by
  have h1 : Measurable (graphNorm (d := d)) := measurable_of_countable _
  have h2 : Measurable (fun m : ℕ => (m : ℝ)) := measurable_of_countable _
  exact h2.comp (h1.comp (measurable_incSum k))

theorem measurableSet_big (a : ℝ) (k : ℕ) :
    MeasurableSet {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum k ξ) : ℕ) : ℝ)} :=
  measurableSet_le measurable_const (measurable_graphNorm_incSum k)

theorem measurableSet_firstBig (a : ℝ) (j : ℕ) :
    MeasurableSet (firstBig (d := d) a j) := by
  have : firstBig (d := d) a j
      = {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum j ξ) : ℕ) : ℝ)}
        ∩ ⋂ k ∈ Finset.range j,
          {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum k ξ) : ℕ) : ℝ)}ᶜ := by
    ext ξ
    simp only [firstBig, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Finset.mem_range]
  rw [this]
  exact (measurableSet_big a j).inter
    (MeasurableSet.biInter (Finset.range j).countable_toSet
      fun k _ => (measurableSet_big a k).compl)

theorem bigSome_eq_iUnion (a : ℝ) (n : ℕ) :
    bigSome (d := d) a n = ⋃ j ∈ Finset.range (n + 1), firstBig a j := by
  ext ξ
  simp only [bigSome, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hbig⟩
    classical
    have hex : ∃ m, a ≤ ((graphNorm (incSum m ξ) : ℕ) : ℝ) := ⟨k, hbig⟩
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun m hm => ?_⟩
    · have : Nat.find hex ≤ k := Nat.find_le hbig
      omega
    · exact Nat.find_min hex hm
  · rintro ⟨j, hj, hbig, -⟩
    exact ⟨j, by omega, hbig⟩

theorem pairwiseDisjoint_firstBig (a : ℝ) :
    Pairwise (Function.onFun Disjoint (firstBig (d := d) a)) := by
  intro j j' hne
  refine Set.disjoint_left.mpr fun ξ hj hj' => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · exact hj'.2 j h hj.1
  · exact hj.2 j' h hj'.1

/-- Reflecting after time `j` does not change the event that `j` is the first
large time. -/
theorem reflectAt_preimage_firstBig (a : ℝ) (j : ℕ) :
    reflectAt (d := d) j ⁻¹' firstBig a j = firstBig a j := by
  ext ξ
  simp only [Set.mem_preimage, firstBig, Set.mem_setOf_eq]
  rw [incSum_reflectAt_of_le le_rfl]
  refine and_congr Iff.rfl (forall_congr' fun k => ?_)
  refine forall_congr' fun hk => ?_
  rw [incSum_reflectAt_of_le (le_of_lt hk)]

theorem measure_preimage_reflectAt (d : ℕ) [NeZero d] (j : ℕ) {S : Set (ℕ → Site d)}
    (hS : MeasurableSet S) :
    incPathLaw d (reflectAt (d := d) j ⁻¹' S) = incPathLaw d S := by
  conv_rhs => rw [← incPathLaw_map_reflectAt d j]
  rw [Measure.map_apply (measurable_reflectAt j) hS]

/-- One step of Lévy's inequality: on the event that `j` is the first large
time, the walk at time `n` is large with probability at least a half. -/
theorem measure_firstBig_le (d : ℕ) [NeZero d] {n j : ℕ} (hj : j ≤ n) (a : ℝ) :
    incPathLaw d (firstBig a j)
      ≤ 2 * incPathLaw d (firstBig a j
          ∩ {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)}) := by
  set A : Set (ℕ → Site d) :=
    {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)} with hA
  have hAmeas : MeasurableSet A := measurableSet_big a n
  have hcover : firstBig (d := d) a j
      ⊆ (firstBig a j ∩ A) ∪ (firstBig a j ∩ reflectAt (d := d) j ⁻¹' A) := by
    intro ξ hξ
    by_cases h : ξ ∈ A
    · exact Or.inl ⟨hξ, h⟩
    · refine Or.inr ⟨hξ, ?_⟩
      have hsum : incSum n ξ + incSum n (reflectAt j ξ) = incSum j ξ + incSum j ξ := by
        rw [incSum_reflectAt_of_ge hj]
        abel
      have htri : graphNorm (incSum j ξ + incSum j ξ)
          ≤ graphNorm (incSum n ξ) + graphNorm (incSum n (reflectAt j ξ)) := by
        rw [← hsum]
        exact graphNorm_add_le _ _
      rw [graphNorm_add_self] at htri
      have h1 : a ≤ ((graphNorm (incSum j ξ) : ℕ) : ℝ) := hξ.1
      have h2 : ((graphNorm (incSum n ξ) : ℕ) : ℝ) < a := by
        simpa [hA, Set.mem_setOf_eq] using h
      have htriR : (2 * (graphNorm (incSum j ξ)) : ℝ)
          ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)
            + ((graphNorm (incSum n (reflectAt j ξ)) : ℕ) : ℝ) := by
        exact_mod_cast htri
      show a ≤ ((graphNorm (incSum n (reflectAt j ξ)) : ℕ) : ℝ)
      linarith
  have hstep : incPathLaw d (firstBig a j)
      ≤ incPathLaw d (firstBig a j ∩ A)
        + incPathLaw d (firstBig a j ∩ reflectAt (d := d) j ⁻¹' A) :=
    le_trans (measure_mono hcover) (measure_union_le _ _)
  have hrefl : incPathLaw d (firstBig a j ∩ reflectAt (d := d) j ⁻¹' A)
      = incPathLaw d (firstBig a j ∩ A) := by
    have : firstBig (d := d) a j ∩ reflectAt (d := d) j ⁻¹' A
        = reflectAt (d := d) j ⁻¹' (firstBig a j ∩ A) := by
      rw [Set.preimage_inter, reflectAt_preimage_firstBig]
    rw [this, measure_preimage_reflectAt d j ((measurableSet_firstBig a j).inter hAmeas)]
  rw [hrefl] at hstep
  calc incPathLaw d (firstBig a j) ≤ incPathLaw d (firstBig a j ∩ A)
        + incPathLaw d (firstBig a j ∩ A) := hstep
    _ = 2 * incPathLaw d (firstBig a j ∩ A) := by ring

/-- **Lévy's inequality.**  The maximal displacement up to time `n` is at most
twice as likely to be large as the displacement at time `n`. -/
theorem measure_bigSome_le (d : ℕ) [NeZero d] (n : ℕ) (a : ℝ) :
    incPathLaw d (bigSome a n)
      ≤ 2 * incPathLaw d {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)} := by
  set A : Set (ℕ → Site d) :=
    {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)} with hA
  rw [bigSome_eq_iUnion, measure_biUnion_finset
    (fun j _ j' _ hne => pairwiseDisjoint_firstBig a hne)
    (fun j _ => measurableSet_firstBig a j)]
  calc ∑ j ∈ Finset.range (n + 1), incPathLaw d (firstBig a j)
      ≤ ∑ j ∈ Finset.range (n + 1), 2 * incPathLaw d (firstBig a j ∩ A) :=
        Finset.sum_le_sum fun j hj =>
          measure_firstBig_le d (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) a
    _ = 2 * ∑ j ∈ Finset.range (n + 1), incPathLaw d (firstBig a j ∩ A) := by
        rw [Finset.mul_sum]
    _ = 2 * incPathLaw d ((⋃ j ∈ Finset.range (n + 1), firstBig a j) ∩ A) := by
        rw [Set.iUnion₂_inter, measure_biUnion_finset
          (fun j _ j' _ hne => (pairwiseDisjoint_firstBig a hne).mono
            Set.inter_subset_left Set.inter_subset_left)
          (fun j _ => (measurableSet_firstBig a j).inter (measurableSet_big a n))]
    _ ≤ 2 * incPathLaw d A := by
        gcongr
        exact Set.inter_subset_right

/-! ### The moment generating function of one coordinate -/

theorem integrable_incLaw {d : ℕ} (hd : 1 ≤ d) (f : Site d → ℝ) :
    Integrable f (incLaw d) := by
  have hint : ∀ a : Site d, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac (by simp [enorm_lt_top])
  have hdne : (d : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hd0 : (2 * (d : ℝ≥0∞)) ≠ 0 := mul_ne_zero two_ne_zero hdne
  rw [incLaw, instructionLaw]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr hd0)
  exact integrable_finsetSum_measure.2 fun i _ => (hint _).add_measure (hint _)

/-- The moment generating function of one coordinate of one increment:
`1 + (cosh θ - 1)/d`. -/
def stepMgf (d : ℕ) (θ : ℝ) : ℝ := (2 * Real.cosh θ + 2 * d - 2) / (2 * d)

theorem stepMgf_nonneg {d : ℕ} (hd : 1 ≤ d) (θ : ℝ) : 0 ≤ stepMgf d θ := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : (1 : ℝ) ≤ Real.cosh θ := Real.one_le_cosh θ
  rw [stepMgf]
  have : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  refine div_nonneg ?_ (le_of_lt this)
  linarith

theorem integral_incLaw_exp {d : ℕ} (hd : 1 ≤ d) (θ : ℝ) (i : Fin d) :
    ∫ v, Real.exp (θ * ((v i : ℤ) : ℝ)) ∂(incLaw d) = stepMgf d θ := by
  haveI : NeZero d := ⟨by omega⟩
  rw [integral_incLaw]
  have hterm : ∀ i' : Fin d,
      Real.exp (θ * (((unit i' : Site d) i : ℤ) : ℝ))
        + Real.exp (θ * (((-unit i' : Site d) i : ℤ) : ℝ))
      = 2 + (if i' = i then Real.exp θ + Real.exp (-θ) - 2 else 0) := by
    intro i'
    by_cases h : i' = i
    · subst h
      have h1 : ((unit i' : Site d) i') = 1 := by simp [unit]
      have h2 : ((-unit i' : Site d) i') = -1 := by simp [h1]
      rw [h1, h2, if_pos rfl]
      simp only [Int.cast_one, Int.cast_neg, mul_one, mul_neg_one]
      ring
    · have h1 : ((unit i' : Site d) i) = 0 := by
        simp [unit, Ne.symm h]
      have h2 : ((-unit i' : Site d) i) = 0 := by
        simp [h1]
      rw [h1, h2, if_neg h]
      norm_num
  rw [Finset.sum_congr rfl fun i' _ => hterm i', Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => Real.exp θ + Real.exp (-θ) - 2)]
  simp only [Finset.mem_univ, if_pos, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [stepMgf, Real.cosh_eq]
  ring

theorem measurable_exp_coord (n : ℕ) (θ : ℝ) (i : Fin d) :
    Measurable fun ξ : ℕ → Site d =>
      ENNReal.ofReal (Real.exp (θ * (((incSum n ξ) i : ℤ) : ℝ))) := by
  have h1 : Measurable fun z : Site d => ((z i : ℤ) : ℝ) := measurable_of_countable _
  have hX : Measurable fun ξ : ℕ → Site d => (((incSum n ξ) i : ℤ) : ℝ) :=
    h1.comp (measurable_incSum n)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul θ))

theorem lintegral_incLaw_exp {d : ℕ} (hd : 1 ≤ d) (θ : ℝ) (i : Fin d) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (θ * ((v i : ℤ) : ℝ))) ∂(incLaw d)
      = ENNReal.ofReal (stepMgf d θ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_incLaw hd _)
    (Filter.Eventually.of_forall fun v => Real.exp_nonneg _), integral_incLaw_exp hd θ i]

/-- The moment generating function of one coordinate of the displacement at
time `n`. -/
theorem lintegral_incPathLaw_exp {d : ℕ} [NeZero d] (hd : 1 ≤ d) (θ : ℝ) (i : Fin d) (n : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (Real.exp (θ * (((incSum n ξ) i : ℤ) : ℝ))) ∂(incPathLaw d)
      = ENNReal.ofReal (stepMgf d θ) ^ n := by
  induction n with
  | zero =>
      have h0 : ∀ ξ : ℕ → Site d,
          ENNReal.ofReal (Real.exp (θ * (((incSum 0 ξ) i : ℤ) : ℝ))) = 1 := by
        intro ξ
        simp [incSum]
      simp only [h0, pow_zero]
      simp
  | succ n ih =>
      have hcons : ∀ (u : Site d) (ω : ℕ → Site d),
          ENNReal.ofReal (Real.exp (θ * (((incSum (n + 1) (consNat u ω)) i : ℤ) : ℝ)))
            = ENNReal.ofReal (Real.exp (θ * ((u i : ℤ) : ℝ)))
              * ENNReal.ofReal (Real.exp (θ * (((incSum n ω) i : ℤ) : ℝ))) := by
        intro u ω
        rw [incSum_consNat, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 1
        simp only [Pi.add_apply]
        push_cast
        ring
      rw [incPathLaw, lintegral_infinitePi_nat_head_tail (incLaw d) _
        (measurable_exp_coord (n + 1) θ i)]
      have hinner : ∀ u : Site d,
          ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (((incSum (n + 1) (consNat u ω)) i : ℤ) : ℝ)))
              ∂(Measure.infinitePi fun _ : ℕ => incLaw d)
            = ENNReal.ofReal (Real.exp (θ * ((u i : ℤ) : ℝ)))
              * ENNReal.ofReal (stepMgf d θ) ^ n := by
        intro u
        rw [lintegral_congr fun ω => hcons u ω, lintegral_const_mul _
          (measurable_exp_coord n θ i)]
        rw [← incPathLaw, ih]
      have hm : Measurable fun v : Site d => ENNReal.ofReal (Real.exp (θ * ((v i : ℤ) : ℝ))) :=
        measurable_of_countable _
      rw [lintegral_congr hinner, lintegral_mul_const _ hm,
        lintegral_incLaw_exp hd θ i, pow_succ]
      exact mul_comm _ _

/-! ### The Chernoff bound at a fixed time -/

theorem measure_coord_ge {d : ℕ} [NeZero d] (hd : 1 ≤ d) (n : ℕ) (i : Fin d) {θ b : ℝ}
    (hθ : 0 ≤ θ) :
    incPathLaw d {ξ : ℕ → Site d | b ≤ (((incSum n ξ) i : ℤ) : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(θ * b)) * stepMgf d θ ^ n) := by
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * b)) with hε
  have hεne : ε ≠ 0 := by
    rw [hε, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (Real.exp_pos _)
  have hεtop : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : {ξ : ℕ → Site d | b ≤ (((incSum n ξ) i : ℤ) : ℝ)}
      ⊆ {ξ : ℕ → Site d | ε ≤ ENNReal.ofReal (Real.exp (θ * (((incSum n ξ) i : ℤ) : ℝ)))} := by
    intro ξ hξ
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left hξ hθ
  have hmark := mul_meas_ge_le_lintegral₀ (μ := incPathLaw d)
    (measurable_exp_coord (d := d) n θ i).aemeasurable ε
  have hkey : ε * incPathLaw d {ξ : ℕ → Site d | b ≤ (((incSum n ξ) i : ℤ) : ℝ)}
      ≤ ENNReal.ofReal (stepMgf d θ) ^ n := by
    refine le_trans ?_ (le_trans hmark (le_of_eq (lintegral_incPathLaw_exp hd θ i n)))
    gcongr
  have htarget : ε * ENNReal.ofReal (Real.exp (-(θ * b)) * stepMgf d θ ^ n)
      = ENNReal.ofReal (stepMgf d θ) ^ n := by
    rw [hε, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← mul_assoc, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, one_mul,
      ENNReal.ofReal_pow (stepMgf_nonneg hd θ)]
  exact (ENNReal.mul_le_mul_iff_right hεne hεtop).mp (hkey.trans_eq htarget.symm)

theorem measure_coord_le {d : ℕ} [NeZero d] (hd : 1 ≤ d) (n : ℕ) (i : Fin d) {θ b : ℝ}
    (hθ : 0 ≤ θ) :
    incPathLaw d {ξ : ℕ → Site d | b ≤ -(((incSum n ξ) i : ℤ) : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(θ * b)) * stepMgf d θ ^ n) := by
  have hzero : ∀ ξ : ℕ → Site d, incSum n (reflectAt 0 ξ) = -incSum n ξ := by
    intro ξ
    rw [incSum_reflectAt_of_ge (Nat.zero_le n)]
    simp [incSum]
  have hpre : {ξ : ℕ → Site d | b ≤ -(((incSum n ξ) i : ℤ) : ℝ)}
      = reflectAt (d := d) 0 ⁻¹' {ξ : ℕ → Site d | b ≤ (((incSum n ξ) i : ℤ) : ℝ)} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hzero ξ]
    norm_num
  have hmeas : MeasurableSet {ξ : ℕ → Site d | b ≤ (((incSum n ξ) i : ℤ) : ℝ)} := by
    have h1 : Measurable fun z : Site d => ((z i : ℤ) : ℝ) := measurable_of_countable _
    exact measurableSet_le measurable_const (h1.comp (measurable_incSum n))
  rw [hpre, measure_preimage_reflectAt d 0 hmeas]
  exact measure_coord_ge hd n i hθ

theorem graphNorm_cast (z : Site d) :
    ((graphNorm z : ℕ) : ℝ) = ∑ i : Fin d, |((z i : ℤ) : ℝ)| := by
  rw [graphNorm, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- The `ℓ¹` norm at a fixed time is exponentially concentrated. -/
theorem measure_big_le {d : ℕ} [NeZero d] (hd : 1 ≤ d) (n : ℕ) {θ a : ℝ}
    (hθ : 0 ≤ θ) :
    incPathLaw d {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)}
      ≤ (2 * d) * ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hcover : {ξ : ℕ → Site d | a ≤ ((graphNorm (incSum n ξ) : ℕ) : ℝ)}
      ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin d)),
        ({ξ : ℕ → Site d | a / d ≤ (((incSum n ξ) i : ℤ) : ℝ)}
          ∪ {ξ : ℕ → Site d | a / d ≤ -(((incSum n ξ) i : ℤ) : ℝ)}) := by
    intro ξ hξ
    by_contra hcon
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_union, Set.mem_setOf_eq,
      exists_prop, true_and, not_exists, not_or, not_le] at hcon
    have hbound : ∀ i : Fin d, |(((incSum n ξ) i : ℤ) : ℝ)| < a / d := by
      intro i
      exact abs_lt.mpr ⟨by linarith [(hcon i).2], (hcon i).1⟩
    have hsum : ((graphNorm (incSum n ξ) : ℕ) : ℝ) < a := by
      rw [graphNorm_cast]
      calc ∑ i : Fin d, |(((incSum n ξ) i : ℤ) : ℝ)|
          < ∑ _i : Fin d, a / d := by
            refine Finset.sum_lt_sum_of_nonempty ?_ fun i _ => hbound i
            exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega))
        _ = a := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    exact absurd hξ (not_le.mpr hsum)
  refine le_trans (measure_mono hcover) (le_trans (measure_biUnion_finset_le _ _) ?_)
  have hterm : ∀ i : Fin d,
      incPathLaw d ({ξ : ℕ → Site d | a / d ≤ (((incSum n ξ) i : ℤ) : ℝ)}
        ∪ {ξ : ℕ → Site d | a / d ≤ -(((incSum n ξ) i : ℤ) : ℝ)})
      ≤ 2 * ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) := by
    intro i
    refine le_trans (measure_union_le _ _) ?_
    have h1 := measure_coord_ge (d := d) hd n i (b := a / d) hθ
    have h2 := measure_coord_le (d := d) hd n i (b := a / d) hθ
    calc incPathLaw d {ξ : ℕ → Site d | a / d ≤ (((incSum n ξ) i : ℤ) : ℝ)}
          + incPathLaw d {ξ : ℕ → Site d | a / d ≤ -(((incSum n ξ) i : ℤ) : ℝ)}
        ≤ ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n)
          + ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) := add_le_add h1 h2
      _ = 2 * ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) := by ring
  calc ∑ i : Fin d, incPathLaw d ({ξ : ℕ → Site d | a / d ≤ (((incSum n ξ) i : ℤ) : ℝ)}
        ∪ {ξ : ℕ → Site d | a / d ≤ -(((incSum n ξ) i : ℤ) : ℝ)})
      ≤ ∑ _i : Fin d, 2 * ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (2 * d) * ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The moment generating function is Gaussian on `[0, 1]` -/

theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  nlinarith

theorem cosh_sub_one_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : Real.cosh θ - 1 ≤ θ ^ 2 := by
  set u : ℝ := θ ^ 2 / 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 2 := by
    rw [hu]
    nlinarith
  have h1 : Real.cosh θ ≤ Real.exp u := Real.cosh_le_exp_half_sq θ
  have h2 : Real.exp u - 1 ≤ u * Real.exp u := by
    have := Real.add_one_le_exp (-u)
    have hpos : 0 < Real.exp u := Real.exp_pos u
    have hmul : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith
  have h3 : Real.exp u ≤ 2 := by
    calc Real.exp u ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hu1
      _ ≤ 2 := exp_half_le_two
  nlinarith

theorem stepMgf_eq {d : ℕ} (hd : 1 ≤ d) (θ : ℝ) :
    stepMgf d θ = 1 + (Real.cosh θ - 1) / d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [stepMgf]
  field_simp
  ring

theorem stepMgf_le_exp {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    stepMgf d θ ≤ Real.exp (θ ^ 2 / d) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  calc stepMgf d θ = 1 + (Real.cosh θ - 1) / d := stepMgf_eq hd θ
    _ ≤ 1 + θ ^ 2 / d := by
        gcongr
        exact cosh_sub_one_le hθ0 hθ1
    _ ≤ Real.exp (θ ^ 2 / d) := by
        have := Real.add_one_le_exp (θ ^ 2 / d)
        linarith

theorem stepMgf_pow_le {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    stepMgf d θ ^ n ≤ Real.exp ((n : ℝ) * θ ^ 2 / d) := by
  calc stepMgf d θ ^ n ≤ Real.exp (θ ^ 2 / d) ^ n :=
        pow_le_pow_left₀ (stepMgf_nonneg hd θ) (stepMgf_le_exp hd hθ0 hθ1) n
    _ = Real.exp ((n : ℝ) * θ ^ 2 / d) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-! ### Beyond the horizon the walk cannot be -/

theorem incLaw_graphNorm_ne_one (d : ℕ) :
    incLaw d {v : Site d | graphNorm v ≠ 1} = 0 := by
  have hunit : ∀ i : Fin d, graphNorm (unit i : Site d) = 1 := by
    intro i
    rw [← dirVec_eq_unit i, graphNorm_dirVec]
  have hnegunit : ∀ i : Fin d, graphNorm (-unit i : Site d) = 1 := by
    intro i
    rw [graphNorm_neg, hunit i]
  rw [incLaw_apply ((Set.to_countable _).measurableSet)]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
  rw [Set.indicator_of_notMem (by simp [hunit i]),
    Set.indicator_of_notMem (by simp [hnegunit i]), add_zero]

theorem measure_bigSome_eq_zero {d : ℕ} [NeZero d] {n : ℕ} {a : ℝ} (ha : (n : ℝ) < a) :
    incPathLaw d (bigSome a n) = 0 := by
  have hbad : ∀ j : ℕ, incPathLaw d {ξ : ℕ → Site d | graphNorm (ξ j) ≠ 1} = 0 := by
    intro j
    have hmap : (incPathLaw d).map (fun ξ : ℕ → Site d => ξ j) = incLaw d :=
      Measure.infinitePi_map_eval _ j
    have hset : MeasurableSet {v : Site d | graphNorm v ≠ 1} :=
      (Set.to_countable _).measurableSet
    have hmj : Measurable fun ξ : ℕ → Site d => ξ j := measurable_pi_apply j
    have := Measure.map_apply (μ := incPathLaw d) hmj hset
    rw [hmap, incLaw_graphNorm_ne_one] at this
    exact this.symm
  have hsub : bigSome (d := d) a n ⊆ ⋃ j : ℕ, {ξ : ℕ → Site d | graphNorm (ξ j) ≠ 1} := by
    intro ξ hξ
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hcon
    obtain ⟨k, hk, hbig⟩ := hξ
    have hle : graphNorm (incSum k ξ) ≤ k := graphNorm_incSum_le fun j _ => hcon j
    have : ((graphNorm (incSum k ξ) : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      have h2 : ((graphNorm (incSum k ξ) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
      linarith
    linarith
  exact measure_mono_null hsub (measure_iUnion_null hbad)

/-! ### The maximal displacement bound -/

/-- **The maximal displacement of simple random walk is Gaussian.**  Up to time
`n` the walk leaves the `ℓ¹` ball of radius `a` about its start with
probability at most `4d exp(-a^2/(4 d^2 n))`.  Since the Euclidean norm is at
most the `ℓ¹` norm, the same bound holds for the Euclidean ball. -/
theorem exists_maxDisp_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (a : ℝ), 1 ≤ n → 0 ≤ a → ∀ x : Site d,
        siteWalkLaw d x {X : ℕ → Site d | ∃ k ≤ n, a ≤ ((graphNorm (X k - x) : ℕ) : ℝ)}
          ≤ ENNReal.ofReal (C * Real.exp (-c * a ^ 2 / n)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd' : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  refine ⟨4 * d, 1 / (4 * (d : ℝ) ^ 2), by positivity, by positivity, ?_⟩
  intro n a hn ha x
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- transfer to the increments
  have hev : MeasurableSet
      {X : ℕ → Site d | ∃ k ≤ n, a ≤ ((graphNorm (X k - x) : ℕ) : ℝ)} := by
    have hcast : {X : ℕ → Site d | ∃ k ≤ n, a ≤ ((graphNorm (X k - x) : ℕ) : ℝ)}
        = ⋃ k ∈ Finset.range (n + 1),
          {X : ℕ → Site d | a ≤ ((graphNorm (X k - x) : ℕ) : ℝ)} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩, fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩⟩
    rw [hcast]
    refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet fun k _ => ?_
    have h1 : Measurable fun z : Site d => ((graphNorm (z - x) : ℕ) : ℝ) :=
      measurable_of_countable _
    exact measurableSet_le measurable_const (h1.comp (measurable_pi_apply k))
  have hpull : siteWalkLaw d x {X : ℕ → Site d | ∃ k ≤ n, a ≤ ((graphNorm (X k - x) : ℕ) : ℝ)}
      = incPathLaw d (bigSome a n) := by
    rw [siteWalkLaw_eq, Measure.map_apply (measurable_sitePath x) hev]
    congr 1
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, bigSome]
    refine exists_congr fun k => and_congr Iff.rfl ?_
    rw [sitePath_eq_add_incSum, add_sub_cancel_left]
  rw [hpull]
  rcases lt_or_ge (n : ℝ) a with hcase | hcase
  · rw [measure_bigSome_eq_zero hcase]
    simp
  -- the Gaussian regime
  set θ : ℝ := a / (2 * n * d) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity)]
    have h1 : (n : ℝ) ≤ 2 * n * d := by nlinarith
    linarith
  have hexp : Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n
      ≤ Real.exp (-(1 / (4 * (d : ℝ) ^ 2)) * a ^ 2 / n) := by
    have hpow : stepMgf d θ ^ n ≤ Real.exp ((n : ℝ) * θ ^ 2 / d) :=
      stepMgf_pow_le hd hθ0 hθ1 n
    calc Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n
        ≤ Real.exp (-(θ * (a / d))) * Real.exp ((n : ℝ) * θ ^ 2 / d) := by
          exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
      _ = Real.exp (-(θ * (a / d)) + (n : ℝ) * θ ^ 2 / d) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(1 / (4 * (d : ℝ) ^ 2)) * a ^ 2 / n) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hθdef]
          have hkey : -(a / (2 * n * d) * (a / d))
              + (n : ℝ) * (a / (2 * n * d)) ^ 2 / d
              = -(a ^ 2 / (2 * n * (d : ℝ) ^ 2)) + a ^ 2 / (4 * n * (d : ℝ) ^ 3) := by
            field_simp
            ring
          rw [hkey]
          have hden : (0 : ℝ) < 4 * n * (d : ℝ) ^ 2 := by positivity
          have hcmp : (4 : ℝ) * n * (d : ℝ) ^ 2 ≤ 4 * n * (d : ℝ) ^ 3 := by nlinarith
          have h1 : a ^ 2 / (4 * n * (d : ℝ) ^ 3) ≤ a ^ 2 / (4 * n * (d : ℝ) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hden hcmp
          have h2 : -(1 / (4 * (d : ℝ) ^ 2)) * a ^ 2 / n
              = -(a ^ 2 / (4 * n * (d : ℝ) ^ 2)) := by
            field_simp
          rw [h2]
          have h3 : a ^ 2 / (2 * n * (d : ℝ) ^ 2) = 2 * (a ^ 2 / (4 * n * (d : ℝ) ^ 2)) := by
            field_simp
            ring
          rw [h3]
          linarith
  have hfinal := measure_big_le (d := d) hd n (θ := θ) (a := a) hθ0
  have hlevy := measure_bigSome_le d n a
  have hchain : incPathLaw d (bigSome a n)
      ≤ 2 * ((2 * (d : ℝ≥0∞)) * ENNReal.ofReal
        (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n)) := by
    refine hlevy.trans ?_
    gcongr
  refine hchain.trans ?_
  have hmono : ENNReal.ofReal (Real.exp (-(θ * (a / d))) * stepMgf d θ ^ n)
      ≤ ENNReal.ofReal (Real.exp (-(1 / (4 * (d : ℝ) ^ 2)) * a ^ 2 / n)) :=
    ENNReal.ofReal_le_ofReal hexp
  refine le_trans (by gcongr) ?_
  have hcast : (2 : ℝ≥0∞) * ((2 * (d : ℝ≥0∞))) = ENNReal.ofReal (4 * (d : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp [ENNReal.ofReal_natCast]
    ring
  rw [← mul_assoc, hcast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by positivity))

end LatticeProb

end
