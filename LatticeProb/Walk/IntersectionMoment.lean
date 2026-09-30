import Mathlib
import LatticeProb.Walk.Markov
import LatticeProb.Walk.GreenPointwise
import LatticeProb.Walk.SRWDiag

/-!
# The second moment of the intersection count in `d ≥ 5`

For two independent simple random walks `X` from `x` and `Y` from `y` on `ℤ^d`, `d ≥ 5`, the
number `I(X, Y) = ∑_{i,j ≥ 0} 1{X_i = Y_j}` of their intersections has
`E_x E_y I(X, Y)² ≤ C (1 + |x - y|)^{4-d}` (`exists_lintegral_interCount_sq_le`; Lawler,
*Intersections of Random Walks*, proof of Theorem 3.3.2 with Proposition 3.2.1). The proof writes
`I = ∑_z L_X(z) L_Y(z)` through the local times, bounds `E_x[L(z) L(w)]` by the Green function
over the two orderings of the visits, and sums the resulting four products with the convolution
bounds of `LatticeProb.Walk.GreenPointwise`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeProb.Intersection

variable {d : ℕ}

/-- The local time `L_X(z) = ∑_{i ≥ 0} 1{X_i = z}` of a path at a site, in `ℝ≥0∞`. -/
def localTime (z : Site d) (X : ℕ → Site d) : ℝ≥0∞ :=
  ∑' i : ℕ, Set.indicator {j : ℕ | X j = z} (fun _ => (1 : ℝ≥0∞)) i

/-- The number `I(X, Y) = ∑_{i, j ≥ 0} 1{X_i = Y_j}` of intersections of two paths, counted
with multiplicity in the pair of times, in `ℝ≥0∞`. -/
def interCount (X Y : ℕ → Site d) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p

/-! ### The marginals of the walk -/

/-- The event `{X_i = z}` is measurable. -/
theorem measurableSet_eval_eq (i : ℕ) (z : Site d) :
    MeasurableSet {X : ℕ → Site d | X i = z} := by
  change MeasurableSet ((fun X : ℕ → Site d => X i) ⁻¹' ({z} : Set (Site d)))
  exact (measurable_pi_apply i) (measurableSet_singleton z)

/-- The first step: `E_x g(X_1) = (2d)⁻¹ ∑ᵢ (g(x + eᵢ) + g(x - eᵢ))`. -/
theorem lintegral_eval_one [NeZero d] (x : Site d) (g : Site d → ℝ≥0∞) :
    ∫⁻ X, g (X 1) ∂(siteWalkLaw d x)
      = (2 * (d : ℝ≥0∞))⁻¹ * ∑ i : Fin d, (g (x + unit i) + g (x - unit i)) := by
  have hf : Measurable (fun X : ℕ → Site d => g (X 1)) :=
    (measurable_of_countable g).comp (measurable_pi_apply 1)
  have hg : Measurable (sitePath x) := measurable_sitePath x
  rw [siteWalkLaw, lintegral_map hf hg]
  have hsite : ∀ ξ : ℕ → Site d, sitePath x ξ 1 = x + ξ 0 := by
    intro ξ
    simp [sitePath]
  simp only [hsite]
  have hstep : ∫⁻ v, g (x + v) ∂(incLaw d)
      = ∫⁻ ξ, g (x + ξ 0) ∂(Measure.infinitePi fun _ : ℕ => incLaw d) := by
    conv_lhs => rw [← Measure.infinitePi_map_eval (fun _ : ℕ => incLaw d) 0]
    rw [lintegral_map (f := fun v : Site d => g (x + v))
      (g := fun ξ : ℕ → Site d => ξ 0) (measurable_of_countable _) (measurable_pi_apply 0)]
  rw [← hstep]
  rw [incLaw, instructionLaw, lintegral_smul_measure, lintegral_finsetSum_measure]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_add_measure, lintegral_dirac, lintegral_dirac]
  simp [sub_eq_add_neg]

/-- The one-time marginal: `P_x(X_n = z) = p_n(z - x)`. -/
theorem siteWalkLaw_eval_eq [NeZero d] (x : Site d) (n : ℕ) (z : Site d) :
    siteWalkLaw d x {X | X n = z} = ENNReal.ofReal (srwHeat d n (z - x)) := by
  have hset : MeasurableSet {X : ℕ → Site d | X n = z} := measurableSet_eval_eq n z
  have hiter : ∀ m : ℕ, walkOp^[m] (fun y : Site d => if y = z then (1 : ℝ) else 0)
      = fun y => srwHeat d m (z - y) := by
    intro m
    induction m with
    | zero =>
        funext y
        rw [Function.iterate_zero_apply, srwHeat_zero]
        by_cases h : y = z
        · rw [if_pos h, if_pos (by rw [h, sub_self])]
        · rw [if_neg h, if_neg (by intro hz; exact h (sub_eq_zero.mp hz).symm)]
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih]
        funext y
        rw [srwHeat_succ, walkOp, nbrSum, walkOp, nbrSum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [show z - (y + unit i) = (z - y) - unit i by abel,
          show z - (y - unit i) = (z - y) + unit i by abel, add_comm]
  have hφ : ∀ y : Site d, ‖(fun y : Site d => if y = z then (1 : ℝ) else 0) y‖ ≤ 1 := by
    intro y
    by_cases h : y = z <;> simp [h]
  have hInt : ∫ X, (fun y : Site d => if y = z then (1 : ℝ) else 0) (X n)
        ∂(siteWalkLaw d x) = srwHeat d n (z - x) := by
    rw [integral_apply_eq_walkOp_iterate d n _ hφ x]
    simpa using congrFun (hiter n) x
  have hInd : ∫ X, {X : ℕ → Site d | X n = z}.indicator (fun _ => (1 : ℝ)) X
        ∂(siteWalkLaw d x) = srwHeat d n (z - x) := by
    rw [← hInt]
    apply integral_congr_ae
    filter_upwards with X
    by_cases h : X n = z <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hval : ∫ X, {X : ℕ → Site d | X n = z}.indicator (fun _ => (1 : ℝ)) X
      ∂(siteWalkLaw d x) = (siteWalkLaw d x).real {X | X n = z} :=
    integral_indicator_one hset
  rw [← hInd, hval, measureReal_def]
  exact (ENNReal.ofReal_toReal (measure_ne_top (siteWalkLaw d x) _)).symm

/-- The two-time marginal: for `i ≤ i'`,
`P_x(X_i = z, X_{i'} = w) = p_i(z - x) p_{i'-i}(w - z)`. -/
theorem siteWalkLaw_eval_eval_eq [NeZero d] (x : Site d) {i i' : ℕ} (h : i ≤ i')
    (z w : Site d) :
    siteWalkLaw d x {X | X i = z ∧ X i' = w}
      = ENNReal.ofReal (srwHeat d i (z - x)) * ENNReal.ofReal (srwHeat d (i' - i) (w - z)) := by
  set P := siteWalkLaw d x with hP
  set F : (ℕ → Site d) → ℝ :=
    Set.indicator {Y | Y (i' - i) = w} (1 : (ℕ → Site d) → ℝ) with hF
  set H : (ℕ → Site d) → ℝ :=
    Set.indicator {X | X i = z} (1 : (ℕ → Site d) → ℝ) with hH
  have hSmeas : MeasurableSet {X : ℕ → Site d | X i = z ∧ X i' = w} :=
    (measurableSet_eval_eq i z).inter (measurableSet_eval_eq i' w)
  have hFm : Measurable F := by
    rw [hF]; exact measurable_const.indicator (measurableSet_eval_eq (i' - i) w)
  have hFb : ∀ X, ‖F X‖ ≤ 1 := by
    intro X
    rw [hF, Set.indicator_apply]
    split_ifs <;> simp
  have hHb : ∀ X, ‖H X‖ ≤ 1 := by
    intro X
    rw [hH, Set.indicator_apply]
    split_ifs <;> simp
  have hHdep : DependsUpTo i H := by
    intro X Y hXY
    have hxi : X i = Y i := hXY i le_rfl
    simp only [hH, Set.indicator_apply, Set.mem_setOf_eq, hxi, Pi.one_apply]
  have hmk := markov_fixed d i x F hFm (CF := 1) hFb H (CH := 1) hHb hHdep
  have hL : ∫ X, F (shiftPath i X) * H X ∂P
      = P.real {X : ℕ → Site d | X i = z ∧ X i' = w} := by
    rw [← integral_indicator_one hSmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only []
    rw [hF, hH, Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_setOf_eq, shiftPath]
    simp only [Nat.add_sub_cancel' h]
    by_cases hz : X i = z <;> by_cases hw : X i' = w <;> simp [hz, hw]
  have hpath : pathExpect d F z = srwHeat d (i' - i) (w - z) := by
    rw [pathExpect, hF, integral_indicator_one (measurableSet_eval_eq (i' - i) w),
      measureReal_def, siteWalkLaw_eval_eq z (i' - i) w,
      ENNReal.toReal_ofReal (srwHeat_nonneg (i' - i) (w - z))]
  have hPa : P.real {X : ℕ → Site d | X i = z} = srwHeat d i (z - x) := by
    rw [measureReal_def, hP, siteWalkLaw_eval_eq x i z,
      ENNReal.toReal_ofReal (srwHeat_nonneg i (z - x))]
  have hR : ∫ X, pathExpect d F (X i) * H X ∂P
      = srwHeat d (i' - i) (w - z) * P.real {X : ℕ → Site d | X i = z} := by
    have hpt : ∀ X, pathExpect d F (X i) * H X
        = srwHeat d (i' - i) (w - z) * H X := by
      intro X
      by_cases hx : X i = z
      · rw [hx, hpath]
      · have hz0 : H X = 0 := by
          rw [hH, Set.indicator_of_notMem]
          exact fun hc => hx hc
        rw [hz0, mul_zero, mul_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hH,
      integral_indicator_one (measurableSet_eval_eq i z)]
  have hreal : P.real {X : ℕ → Site d | X i = z ∧ X i' = w}
      = srwHeat d i (z - x) * srwHeat d (i' - i) (w - z) := by
    rw [← hL, hmk, hR, hPa]
    ring
  have hfin : P {X : ℕ → Site d | X i = z ∧ X i' = w} ≠ ∞ :=
    measure_ne_top P _
  rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, hreal,
    ENNReal.ofReal_mul (srwHeat_nonneg i (z - x))]

/-! ### The local times -/

/-- The local time at a site is a measurable function of the path. -/
theorem measurable_localTime (z : Site d) : Measurable (localTime z) := by
  unfold localTime
  apply Measurable.tsum
  intro i
  have hterm : (fun X : ℕ → Site d =>
        Set.indicator {j : ℕ | X j = z} (fun _ => (1 : ℝ≥0∞)) i)
      = Set.indicator {X : ℕ → Site d | X i = z} (fun _ => (1 : ℝ≥0∞)) := by
    funext X
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : X i = z <;> simp [h]
  rw [hterm]
  exact measurable_const.indicator (by
    change MeasurableSet ((fun X : ℕ → Site d => X i) ⁻¹' ({z} : Set (Site d)))
    exact (measurable_pi_apply i) (measurableSet_singleton z))

/-- The `z`-sum of a product of two indicators is the indicator of `p = q`. -/
private lemma tsum_indicator_mul (p q : Site d) :
    (∑' z : Site d, (if p = z then (1 : ℝ≥0∞) else 0) * (if q = z then 1 else 0))
      = if p = q then 1 else 0 := by
  have hterm : ∀ z : Site d,
      (if p = z then (1 : ℝ≥0∞) else 0) * (if q = z then 1 else 0)
        = if z = p then (if q = p then (1 : ℝ≥0∞) else 0) else 0 := by
    intro z
    by_cases hz : z = p
    · subst hz; simp
    · rw [if_neg (Ne.symm hz), if_neg hz, zero_mul]
  simp_rw [hterm]
  rw [tsum_ite_eq]
  by_cases h : p = q <;> simp [h, eq_comm]

/-- A product of two `tsum`s is the `tsum` over the product index. -/
private lemma tsum_mul_tsum {α β : Type*} (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) :
    (∑' a, f a) * (∑' b, g b) = ∑' p : α × β, f p.1 * g p.2 := by
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  rw [← ENNReal.tsum_mul_left]

/-- The intersection count is the sum over common sites of the product of the local times. -/
private lemma interCount_eq (X Y : ℕ → Site d) :
    interCount X Y = ∑' z : Site d, localTime z X * localTime z Y := by
  rw [interCount]
  simp only [localTime, Set.indicator_apply, Set.mem_setOf_eq]
  simp_rw [tsum_mul_tsum]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  exact (tsum_indicator_mul (X p.1) (Y p.2)).symm

/-- The square of the intersection count through the local times:
`I(X, Y)² = ∑_{z,w} L_X(z) L_X(w) L_Y(z) L_Y(w)`. -/
theorem interCount_sq_eq (X Y : ℕ → Site d) :
    interCount X Y ^ 2
      = ∑' p : Site d × Site d,
          (localTime p.1 X * localTime p.2 X) * (localTime p.1 Y * localTime p.2 Y) := by
  rw [interCount_eq, sq, tsum_mul_tsum]
  apply tsum_congr
  intro p
  ac_rfl

/-- The product of the two local times is the double sum of the indicator of the
intersection event. -/
private lemma localTime_mul_eq_tsum (z w : Site d) (X : ℕ → Site d) :
    localTime z X * localTime w X
      = ∑' p : ℕ × ℕ, Set.indicator {X : ℕ → Site d | X p.1 = z ∧ X p.2 = w}
          (fun _ => (1 : ℝ≥0∞)) X := by
  have h1 : (∑' i : ℕ, Set.indicator {j : ℕ | X j = z} (fun _ => (1 : ℝ≥0∞)) i)
        * (∑' j : ℕ, Set.indicator {j : ℕ | X j = w} (fun _ => (1 : ℝ≥0∞)) j)
      = ∑' p : ℕ × ℕ, Set.indicator {j : ℕ | X j = z} (fun _ => (1 : ℝ≥0∞)) p.1
          * Set.indicator {j : ℕ | X j = w} (fun _ => (1 : ℝ≥0∞)) p.2 := by
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro i
    rw [← ENNReal.tsum_mul_left]
  simp only [localTime]
  rw [h1]
  apply tsum_congr
  intro p
  by_cases hz : X p.1 = z <;> by_cases hw : X p.2 = w <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz, hw]

/-- Reindexing the upper-triangular pairs by `(i,j) ↦ (i, i+j)`. -/
private lemma tsum_ite_le_eq (f : ℕ × ℕ → ℝ≥0∞) :
    (∑' p : ℕ × ℕ, if p.1 ≤ p.2 then f p else 0)
      = ∑' q : ℕ × ℕ, f (q.1, q.1 + q.2) := by
  have hg : Function.Injective (fun q : ℕ × ℕ => (q.1, q.1 + q.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext <;> omega
  have hsupp : Function.support (fun p : ℕ × ℕ => if p.1 ≤ p.2 then f p else 0)
      ⊆ Set.range (fun q : ℕ × ℕ => (q.1, q.1 + q.2)) := by
    rintro ⟨a, b⟩ hp
    simp only [Function.mem_support] at hp
    have hle : a ≤ b := by
      by_contra h
      simp [if_neg h] at hp
    exact ⟨(a, b - a), by simp [Nat.add_sub_of_le hle]⟩
  rw [(Function.Injective.tsum_eq hg hsupp).symm]
  apply tsum_congr
  intro q
  rw [if_pos (by omega)]

/-- Reindexing the lower-triangular pairs by `(i,j) ↦ (i+j, i)`. -/
private lemma tsum_ite_ge_eq (f : ℕ × ℕ → ℝ≥0∞) :
    (∑' p : ℕ × ℕ, if p.2 ≤ p.1 then f p else 0)
      = ∑' q : ℕ × ℕ, f (q.1 + q.2, q.1) := by
  have hg : Function.Injective (fun q : ℕ × ℕ => (q.1 + q.2, q.1)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext <;> omega
  have hsupp : Function.support (fun p : ℕ × ℕ => if p.2 ≤ p.1 then f p else 0)
      ⊆ Set.range (fun q : ℕ × ℕ => (q.1 + q.2, q.1)) := by
    rintro ⟨a, b⟩ hp
    simp only [Function.mem_support] at hp
    have hle : b ≤ a := by
      by_contra h
      simp [if_neg h] at hp
    exact ⟨(b, a - b), by simp [Nat.add_sub_of_le hle]⟩
  rw [(Function.Injective.tsum_eq hg hsupp).symm]
  apply tsum_congr
  intro q
  rw [if_pos (by omega)]

/-- Product of two `ℝ≥0∞`-sums over `ℕ`. -/
private lemma tsum_mul_tsum_ennreal (f g : ℕ → ℝ≥0∞) :
    (∑' i, f i) * (∑' j, g j) = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro i
  rw [← ENNReal.tsum_mul_left]

/-- The second moment of the local times:
`E_x[L(z) L(w)] ≤ G(z - x) G(w - z) + G(w - x) G(z - w)` in `d ≥ 3`. -/
theorem lintegral_localTime_mul_le (hd : 3 ≤ d) [NeZero d] (x z w : Site d) :
    ∫⁻ X, localTime z X * localTime w X ∂(siteWalkLaw d x)
      ≤ ENNReal.ofReal (srwGreenInf d (z - x) * srwGreenInf d (w - z)
          + srwGreenInf d (w - x) * srwGreenInf d (z - w)) := by
  let P : ℕ × ℕ → ℝ≥0∞ := fun p =>
    siteWalkLaw d x {X : ℕ → Site d | X p.1 = z ∧ X p.2 = w}
  have hset : ∀ p : ℕ × ℕ, MeasurableSet {X : ℕ → Site d | X p.1 = z ∧ X p.2 = w} :=
    fun p => (measurableSet_eval_eq p.1 z).inter (measurableSet_eval_eq p.2 w)
  have hInt : ∫⁻ X, localTime z X * localTime w X ∂(siteWalkLaw d x) = ∑' p, P p := by
    have hmeas : ∀ p : ℕ × ℕ, AEMeasurable (fun X : ℕ → Site d =>
        Set.indicator {X : ℕ → Site d | X p.1 = z ∧ X p.2 = w}
          (fun _ => (1 : ℝ≥0∞)) X) (siteWalkLaw d x) :=
      fun p => (measurable_const.indicator (hset p)).aemeasurable
    rw [show (fun X : ℕ → Site d => localTime z X * localTime w X)
        = (fun X => ∑' p : ℕ × ℕ, Set.indicator
            {X : ℕ → Site d | X p.1 = z ∧ X p.2 = w}
            (fun _ => (1 : ℝ≥0∞)) X) from funext (localTime_mul_eq_tsum z w)]
    rw [lintegral_tsum hmeas]
    apply tsum_congr
    intro p
    simp only [P]
    exact lintegral_indicator_one (hset p)
  rw [hInt]
  have hsplit : ∑' p, P p
      ≤ (∑' p, if p.1 ≤ p.2 then P p else 0) + ∑' p, if p.2 ≤ p.1 then P p else 0 := by
    rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro p
    by_cases h : p.1 ≤ p.2
    · rw [if_pos h]; exact le_self_add
    · have h' : p.2 ≤ p.1 := le_of_not_ge h
      rw [if_neg h, if_pos h', zero_add]
  have hfirst : (∑' p : ℕ × ℕ, if p.1 ≤ p.2 then P p else 0)
      = ENNReal.ofReal (srwGreenInf d (z - x)) * ENNReal.ofReal (srwGreenInf d (w - z)) := by
    rw [tsum_ite_le_eq]
    have hP : ∀ q : ℕ × ℕ, P (q.1, q.1 + q.2)
        = ENNReal.ofReal (srwHeat d q.1 (z - x)) * ENNReal.ofReal (srwHeat d q.2 (w - z)) := by
      intro q
      simp only [P]
      rw [siteWalkLaw_eval_eval_eq x (by omega) z w, Nat.add_sub_cancel_left]
    simp_rw [hP]
    rw [← tsum_mul_tsum_ennreal (f := fun i => ENNReal.ofReal (srwHeat d i (z - x)))
      (g := fun j => ENNReal.ofReal (srwHeat d j (w - z)))]
    congr 1
    · rw [srwGreenInf]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun i => srwHeat_nonneg i (z - x))
        (summable_srwHeat (by omega) (z - x))).symm
    · rw [srwGreenInf]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun j => srwHeat_nonneg j (w - z))
        (summable_srwHeat (by omega) (w - z))).symm
  have hsecond : (∑' p : ℕ × ℕ, if p.2 ≤ p.1 then P p else 0)
      = ENNReal.ofReal (srwGreenInf d (w - x)) * ENNReal.ofReal (srwGreenInf d (z - w)) := by
    rw [tsum_ite_ge_eq]
    have hP : ∀ q : ℕ × ℕ, P (q.1 + q.2, q.1)
        = ENNReal.ofReal (srwHeat d q.1 (w - x)) * ENNReal.ofReal (srwHeat d q.2 (z - w)) := by
      intro q
      simp only [P]
      rw [show {X : ℕ → Site d | X (q.1 + q.2) = z ∧ X q.1 = w}
          = {X : ℕ → Site d | X q.1 = w ∧ X (q.1 + q.2) = z} by ext X; exact and_comm]
      rw [siteWalkLaw_eval_eval_eq x (by omega) w z, Nat.add_sub_cancel_left]
    simp_rw [hP]
    rw [← tsum_mul_tsum_ennreal (f := fun i => ENNReal.ofReal (srwHeat d i (w - x)))
      (g := fun j => ENNReal.ofReal (srwHeat d j (z - w)))]
    congr 1
    · rw [srwGreenInf]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun i => srwHeat_nonneg i (w - x))
        (summable_srwHeat (by omega) (w - x))).symm
    · rw [srwGreenInf]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun j => srwHeat_nonneg j (z - w))
        (summable_srwHeat (by omega) (z - w))).symm
  have hG1 : 0 ≤ srwGreenInf d (z - x) := by
    rw [srwGreenInf]; exact tsum_nonneg (fun i => srwHeat_nonneg i (z - x))
  have hG2 : 0 ≤ srwGreenInf d (w - z) := by
    rw [srwGreenInf]; exact tsum_nonneg (fun i => srwHeat_nonneg i (w - z))
  have hG3 : 0 ≤ srwGreenInf d (w - x) := by
    rw [srwGreenInf]; exact tsum_nonneg (fun i => srwHeat_nonneg i (w - x))
  have hG4 : 0 ≤ srwGreenInf d (z - w) := by
    rw [srwGreenInf]; exact tsum_nonneg (fun i => srwHeat_nonneg i (z - w))
  have hofReal : ENNReal.ofReal (srwGreenInf d (z - x)) * ENNReal.ofReal (srwGreenInf d (w - z))
        + ENNReal.ofReal (srwGreenInf d (w - x)) * ENNReal.ofReal (srwGreenInf d (z - w))
      = ENNReal.ofReal (srwGreenInf d (z - x) * srwGreenInf d (w - z)
          + srwGreenInf d (w - x) * srwGreenInf d (z - w)) := by
    rw [← ENNReal.ofReal_mul hG1, ← ENNReal.ofReal_mul hG3]
    exact (ENNReal.ofReal_add (mul_nonneg hG1 hG2) (mul_nonneg hG3 hG4)).symm
  calc ∑' p, P p
      ≤ (∑' p : ℕ × ℕ, if p.1 ≤ p.2 then P p else 0)
        + ∑' p : ℕ × ℕ, if p.2 ≤ p.1 then P p else 0 := hsplit
    _ = ENNReal.ofReal (srwGreenInf d (z - x)) * ENNReal.ofReal (srwGreenInf d (w - z))
        + ENNReal.ofReal (srwGreenInf d (w - x)) * ENNReal.ofReal (srwGreenInf d (z - w)) := by
        rw [hfirst, hsecond]
    _ = ENNReal.ofReal (srwGreenInf d (z - x) * srwGreenInf d (w - z)
        + srwGreenInf d (w - x) * srwGreenInf d (z - w)) := hofReal

/-- The infinite Green function is nonnegative. -/
private lemma srwGreenInf_nonneg' (u : Site d) : 0 ≤ srwGreenInf d u := by
  rw [srwGreenInf]
  exact tsum_nonneg fun j => srwHeat_nonneg j u

/-- The second intersection moment is at most the sum over pairs of sites of the products
of the two local-time bounds. -/
theorem lintegral_lintegral_interCount_sq_le (hd : 3 ≤ d) [NeZero d] (x y : Site d) :
    ∫⁻ X, ∫⁻ Y, interCount X Y ^ 2 ∂(siteWalkLaw d y) ∂(siteWalkLaw d x)
      ≤ ∑' p : Site d × Site d,
          ENNReal.ofReal ((srwGreenInf d (p.1 - x) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - x) * srwGreenInf d (p.1 - p.2))
            * (srwGreenInf d (p.1 - y) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - y) * srwGreenInf d (p.1 - p.2))) := by
  have h_inner : ∀ X : ℕ → Site d,
      ∫⁻ Y, interCount X Y ^ 2 ∂(siteWalkLaw d y)
        = ∑' p : Site d × Site d,
            (localTime p.1 X * localTime p.2 X)
              * ∫⁻ Y, localTime p.1 Y * localTime p.2 Y ∂(siteWalkLaw d y) := by
    intro X
    simp_rw [interCount_sq_eq]
    rw [lintegral_tsum]
    · apply tsum_congr
      intro p
      rw [lintegral_const_mul]
      exact (measurable_localTime p.1).mul (measurable_localTime p.2)
    · intro p
      exact (((measurable_localTime p.1).mul (measurable_localTime p.2)).const_mul
        (localTime p.1 X * localTime p.2 X)).aemeasurable
  have h_outer : ∫⁻ X,
        (∑' p : Site d × Site d,
            (localTime p.1 X * localTime p.2 X)
              * ∫⁻ Y, localTime p.1 Y * localTime p.2 Y ∂(siteWalkLaw d y))
        ∂(siteWalkLaw d x)
      = ∑' p : Site d × Site d,
          (∫⁻ X, localTime p.1 X * localTime p.2 X ∂(siteWalkLaw d x))
            * ∫⁻ Y, localTime p.1 Y * localTime p.2 Y ∂(siteWalkLaw d y) := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro p
      rw [lintegral_mul_const]
      exact (measurable_localTime p.1).mul (measurable_localTime p.2)
    · intro p
      exact (((measurable_localTime p.1).mul (measurable_localTime p.2)).mul_const _).aemeasurable
  calc
    ∫⁻ X, ∫⁻ Y, interCount X Y ^ 2 ∂(siteWalkLaw d y) ∂(siteWalkLaw d x)
        = ∫⁻ X, (∑' p : Site d × Site d,
            (localTime p.1 X * localTime p.2 X)
              * ∫⁻ Y, localTime p.1 Y * localTime p.2 Y ∂(siteWalkLaw d y))
            ∂(siteWalkLaw d x) := by
          apply lintegral_congr
          intro X
          exact h_inner X
    _ = ∑' p : Site d × Site d,
          (∫⁻ X, localTime p.1 X * localTime p.2 X ∂(siteWalkLaw d x))
            * ∫⁻ Y, localTime p.1 Y * localTime p.2 Y ∂(siteWalkLaw d y) := h_outer
    _ ≤ ∑' p : Site d × Site d,
          ENNReal.ofReal (srwGreenInf d (p.1 - x) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - x) * srwGreenInf d (p.1 - p.2))
            * ENNReal.ofReal (srwGreenInf d (p.1 - y) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - y) * srwGreenInf d (p.1 - p.2)) := by
          apply ENNReal.tsum_le_tsum
          intro p
          exact mul_le_mul' (lintegral_localTime_mul_le hd x p.1 p.2)
            (lintegral_localTime_mul_le hd y p.1 p.2)
    _ = ∑' p : Site d × Site d,
          ENNReal.ofReal ((srwGreenInf d (p.1 - x) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - x) * srwGreenInf d (p.1 - p.2))
            * (srwGreenInf d (p.1 - y) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - y) * srwGreenInf d (p.1 - p.2))) := by
          apply tsum_congr
          intro p
          have hA : 0 ≤ srwGreenInf d (p.1 - x) * srwGreenInf d (p.2 - p.1)
              + srwGreenInf d (p.2 - x) * srwGreenInf d (p.1 - p.2) :=
            add_nonneg (mul_nonneg (srwGreenInf_nonneg' _) (srwGreenInf_nonneg' _))
              (mul_nonneg (srwGreenInf_nonneg' _) (srwGreenInf_nonneg' _))
          rw [← ENNReal.ofReal_mul hA]

/-! ### The four orderings -/

/-- The Green function at a site, in `ℝ≥0∞`. -/
private def gInf (k : ℕ) : Site (k + 5) → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (srwGreenInf (k + 5) z)

/-- The Green function is even. -/
private lemma green_neg (k : ℕ) (u : Site (k + 5)) :
    srwGreenInf (k + 5) (-u) = srwGreenInf (k + 5) u := by
  simp only [srwGreenInf]
  exact tsum_congr (fun j => srwHeat_neg j u)

/-- The Green function in `ℝ≥0∞` is even. -/
private lemma gInf_sub_comm (k : ℕ) (z w : Site (k + 5)) : gInf k (z - w) = gInf k (w - z) := by
  rw [gInf, gInf, show z - w = -(w - z) by abel, green_neg]

/-- The product of the two brackets splits into four nonnegative orderings. -/
private lemma ofReal_four (k : ℕ) (x y z w : Site (k + 5)) :
    ENNReal.ofReal ((srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (w-z)
        + srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (z-w))
      * (srwGreenInf (k+5) (z-y) * srwGreenInf (k+5) (w-z)
        + srwGreenInf (k+5) (w-y) * srwGreenInf (k+5) (z-w)))
      = gInf k (z-x) * gInf k (z-y) * gInf k (w-z)^2
        + gInf k (z-x) * gInf k (w-y) * gInf k (w-z)^2
        + gInf k (w-x) * gInf k (z-y) * gInf k (w-z)^2
        + gInf k (w-x) * gInf k (w-y) * gInf k (w-z)^2 := by
  have hG : ∀ u : Site (k+5), 0 ≤ srwGreenInf (k+5) u :=
    fun u => tsum_nonneg fun j => srwHeat_nonneg j u
  have h1 : srwGreenInf (k+5) (z-w) = srwGreenInf (k+5) (w-z) := by
    rw [show z - w = -(w - z) by abel]; exact green_neg k (w - z)
  rw [h1]
  have hreal : (srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (w-z)
        + srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (w-z))
      * (srwGreenInf (k+5) (z-y) * srwGreenInf (k+5) (w-z)
        + srwGreenInf (k+5) (w-y) * srwGreenInf (k+5) (w-z))
      = srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (z-y) * srwGreenInf (k+5) (w-z)^2
        + (srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (w-y) * srwGreenInf (k+5) (w-z)^2
        + (srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (z-y) * srwGreenInf (k+5) (w-z)^2
        + srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (w-y) * srwGreenInf (k+5) (w-z)^2)) := by
    ring
  rw [hreal]
  have hA : ENNReal.ofReal (srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (z-y)
      * srwGreenInf (k+5) (w-z)^2)
      = gInf k (z-x) * gInf k (z-y) * gInf k (w-z)^2 := by
    rw [ENNReal.ofReal_mul (mul_nonneg (hG _) (hG _)), ENNReal.ofReal_mul (hG _),
      ENNReal.ofReal_pow (hG _)]
    simp only [gInf]
  have hB : ENNReal.ofReal (srwGreenInf (k+5) (z-x) * srwGreenInf (k+5) (w-y)
      * srwGreenInf (k+5) (w-z)^2)
      = gInf k (z-x) * gInf k (w-y) * gInf k (w-z)^2 := by
    rw [ENNReal.ofReal_mul (mul_nonneg (hG _) (hG _)), ENNReal.ofReal_mul (hG _),
      ENNReal.ofReal_pow (hG _)]
    simp only [gInf]
  have hC : ENNReal.ofReal (srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (z-y)
      * srwGreenInf (k+5) (w-z)^2)
      = gInf k (w-x) * gInf k (z-y) * gInf k (w-z)^2 := by
    rw [ENNReal.ofReal_mul (mul_nonneg (hG _) (hG _)), ENNReal.ofReal_mul (hG _),
      ENNReal.ofReal_pow (hG _)]
    simp only [gInf]
  have hD : ENNReal.ofReal (srwGreenInf (k+5) (w-x) * srwGreenInf (k+5) (w-y)
      * srwGreenInf (k+5) (w-z)^2)
      = gInf k (w-x) * gInf k (w-y) * gInf k (w-z)^2 := by
    rw [ENNReal.ofReal_mul (mul_nonneg (hG _) (hG _)), ENNReal.ofReal_mul (hG _),
      ENNReal.ofReal_pow (hG _)]
    simp only [gInf]
  have hnn : ∀ a b c : Site (k+5),
      0 ≤ srwGreenInf (k+5) a * srwGreenInf (k+5) b * srwGreenInf (k+5) c ^ 2 :=
    fun a b c => mul_nonneg (mul_nonneg (hG a) (hG b)) (sq_nonneg _)
  rw [ENNReal.ofReal_add (hnn _ _ _) (add_nonneg (hnn _ _ _) (add_nonneg (hnn _ _ _) (hnn _ _ _))),
    ENNReal.ofReal_add (hnn _ _ _) (add_nonneg (hnn _ _ _) (hnn _ _ _)),
    ENNReal.ofReal_add (hnn _ _ _) (hnn _ _ _), hA, hB, hC, hD]
  abel

/-- The diagonal ordering: `∑ G(z - x) G(z - y) G(w - z)^2 ≤ C S / (1 + |x - y|₁)^(k+1)`. -/
private lemma tsum_diag_le (k : ℕ) (C S : ℝ) (hCpos : 0 < C)
    (hSumm : ∀ u : Site (k+5),
      Summable (fun z => srwGreenInf (k+5) z * srwGreenInf (k+5) (z+u)))
    (hC : ∀ u : Site (k+5), (∑' z, srwGreenInf (k+5) z * srwGreenInf (k+5) (z+u))
        ≤ C / (1 + ((graphNorm u : ℕ) : ℝ))^(k+1))
    (hS : S = ∑' z, srwGreenInf (k+5) z ^ 2) (x y : Site (k+5)) :
    ∑' p : Site (k+5) × Site (k+5),
        gInf k (p.1-x) * gInf k (p.1-y) * gInf k (p.2-p.1)^2
      ≤ ENNReal.ofReal (C / (1 + ((graphNorm (x-y) : ℕ) : ℝ))^(k+1) * S) := by
  have hGnn : ∀ u : Site (k+5), 0 ≤ srwGreenInf (k+5) u :=
    fun u => tsum_nonneg fun j => srwHeat_nonneg j u
  have hsumsq : Summable (fun z : Site (k+5) => srwGreenInf (k+5) z ^ 2) :=
    summable_srwGreenInf_sq k
  have hB : (∑' w : Site (k+5), gInf k w ^ 2) = ENNReal.ofReal S := by
    have h1 : (∑' w : Site (k+5), gInf k w ^ 2)
        = ∑' w, ENNReal.ofReal (srwGreenInf (k+5) w ^ 2) :=
      tsum_congr (fun w => by rw [gInf, ENNReal.ofReal_pow (hGnn w)])
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun w => sq_nonneg _) hsumsq, hS]
  have hA : (∑' z : Site (k+5), gInf k (z-x) * gInf k (z-y))
      ≤ ENNReal.ofReal (C / (1 + ((graphNorm (x-y) : ℕ) : ℝ))^(k+1)) := by
    have hshift : (∑' z : Site (k+5), gInf k (z-x) * gInf k (z-y))
        = ∑' z, gInf k z * gInf k (z + (x-y)) := by
      rw [← Equiv.tsum_eq (Equiv.addRight x) (fun z => gInf k (z-x) * gInf k (z-y))]
      apply tsum_congr
      intro z
      change gInf k (z+x-x) * gInf k (z+x-y) = gInf k z * gInf k (z+(x-y))
      rw [show z + x - x = z by abel, show z + x - y = z + (x - y) by abel]
    rw [hshift]
    calc ∑' z : Site (k+5), gInf k z * gInf k (z + (x-y))
        = ∑' z, ENNReal.ofReal (srwGreenInf (k+5) z * srwGreenInf (k+5) (z + (x-y))) :=
          tsum_congr (fun z => by rw [gInf, gInf, ENNReal.ofReal_mul (hGnn z)])
      _ = ENNReal.ofReal (∑' z, srwGreenInf (k+5) z * srwGreenInf (k+5) (z + (x-y))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hGnn z) (hGnn _))
            (hSumm (x-y))).symm
      _ ≤ ENNReal.ofReal (C / (1 + ((graphNorm (x-y) : ℕ) : ℝ))^(k+1)) :=
          ENNReal.ofReal_le_ofReal (hC (x-y))
  rw [ENNReal.tsum_prod']
  have hinner : ∀ z : Site (k+5),
      (∑' w, gInf k (z-x) * gInf k (z-y) * gInf k (w-z)^2)
        = gInf k (z-x) * gInf k (z-y) * (∑' w, gInf k w ^ 2) := by
    intro z
    rw [show (∑' w : Site (k+5), gInf k (z-x) * gInf k (z-y) * gInf k (w-z)^2)
        = ∑' w, (gInf k (z-x) * gInf k (z-y)) * gInf k (w-z)^2 by
          exact tsum_congr (fun w => by ring)]
    rw [ENNReal.tsum_mul_left]
    congr 1
    exact Equiv.tsum_eq (Equiv.subRight z) (fun w : Site (k+5) => gInf k w ^ 2)
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_right, hB]
  calc (∑' z : Site (k+5), gInf k (z-x) * gInf k (z-y)) * ENNReal.ofReal S
      ≤ ENNReal.ofReal (C / (1 + ((graphNorm (x-y) : ℕ) : ℝ))^(k+1)) * ENNReal.ofReal S := by
        gcongr
    _ = ENNReal.ofReal (C / (1 + ((graphNorm (x-y) : ℕ) : ℝ))^(k+1) * S) := by
        rw [ENNReal.ofReal_mul (by positivity)]

/-- The crossed ordering: `∑ G(z - x) G(w - y) G(w - z)^2 ≤ C / (1 + |y - x|_∞)^(k+1)`. -/
private lemma tsum_cross_le (k : ℕ) (C : ℝ)
    (hSumm : ∀ v : Site (k + 5),
      Summable (fun p : Site (k + 5) × Site (k + 5) =>
        srwGreenInf (k + 5) p.1 * srwGreenInf (k + 5) (p.2 - p.1) ^ 2
          * srwGreenInf (k + 5) (p.2 - v)))
    (hC : ∀ v : Site (k + 5),
      (∑' p : Site (k + 5) × Site (k + 5), srwGreenInf (k + 5) p.1
          * srwGreenInf (k + 5) (p.2 - p.1) ^ 2 * srwGreenInf (k + 5) (p.2 - v))
        ≤ C / (1 + ((supNorm v : ℕ) : ℝ)) ^ (k + 1))
    (x y : Site (k + 5)) :
    ∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.1 - x) * gInf k (p.2 - y) * gInf k (p.2 - p.1) ^ 2
      ≤ ENNReal.ofReal (C / (1 + ((supNorm (y - x) : ℕ) : ℝ)) ^ (k + 1)) := by
  have hGnn : ∀ u : Site (k + 5), 0 ≤ srwGreenInf (k + 5) u :=
    fun u => tsum_nonneg fun j => srwHeat_nonneg j u
  have hshift : (∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.1 - x) * gInf k (p.2 - y) * gInf k (p.2 - p.1) ^ 2)
      = ∑' p : Site (k + 5) × Site (k + 5),
          gInf k p.1 * gInf k (p.2 - (y - x)) * gInf k (p.2 - p.1) ^ 2 := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr (Equiv.addRight x) (Equiv.addRight x))]
    apply tsum_congr
    rintro ⟨z, w⟩
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.coe_addRight]
    rw [show z + x - x = z by abel, show w + x - y = w - (y - x) by abel,
      show w + x - (z + x) = w - z by abel]
  rw [hshift]
  have hnn : ∀ p : Site (k + 5) × Site (k + 5), 0 ≤ srwGreenInf (k + 5) p.1
      * srwGreenInf (k + 5) (p.2 - p.1) ^ 2 * srwGreenInf (k + 5) (p.2 - (y - x)) :=
    fun p => mul_nonneg (mul_nonneg (hGnn p.1) (sq_nonneg _)) (hGnn _)
  have hpt : ∀ p : Site (k + 5) × Site (k + 5),
      gInf k p.1 * gInf k (p.2 - (y - x)) * gInf k (p.2 - p.1) ^ 2
        = ENNReal.ofReal (srwGreenInf (k + 5) p.1 * srwGreenInf (k + 5) (p.2 - p.1) ^ 2
          * srwGreenInf (k + 5) (p.2 - (y - x))) := by
    intro p
    rw [ENNReal.ofReal_mul (mul_nonneg (hGnn p.1) (sq_nonneg _)),
      ENNReal.ofReal_mul (hGnn p.1), ENNReal.ofReal_pow (hGnn (p.2 - p.1))]
    simp only [gInf]
    ring
  rw [tsum_congr hpt, ← ENNReal.ofReal_tsum_of_nonneg hnn (hSumm (y - x))]
  exact ENNReal.ofReal_le_ofReal (hC (y - x))

/-- Exchanging the two sites turns the fourth ordering into the diagonal one. -/
private lemma tsum_four_eq_one (k : ℕ) (x y : Site (k + 5)) :
    ∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.2 - x) * gInf k (p.2 - y) * gInf k (p.2 - p.1) ^ 2
      = ∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.1 - x) * gInf k (p.1 - y) * gInf k (p.2 - p.1) ^ 2 := by
  rw [← Equiv.tsum_eq (Equiv.prodComm (Site (k + 5)) (Site (k + 5)))]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [gInf_sub_comm k p.1 p.2]

/-- Exchanging the two sites turns the third ordering into the crossed one. -/
private lemma tsum_three_eq_two (k : ℕ) (x y : Site (k + 5)) :
    ∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.2 - x) * gInf k (p.1 - y) * gInf k (p.2 - p.1) ^ 2
      = ∑' p : Site (k + 5) × Site (k + 5),
        gInf k (p.1 - x) * gInf k (p.2 - y) * gInf k (p.2 - p.1) ^ 2 := by
  rw [← Equiv.tsum_eq (Equiv.prodComm (Site (k + 5)) (Site (k + 5)))]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [gInf_sub_comm k p.1 p.2]

/-- The two decay rates, in the graph and the sup norms, are both at most a multiple of
`(1 + |u|)^(4 - d)` in dimension `d = k + 5`. -/
private lemma two_rates_le (k : ℕ) (C₁ S C₂ : ℝ) (hC₁ : 0 < C₁) (hS : 0 ≤ S)
    (hC₂ : 0 < C₂) (u : Site (k + 5)) :
    2 * (C₁ / (1 + ((graphNorm u : ℕ) : ℝ)) ^ (k + 1) * S)
        + 2 * (C₂ / (1 + ((supNorm u : ℕ) : ℝ)) ^ (k + 1))
      ≤ (2 * C₁ * S + 2 * C₂ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1))
          * (1 + euclidNorm u) ^ (4 - ((k + 5 : ℕ) : ℝ)) := by
  have he := euclidNorm_nonneg u
  have hg := euclidNorm_le_graphNorm u
  have hs := euclidNorm_le_sqrt_mul_supNorm u
  have hr : 1 ≤ Real.sqrt ((k + 5 : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ k + 5 by omega))
  have hsu : (0 : ℝ) ≤ ((supNorm u : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow : (1 + euclidNorm u) ^ (4 - ((k + 5 : ℕ) : ℝ))
      = ((1 + euclidNorm u) ^ (k + 1))⁻¹ := by
    rw [show (4 : ℝ) - ((k + 5 : ℕ) : ℝ) = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h1 : C₁ / (1 + ((graphNorm u : ℕ) : ℝ)) ^ (k + 1)
      ≤ C₁ / (1 + euclidNorm u) ^ (k + 1) :=
    div_le_div_of_nonneg_left hC₁.le (by positivity) (pow_le_pow_left₀ (by positivity)
      (by linarith) _)
  have hes : 1 + euclidNorm u
      ≤ Real.sqrt ((k + 5 : ℕ) : ℝ) * (1 + ((supNorm u : ℕ) : ℝ)) := by
    nlinarith
  have h2 : C₂ / (1 + ((supNorm u : ℕ) : ℝ)) ^ (k + 1)
      ≤ C₂ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1) / (1 + euclidNorm u) ^ (k + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), mul_assoc]
    gcongr
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hes _
  rw [hpow]
  have h1' := mul_le_mul_of_nonneg_right h1 hS
  have hsum : 2 * (C₁ / (1 + euclidNorm u) ^ (k + 1) * S)
      + 2 * (C₂ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1) / (1 + euclidNorm u) ^ (k + 1))
      = (2 * C₁ * S + 2 * C₂ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1))
          * ((1 + euclidNorm u) ^ (k + 1))⁻¹ := by
    ring
  linarith

/-- The four orderings of the Green functions sum to `O((1 + |x - y|)^{4-d})` in `d = k + 5`. -/
theorem exists_tsum_green_four_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site (k + 5),
      ∑' p : Site (k + 5) × Site (k + 5),
          ENNReal.ofReal ((srwGreenInf (k + 5) (p.1 - x) * srwGreenInf (k + 5) (p.2 - p.1)
              + srwGreenInf (k + 5) (p.2 - x) * srwGreenInf (k + 5) (p.1 - p.2))
            * (srwGreenInf (k + 5) (p.1 - y) * srwGreenInf (k + 5) (p.2 - p.1)
              + srwGreenInf (k + 5) (p.2 - y) * srwGreenInf (k + 5) (p.1 - p.2)))
        ≤ ENNReal.ofReal (C * (1 + euclidNorm (x - y)) ^ (4 - ((k + 5 : ℕ) : ℝ))) := by
  obtain ⟨C₁, hC₁, hH⟩ := exists_tsum_srwGreenInf_mul_le k
  obtain ⟨C₂, hC₂, hX⟩ := exists_tsum_srwGreenInf_crossed_le k
  set S := ∑' z : Site (k + 5), srwGreenInf (k + 5) z ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun z => sq_nonneg _
  refine ⟨2 * C₁ * S + 2 * C₂ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1), by positivity,
    fun x y => ?_⟩
  rw [tsum_congr fun p : Site (k + 5) × Site (k + 5) => ofReal_four k x y p.1 p.2,
    ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, tsum_four_eq_one, tsum_three_eq_two]
  have hA := tsum_diag_le k C₁ S hC₁ (fun u => (hH u).1) (fun u => (hH u).2) hS x y
  have hB := tsum_cross_le k C₂ (fun v => (hX v).1) (fun v => (hX v).2) x y
  rw [show y - x = -(x - y) by abel, supNorm_neg] at hB
  set A := C₁ / (1 + ((graphNorm (x - y) : ℕ) : ℝ)) ^ (k + 1) * S with hAdef
  set B := C₂ / (1 + ((supNorm (x - y) : ℕ) : ℝ)) ^ (k + 1) with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  calc _ ≤ ENNReal.ofReal A + ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal A := by
        gcongr
    _ = ENNReal.ofReal (A + B + B + A) := by
        rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hA0 hB0) hB0) hA0,
          ENNReal.ofReal_add (add_nonneg hA0 hB0) hB0, ENNReal.ofReal_add hA0 hB0]
    _ = ENNReal.ofReal (2 * A + 2 * B) := by congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (two_rates_le k C₁ S C₂ hC₁ hS0 hC₂ (x - y))

/-- **The second moment of the intersection count** in `d ≥ 5` (Lawler, *Intersections of
Random Walks*, proof of Theorem 3.3.2): `E_x E_y I(X, Y)² ≤ C (1 + |x - y|)^{4-d}`. -/
theorem exists_lintegral_interCount_sq_le :
    ∀ d : ℕ, 5 ≤ d →
      ∃ C : ℝ, 0 < C ∧
        ∀ x y : Site d,
          (∫⁻ X, ∫⁻ Y, interCount X Y ^ 2 ∂(siteWalkLaw d y) ∂(siteWalkLaw d x)) ≤
            ENNReal.ofReal (C * (1 + euclidNorm (x - y)) ^ (4 - (d : ℝ))) := by
  intro d hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
  haveI : NeZero (k + 5) := ⟨by omega⟩
  obtain ⟨C, hC, h⟩ := exists_tsum_green_four_le k
  exact ⟨C, hC, fun x y => (lintegral_lintegral_interCount_sq_le (by omega) x y).trans (h x y)⟩

end LatticeProb.Intersection
