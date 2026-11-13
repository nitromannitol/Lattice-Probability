import Mathlib
import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Gauss.TailMills

/-!
# Brownian motion stays in a ball up to the square of its radius

For Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)` started at `u`, the probability that
it stays in the open ball of radius `r` about `u` up to time `r ^ 2` is at least a constant
`c₂ > 0` depending only on `d` (`exists_brownian_stay_pos`).  By Brownian scaling the probability
does not depend on `r`; the point is that it is positive, and the proof below gives an explicit
lower bound without using scaling.

## The one-dimensional estimate

`le_measure_forall_abs_sub_le` is a chaining argument.  The time interval `[0, 4 a ^ 2]` is cut
into `N = 5184` intervals of length `h = (a / 36) ^ 2`.  On the `k`-th interval the increments of
the path form a Brownian motion independent of the path before the interval (the Markov property
at a deterministic time, `IsPreBrownianReal.indepFun_shift`).  The event asked of the `k`-th
interval is that the increments stay below `a / 2` in absolute value, and that the increment over
the whole interval lies in `(0, a / (2 N)]`.  Its probability is at least
`1 / 2304 - 4 e ^ (-10)`: the Gaussian mass of `(0, a / (2 N)]`
(`le_gaussianReal_Ioc_zero`) minus the Gaussian maximal estimate
(`measure_exists_abs_sub_ge_le'`).  The intervals being independent, all `N` events hold with
probability at least the `N`-th power, and on all of them the path moves by at most
`a / 2 + N · a / (2 N) = a` from its starting value before time `4 a ^ 2`.

## Dimension `d`

The coordinates of a continuous version of the motion (`IsBrownianSpace.exists_continuousVersion`)
are independent real Brownian motions.  Each of them stays within `r / 2` of its starting value up
to time `r ^ 2` with the one-dimensional probability, and when all of them do, the motion stays
within distance `r / 2` of `u`.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Elementary estimates -/

/-- **The centred Gaussian mass of a short interval.**  For `0 ≤ b` with `b ^ 2 ≤ v`, the
interval `(0, b]` has mass at least `b / (8 √v)` under the centred Gaussian law of variance `v`:
the density on it is at least its value at `b`, which is at least `1 / (8 √v)`. -/
theorem le_gaussianReal_Ioc_zero {v : ℝ≥0} (hv : 0 < (v : ℝ)) {b : ℝ} (hb : 0 ≤ b)
    (hbv : b ^ 2 ≤ v) :
    ENNReal.ofReal (b / (8 * Real.sqrt v)) ≤ gaussianReal 0 v (Set.Ioc 0 b) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv
    exact lt_irrefl _ hv
  rw [gaussianReal_apply_eq_integral 0 hv0]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans ?_ (GaussTail.le_setIntegral_gaussianPDFReal_Ioc le_rfl hb)
  simp only [gaussianPDFReal_def, sub_zero]
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hv
  have hr : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hr2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi * v)
  have hs2 := Real.sq_sqrt hv.le
  have hpT : Real.pi * v ≤ 4 * v := mul_le_mul_of_nonneg_right Real.pi_le_four hv.le
  have hrs : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ 4 * Real.sqrt (v : ℝ) := by
    nlinarith [hr2, hs2, hpT, hr, hs]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-b ^ 2 / (2 * v)) := by
    have h1 : -(1 / 2 : ℝ) ≤ -b ^ 2 / (2 * v) := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
      nlinarith
    linarith [Real.add_one_le_exp (-b ^ 2 / (2 * (v : ℝ)))]
  calc b / (8 * Real.sqrt v) = b * ((4 * Real.sqrt v)⁻¹ * (1 / 2)) := by ring
    _ ≤ b * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-b ^ 2 / (2 * v))) := by
        refine mul_le_mul_of_nonneg_left ?_ hb
        exact mul_le_mul (inv_anti₀ hr hrs) he (by norm_num) (inv_nonneg.2 hr.le)

/-- The numerical fact behind the chaining: `4 e ^ (-10) < 1 / 2304`, because
`e ^ 10 > 2.7 ^ 10 > 9216`. -/
theorem four_mul_exp_neg_ten_lt : 4 * Real.exp (-10) < 1 / 2304 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he10 : Real.exp 10 = Real.exp 1 ^ 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7 : ℝ) ^ 10 < Real.exp 1 ^ 10 := by gcongr
  have hE : 9216 < Real.exp 10 := by
    rw [he10]
    have : (9216 : ℝ) < 2.7 ^ 10 := by norm_num
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  linarith

/-- The probability that one interval of the chaining succeeds is bounded below by the positive
number `1 / 2304 - 4 e ^ (-10)`. -/
theorem one_div_sub_four_mul_exp_neg_ten_pos : 0 < 1 / 2304 - 4 * Real.exp (-10) :=
  sub_pos.2 four_mul_exp_neg_ten_lt

omit [MeasurableSpace Ω] in
/-- A closed bound on a continuous path at the times of a dense subset of `[0, h]` holds at
every time of `[0, h]`. -/
theorem abs_le_of_forall_mem_dense {f : ℝ≥0 → ℝ} (hf : Continuous f) {h : ℝ≥0}
    {D : Set (Set.Icc (0 : ℝ≥0) h)} (hD : Dense D) {c : ℝ}
    (hfD : ∀ q ∈ D, |f (q : ℝ≥0)| ≤ c) {s : ℝ≥0} (hs : s ≤ h) : |f s| ≤ c := by
  by_contra hcon
  have hopen : IsOpen {r : Set.Icc (0 : ℝ≥0) h | c < |f (r : ℝ≥0)|} :=
    isOpen_lt continuous_const (continuous_abs.comp (hf.comp continuous_subtype_val))
  obtain ⟨q, hqD, hq⟩ := hD.exists_mem_open hopen ⟨⟨s, zero_le, hs⟩, not_le.1 hcon⟩
  simp only [Set.mem_ofPred_eq] at hq
  exact absurd (hfD q hqD) (not_le.2 hq)

omit [MeasurableSpace Ω] in
/-- A bound on an increment of the path between two times before `t₀` is an event of the past
at `t₀`: it is measurable for the σ-algebra generated by the path up to `t₀`. -/
theorem measurableSet_comap_abs_sub_le {X : ℝ≥0 → Ω → ℝ} {t₀ t s : ℝ≥0} (ht : t ≤ t₀)
    (hs : s ≤ t₀) (c : ℝ) :
    MeasurableSet[MeasurableSpace.comap (fun ω (r : Set.Iic t₀) => X (r : ℝ≥0) ω) inferInstance]
      {ω | |X t ω - X s ω| ≤ c} :=
  ⟨{g : Set.Iic t₀ → ℝ | |g ⟨t, ht⟩ - g ⟨s, hs⟩| ≤ c},
    measurableSet_le (continuous_abs.measurable.comp
      ((measurable_pi_apply (⟨t, ht⟩ : Set.Iic t₀)).sub
        (measurable_pi_apply (⟨s, hs⟩ : Set.Iic t₀)))) measurable_const, rfl⟩

/-! ### One interval of the chaining -/

/-- **One interval of the chaining.**  A Brownian motion `Y` stays within `c` of its starting
value up to time `h`, and has its increment over `[0, h]` in `(0, b]`, with probability at least
`b / (8 √h) - 4 exp (- c ^ 2 / (32 h))`, for `0 ≤ b` with `b ^ 2 ≤ h`: the Gaussian mass of
`(0, b]` minus the Gaussian maximal estimate for the event of moving by `c`. -/
theorem le_measure_forall_abs_sub_lt_and_mem_Ioc [IsProbabilityMeasure P]
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsBrownianReal Y P) {h : ℝ≥0} (hh : 0 < (h : ℝ)) {b c : ℝ}
    (hb : 0 ≤ b) (hbh : b ^ 2 ≤ h) (hc : 0 < c) :
    ENNReal.ofReal (b / (8 * Real.sqrt h) - 4 * Real.exp (-(c ^ 2 / (32 * (h : ℝ)))))
      ≤ P {ω | (∀ s : ℝ≥0, s ≤ h → |Y s ω - Y 0 ω| < c) ∧
          0 < Y h ω - Y 0 ω ∧ Y h ω - Y 0 ω ≤ b} := by
  have hlaw : HasLaw (fun ω => Y h ω - Y 0 ω) (gaussianReal 0 h) P := by
    have h' := hY.hasLaw_sub h 0
    convert h' using 2
    ext
    simp
  have hPG : P {ω | 0 < Y h ω - Y 0 ω ∧ Y h ω - Y 0 ω ≤ b}
      = gaussianReal 0 h (Set.Ioc 0 b) := by
    rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Ioc]
    rfl
  have hGsub : {ω | 0 < Y h ω - Y 0 ω ∧ Y h ω - Y 0 ω ≤ b}
      ⊆ {ω | (∀ s : ℝ≥0, s ≤ h → |Y s ω - Y 0 ω| < c) ∧
          0 < Y h ω - Y 0 ω ∧ Y h ω - Y 0 ω ≤ b} ∪
        {ω | ∃ s : ℝ≥0, s ≤ h ∧ c ≤ |Y s ω - Y 0 ω|} := by
    intro ω hω
    by_cases hbad : ∃ s : ℝ≥0, s ≤ h ∧ c ≤ |Y s ω - Y 0 ω|
    · exact Or.inr hbad
    · refine Or.inl ⟨fun s hs => ?_, hω⟩
      by_contra hcon
      exact hbad ⟨s, hs, not_lt.1 hcon⟩
  have hPGle := (measure_mono hGsub).trans (measure_union_le (μ := P) _ _)
  have hPBad := measure_exists_abs_sub_ge_le' hY h hc
  have hGlow := le_gaussianReal_Ioc_zero hh hb hbh
  rw [← hPG] at hGlow
  calc ENNReal.ofReal (b / (8 * Real.sqrt h) - 4 * Real.exp (-(c ^ 2 / (32 * (h : ℝ)))))
      = ENNReal.ofReal (b / (8 * Real.sqrt h))
          - 4 * ENNReal.ofReal (Real.exp (-(c ^ 2 / (32 * (h : ℝ))))) := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
    _ ≤ _ := tsub_le_tsub hGlow hPBad
    _ ≤ _ := tsub_le_iff_right.2 hPGle

/-! ### The one-dimensional estimate -/

/-- **A real Brownian motion stays within `a` of its start up to time `4 a ^ 2`** with probability
at least `(1 / 2304 - 4 e ^ (-10)) ^ 5184`, for every `a > 0`.  The paths are assumed continuous
everywhere (a continuous version exists, `IsBrownianReal.exists_continuous_indistinguishable`).

The proof chains `5184` intervals of length `(a / 36) ^ 2`: on each of them the increments stay
below `a / 2` and the increment over the interval lies in `(0, a / 10368]`; the intervals are
independent by the Markov property at the left endpoints. -/
theorem le_measure_forall_abs_sub_le [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsBrownianReal X P) (hcont : ∀ ω, Continuous fun t => X t ω) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal ((1 / 2304 - 4 * Real.exp (-10)) ^ 5184)
      ≤ P {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ 4 * a ^ 2 → |X s ω - X 0 ω| ≤ a} := by
  set q : ℝ := 1 / 2304 - 4 * Real.exp (-10) with hqdef
  have hq0 : 0 < q := one_div_sub_four_mul_exp_neg_ten_pos
  set h : ℝ≥0 := ⟨(a / 36) ^ 2, by positivity⟩ with hhdef
  have hhc : (h : ℝ) = (a / 36) ^ 2 := rfl
  have hh0 : 0 < (h : ℝ) := by rw [hhc]; positivity
  set ε : ℝ := a / 10368 with hεdef
  set c : ℝ := a / 2 with hcdef
  have hε0 : 0 ≤ ε := by positivity
  have hc0 : 0 < c := by positivity
  have hεh : ε ^ 2 ≤ h := by
    rw [hhc, hεdef]
    nlinarith [sq_nonneg a]
  set t : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * h with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have ht_succ : ∀ j, t j + h = t (j + 1) := fun j => by
    simp only [htdef]
    push_cast
    ring
  have ht_mono : Monotone t := fun i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) h)
  -- the event asked of one interval, as a measurable set of paths
  set S : Set (ℝ≥0 → ℝ) :=
    (⋂ r ∈ D, {f : ℝ≥0 → ℝ | |f (r : ℝ≥0)| ≤ c}) ∩ {f | |f h| ≤ ε} with hSdef
  have hS : MeasurableSet S :=
    (MeasurableSet.biInter hDc fun r _ =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply (r : ℝ≥0)))
        measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply h))
        measurable_const)
  -- the increments after `t k`, and the event that the first `k` intervals succeed
  set Y : ℕ → Ω → ℝ≥0 → ℝ := fun k ω s => X (t k + s) ω - X (t k) ω with hYdef
  set A : ℕ → Set Ω := fun k => {ω | ∀ j < k, Y j ω ∈ S} with hAdef
  have hAmeas : ∀ k, MeasurableSet[MeasurableSpace.comap
      (fun ω (r : Set.Iic (t k)) => X (r : ℝ≥0) ω) inferInstance] (A k) := by
    intro k
    have hEq : A k = ⋂ j ∈ {j : ℕ | j < k},
        ((⋂ r ∈ D, {ω | |X (t j + (r : ℝ≥0)) ω - X (t j) ω| ≤ c}) ∩
          {ω | |X (t j + h) ω - X (t j) ω| ≤ ε}) := by
      ext ω
      simp only [hAdef, hYdef, hSdef, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [hEq]
    refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
    have hjk : t (j + 1) ≤ t k := ht_mono (Nat.succ_le_of_lt hj)
    have hj0 : t j ≤ t k := le_trans (ht_mono (Nat.le_succ j)) hjk
    refine MeasurableSet.inter (MeasurableSet.biInter hDc fun r _ => ?_) ?_
    · refine measurableSet_comap_abs_sub_le ?_ hj0 c
      refine le_trans ?_ hjk
      rw [← ht_succ]
      exact add_le_add le_rfl r.2.2
    · exact measurableSet_comap_abs_sub_le (by rw [ht_succ]; exact hjk) hj0 ε
  -- one interval succeeds with probability at least `q`
  have hpiece : ∀ k, ENNReal.ofReal q ≤ P (Y k ⁻¹' S) := by
    intro k
    have hYk : IsBrownianReal (fun s ω => X (t k + s) ω - X (t k) ω) P := hX.shift (t k)
    have hbound := le_measure_forall_abs_sub_lt_and_mem_Ioc hYk hh0 hε0 hεh hc0
    have hqle : q ≤ ε / (8 * Real.sqrt h) - 4 * Real.exp (-(c ^ 2 / (32 * (h : ℝ)))) := by
      have hsq : Real.sqrt (h : ℝ) = a / 36 := by
        rw [hhc]
        exact Real.sqrt_sq (by positivity)
      have h1 : ε / (8 * Real.sqrt h) = 1 / 2304 := by
        rw [hsq, hεdef, div_eq_iff (by positivity)]
        ring
      have h2 : c ^ 2 / (32 * (h : ℝ)) = 81 / 8 := by
        rw [hhc, hcdef, div_eq_iff (by positivity)]
        ring
      rw [h1, h2, hqdef]
      have : Real.exp (-(81 / 8)) ≤ Real.exp (-10) := Real.exp_le_exp.2 (by norm_num)
      linarith
    refine le_trans (ENNReal.ofReal_le_ofReal hqle) (le_trans hbound (measure_mono ?_))
    intro ω hω
    obtain ⟨hosc, hpos, hle⟩ := hω
    simp only [add_zero, sub_self, sub_zero] at hosc hpos hle
    simp only [hYdef, hSdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    refine ⟨fun r _ => (hosc r r.2.2).le, ?_⟩
    rw [abs_of_pos hpos]
    exact hle
  -- the intervals are independent
  have hind : ∀ k : ℕ, ENNReal.ofReal q ^ k ≤ P (A k) := by
    intro k
    induction k with
    | zero =>
      have hA0 : A 0 = Set.univ := by
        ext ω
        simp [hAdef]
      rw [hA0, measure_univ, pow_zero]
    | succ k ih =>
      have hsplit : A (k + 1) = Y k ⁻¹' S ∩ A k := by
        ext ω
        simp only [hAdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · intro hω
          exact ⟨hω k (Nat.lt_succ_self k), fun j hj => hω j (Nat.lt_succ_of_lt hj)⟩
        · rintro ⟨hk, hω⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hω j hj
          · exact hk
      obtain ⟨R, hR, hRA⟩ := MeasurableSpace.measurableSet_comap.1 (hAmeas k)
      have hindep := hX.toIsPreBrownianReal.indepFun_shift (t k)
      have hmul : P (A (k + 1)) = P (Y k ⁻¹' S) * P (A k) := by
        rw [hsplit, ← hRA, hYdef]
        exact hindep.measure_inter_preimage_eq_mul S R hS hR
      rw [hmul, pow_succ, mul_comm (P (Y k ⁻¹' S))]
      exact mul_le_mul' ih (hpiece k)
  -- on all the intervals the path stays within `a` of its start
  have hpath : ∀ ω ∈ A 5184, ∀ s : ℝ≥0, (s : ℝ) ≤ 4 * a ^ 2 → |X s ω - X 0 ω| ≤ a := by
    intro ω hω
    simp only [hAdef, Set.mem_ofPred_eq] at hω
    have hmem : ∀ j < 5184, (∀ r ∈ D, |X (t j + (r : ℝ≥0)) ω - X (t j) ω| ≤ c) ∧
        |X (t j + h) ω - X (t j) ω| ≤ ε := by
      intro j hj
      have hj' := hω j hj
      simp only [hYdef, hSdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hj'
      exact hj'
    have hstep1 : ∀ j, j ≤ 5184 → |X (t j) ω - X 0 ω| ≤ j * ε := by
      intro j
      induction j with
      | zero =>
        intro _
        simp [ht0]
      | succ j ih =>
        intro hj
        have hjN : j < 5184 := hj
        have h1 := (hmem j hjN).2
        rw [ht_succ] at h1
        calc |X (t (j + 1)) ω - X 0 ω|
            ≤ |X (t (j + 1)) ω - X (t j) ω| + |X (t j) ω - X 0 ω| := abs_sub_le _ _ _
          _ ≤ ε + j * ε := add_le_add h1 (ih hjN.le)
          _ = ((j + 1 : ℕ) : ℝ) * ε := by push_cast; ring
    have hstep2 : ∀ j, j ≤ 5184 → ∀ s : ℝ≥0, s ≤ t j → |X s ω - X 0 ω| ≤ c + j * ε := by
      intro j
      induction j with
      | zero =>
        intro _ s hs
        rw [ht0] at hs
        rw [nonpos_iff_eq_zero.1 hs, sub_self, abs_zero, Nat.cast_zero, zero_mul, add_zero]
        exact hc0.le
      | succ j ih =>
        intro hj s hs
        have hjN : j < 5184 := hj
        have hstep : (j : ℝ) * ε ≤ ((j + 1 : ℕ) : ℝ) * ε :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hε0
        by_cases hsj : s ≤ t j
        · exact le_trans (ih hjN.le s hsj) (by linarith)
        · have hsj' : t j ≤ s := (not_le.1 hsj).le
          have hr : s - t j ≤ h := by
            rw [← ht_succ] at hs
            exact tsub_le_iff_left.2 hs
          have hcj : Continuous fun r : ℝ≥0 => X (t j + r) ω - X (t j) ω :=
            ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
          have hbd : |X (t j + (s - t j)) ω - X (t j) ω| ≤ c :=
            abs_le_of_forall_mem_dense hcj hDd (hmem j hjN).1 hr
          rw [add_tsub_cancel_of_le hsj'] at hbd
          calc |X s ω - X 0 ω| ≤ |X s ω - X (t j) ω| + |X (t j) ω - X 0 ω| :=
                abs_sub_le _ _ _
            _ ≤ c + j * ε := add_le_add hbd (hstep1 j hjN.le)
            _ ≤ c + ((j + 1 : ℕ) : ℝ) * ε := by linarith
    intro s hs
    have htN : ((t 5184 : ℝ≥0) : ℝ) = 4 * a ^ 2 := by
      show ((((5184 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) = 4 * a ^ 2
      rw [NNReal.coe_mul, NNReal.coe_natCast, hhc]
      push_cast
      ring
    have hsN : s ≤ t 5184 := by
      rw [← NNReal.coe_le_coe, htN]
      exact hs
    have hfin : c + ((5184 : ℕ) : ℝ) * ε = a := by
      rw [hcdef, hεdef]
      push_cast
      ring
    have := hstep2 5184 le_rfl s hsN
    linarith
  calc ENNReal.ofReal (q ^ 5184) = ENNReal.ofReal q ^ 5184 := ENNReal.ofReal_pow hq0.le _
    _ ≤ P (A 5184) := hind 5184
    _ ≤ _ := measure_mono fun ω hω => hpath ω hω

/-! ### Dimension `d` -/

/-- A vector `v` of `ℝ ^ d` such that every coordinate of `√d • v` is at most `a` in absolute
value has norm less than every `r > a`. -/
theorem norm_lt_of_forall_abs_sqrt_smul_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) {a r : ℝ}
    (ha : 0 ≤ a) (har : a < r) (h : ∀ i, |(Real.sqrt d • v) i| ≤ a) : ‖v‖ < r := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hv : v = 0 := Subsingleton.elim v 0
    rw [hv, norm_zero]
    exact lt_of_le_of_lt ha har
  · have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hnorm := norm_le_sqrt_mul_of_forall_abs_le (Real.sqrt d • v) ha h
    rw [norm_smul, Real.norm_of_nonneg hsq.le] at hnorm
    exact lt_of_le_of_lt (le_of_mul_le_mul_left hnorm hsq) har

omit [MeasurableSpace Ω] in
/-- **The pathwise step in dimension `d`.**  Let `C t = √d • (b t - u)` be continuous with
`b 0 = u`.  If every coordinate of `C` stays within `a` of its starting value at the times of a
dense subset of `[0, T]`, then `b` stays at distance less than `r` from `u` up to time `T`, for
every `r > a`. -/
theorem norm_sub_lt_of_forall_mem_dense {d : ℕ} {C b : ℝ≥0 → EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d)} (hC : Continuous C)
    (hCb : ∀ t, C t = Real.sqrt d • (b t - u)) (hb0 : b 0 = u) {T : ℝ≥0}
    {D : Set (Set.Icc (0 : ℝ≥0) T)} (hD : Dense D) {a r : ℝ} (ha : 0 ≤ a) (har : a < r)
    (hmem : ∀ i, ∀ q ∈ D, |C (q : ℝ≥0) i - C 0 i| ≤ a) {s : ℝ≥0} (hs : s ≤ T) :
    ‖b s - u‖ < r := by
  have hC0 : C 0 = 0 := by rw [hCb 0, hb0, sub_self, smul_zero]
  refine norm_lt_of_forall_abs_sqrt_smul_le (b s - u) ha har fun i => ?_
  rw [← hCb s]
  have hci : Continuous fun t : ℝ≥0 => C t i - C 0 i :=
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp hC).sub continuous_const
  have h1 : |C s i - C 0 i| ≤ a := abs_le_of_forall_mem_dense hci hD (hmem i) hs
  rwa [hC0, PiLp.zero_apply, sub_zero] at h1

/-- **Brownian motion stays in a ball up to the square of its radius with probability bounded
below.**  For Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)` started at `u`, the
probability that it stays in the open ball of radius `r` about `u` at all times before `r ^ 2` is
at least a constant `c₂ > 0` depending only on `d`.  The proof takes
`c₂ = ((1 / 2304 - 4 e ^ (-10)) ^ 5184) ^ d`: each of the `d` independent coordinates of a
continuous version, a real Brownian motion, stays within `r / 2` of its start up to time `r ^ 2`
with probability at least `(1 / 2304 - 4 e ^ (-10)) ^ 5184` (`le_measure_forall_abs_sub_le`), and
then the motion stays within distance `r / 2` of `u`. -/
theorem exists_brownian_stay_pos (d : ℕ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (u : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          IsBrownianSpace d u B P → ∀ r : ℝ, 0 < r →
            ENNReal.ofReal c₂ ≤ P {ω | ∀ s : ℝ≥0, (s : ℝ) < r ^ 2 → ‖B s ω - u‖ < r} := by
  have hp0 : 0 < (1 / 2304 - 4 * Real.exp (-10)) ^ 5184 :=
    pow_pos one_div_sub_four_mul_exp_neg_ten_pos _
  refine ⟨((1 / 2304 - 4 * Real.exp (-10)) ^ 5184) ^ d, pow_pos hp0 _, ?_⟩
  intro u Ω _ P hP B hB r hr
  have := hP
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / 2 := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; positivity
  have har : a < r := by rw [hadef]; exact half_lt_self hr
  have hr2 : r ^ 2 = 4 * a ^ 2 := by rw [hadef]; ring
  obtain ⟨T, hTc⟩ : ∃ T : ℝ≥0, (T : ℝ) = 4 * a ^ 2 := ⟨⟨4 * a ^ 2, by positivity⟩, rfl⟩
  obtain ⟨C, -, hCc, -, hCae, hCcoord, hCind⟩ := hB.exists_continuousVersion
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  set V : Set (ℝ≥0 → ℝ) := ⋂ q ∈ D, {f : ℝ≥0 → ℝ | |f (q : ℝ≥0) - f 0| ≤ a} with hVdef
  have hV : MeasurableSet V :=
    MeasurableSet.biInter hDc fun q _ =>
      measurableSet_le (continuous_abs.measurable.comp
        ((measurable_pi_apply (q : ℝ≥0)).sub (measurable_pi_apply (0 : ℝ≥0)))) measurable_const
  set E : Fin d → Set Ω := fun i => (fun ω (t : ℝ≥0) => C t ω i) ⁻¹' V with hEdef
  have hE : ∀ i, ENNReal.ofReal ((1 / 2304 - 4 * Real.exp (-10)) ^ 5184) ≤ P (E i) := by
    intro i
    refine le_trans (le_measure_forall_abs_sub_le (hCcoord i)
      (fun ω => (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp (hCc ω)) ha)
      (measure_mono ?_)
    intro ω hω
    simp only [hEdef, hVdef, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    intro q _
    exact hω q (by rw [← hTc]; exact NNReal.coe_le_coe.2 q.2.2)
  have hprod : P (⋂ i ∈ (Finset.univ : Finset (Fin d)), E i) = ∏ i, P (E i) :=
    hCind.meas_biInter fun i _ => ⟨V, hV, rfl⟩
  have hsub : (⋂ i ∈ (Finset.univ : Finset (Fin d)), E i)
      ≤ᵐ[P] {ω | ∀ s : ℝ≥0, (s : ℝ) < r ^ 2 → ‖B s ω - u‖ < r} := by
    filter_upwards [hCae, hB.start] with ω hω hstart hmem
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, hEdef, hVdef, Set.mem_preimage,
      Set.mem_ofPred_eq] at hmem
    intro s hs
    have hsT : s ≤ T := by
      rw [← NNReal.coe_le_coe, hTc, ← hr2]
      exact hs.le
    exact norm_sub_lt_of_forall_mem_dense (hCc ω) hω hstart hDd ha.le har hmem hsT
  calc ENNReal.ofReal (((1 / 2304 - 4 * Real.exp (-10)) ^ 5184) ^ d)
      = ENNReal.ofReal ((1 / 2304 - 4 * Real.exp (-10)) ^ 5184) ^ d :=
        ENNReal.ofReal_pow hp0.le _
    _ = ∏ _i : Fin d, ENNReal.ofReal ((1 / 2304 - 4 * Real.exp (-10)) ^ 5184) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, P (E i) := Finset.prod_le_prod fun i _ => hE i
    _ = P (⋂ i ∈ (Finset.univ : Finset (Fin d)), E i) := hprod.symm
    _ ≤ _ := measure_mono_ae hsub

end LatticeProb

end
