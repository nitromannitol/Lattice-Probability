import LatticeProb.Analysis.ExcursionCountRational

/-!
# Laplace functional of the excursion count

For a set `K ⊆ ℝ` and `s ≤ t`, write `N x = excursionCount K s t x` for the number of complementary intervals of
`K` in `[s, t]` (connected components of `[s, t] \ K`) of length larger than `x`. By Tonelli,
`H = ∫_0^∞ e^{-x} N x dx` is the sum of `1 - e^{-|C|}` over the complementary intervals `C`. This file proves the
two deterministic bounds on `H` used to identify the constant in Lévy's excursion-count theorem by a Laplace
transform:

* `ofReal_one_sub_exp_le_lintegral_excursionCount`: if `K` is closed and `K ∩ [s, t]` is Lebesgue-null, then
  `1 - e^{-(t - s)} ≤ H` (the complementary intervals fill `[s, t]` up to a null set, and on an interval
  `C ⊆ [s, t]` the integral of `e^{-(u - s)}` is at most `1 - e^{-|C|}`);
* `lintegral_excursionCount_le`: for every `δ > 0`, `H ≤ 1 - e^{-(t - s)} + ∫_0^δ N x dx + N δ (N δ - 1)` (the
  thresholds `x ≤ δ` contribute at most `∫_0^δ N`, and for the `n = N δ` intervals longer than `δ` one has
  `∑ (1 - e^{-|C_i|}) ≤ 1 - e^{-∑ |C_i|} + n (n - 1)` and `∑ |C_i| ≤ t - s`).

Auxiliary facts: complementary intervals are measurable, only countably many of them have positive length
(`countable_setOf_pos_diam`), and for closed `K` and `s < t` every point of `[s, t] \ K` lies in one of positive
length (`exists_mem_complementaryIntervals_pos_diam`).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LadderSet

variable {K : Set ℝ} {s t : ℝ}

/-- A complementary interval is an interval, hence a Borel set. -/
theorem measurableSet_of_mem_complementaryIntervals {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t) :
    MeasurableSet C :=
  (isPreconnected_iff_ordConnected.1 (isConnected_of_mem_complementaryIntervals hC).isPreconnected).measurableSet

/-- Only countably many complementary intervals have positive length (each contains a rational point, and
different ones are disjoint). -/
theorem countable_setOf_pos_diam (K : Set ℝ) (s t : ℝ) :
    {C ∈ complementaryIntervals K s t | 0 < diam C}.Countable := by
  have h : ∀ C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C}, ∃ p : ℚ, (p : ℝ) ∈ (C : Set ℝ) := fun C => by
    obtain ⟨p, q, hpq, hsub⟩ :=
      exists_rat_Icc_subset_of_mem_complementaryIntervals (Set.mem_sep_iff.1 C.2).1 (Set.mem_sep_iff.1 C.2).2
    exact ⟨p, hsub (left_mem_Icc.2 (by linarith))⟩
  choose f hf using h
  have hinj : Function.Injective f := fun C D hCD => by
    have hD : ((f C : ℚ) : ℝ) ∈ (D : Set ℝ) := by rw [hCD]; exact hf D
    exact Subtype.ext (eq_of_mem_complementaryIntervals (Set.mem_sep_iff.1 C.2).1 (Set.mem_sep_iff.1 D.2).1
      (hf C) hD)
  exact Set.countable_coe_iff.mp hinj.countable

/-- For closed `K` and `s < t`, every point of `[s, t] \ K` lies in a complementary interval of positive length. -/
theorem exists_mem_complementaryIntervals_pos_diam (hK : IsClosed K) (hst : s < t) {y : ℝ}
    (hy : y ∈ Icc s t \ K) : ∃ C ∈ {C ∈ complementaryIntervals K s t | 0 < diam C}, y ∈ C := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl y hy.2
  have hy1 := hy.1.1
  have hy2 := hy.1.2
  have hab : max s (y - η / 2) < min t (y + η / 2) :=
    max_lt (lt_min hst (by linarith)) (lt_min (by linarith) (by linarith))
  have hsub : Icc (max s (y - η / 2)) (min t (y + η / 2)) ⊆ Icc s t \ K := fun x hx => by
    have h1 := (le_max_right s (y - η / 2)).trans hx.1
    have h2 := hx.2.trans (min_le_right t (y + η / 2))
    refine ⟨⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, fun hxK => hball ?_ hxK⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hya : y ∈ Icc (max s (y - η / 2)) (min t (y + η / 2)) :=
    ⟨max_le hy1 (by linarith), le_min hy2 (by linarith)⟩
  have hC : Icc (max s (y - η / 2)) (min t (y + η / 2)) ⊆ connectedComponentIn (Icc s t \ K) y :=
    isPreconnected_Icc.subset_connectedComponentIn hya hsub
  refine ⟨connectedComponentIn (Icc s t \ K) y, ⟨⟨y, hy, rfl⟩, ?_⟩, mem_connectedComponentIn hy⟩
  have hbdd : Bornology.IsBounded (connectedComponentIn (Icc s t \ K) y) :=
    isBounded_of_mem_complementaryIntervals ⟨y, hy, rfl⟩
  calc (0 : ℝ) < min t (y + η / 2) - max s (y - η / 2) := by linarith
    _ = diam (Icc (max s (y - η / 2)) (min t (y + η / 2))) := (Real.diam_Icc hab.le).symm
    _ ≤ _ := diam_mono hC hbdd

/-- `∫_a^b e^{-(u - c)} du = e^{-(a - c)} - e^{-(b - c)}`, as a lower Lebesgue integral. -/
theorem lintegral_Ioc_exp_neg_sub {a b : ℝ} (c : ℝ) (hab : a ≤ b) :
    ∫⁻ u in Ioc a b, ENNReal.ofReal (Real.exp (-(u - c))) =
      ENNReal.ofReal (Real.exp (-(a - c)) - Real.exp (-(b - c))) := by
  have hcont : Continuous fun u : ℝ => Real.exp (-(u - c)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le), ← intervalIntegral.integral_of_le hab]
  congr 1
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (fun u => -Real.exp (-(u - c))) (Real.exp (-(u - c))) u := by
    intro u _
    have h := ((hasDerivAt_id u).sub_const c).neg.exp.neg
    convert h using 1 <;> (try funext x) <;> simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  ring

/-- `∫_0^∞ e^{-x} 1{x < d} dx = 1 - e^{-d}` for `d ≥ 0`. -/
theorem lintegral_Ioi_indicator_exp_neg {d : ℝ} (hd : 0 ≤ d) :
    ∫⁻ x in Ioi 0, (Iio d).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x =
      ENNReal.ofReal (1 - Real.exp (-d)) := by
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, inter_comm,
    Ioi_inter_Iio, setLIntegral_congr Ioo_ae_eq_Ioc]
  simpa using lintegral_Ioc_exp_neg_sub 0 hd

/-- On an interval `[a, b] ⊆ [s, ∞)`: `e^{-(a - s)} - e^{-(b - s)} ≤ 1 - e^{-(b - a)}`. -/
theorem exp_neg_sub_sub_exp_neg_sub_le {a b : ℝ} (hsa : s ≤ a) (hab : a ≤ b) :
    Real.exp (-(a - s)) - Real.exp (-(b - s)) ≤ 1 - Real.exp (-(b - a)) := by
  have h1 : Real.exp (-(b - s)) = Real.exp (-(a - s)) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(a - s)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [h1]
  nlinarith [mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 h3)]

/-- **Bonferroni bound.** For `d i ≥ 0`, `∑ (1 - e^{-d i}) ≤ 1 - e^{-∑ d i} + n (n - 1)` with `n` the number of
terms. -/
theorem sum_one_sub_exp_neg_le {ι : Type*} (L : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ L, 0 ≤ d i) :
    ∑ i ∈ L, (1 - Real.exp (-d i)) ≤
      (1 - Real.exp (-∑ i ∈ L, d i)) + (L.card : ℝ) * ((L.card : ℝ) - 1) := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert a L ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ih := ih fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hda := hd a (Finset.mem_insert_self a L)
    have hS : 0 ≤ ∑ i ∈ L, d i := Finset.sum_nonneg fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hA := Real.exp_pos (-d a)
    have hA1 : Real.exp (-d a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hBn : 1 - Real.exp (-∑ i ∈ L, d i) ≤ L.card := by
      rcases L.eq_empty_or_nonempty with rfl | hne
      · simp
      · have h1 : (1 : ℝ) ≤ L.card := by exact_mod_cast hne.card_pos
        linarith [Real.exp_pos (-∑ i ∈ L, d i)]
    have hexp : Real.exp (-(d a + ∑ i ∈ L, d i)) = Real.exp (-d a) * Real.exp (-∑ i ∈ L, d i) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hBn (sub_nonneg.2 hA1), mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) L.card)]

/-- Finitely many complementary intervals of `K` in `[s, t]` have total length at most `t - s`. -/
theorem sum_diam_le (hst : s ≤ t) {L : Finset (Set ℝ)} (hL : ∀ C ∈ L, C ∈ complementaryIntervals K s t) :
    ∑ C ∈ L, diam C ≤ t - s := by
  have hdisj : (L : Set (Set ℝ)).PairwiseDisjoint id := fun C hC D hD hCD =>
    show Disjoint C D from Set.disjoint_left.2 fun y hyC hyD =>
      hCD (eq_of_mem_complementaryIntervals (hL C hC) (hL D hD) hyC hyD)
  have h : ENNReal.ofReal (∑ C ∈ L, diam C) ≤ ENNReal.ofReal (t - s) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun C _ => diam_nonneg, ← Real.volume_Icc]
    calc ∑ C ∈ L, ENNReal.ofReal (diam C) ≤ ∑ C ∈ L, volume C :=
          Finset.sum_le_sum fun C hC => ofReal_diam_le_volume_of_mem_complementaryIntervals (hL C hC)
      _ = volume (⋃ C ∈ L, id C) :=
          (measure_biUnion_finset hdisj fun C hC => measurableSet_of_mem_complementaryIntervals (hL C hC)).symm
      _ ≤ volume (Icc s t) :=
          measure_mono (iUnion₂_subset fun C hC => (subset_of_mem_complementaryIntervals (hL C hC)).trans
            sdiff_subset)
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h

/-- **Lower bound for the Laplace functional of the excursion count.** If `K` is closed and `K ∩ [s, t]` is
Lebesgue-null, then `1 - e^{-(t - s)} ≤ ∫_0^∞ e^{-x} N x dx`, `N x = excursionCount K s t x`. -/
theorem ofReal_one_sub_exp_le_lintegral_excursionCount (hK : IsClosed K) (hst : s ≤ t)
    (hK0 : volume (K ∩ Icc s t) = 0) :
    ENNReal.ofReal (1 - Real.exp (-(t - s))) ≤
      ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hS := countable_setOf_pos_diam K s t
  have := hS.to_subtype
  have he : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x)) :=
    (Real.measurable_exp.comp measurable_neg).ennreal_ofReal
  have hcover : Ioc s t ⊆ (⋃ C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C}, (C : Set ℝ)) ∪ (K ∩ Icc s t) :=
    fun u hu => by
      by_cases huK : u ∈ K
      · exact Or.inr ⟨huK, Ioc_subset_Icc_self hu⟩
      · obtain ⟨C, hC, huC⟩ := exists_mem_complementaryIntervals_pos_diam hK hst ⟨Ioc_subset_Icc_self hu, huK⟩
        exact Or.inl (mem_iUnion.2 ⟨⟨C, hC⟩, huC⟩)
  have hcomp : ∀ C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C},
      ∫⁻ u in (C : Set ℝ), ENNReal.ofReal (Real.exp (-(u - s))) ≤
        ∫⁻ x in Ioi 0, (Iio (diam (C : Set ℝ))).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x := by
    intro C
    have hC := (Set.mem_sep_iff.1 C.2).1
    have hbdd := isBounded_of_mem_complementaryIntervals hC
    have hne : (C : Set ℝ).Nonempty := (isConnected_of_mem_complementaryIntervals hC).nonempty
    have hsa : s ≤ sInf (C : Set ℝ) :=
      le_csInf hne fun x hx => (subset_of_mem_complementaryIntervals hC hx).1.1
    have hab : sInf (C : Set ℝ) ≤ sSup (C : Set ℝ) := csInf_le_csSup hne hbdd.bddBelow hbdd.bddAbove
    rw [lintegral_Ioi_indicator_exp_neg diam_nonneg, Real.diam_eq hbdd]
    calc ∫⁻ u in (C : Set ℝ), ENNReal.ofReal (Real.exp (-(u - s)))
        ≤ ∫⁻ u in Icc (sInf (C : Set ℝ)) (sSup (C : Set ℝ)), ENNReal.ofReal (Real.exp (-(u - s))) :=
          lintegral_mono_set (subset_Icc_csInf_csSup hbdd.bddBelow hbdd.bddAbove)
      _ = ∫⁻ u in Ioc (sInf (C : Set ℝ)) (sSup (C : Set ℝ)), ENNReal.ofReal (Real.exp (-(u - s))) :=
          (setLIntegral_congr Ioc_ae_eq_Icc).symm
      _ = ENNReal.ofReal (Real.exp (-(sInf (C : Set ℝ) - s)) - Real.exp (-(sSup (C : Set ℝ) - s))) :=
          lintegral_Ioc_exp_neg_sub s hab
      _ ≤ _ := ENNReal.ofReal_le_ofReal (exp_neg_sub_sub_exp_neg_sub_le hsa hab)
  have hfinite : ∀ F : Finset ↥{C ∈ complementaryIntervals K s t | 0 < diam C},
      ∑ C ∈ F, ∫⁻ x in Ioi 0, (Iio (diam (C : Set ℝ))).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x ≤
        ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x := by
    intro F
    refine Eq.trans_le (lintegral_finsetSum F
      (f := fun C x => (Iio (diam (C : Set ℝ))).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x)
      fun C _ => he.indicator measurableSet_Iio).symm ?_
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    simp only [Set.indicator_apply, Set.mem_Iio]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul']
    gcongr
    have hfin := finite_setOf_lt_diam K s t (ε := x) hx
    unfold excursionCount
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
    refine Set.ncard_le_ncard ?_ hfin
    rintro _ ⟨C, hC, rfl⟩
    exact ⟨(Set.mem_sep_iff.1 C.2).1, (Finset.mem_filter.1 (Finset.mem_coe.1 hC)).2⟩
  calc ENNReal.ofReal (1 - Real.exp (-(t - s)))
      = ∫⁻ u in Ioc s t, ENNReal.ofReal (Real.exp (-(u - s))) := by
        rw [lintegral_Ioc_exp_neg_sub s hst.le, sub_self, neg_zero, Real.exp_zero]
    _ ≤ ∫⁻ u in (⋃ C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C}, (C : Set ℝ)) ∪ (K ∩ Icc s t),
          ENNReal.ofReal (Real.exp (-(u - s))) := lintegral_mono_set hcover
    _ ≤ (∫⁻ u in ⋃ C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C}, (C : Set ℝ),
          ENNReal.ofReal (Real.exp (-(u - s)))) + ∫⁻ u in K ∩ Icc s t, ENNReal.ofReal (Real.exp (-(u - s))) :=
        lintegral_union_le _ _ _
    _ = ∑' C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C},
          ∫⁻ u in (C : Set ℝ), ENNReal.ofReal (Real.exp (-(u - s))) := by
        rw [setLIntegral_measure_zero _ _ hK0, add_zero]
        exact lintegral_iUnion (fun C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C} =>
            measurableSet_of_mem_complementaryIntervals (Set.mem_sep_iff.1 C.2).1)
          (fun (C D : ↥{C ∈ complementaryIntervals K s t | 0 < diam C}) hCD => show Disjoint (C : Set ℝ) D from Set.disjoint_left.2 fun y hyC hyD =>
            hCD (Subtype.ext (eq_of_mem_complementaryIntervals (Set.mem_sep_iff.1 C.2).1
              (Set.mem_sep_iff.1 D.2).1 hyC hyD))) _
    _ ≤ ∑' C : ↥{C ∈ complementaryIntervals K s t | 0 < diam C},
          ∫⁻ x in Ioi 0, (Iio (diam (C : Set ℝ))).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x :=
        ENNReal.tsum_le_tsum hcomp
    _ ≤ _ := by
        rw [ENNReal.tsum_eq_iSup_sum]
        exact iSup_le hfinite

/-- **Upper bound for the Laplace functional of the excursion count.** For `s ≤ t` and `δ > 0`, with
`N x = excursionCount K s t x`:
`∫_0^∞ e^{-x} N x dx ≤ 1 - e^{-(t - s)} + ∫_0^δ N x dx + N δ (N δ - 1)`. -/
theorem lintegral_excursionCount_le (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x ≤
      ENNReal.ofReal (1 - Real.exp (-(t - s))) + (∫⁻ x in Ioc 0 δ, (excursionCount K s t x : ℝ≥0∞)) +
        ((excursionCount K s t δ * (excursionCount K s t δ - 1) : ℕ) : ℝ≥0∞) := by
  have he : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x)) :=
    (Real.measurable_exp.comp measurable_neg).ennreal_ofReal
  obtain ⟨L, hL⟩ : ∃ L : Finset (Set ℝ), (L : Set (Set ℝ)) = {C ∈ complementaryIntervals K s t | δ < diam C} :=
    ⟨(finite_setOf_lt_diam K s t hδ).toFinset, (finite_setOf_lt_diam K s t hδ).coe_toFinset⟩
  have hLmem : ∀ C ∈ L, C ∈ complementaryIntervals K s t ∧ δ < diam C := fun C hC => by
    have h : C ∈ (L : Set (Set ℝ)) := hC
    rw [hL] at h
    exact h
  have hN : excursionCount K s t δ = L.card := by
    rw [excursionCount, ← hL, Set.ncard_coe_finset]
  have hsmall : ∫⁻ x in Ioc 0 δ, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x ≤
      ∫⁻ x in Ioc 0 δ, (excursionCount K s t x : ℝ≥0∞) :=
    setLIntegral_mono' measurableSet_Ioc fun x hx =>
      mul_le_of_le_one_left (by simp) (ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by linarith [hx.1])))
  have hlong : ∫⁻ x in Ioi δ, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x ≤
      ∑ C ∈ L, ENNReal.ofReal (1 - Real.exp (-diam C)) := by
    calc ∫⁻ x in Ioi δ, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x
        ≤ ∫⁻ x in Ioi δ, ∑ C ∈ L, (Iio (diam C)).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x := by
          refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
          simp only [Set.indicator_apply, Set.mem_Iio]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul']
          gcongr
          unfold excursionCount
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard (fun C hC => ?_) (Finset.finite_toSet _)
          have hCL : C ∈ (L : Set (Set ℝ)) := by
            rw [hL]
            exact ⟨hC.1, lt_trans hx hC.2⟩
          exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hCL, hC.2⟩)
      _ = ∑ C ∈ L, ∫⁻ x in Ioi δ, (Iio (diam C)).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x :=
          lintegral_finsetSum L (f := fun C x => (Iio (diam C)).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x)
            fun C _ => he.indicator measurableSet_Iio
      _ ≤ ∑ C ∈ L, ∫⁻ x in Ioi 0, (Iio (diam C)).indicator (fun x => ENNReal.ofReal (Real.exp (-x))) x :=
          Finset.sum_le_sum fun C _ => lintegral_mono_set (Ioi_subset_Ioi hδ.le)
      _ = ∑ C ∈ L, ENNReal.ofReal (1 - Real.exp (-diam C)) :=
          Finset.sum_congr rfl fun C _ => lintegral_Ioi_indicator_exp_neg diam_nonneg
  have hsum : ∑ C ∈ L, ENNReal.ofReal (1 - Real.exp (-diam C)) ≤
      ENNReal.ofReal (1 - Real.exp (-(t - s))) + ((L.card * (L.card - 1) : ℕ) : ℝ≥0∞) := by
    have hd : ∀ C ∈ L, 0 ≤ diam C := fun C _ => diam_nonneg
    have hle := sum_diam_le hst fun C hC => (hLmem C hC).1
    have hB := sum_one_sub_exp_neg_le L (fun C => diam C) hd
    have hcast : ((L.card * (L.card - 1) : ℕ) : ℝ) = (L.card : ℝ) * ((L.card : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos L.card with h | h
      · simp [h]
      · rw [Nat.cast_mul, Nat.cast_pred h]
    have hexp : Real.exp (-(t - s)) ≤ Real.exp (-∑ C ∈ L, diam C) := Real.exp_le_exp.2 (by linarith)
    rw [← ENNReal.ofReal_sum_of_nonneg fun C hC => sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith [hd C hC])),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
        (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hcast]
    linarith
  calc ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x
      ≤ (∫⁻ x in Ioc 0 δ, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x) +
          ∫⁻ x in Ioi δ, ENNReal.ofReal (Real.exp (-x)) * excursionCount K s t x := by
        rw [← Ioc_union_Ioi_eq_Ioi hδ.le]
        exact lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in Ioc 0 δ, (excursionCount K s t x : ℝ≥0∞)) +
          (ENNReal.ofReal (1 - Real.exp (-(t - s))) + ((L.card * (L.card - 1) : ℕ) : ℝ≥0∞)) :=
        add_le_add hsmall (hlong.trans hsum)
    _ = _ := by rw [hN]; ring

end LatticeProb.LadderSet
