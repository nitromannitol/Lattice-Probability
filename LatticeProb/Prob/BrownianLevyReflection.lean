import LatticeProb.Prob.BrownianMax
import LatticeProb.Prob.BrownianDriftSmallBall
import LatticeProb.Gauss.TailMills

/-!
# Lévy's reflection inequality for Brownian motion

For a Brownian motion `B`, the chance that the path reaches the level `a` before time `T` is at
most twice the chance that `B T - B 0 ≥ a`:
`P (∃ s ≤ T, a < B s - B 0) ≤ 2 P (a ≤ B T - B 0)`.
The constant `2` is sharp (the reflection principle gives equality), and it is what makes the
survival probability `P (∀ s ≤ T, -a ≤ B s - B 0)` at least `P (|B T - B 0| < a)`, a quantity
of order `a / √T`.

The route is Lévy's inequality on a finite grid, as for the Gaussian maximal estimate in
`LatticeProb/Prob/BrownianMax.lean`: no reflection principle at stopping times and no
continuous-time martingale theory is needed.  If the path first passes `a` at the grid point
`t k`, it ends above `a` as soon as the increment from `t k` to the last grid point is
nonnegative; that increment is independent of the first passage event and is a centred Gaussian
variable, hence nonnegative with probability at least one half.

## Main results

* `one_le_two_mul_measure_nonneg`: a centred Gaussian variable is nonnegative with probability
  at least `1 / 2`.
* `measure_grid_exists_ge_le_two_mul`: Lévy's inequality on a finite grid.
* `measure_exists_lt_le_two_mul`: Lévy's inequality for the whole path on `[0, T]`.
* `le_measure_forall_ge_neg`: the survival lower bound
  `a / (16 √T) ≤ P (∀ s ≤ T, -a ≤ B s - B 0)` for `0 < a`, `a ^ 2 ≤ T`.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A centred Gaussian variable is nonnegative with probability at least one half, written
`1 ≤ 2 P (0 ≤ X)`: the law is invariant under `x ↦ -x`, and `[0, ∞)` and `(-∞, 0]` cover the
line. -/
theorem one_le_two_mul_measure_nonneg [IsProbabilityMeasure P] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : 1 ≤ 2 * P {ω | 0 ≤ X ω} := by
  have h1 : P {ω | 0 ≤ X ω} = gaussianReal 0 v (Set.Ici 0) := by
    rw [← hX.map_eq, Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Ici]
    rfl
  have hneg : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have h2 : gaussianReal 0 v (Set.Iic 0) = gaussianReal 0 v (Set.Ici 0) := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have h3 : (1 : ℝ≥0∞) ≤ gaussianReal 0 v (Set.Ici 0) + gaussianReal 0 v (Set.Iic 0) := by
    calc (1 : ℝ≥0∞) = gaussianReal 0 v Set.univ := measure_univ.symm
      _ ≤ gaussianReal 0 v (Set.Ici 0 ∪ Set.Iic 0) := by
          refine measure_mono fun x _ => ?_
          rcases le_total 0 x with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ _ := measure_union_le _ _
  rw [h2, ← two_mul] at h3
  rw [h1]
  exact h3

/-- **Lévy's inequality on a finite grid.**  For a monotone family of times `t 0 ≤ … ≤ t N`,
the chance that `B (t k) - B (t 0)` reaches `a` for some `k ≤ N` is at most twice the chance
that `B (t N) - B (t 0)` does.  The first passage event at `t k` depends on the increments
before `t k`; the event `B (t N) - B (t k) ≥ 0` depends on the increments after `t k`, is
independent of it and has probability at least `1 / 2`. -/
theorem measure_grid_exists_ge_le_two_mul [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (N : ℕ) (t : ℕ → ℝ≥0) (hmono : Monotone t) (a : ℝ) :
    P {ω | ∃ k ≤ N, a ≤ B (t k) ω - B (t 0) ω} ≤ 2 * P {ω | a ≤ B (t N) ω - B (t 0) ω} := by
  classical
  set D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω with hD
  have hDm : ∀ i, Measurable (D i) := fun i => (hm _).sub (hm _)
  have hind : iIndepFun D P := hB.hasIndepIncrements.nat hmono
  set m : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (D i) inferInstance with hmdef
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := fun i => (hDm i).comap_le
  have hiIndep : iIndep m P := hind
  have hIndepk : ∀ k : ℕ, Indep (⨆ i ∈ Set.Iio k, m i) (⨆ i ∈ Set.Ici k, m i) P := fun k =>
    indep_iSup_of_disjoint hle hiIndep (Set.Iio_disjoint_Ici le_rfl)
  have hmeas_sum : ∀ (I : Set ℕ) (s : Finset ℕ), (∀ i ∈ s, i ∈ I) →
      Measurable[⨆ i ∈ I, m i] (fun ω => ∑ i ∈ s, D i ω) := by
    intro I s hs
    refine Finset.measurable_sum s (fun i hi => ?_)
    exact Measurable.mono (measurable_iff_comap_le.2 le_rfl) (le_biSup m (hs i hi)) le_rfl
  set S : ℕ → Ω → ℝ := fun j ω => B (t j) ω - B (t 0) ω with hS
  have hSsum : ∀ j, (fun ω => ∑ i ∈ Finset.range j, D i ω) = S j := by
    intro j
    funext ω
    exact Finset.sum_range_sub (fun i => B (t i) ω) j
  have hSmeas : ∀ k j, j ≤ k → Measurable[⨆ i ∈ Set.Iio k, m i] (S j) := by
    intro k j hjk
    rw [← hSsum j]
    exact hmeas_sum _ _ (fun i hi => lt_of_lt_of_le (Finset.mem_range.1 hi) hjk)
  set A : ℕ → Set Ω := fun k =>
    {ω | a ≤ S k ω} ∩ ⋂ j ∈ Finset.range k, {ω | S j ω < a} with hA
  set G : ℕ → Set Ω := fun k => {ω | 0 ≤ B (t N) ω - B (t k) ω} with hG
  have hAmeas : ∀ k, MeasurableSet[⨆ i ∈ Set.Iio k, m i] (A k) := by
    intro k
    refine MeasurableSet.inter
      (measurableSet_le measurable_const (hSmeas k k le_rfl)) ?_
    refine MeasurableSet.biInter (Finset.range k).countable_toSet (fun j hj => ?_)
    exact measurableSet_lt
      (hSmeas k j (le_of_lt (Finset.mem_range.1 hj))) measurable_const
  have hGmeas : ∀ k, k ≤ N → MeasurableSet[⨆ i ∈ Set.Ici k, m i] (G k) := by
    intro k hk
    have heq : (fun ω => ∑ i ∈ Finset.Ico k N, D i ω) = fun ω => B (t N) ω - B (t k) ω := by
      funext ω
      exact sum_Ico_sub_telescope (fun i => B (t i) ω) hk
    have hmeas : Measurable[⨆ i ∈ Set.Ici k, m i] (fun ω => B (t N) ω - B (t k) ω) := by
      rw [← heq]
      exact hmeas_sum _ _ (fun i hi => (Finset.mem_Ico.1 hi).1)
    exact measurableSet_le measurable_const hmeas
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (iSup₂_le fun i (_ : i ∈ Set.Iio k) => hle i) _ (hAmeas k)
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_le measurable_const ((hm _).sub (hm _))
  have hindep : ∀ k, k ≤ N → P (A k ∩ G k) = P (A k) * P (G k) := by
    intro k hk
    exact ((hIndepk k).indepSet_of_measurableSet (hAmeas k) (hGmeas k hk)).measure_inter_eq_mul
  have hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    rintro ω ⟨hωj, hωj'⟩ ⟨hωk, hωk'⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hωj' hωk' hωj hωk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact absurd hωj (not_le.2 (hωk' j (Finset.mem_range.2 h)))
    · exact absurd hωk (not_le.2 (hωj' k (Finset.mem_range.2 h)))
  have hM : {ω | ∃ k ≤ N, a ≤ S k ω} ⊆ ⋃ k ∈ Finset.range (N + 1), A k := by
    rintro ω ⟨k, hkN, hk⟩
    have hex : ∃ j, a ≤ S j ω := ⟨k, hk⟩
    have hk0 : a ≤ S (Nat.find hex) ω := Nat.find_spec hex
    have hk0le : Nat.find hex ≤ k := Nat.find_le hk
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hk0le hkN))) ?_
    refine ⟨hk0, ?_⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro j hj
    exact not_le.1 (Nat.find_min hex (Finset.mem_range.1 hj))
  have hsub : ∀ k, A k ∩ G k ⊆ {ω | a ≤ S N ω} := by
    rintro k ω ⟨⟨hωA, -⟩, hωG⟩
    simp only [hG, hS, Set.mem_ofPred_eq] at hωA hωG ⊢
    linarith
  have hGhalf : ∀ k, 1 ≤ 2 * P (G k) := fun k =>
    one_le_two_mul_measure_nonneg (hB.hasLaw_sub (t N) (t k))
  have hdisjAG : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint fun k => A k ∩ G k := by
    intro j _ k _ hjk
    exact (hdisj j k hjk).mono Set.inter_subset_left Set.inter_subset_left
  have hdisjA : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint A := by
    intro j _ k _ hjk
    exact hdisj j k hjk
  calc P {ω | ∃ k ≤ N, a ≤ S k ω}
      ≤ P (⋃ k ∈ Finset.range (N + 1), A k) := measure_mono hM
    _ = ∑ k ∈ Finset.range (N + 1), P (A k) :=
        measure_biUnion_finset hdisjA (fun k _ => hAm k)
    _ ≤ ∑ k ∈ Finset.range (N + 1), 2 * P (A k ∩ G k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [hindep k hkN]
        calc P (A k) = P (A k) * 1 := (mul_one _).symm
          _ ≤ P (A k) * (2 * P (G k)) := by gcongr; exact hGhalf k
          _ = 2 * (P (A k) * P (G k)) := by ring
    _ = 2 * P (⋃ k ∈ Finset.range (N + 1), A k ∩ G k) := by
        rw [← Finset.mul_sum, measure_biUnion_finset hdisjAG (fun k _ => (hAm k).inter (hGm k))]
    _ ≤ 2 * P {ω | a ≤ S N ω} := by
        gcongr
        exact Set.iUnion₂_subset fun k _ => hsub k

/-- **Lévy's reflection inequality.**  For a Brownian motion, the chance that `B s - B 0`
exceeds `a` at some time `s ≤ T` is at most twice the chance that `B T - B 0 ≥ a`.  A path which
exceeds `a` at a time `s ≤ T` exceeds it at the dyadic times below `s` close to `s`, by
continuity; on each dyadic grid of `[0, T]`, completed by the endpoint `T`, Lévy's inequality
on a finite grid applies, and the dyadic events increase. -/
theorem measure_exists_lt_le_two_mul [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (T : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ T, a < B s ω - B 0 ω} ≤ 2 * P {ω | a ≤ B T ω - B 0 ω} := by
  classical
  set NN : ℕ → ℕ := fun n => ⌊(T : ℝ) * 2 ^ n⌋₊ with hNN
  set E : ℕ → Set Ω := fun n => {ω | ∃ k ≤ NN n, a < B (dyadicGrid n k) ω - B 0 ω} with hE
  have hgT : ∀ n k, k ≤ NN n → dyadicGrid n k ≤ T := fun n k hk =>
    (dyadicGrid_mono n hk).trans (dyadicGrid_floor_le T n)
  have hEbound : ∀ n, P (E n) ≤ 2 * P {ω | a ≤ B T ω - B 0 ω} := by
    intro n
    set g : ℕ → ℝ≥0 := fun k => if k ≤ NN n then dyadicGrid n k else T with hg
    have hgmono : Monotone g := by
      intro i j hij
      simp only [hg]
      split_ifs with hi hj hj
      · exact dyadicGrid_mono n hij
      · exact hgT n i hi
      · exact absurd (hij.trans hj) hi
      · exact le_rfl
    have hg0 : g 0 = 0 := by simp [hg, dyadicGrid]
    have hgN : g (NN n + 1) = T := by simp [hg]
    have hgrid := measure_grid_exists_ge_le_two_mul hB.toIsPreBrownianReal hm (NN n + 1) g
      hgmono a
    rw [hg0, hgN] at hgrid
    refine le_trans (measure_mono ?_) hgrid
    rintro ω ⟨k, hk, hka⟩
    refine ⟨k, hk.trans (Nat.le_succ _), ?_⟩
    have hgk : g k = dyadicGrid n k := by simp [hg, hk]
    rw [hgk]
    exact hka.le
  have hEmono : Monotone E := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rintro ω ⟨k, hk, hka⟩
    refine ⟨2 * k, ?_, ?_⟩
    · have h1 : (k : ℝ) ≤ (T : ℝ) * 2 ^ n := (Nat.le_floor_iff (by positivity)).1 hk
      refine (Nat.le_floor_iff (by positivity)).2 ?_
      push_cast
      calc (2 : ℝ) * k ≤ 2 * ((T : ℝ) * 2 ^ n) := by linarith
        _ = (T : ℝ) * 2 ^ (n + 1) := by ring
    · have hgg : dyadicGrid (n + 1) (2 * k) = dyadicGrid n k := by
        rw [← NNReal.coe_inj, coe_dyadicGrid, coe_dyadicGrid]
        push_cast
        rw [pow_succ, mul_comm (2 : ℝ) (k : ℝ), mul_div_mul_right _ _ two_ne_zero]
      rw [hgg]
      exact hka
  have hinc : {ω | ∃ s ≤ T, a < B s ω - B 0 ω} ≤ᵐ[P] ⋃ n, E n := by
    filter_upwards [hB.cont] with ω hcont hω
    obtain ⟨s, hs, hsa⟩ := hω
    have hlim : Tendsto (fun n : ℕ => B (dyadicGrid n ⌊(s : ℝ) * 2 ^ n⌋₊) ω - B 0 ω) atTop
        (𝓝 (B s ω - B 0 ω)) :=
      ((hcont.tendsto s).comp (tendsto_dyadicGrid_floor s)).sub_const _
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hsa)).exists
    refine Set.mem_iUnion.2 ⟨n, ⌊(s : ℝ) * 2 ^ n⌋₊, ?_, hn⟩
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity))
  refine le_trans (measure_mono_ae hinc) ?_
  rw [hEmono.measure_iUnion]
  exact iSup_le hEbound

/-- **Survival lower bound.**  For `0 < a` with `a ^ 2 ≤ T`, a Brownian motion stays above
`B 0 - a` during `[0, T]` with probability at least `a / (16 √T)`.  By Lévy's reflection
inequality for `-B`, the failure probability is at most `2 P (B T - B 0 ≤ -a)`; by symmetry of
the centred Gaussian law of `B T - B 0` the complement contains `P (0 < B T - B 0 ≤ a / 2)`,
which is at least `(a / 2)` times the density at `a / 2`. -/
theorem le_measure_forall_ge_neg [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {T : ℝ≥0} {a : ℝ} (ha : 0 < a) (haT : a ^ 2 ≤ T) :
    ENNReal.ofReal (a / (16 * Real.sqrt T)) ≤ P {ω | ∀ s ≤ T, -a ≤ B s ω - B 0 ω} := by
  set S : Set Ω := {ω | ∀ s ≤ T, -a ≤ B s ω - B 0 ω} with hS
  have hT : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) haT
  have hT0 : T ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hT
    exact lt_irrefl _ hT
  have hlaw : HasLaw (fun ω => B T ω - B 0 ω) (gaussianReal 0 T) P := by
    have h := hB.hasLaw_sub T 0
    convert h using 2
    ext
    simp
  have hmeasP : ∀ s : Set ℝ, MeasurableSet s → P {ω | B T ω - B 0 ω ∈ s} = gaussianReal 0 T s := by
    intro s hs
    rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable hs]
    rfl
  have hrefl : P Sᶜ ≤ 2 * gaussianReal 0 T (Set.Iic (-a)) := by
    have h := measure_exists_lt_le_two_mul hB.neg (fun t => (hm t).neg) T a
    refine le_trans (measure_mono ?_) (le_trans h (le_of_eq ?_))
    · intro ω hω
      simp only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨s, hs, hlt⟩ := hω
      refine ⟨s, hs, ?_⟩
      simp only [Pi.neg_apply]
      linarith
    · rw [← hmeasP _ measurableSet_Iic]
      congr 2
      ext ω
      simp only [Pi.neg_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      constructor <;> intro h <;> linarith
  have hsym : gaussianReal 0 T (Set.Ici a) = gaussianReal 0 T (Set.Iic (-a)) := by
    have hneg : (gaussianReal 0 T).map (fun x => -x) = gaussianReal 0 T := by
      rw [gaussianReal_map_neg, neg_zero]
    conv_rhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_Ici, Set.mem_preimage, Set.mem_Iic, neg_le_neg_iff]
  have hsum : gaussianReal 0 T (Set.Ioc 0 (a / 2)) + 2 * gaussianReal 0 T (Set.Iic (-a)) ≤ 1 := by
    have hd1 : Disjoint (Set.Ioc 0 (a / 2)) (Set.Iic (-a)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_Ioc, Set.mem_Iic] at hx hx'
      linarith [hx.1]
    have hd2 : Disjoint (Set.Ioc 0 (a / 2) ∪ Set.Iic (-a)) (Set.Ici a) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Iic, Set.mem_Ici] at hx hx'
      rcases hx with hx | hx
      · linarith [hx.2]
      · linarith
    calc gaussianReal 0 T (Set.Ioc 0 (a / 2)) + 2 * gaussianReal 0 T (Set.Iic (-a))
        = gaussianReal 0 T (Set.Ioc 0 (a / 2)) + gaussianReal 0 T (Set.Iic (-a)) + gaussianReal 0 T (Set.Ici a) := by
          rw [hsym, two_mul, add_assoc]
      _ = gaussianReal 0 T (Set.Ioc 0 (a / 2) ∪ Set.Iic (-a) ∪ Set.Ici a) := by
          rw [measure_union hd2 measurableSet_Ici, measure_union hd1 measurableSet_Iic]
      _ ≤ 1 := prob_le_one
  have hcover : (1 : ℝ≥0∞) ≤ P S + P Sᶜ := by
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ P S + P Sᶜ := measure_union_le _ _
  have hJ : ENNReal.ofReal (a / (16 * Real.sqrt T)) ≤ gaussianReal 0 T (Set.Ioc 0 (a / 2)) := by
    rw [gaussianReal_apply_eq_integral 0 hT0]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans ?_ (GaussTail.le_setIntegral_gaussianPDFReal_Ioc le_rfl (by linarith : (0 : ℝ) ≤ a / 2))
    simp only [gaussianPDFReal_def, sub_zero]
    have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT
    have hr : 0 < Real.sqrt (2 * Real.pi * (T : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have hr2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi * T)
    have hs2 := Real.sq_sqrt hT.le
    have hpT : Real.pi * T ≤ 4 * T := mul_le_mul_of_nonneg_right Real.pi_le_four hT.le
    have hrs : Real.sqrt (2 * Real.pi * (T : ℝ)) ≤ 4 * Real.sqrt (T : ℝ) := by
      nlinarith [hr2, hs2, hpT, hr, hs]
    have he : (1 / 2 : ℝ) ≤ Real.exp (-(a / 2) ^ 2 / (2 * T)) := by
      have h1 : -(1 / 2 : ℝ) ≤ -(a / 2) ^ 2 / (2 * T) := by
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
        nlinarith
      linarith [Real.add_one_le_exp (-(a / 2) ^ 2 / (2 * (T : ℝ)))]
    have hs' : Real.sqrt (T : ℝ) ≠ 0 := hs.ne'
    calc a / (16 * Real.sqrt T) = a / 2 * ((4 * Real.sqrt T)⁻¹ * (1 / 2)) := by
          field_simp
          ring
      _ ≤ a / 2 * ((Real.sqrt (2 * Real.pi * T))⁻¹ * Real.exp (-(a / 2) ^ 2 / (2 * T))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (inv_anti₀ hr hrs) he (by norm_num) (inv_nonneg.2 hr.le)
  have hfin : 2 * gaussianReal 0 T (Set.Iic (-a)) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)
  refine le_trans hJ ?_
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc gaussianReal 0 T (Set.Ioc 0 (a / 2)) + 2 * gaussianReal 0 T (Set.Iic (-a)) ≤ 1 := hsum
    _ ≤ P S + P Sᶜ := hcover
    _ ≤ P S + 2 * gaussianReal 0 T (Set.Iic (-a)) := by gcongr

end LatticeProb

end
