import Mathlib
import LatticeProb.Prob.KolmogorovPi

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb ENNReal
open scoped ENNReal NNReal

/-- The clamped process inherits the moment bound: the increment of `X`
between the clamps of two points is bounded by the moment bound at the
unclamped distance, because clamping contracts distances. -/
theorem LatticeProb.boxClamp_process_le {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {p q M : ℝ} (hq : 0 ≤ q) (hM : 0 ≤ M) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {X : (Fin k → ℝ) → Ω → ℝ}
    (hbound : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q)
    (u v : Fin k → ℝ) :
    ∫ ω, |X (boxClamp a b hab u) ω - X (boxClamp a b hab v) ω| ^ p ∂P
      ≤ M * dist u v ^ q := by
  refine (hbound (boxClamp a b hab u) (boxClamp_mem a b hab u) (boxClamp a b hab v) (boxClamp_mem a b hab v)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow dist_nonneg (LatticeProb.dist_boxClamp_le a b hab u v) hq) hM
/-- On the good event, the modulus of the continuous process at the level-`m`
dyadic scale: two points of the box `[-m, m]^k` within `2^{-m}` in every
coordinate differ by at most the dyadic tail plus one level increment. -/
theorem LatticeProb.modulus_on_grid {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : Continuous f)
    {r : ℕ → ℝ} {n₀ : ℕ} (hb : DyadicIncBoundPi f r n₀) (ha : ∀ n, 0 ≤ r n)
    (hsum : Summable r) {m : ℕ} (hm : n₀ ≤ m) {s t : Fin k → ℝ}
    (hs : ∀ i, |s i| ≤ (m : ℝ)) (ht : ∀ i, |t i| ≤ (m : ℝ))
    (hst : ∀ i, |t i - s i| ≤ 1 / 2 ^ m) :
    |f t - f s| ≤ 2 * ((k : ℝ) * dtail r m) + (k : ℝ) * r m := by
  rw [← LatticeProb.dlimPi_eq_of_continuous hf t, ← LatticeProb.dlimPi_eq_of_continuous hf s]
  exact LatticeProb.dlimPi_dist_le hb ha hsum hm hs ht hst
/-- The union of the dyadic bad events from level `N` on has probability at
most the tail of the geometric series of moment bounds. -/
theorem LatticeProb.measure_union_badSetPi_le {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : (Fin k → ℝ) → Ω → ℝ}
    (_hmeas : ∀ n j, Measurable (fun ω => X (gridPt n j) ω))
    {p q M c : ℝ} (hp : 0 < p) (hM : 0 ≤ M) (hc : 0 < c)
    (hint : ∀ u v, Integrable (fun ω => |X u ω - X v ω| ^ p) P)
    (hbound : ∀ u v, ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q)
    (N : ℕ) :
    P (⋃ n ∈ Set.Ici N, badSetPi X (fun n => c ^ n) (n + 1) n)
      ≤ ∑' j : ℕ, ENNReal.ofReal
        (M * (k : ℝ) * 3 ^ k * (((j + N : ℕ) : ℝ) + 1) ^ k * ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ (j + N)) := by
  refine (measure_mono ?_).trans (measure_iUnion_le (fun j : ℕ => badSetPi X (fun n => c ^ n) ((j + N) + 1) (j + N))) |>.trans ?_
  · intro ω hω
    simp only [Set.mem_iUnion, Set.mem_Ici] at hω ⊢
    obtain ⟨n, hn, hbad⟩ := hω
    exact ⟨n - N, by rw [Nat.sub_add_cancel hn]; exact hbad⟩
  · apply ENNReal.tsum_le_tsum
    intro j
    have h := LatticeProb.measure_badSetPi_le_geometric P hp hM hc hint hbound (j + N)
    push_cast at h ⊢
    exact h
/-- On the complement of the dyadic bad events from level `N` on, the clamped
process obeys the modulus `2^{-N}`: two points of the box within `2^{-N}` in
the sup metric differ by at most the dyadic tail bound. -/
theorem LatticeProb.modulus_good_event {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {Ω : Type} [MeasurableSpace Ω] {X : (Fin k → ℝ) → Ω → ℝ}
    (hcont : ∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b))
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hsum : Summable r) {N : ℕ}
    {ω : Ω} (hgood : ∀ n, N ≤ n → ω ∉ badSetPi (fun u => X (boxClamp a b hab u)) r (n + 1) n)
    {u v : Fin k → ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
    (huN : ∀ i, |u i| ≤ (N : ℝ)) (hvN : ∀ i, |v i| ≤ (N : ℝ))
    (hdist : dist u v < 1 / 2 ^ N) :
    |X u ω - X v ω| ≤ 2 * ((k : ℝ) * dtail r N) + (k : ℝ) * r N := by
  set Y : (Fin k → ℝ) → Ω → ℝ := fun u => X (boxClamp a b hab u) with hY
  set f : (Fin k → ℝ) → ℝ := fun t => Y t ω with hf
  have hb : DyadicIncBoundPi f r N := dyadicIncBoundPi_of_notMem hgood
  have hfc : Continuous f := by
    have h1 : Continuous (boxClamp a b hab) := continuous_boxClamp a b hab
    have h2 : ContinuousOn (fun t => X t ω) (Set.Icc a b) := hcont ω
    have h3 : ∀ t, boxClamp a b hab t ∈ Set.Icc a b := boxClamp_mem a b hab
    exact h2.comp_continuous h1 h3
  have hu' : f u = X u ω := by
    have hc : boxClamp a b hab u = u := boxClamp_eq hab hu
    simp [hf, hY, hc]
  have hv' : f v = X v ω := by
    have hc : boxClamp a b hab v = v := boxClamp_eq hab hv
    simp [hf, hY, hc]
  have hst : ∀ i, |v i - u i| ≤ 1 / 2 ^ N := by
    intro i
    have hlt : dist (u i) (v i) < 1 / 2 ^ N := (dist_pi_lt_iff (by positivity)).mp hdist i
    rw [Real.dist_eq, abs_sub_comm] at hlt
    exact le_of_lt hlt
  rw [← hu', ← hv', ← dlimPi_eq_of_continuous hfc u, ← dlimPi_eq_of_continuous hfc v]
  rw [abs_sub_comm]
  apply dlimPi_dist_le hb (fun n => (hr n).le) hsum le_rfl
  · exact huN
  · exact hvN
  · exact hst

/-- The modulus event is contained in the union of the dyadic bad events from
level `N` on: on the complement the deterministic modulus bound holds and
contradicts `η < |X u ω - X v ω|`. -/
theorem LatticeProb.event_subset_badSetPi {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {Ω : Type} [MeasurableSpace Ω] {X : (Fin k → ℝ) → Ω → ℝ}
    (hcont : ∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {R N : ℕ} (hN : R ≤ N)
    (hR : ∀ u ∈ Set.Icc a b, ∀ i, |u i| ≤ (R : ℝ))
    {η : ℝ} (hmod : 2 * ((k : ℝ) * dtail (fun n => c ^ n) N) + (k : ℝ) * c ^ N < η) :
    {ω : Ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        dist u v < 1 / 2 ^ N ∧ η < |X u ω - X v ω|}
      ⊆ ⋃ n ∈ Set.Ici N, badSetPi (fun u => X (boxClamp a b hab u)) (fun n => c ^ n) (n + 1) n := by
  intro ω hω
  by_contra hgood
  have hgood' : ∀ n, N ≤ n →
      ω ∉ badSetPi (fun u => X (boxClamp a b hab u)) (fun n => c ^ n) (n + 1) n :=
    fun n hn hmem => hgood (Set.mem_iUnion₂.mpr ⟨n, hn, hmem⟩)
  obtain ⟨u, hu, v, hv, hdist, hlt⟩ := hω
  have hsum : Summable (fun n => c ^ n) := summable_geometric_of_abs_lt_one (by rw [abs_of_pos hc]; linarith)
  have hb := modulus_good_event hab hcont (fun n => pow_pos hc n) hsum hgood' hu hv
    (fun i => (hR u hu i).trans (Nat.cast_le.2 hN))
    (fun i => (hR v hv i).trans (Nat.cast_le.2 hN)) hdist
  linarith


/-- **Kolmogorov's modulus theorem on a box** (quantitative form). -/
theorem LatticeProb.kolmogorovModulusPi :
  ∀ (k : ℕ) (a b : Fin k → ℝ) (p q M : ℝ), 0 < p → (k : ℝ) < q →
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            MeasureTheory.Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < δ ∧ η < |X u ω - X v ω|}
            ≤ ENNReal.ofReal ε := by
  intro k a b p q M hp hq ε η hε hη
  set M' : ℝ := max M 0 with hM'
  have hMM' : M ≤ M' := by rw [hM']; exact le_max_left _ _
  have hq0 : 0 ≤ q := (Nat.cast_nonneg k).trans hq.le
  have hM'0 : 0 ≤ M' := le_max_right _ _
  by_cases hab : a ≤ b
  · obtain ⟨c, hc0, hc1, hθ⟩ := exists_incr_exponent_pi k hp hq
    have hrsum : Summable (fun n => c ^ n) :=
      summable_geometric_of_abs_lt_one (by rw [abs_of_pos hc0]; linarith)
    have hθ0 : 0 < (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p := by positivity
    have hgsum : Summable (fun n : ℕ => M' * (k : ℝ) * 3 ^ k * ((n : ℝ) + 1) ^ k *
        ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n) :=
      summable_polynomial_geometric k hθ0 hθ
    have hg0 : ∀ n : ℕ, 0 ≤ M' * (k : ℝ) * 3 ^ k * ((n : ℝ) + 1) ^ k *
        ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n := fun n => by positivity
    set S : ℝ := ∑ i : Fin k, ((|a i| + |b i| : ℝ)) with hS
    have hSpos : 0 ≤ S := by rw [hS]; positivity
    set R : ℕ := Nat.ceil S + 1 with hR
    have hRbound : ∀ u ∈ Set.Icc a b, ∀ i, |u i| ≤ (R : ℝ) := by
      intro u hu i
      have hai : a i ≤ u i := hu.1 i
      have hbi : u i ≤ b i := hu.2 i
      have h1 : |u i| ≤ |a i| + |b i| := by
        rcases le_or_gt 0 (u i) with h | h
        · rw [abs_of_nonneg h]
          calc u i ≤ |b i| := hbi.trans (le_abs_self _)
            _ ≤ |a i| + |b i| := le_add_of_nonneg_left (abs_nonneg _)
        · rw [abs_of_neg h]
          calc -u i ≤ -a i := neg_le_neg hai
            _ ≤ |a i| := by rw [← abs_neg (a i)]; exact le_abs_self (-a i)
            _ ≤ |a i| + |b i| := le_add_of_nonneg_right (abs_nonneg _)
      have h2 : |a i| + |b i| ≤ S := by
        rw [hS]
        exact Finset.single_le_sum (f := fun i' => |a i'| + |b i'|) (fun i' _ => by positivity)
          (Finset.mem_univ i)
      have h3 : S ≤ (Nat.ceil S : ℝ) := Nat.le_ceil S
      have h4 : (Nat.ceil S : ℝ) < (R : ℝ) := by rw [hR]; exact_mod_cast Nat.lt_succ_self _
      exact h1.trans (h2.trans (h3.trans h4.le))
    obtain ⟨N, hNR, hmod, htail⟩ := exists_level_of_summable k (R + 1) hrsum hgsum hg0 hε hη
    refine ⟨1 / 2 ^ N, by positivity, ?_⟩
    intro Ω _ P hP X hmeas hint hbound hcont
    have hintY : ∀ u v, Integrable (fun ω =>
        |X (boxClamp a b hab u) ω - X (boxClamp a b hab v) ω| ^ p) P :=
      fun u v => hint (boxClamp a b hab u) (boxClamp_mem a b hab u)
        (boxClamp a b hab v) (boxClamp_mem a b hab v)
    have hboundY : ∀ u v, ∫ ω, |X (boxClamp a b hab u) ω - X (boxClamp a b hab v) ω| ^ p ∂P
        ≤ M' * dist u v ^ q := by
      intro u v
      calc ∫ ω, |X (boxClamp a b hab u) ω - X (boxClamp a b hab v) ω| ^ p ∂P
          ≤ M * dist (boxClamp a b hab u) (boxClamp a b hab v) ^ q :=
            hbound (boxClamp a b hab u) (boxClamp_mem a b hab u)
              (boxClamp a b hab v) (boxClamp_mem a b hab v)
        _ ≤ M' * dist (boxClamp a b hab u) (boxClamp a b hab v) ^ q :=
            mul_le_mul_of_nonneg_right hMM' (Real.rpow_nonneg dist_nonneg _)
        _ ≤ M' * dist u v ^ q :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow dist_nonneg (LatticeProb.dist_boxClamp_le a b hab u v) hq0) hM'0
    have hRbound' : ∀ u ∈ Set.Icc a b, ∀ i, |u i| ≤ ((R + 1 : ℕ) : ℝ) :=
      fun u hu i => (hRbound u hu i).trans (by exact_mod_cast Nat.le_succ R)
    have hsub := event_subset_badSetPi hab hcont hc0 hc1 hNR hRbound' hmod
    have hmeasY : ∀ n j, Measurable (fun ω => X (boxClamp a b hab (gridPt n j)) ω) :=
      fun n j => hmeas _
    calc P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
          dist u v < 1 / 2 ^ N ∧ η < |X u ω - X v ω|}
        ≤ P (⋃ n ∈ Set.Ici N, badSetPi (fun u => X (boxClamp a b hab u)) (fun n => c ^ n) (n + 1) n) :=
          measure_mono hsub
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (M' * (k : ℝ) * 3 ^ k * (((j + N : ℕ) : ℝ) + 1) ^ k *
          ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ (j + N)) :=
          measure_union_badSetPi_le P hmeasY hp (by positivity) hc0 hintY hboundY N
      _ ≤ ENNReal.ofReal ε := htail
  · refine ⟨1, one_pos, ?_⟩
    intro Ω _ P hP X hmeas hint hbound hcont
    have hnot : ∃ i, b i < a i := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      exact hab hc
    obtain ⟨i, hi⟩ := hnot
    have hempty : Set.Icc a b = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hai := hu.1 i
      have hbi := hu.2 i
      exact absurd hai (not_le.mpr (by linarith))
    have hev : {ω : Ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        dist u v < 1 ∧ η < |X u ω - X v ω|} = ∅ := by
      simp [hempty]
    rw [hev]
    simp

/-- If the box is empty (`¬ a ≤ b` in the pointwise order on `Fin k → ℝ`),
the modulus event is empty. -/
theorem LatticeProb.modulus_event_eq_empty {k : ℕ} {a b : Fin k → ℝ} (hab : ¬ a ≤ b)
    {Ω : Type} [MeasurableSpace Ω] (X : (Fin k → ℝ) → Ω → ℝ) (δ η : ℝ) :
    {ω : Ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        dist u v < δ ∧ η < |X u ω - X v ω|} = ∅ := by
  obtain ⟨i, hi⟩ := not_forall.mp hab
  have hi : b i < a i := not_le.mp hi
  have hempty : Set.Icc a b = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun u hu =>
      absurd (hu.1 i) (not_le.mpr ((hu.right i).trans_lt hi))
  simp [hempty]

/-- Every point of the box `Icc a b` is bounded coordinatewise by the natural
radius `R = ⌈∑ i, |a i| + |b i|⌉ + 1`. -/
theorem LatticeProb.abs_le_box_radius {k : ℕ} {a b : Fin k → ℝ} (u : Fin k → ℝ)
    (hu : u ∈ Set.Icc a b) (i : Fin k) :
    |u i| ≤ ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) + 1 := by
  have hai : a i ≤ u i := hu.1 i
  have hbi : u i ≤ b i := hu.2 i
  have h1 : |u i| ≤ |a i| + |b i| := by
    rw [abs_le]
    constructor
    · have hnaa : -a i ≤ |a i| := by
        rw [← abs_neg (a i)]
        exact le_abs_self (-a i)
      have hnb : -(|a i| + |b i|) ≤ -|a i| := by
        have : |b i| ≥ 0 := abs_nonneg (b i)
        linarith
      have hna2 : -|a i| ≤ a i := by
        have : |a i| ≥ -a i := by rw [← abs_neg (a i)]; exact le_abs_self (-a i)
        linarith
      linarith
    · have hbb : b i ≤ |b i| := le_abs_self (b i)
      have haa : |a i| ≥ 0 := abs_nonneg (a i)
      linarith
  have h2 : |a i| + |b i| ≤ ∑ j : Fin k, ((|a j| + |b j| : ℝ)) :=
    Finset.single_le_sum (f := fun j => |a j| + |b j|) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : ∑ j : Fin k, ((|a j| + |b j| : ℝ)) ≤ ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) :=
    Nat.le_ceil _
  have h4 : ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) <
      ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) + 1 := by linarith
  calc |u i| ≤ |a i| + |b i| := h1
    _ ≤ ∑ j : Fin k, ((|a j| + |b j| : ℝ)) := h2
    _ ≤ ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) := h3
    _ ≤ ((Nat.ceil (∑ j : Fin k, ((|a j| + |b j| : ℝ)))) : ℝ) + 1 := le_of_lt h4

/-- Markov's inequality at exponent `p` for a real integral: the tail
probability of `|f|` beyond `t` is at most the `p`-th moment divided by
`t ^ p`. -/
theorem LatticeProb.measure_lt_le_of_integral_le {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p t M : ℝ} (hp : 0 < p) (ht : 0 < t)
    {f : Ω → ℝ} (hint : Integrable (fun ω => |f ω| ^ p) P)
    (hbound : ∫ ω, |f ω| ^ p ∂P ≤ M) :
    P {ω | t < |f ω|} ≤ ENNReal.ofReal (M / t ^ p) := by
  have htp : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|f ω| ^ p)) P :=
    AEMeasurable.ennreal_ofReal (hint.aemeasurable)
  have hset : {ω | t < |f ω|} ⊆ {ω | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|f ω| ^ p)} :=
    fun ω h => ENNReal.ofReal_le_ofReal (Real.rpow_lt_rpow ht.le h hp).le
  refine (measure_mono hset).trans ?_
  have hdiv := meas_ge_le_lintegral_div hmeas
    (fun h0 => absurd ((ofReal_eq_zero).mp h0) (not_le.mpr htp)) (fun htop => absurd htop ENNReal.ofReal_ne_top)
  refine hdiv.trans ?_
  have hint' : Integrable (fun ω => |f ω| ^ p) P := hint
  have hae : 0 ≤ᵐ[P] (fun ω => |f ω| ^ p) := by
    filter_upwards with ω
    exact Real.rpow_nonneg (abs_nonneg (f ω)) p
  have hlint := ofReal_integral_eq_lintegral_ofReal hint' hae
  have hinteg : ENNReal.ofReal (∫ ω, |f ω| ^ p ∂P) ≤ ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal hbound
  rw [← hlint]
  have hfin : ENNReal.ofReal (∫ ω, |f ω| ^ p ∂P) / ENNReal.ofReal (t ^ p) ≤
      ENNReal.ofReal M / ENNReal.ofReal (t ^ p) :=
    ENNReal.div_le_div_right hinteg _
  refine hfin.trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos htp]

/-- If `t` dominates the `p`-th root of `2 * M / ε` then `t ^ p` dominates `2 * M / ε`. -/
theorem LatticeProb.rpow_root_le_pow {M ε p t : ℝ} (hp : 0 < p) (hε : 0 < ε) (hM : 0 ≤ M)
    (ht : (2 * M / ε) ^ (1 / p) ≤ t) : 2 * M / ε ≤ t ^ p := by
  have h2 : 0 ≤ 2 * M / ε := by positivity
  have hinv : 0 < 1 / p := by positivity
  have hroot : 0 ≤ (2 * M / ε) ^ (1 / p) := Real.rpow_nonneg h2 _
  have ht0 : 0 ≤ t := hroot.trans ht
  have hkey : ((2 * M / ε) ^ (1 / p)) ^ p = 2 * M / ε := by
    rw [← Real.rpow_mul h2, one_div_mul_cancel hp.ne', Real.rpow_one]
  have hmono : ((2 * M / ε) ^ (1 / p)) ^ p ≤ t ^ p :=
    Real.rpow_le_rpow hroot ht hp.le
  exact hkey ▸ hmono

/-- If `N` exceeds `D / δ` then `D / N < δ`. -/
theorem LatticeProb.div_lt_of_div_lt {D δ : ℝ} (_hD : 0 ≤ D) {N : ℕ} (hN : 0 < N) (hδ : 0 < δ)
    (hND : D / δ < N) : D / N < δ := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : D < N * δ := (div_lt_iff₀ hδ).mp hND
  rw [div_lt_iff₀ hN']
  linarith

/-- If `f` is bounded by `t` at `a` and its modulus on the box is at most `1` at distance
`< δ`, then `f` is bounded by `t + N` everywhere on the box, provided the box is convex
and `N` steps of the segment from `a` to `u` are `δ`-short. -/
theorem LatticeProb.abs_le_of_modulus_and_bound {k : ℕ} (a b : Fin k → ℝ) {X : (Fin k → ℝ) → ℝ} {t δ : ℝ} {N : ℕ}
    (hN : 0 < N) (_hδ : 0 < δ) (hstep : dist a b / N < δ)
    (hmod : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, dist s r < δ → |X s - X r| ≤ 1)
    (ha : |X a| ≤ t) (u : Fin k → ℝ) (hu : u ∈ Set.Icc a b) :
    |X u| ≤ t + N := by
  have hnn : 0 ≤ dist a b := dist_nonneg
  have h1 : dist a u ≤ dist a b := by
    rw [dist_pi_le_iff hnn]
    intro i
    have hle1 : a i ≤ u i := hu.1 i
    have hle2 : u i ≤ b i := hu.2 i
    have hle3 : dist (a i) (u i) ≤ dist (a i) (b i) := by
      rw [Real.dist_eq, Real.dist_eq]
      have habs1 : |a i - u i| ≤ |a i - b i| := by
        rw [abs_le]
        have habs1 : |a i - b i| ≥ a i - b i := le_abs_self (a i - b i)
        have habs2 : |a i - b i| ≥ b i - a i := by
          rw [← abs_sub_comm (b i) (a i)]
          exact le_abs_self (b i - a i)
        constructor
        · linarith
        · linarith
      exact habs1
    have hkey : dist (a i) (b i) ≤ dist a b := by
      have h1' : dist (a i) (b i) = ‖(a - b) i‖ := by
        show |a i - b i| = ‖a i - b i‖
        rfl
      have h2' : dist a b = ‖a - b‖ := rfl
      rw [h1', h2']
      exact norm_le_pi_norm (a - b) i
    exact hle3.trans hkey
  have h3 : (0:ℝ) < N := by exact_mod_cast hN
  have hstep_u : dist a u / (N : ℝ) < δ := by
    have h2 : dist a u / (N : ℝ) ≤ dist a b / (N : ℝ) := by
      exact (div_le_div_iff_of_pos_right h3).mpr h1
    have h4 : dist a b / (N : ℝ) < δ := hstep
    exact h2.trans_lt h4
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have ha : a ∈ Set.Icc a b := ⟨fun i => le_rfl, fun i => (hu.1 i).trans (hu.2 i)⟩
  have hchain := LatticeProb.abs_sub_le_of_modulus_on_convex hconv ha hu hN hstep_u hmod
  have htri : |X u| ≤ |X u - X a| + |X a| := by
    have habs : |X u| = |(X u - X a) + X a| := by rw [sub_add_cancel]
    rw [habs]
    exact abs_add_le (X u - X a) (X a)
  calc |X u| ≤ |X u - X a| + |X a| := htri
    _ ≤ (N : ℝ) + t := by linarith
    _ = t + (N:ℝ) := add_comm _ _

/-- In the sup metric on `Fin k → ℝ`, every point of the box `Icc a b` is at distance at
most `dist a b` from `a`. -/
theorem LatticeProb.dist_le_dist_of_mem_Icc {k : ℕ} (a b u : Fin k → ℝ) (hu : u ∈ Set.Icc a b) :
    dist a u ≤ dist a b := by
  have hnn : 0 ≤ dist a b := dist_nonneg
  rw [dist_pi_le_iff hnn]
  intro i
  have hle1 : a i ≤ u i := hu.1 i
  have hle2 : u i ≤ b i := hu.2 i
  have hle3 : dist (a i) (u i) ≤ dist (a i) (b i) := by
    rw [Real.dist_eq, Real.dist_eq]
    have habs1 : |a i - u i| ≤ |a i - b i| := by
      rw [abs_le]
      have habs1 : |a i - b i| ≥ a i - b i := le_abs_self (a i - b i)
      have habs2 : |a i - b i| ≥ b i - a i := by
        rw [← abs_sub_comm (b i) (a i)]
        exact le_abs_self (b i - a i)
      constructor
      · linarith
      · linarith
    exact habs1
  have hkey : dist (a i) (b i) ≤ dist a b := by
    have h1 : dist (a i) (b i) = ‖(a - b) i‖ := by
      show |a i - b i| = ‖a i - b i‖
      rfl
    have h2 : dist a b = ‖a - b‖ := rfl
    rw [h1, h2]
    exact norm_le_pi_norm (a - b) i
  exact hle3.trans hkey

/-- **Kolmogorov's boundedness theorem on a box** (quantitative form): under the
Kolmogorov–Chentsov moment and continuity hypotheses, the process is uniformly
bounded on the box outside an event of probability at most `ε`, with an explicit
bound `B` depending only on the parameters. -/
theorem LatticeProb.kolmogorovBoundPi :
  ∀ (k : ℕ) (a b : Fin k → ℝ) (p q M : ℝ), 0 < p → (k : ℝ) < q →
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            MeasureTheory.Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) →
          MeasureTheory.Integrable (fun ω => |X a ω| ^ p) P →
          (∫ ω, |X a ω| ^ p ∂P ≤ M) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, B < |X u ω|} ≤ ENNReal.ofReal ε := by
  intro k a b p q M hp hq ε hε
  by_cases hab : a ≤ b
  · set M' : ℝ := max M 0 with hM'
    have hMM' : M ≤ M' := by rw [hM']; exact le_max_left _ _
    have hM'0 : 0 ≤ M' := le_max_right _ _
    -- modulus at accuracy ε/2, threshold 1
    obtain ⟨δ, hδ0, hmod⟩ := kolmogorovModulusPi k a b p q M hp hq (ε / 2) 1
      (by linarith) one_pos
    -- Markov threshold t
    set t : ℝ := (2 * M' / ε) ^ (1 / p) + 1 with ht1
    have hroot0 : 0 ≤ (2 * M' / ε) ^ (1 / p) := Real.rpow_nonneg (by positivity) _
    have ht0 : 0 < t := by rw [ht1]; linarith
    have htp : 2 * M' / ε ≤ t ^ p :=
      rpow_root_le_pow hp hε hM'0 (by rw [ht1]; exact le_add_of_nonneg_right zero_le_one)
    -- number of chaining steps N
    set N : ℕ := Nat.ceil (dist a b / δ) + 1 with hN1
    have hN0 : 0 < N := Nat.succ_pos _
    have hND : dist a b / δ < N := by
      have h1 : dist a b / δ ≤ Nat.ceil (dist a b / δ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (dist a b / δ) : ℕ) : ℝ) = Nat.ceil (dist a b / δ) := rfl
      rw [hN1]
      have h3 : ((Nat.ceil (dist a b / δ) : ℕ) : ℝ) < N := by
        exact_mod_cast Nat.lt_succ_self _
      linarith
    have hstep : dist a b / (N : ℝ) < δ := div_lt_of_div_lt dist_nonneg hN0 hδ0 hND
    refine ⟨t + N, ?_⟩
    intro Ω _ P hP X hmeas hint hbound hinta hinta' hcont
    -- the two bad events
    set E1 : Set Ω := {ω | t < |X a ω|} with hE1
    set E2 : Set Ω := {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
      dist u v < δ ∧ 1 < |X u ω - X v ω|} with hE2
    have hE2le : P E2 ≤ ENNReal.ofReal (ε / 2) :=
      hmod P hP X hmeas hint hbound hcont
    have hE1le : P E1 ≤ ENNReal.ofReal (M' / t ^ p) :=
      measure_lt_le_of_integral_le P hp ht0 hinta (hinta'.trans hMM')
    have hE1le' : P E1 ≤ ENNReal.ofReal (ε / 2) := by
      refine hE1le.trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos ht0 p
      have h1 : 2 * M' ≤ ε * t ^ p := by
        rw [mul_comm ε, ← div_le_iff₀ hε]
        exact htp
      rw [div_le_iff₀ h2]
      linarith
    -- containment
    have hsub : {ω | ∃ u ∈ Set.Icc a b, t + N < |X u ω|} ⊆ E1 ∪ E2 := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨hcon1, hcon2⟩ := hcon
      obtain ⟨u, hu, hbu⟩ := hω
      have hnota : ¬ t < |X a ω| := by
        intro h
        exact hcon1 h
      have hnotm : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, dist s r < δ → |X s ω - X r ω| ≤ 1 := by
        intro s hs r hr hsr
        by_contra hgt
        exact hcon2 ⟨s, hs, r, hr, hsr, Std.not_le.mp hgt⟩
      have hK10 := abs_le_of_modulus_and_bound (a := a) (b := b) (X := fun u => X u ω) hN0 hδ0 hstep hnotm (Std.not_lt.mp hnota) u hu
      linarith
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le E1 E2).trans ?_
    have hsum : P E1 + P E2 ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add hE1le' hE2le
    have h2 : (0:ℝ) ≤ ε / 2 := by linarith
    have heq : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add h2 h2, add_halves]
    exact hsum.trans_eq heq
  · -- empty box: the event is empty
    obtain ⟨i, hi⟩ := not_forall.mp hab
    have hi : b i < a i := not_le.mp hi
    have hempty : Set.Icc a b = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun u hu =>
        absurd (hu.1 i) (not_le.mpr ((hu.right i).trans_lt hi))
    refine ⟨0, ?_⟩
    intro Ω _ P hP X hmeas hint hbound hinta hinta' hcont
    have hset : {ω | ∃ u ∈ Set.Icc a b, (0:ℝ) < |X u ω|} = ∅ := by
      rw [hempty]
      simp
    rw [hset]
    simp

