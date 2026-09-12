/-
Towards the multi-parameter Kolmogorov-Chentsov theorem: the passage from the
Kolmogorov condition over `Fin k → ℝ` to the dyadic bad events, and the
continuity of the chained limit.

The Kolmogorov condition is stated with a lower integral of `edist ^ p`.  The
quantitative theorems of `KolmogorovPi` and `KolmogorovBound` are stated with a
Bochner integral of `|X u - X v| ^ p` together with its integrability, which is
the form the moment estimates of the applications come in.  The two are related
here: a Kolmogorov process has integrable `p`-th moments of its increments, with
the Bochner integral bounded by the same constant, because the lower integral
bound is finite.  With that, the level-`n` bad events of the dyadic grid have
summable probabilities, Borel-Cantelli makes the increment bounds hold from some
level on almost surely, and the chained limit `dlimPi` is continuous.
-/
import LatticeProb.Prob.Chentsov
import LatticeProb.Prob.KolmogorovBound

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

/-- The dyadic truncation of a point of `Fin k → ℝ` is within `2 ^ (-n)` of it
in the sup metric. -/
theorem LatticeProb.edist_dtruncPi_le {k : ℕ} (n : ℕ) (z : Fin k → ℝ) :
    edist (dtruncPi n z) z ≤ ENNReal.ofReal (1 / 2 ^ n) := by
  rw [edist_pi_def]
  refine Finset.sup_le fun i _ => ?_
  have h1 : dtruncPi n z i ≤ z i := dtruncPi_le n z i
  have h2 : z i - dtruncPi n z i < 1 / 2 ^ n := sub_dtruncPi_lt n z i
  rw [edist_dist, Real.dist_eq, abs_of_nonpos (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Chebyshev for a Kolmogorov process over an arbitrary index space. -/
theorem LatticeProb.measure_edist_ge_le_gen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p q : ℝ} {M : ℝ≥0} {T : Type*} [PseudoEMetricSpace T] {Y : T → Ω → ℝ}
    (hY : IsKolmogorovProcess Y P p q M) (u v : T) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    P {ω | ε ≤ edist (Y u ω) (Y v ω)} ≤ M * edist u v ^ q / ε ^ p := by
  have hp := hY.p_pos
  have hεp0 : ε ^ p ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hε, hε', hp, not_lt.2 hp.le]
  have hεptop : ε ^ p ≠ ∞ := by
    simp [ENNReal.rpow_eq_top_iff, hε, hε', not_lt.2 hp.le, hp]
  have hsub : {ω | ε ≤ edist (Y u ω) (Y v ω)}
      ⊆ {ω | ε ^ p ≤ edist (Y u ω) (Y v ω) ^ p} := fun ω hω =>
    ENNReal.rpow_le_rpow hω hp.le
  calc P {ω | ε ≤ edist (Y u ω) (Y v ω)}
      ≤ P {ω | ε ^ p ≤ edist (Y u ω) (Y v ω) ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, edist (Y u ω) (Y v ω) ^ p ∂P) / ε ^ p :=
        meas_ge_le_lintegral_div (hY.measurable_edist.aemeasurable.pow_const _) hεp0 hεptop
    _ ≤ M * edist u v ^ q / ε ^ p := by gcongr; exact hY.kolmogorovCondition u v

/-- The increments of a Kolmogorov process have integrable `p`-th moments: the
Kolmogorov condition bounds their lower integral by a finite quantity. -/
theorem LatticeProb.integrable_abs_sub_rpow_of_isKolmogorovProcess {k : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {p q : ℝ} {M : ℝ≥0} {X : (Fin k → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (u v : Fin k → ℝ) :
    Integrable (fun ω => |X u ω - X v ω| ^ p) P := by
  have hp := hX.p_pos
  have hq := hX.q_pos
  have hmeas : Measurable fun ω => |X u ω - X v ω| ^ p :=
    ((hX.measurable u).sub (hX.measurable v)).abs.pow_const p
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpt : ∀ ω, ‖|X u ω - X v ω| ^ p‖ₑ = edist (X u ω) (X v ω) ^ p := by
    intro ω
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (abs_nonneg _) p),
      ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le, edist_dist, Real.dist_eq]
  have hfin : (M : ℝ≥0∞) * edist u v ^ q ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hq.le (edist_ne_top u v))
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ ω, ‖|X u ω - X v ω| ^ p‖ₑ ∂P
      = ∫⁻ ω, edist (X u ω) (X v ω) ^ p ∂P := by simp_rw [hpt]
    _ ≤ (M : ℝ≥0∞) * edist u v ^ q := hX.kolmogorovCondition u v
    _ < ⊤ := hfin.lt_top

/-- The Bochner form of the Kolmogorov condition over a finite product. -/
theorem LatticeProb.integral_abs_sub_rpow_le_of_isKolmogorovProcess {k : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {p q : ℝ} {M : ℝ≥0} {X : (Fin k → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (u v : Fin k → ℝ) :
    ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ (M : ℝ) * dist u v ^ q := by
  have hp := hX.p_pos
  have hq := hX.q_pos
  have hmeas : Measurable fun ω => |X u ω - X v ω| ^ p :=
    ((hX.measurable u).sub (hX.measurable v)).abs.pow_const p
  have hnn : 0 ≤ᵐ[P] fun ω => |X u ω - X v ω| ^ p :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p
  have hpt : ∀ ω, ENNReal.ofReal (|X u ω - X v ω| ^ p) = edist (X u ω) (X v ω) ^ p := by
    intro ω
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le, edist_dist, Real.dist_eq]
  have hle : ∫⁻ ω, ENNReal.ofReal (|X u ω - X v ω| ^ p) ∂P
      ≤ (M : ℝ≥0∞) * edist u v ^ q := by
    simp_rw [hpt]
    exact hX.kolmogorovCondition u v
  have hfin : (M : ℝ≥0∞) * edist u v ^ q ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hq.le (edist_ne_top u v))
  have hmq : (0:ℝ) ≤ (M : ℝ) * dist u v ^ q := by positivity
  have heq : ((M : ℝ≥0∞) * edist u v ^ q).toReal = (M : ℝ) * dist u v ^ q := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal hmq]
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (|X u ω - X v ω| ^ p) ∂P).toReal
      ≤ ((M : ℝ≥0∞) * edist u v ^ q).toReal := ENNReal.toReal_mono hfin hle
    _ = (M : ℝ) * dist u v ^ q := heq

/-- The probabilities of the level-`n` dyadic bad events are summable when the
geometric ratio of moment factors is below one. -/
theorem LatticeProb.tsum_measure_badSetPi_ne_top {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : (Fin k → ℝ) → Ω → ℝ} {p q M c : ℝ}
    (hp : 0 < p) (hM : 0 ≤ M) (hc : 0 < c)
    (hθ : (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p < 1)
    (hint : ∀ u v, Integrable (fun ω => |X u ω - X v ω| ^ p) P)
    (hbound : ∀ u v, ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) :
    ∑' n : ℕ, P (badSetPi X (fun n => c ^ n) (n + 1) n) ≠ ∞ := by
  have hθ0 : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p := by positivity
  have hle : ∀ n : ℕ, P (badSetPi X (fun n => c ^ n) (n + 1) n)
      ≤ ENNReal.ofReal (M * (k : ℝ) * 3 ^ k * (n + 1 : ℝ) ^ k *
        ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n) :=
    fun n => measure_badSetPi_le_geometric P hp hM hc hint hbound n
  have hgs : Summable (fun n : ℕ => M * (k : ℝ) * 3 ^ k * (n + 1 : ℝ) ^ k *
      ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n) :=
    summable_polynomial_geometric k hθ0 hθ
  have hnn : ∀ n : ℕ, 0 ≤ M * (k : ℝ) * 3 ^ k * (n + 1 : ℝ) ^ k *
      ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ n := by
    intro n
    positivity
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hgs]
  exact ENNReal.ofReal_ne_top

/-- Borel-Cantelli: almost every sample avoids the dyadic bad events from some
level on. -/
theorem LatticeProb.ae_exists_notMem_badSetPi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : (Fin k → ℝ) → Ω → ℝ} {r : ℕ → ℝ}
    (hsum : ∑' n : ℕ, P (badSetPi X r (n + 1) n) ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ω ∉ badSetPi X r (n + 1) n := by
  have hBC : P (limsup (fun n => badSetPi X r (n + 1) n) atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsum
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hBC
  simp only [Set.mem_setOf_eq, not_exists, not_forall] at hω
  rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
  intro n₀
  obtain ⟨n, hn, hmem⟩ := hω n₀
  exact ⟨n, hn, by simpa using hmem⟩

/-- The chained limit of a function with summable dyadic increment bounds is
continuous on all of `Fin k → ℝ`. -/
theorem LatticeProb.continuous_dlimPi {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    Continuous (dlimPi f) := by
  refine continuous_iff_continuousAt.mpr fun z => Metric.continuousAt_iff.mpr fun ε hε => ?_
  have hzero : Tendsto (fun m => 2 * ((k : ℝ) * dtail a m) + (k : ℝ) * a m) atTop (𝓝 0) := by
    have h1 := ((tendsto_dtail a).const_mul ((k : ℝ))).const_mul (2 : ℝ)
    have h2 := hsum.tendsto_atTop_zero.const_mul ((k : ℝ))
    simpa using h1.add h2
  obtain ⟨N, hN⟩ := (hzero.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  set m := max (max n₀ ⌈‖z‖ + 1⌉₊) N with hmdef
  have hm : n₀ ≤ m := le_max_of_le_left (le_max_left _ _)
  have hNm : N ≤ m := le_max_right _ _
  have hzm : ‖z‖ + 1 ≤ (m : ℝ) := le_trans (Nat.le_ceil _)
    (by exact_mod_cast Nat.cast_le.mpr (le_max_of_le_left (le_max_right _ _)))
  have hzn : ∀ i, |z i| ≤ ‖z‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hz : ∀ i, |z i| ≤ (m : ℝ) := fun i => le_trans (hzn i) (by linarith)
  have hhalf : (1 : ℝ) / 2 ^ m ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  refine ⟨1 / 2 ^ m, by positivity, fun {t} hdist => ?_⟩
  have hst : ∀ i, |t i - z i| ≤ 1 / 2 ^ m := by
    intro i
    have h := dist_le_pi_dist t z i
    rw [Real.dist_eq] at h
    linarith
  have ht : ∀ i, |t i| ≤ (m : ℝ) := by
    intro i
    have h1 := hst i
    have h2 := hzn i
    have h3 := abs_sub_abs_le_abs_sub (t i) (z i)
    linarith
  calc dist (dlimPi f t) (dlimPi f z) = |dlimPi f t - dlimPi f z| := Real.dist_eq _ _
    _ ≤ 2 * ((k : ℝ) * dtail a m) + (k : ℝ) * a m := dlimPi_dist_le hb ha hsum hm hz ht hst
    _ < ε := hN m hNm


/-- The dyadic truncations of a Kolmogorov process converge to it in measure. -/
theorem LatticeProb.tendstoInMeasure_dtruncPi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p q : ℝ} {M : ℝ≥0} {X : (Fin k → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (z : Fin k → ℝ) :
    TendstoInMeasure P (fun n ω => X (dtruncPi n z) ω) atTop (X z) := by
  have hp := hX.p_pos
  have hq := hX.q_pos
  refine tendstoInMeasure_of_ne_top fun ε hε hε' => ?_
  set c : ℝ := ((1 : ℝ) / 2) ^ q with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : c < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hq
  have hkern : ∀ n : ℕ, ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q = ENNReal.ofReal (c ^ n) := by
    intro n
    rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
    congr 1
    rw [hcdef, ← rpow_pow_comm (by norm_num) q n, one_div, ← inv_pow, ← one_div]
  have hεp0 : ε ^ p ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hε.ne', hε', hp, not_lt.2 hp.le]
  have hbdd : ∀ n : ℕ, P {ω | ε ≤ edist (X (dtruncPi n z) ω) (X z ω)}
      ≤ ((M : ℝ≥0∞) * (ε ^ p)⁻¹) * ENNReal.ofReal (c ^ n) := by
    intro n
    refine le_trans (measure_edist_ge_le_gen hX _ _ hε.ne' hε') ?_
    have h2 : edist (dtruncPi n z) z ^ q ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q :=
      ENNReal.rpow_le_rpow (edist_dtruncPi_le n z) hq.le
    refine le_trans (ENNReal.div_le_div_right (mul_le_mul_right h2 _) _) ?_
    rw [hkern n, div_eq_mul_inv, mul_right_comm]
  have hK : (M : ℝ≥0∞) * (ε ^ p)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.mpr hεp0)
  have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (c ^ n)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1)
    simpa [Function.comp_def] using this
  have h3 : Tendsto (fun n : ℕ => ((M : ℝ≥0∞) * (ε ^ p)⁻¹) * ENNReal.ofReal (c ^ n))
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => zero_le) hbdd

/-- **The multi-parameter Kolmogorov-Chentsov theorem.**  A process indexed by
`Fin k → ℝ` whose increments satisfy the Kolmogorov condition with exponent
`q > k` has a modification whose sample paths are continuous.  The exponent
condition is `k < q` rather than `1 < q` because the level-`n` dyadic grid of a
box in `k` variables has of the order of `2 ^ (n k)` cells. -/
theorem LatticeProb.exists_continuous_modification_pi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {M : ℝ≥0} {X : (Fin k → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (hq : (k : ℝ) < q) :
    ∃ Y : (Fin k → ℝ) → Ω → ℝ, (∀ z, Measurable (Y z)) ∧ (∀ z, X z =ᵐ[P] Y z) ∧
      ∀ᵐ ω ∂P, Continuous fun z => Y z ω := by
  have hp := hX.p_pos
  obtain ⟨c, hc0, hc1, hθ⟩ := exists_incr_exponent_pi k hp hq
  set r : ℕ → ℝ := fun n => c ^ n with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => pow_pos hc0 n
  have hrsum : Summable r := summable_geometric_of_lt_one hc0.le hc1
  have hint : ∀ u v, Integrable (fun ω => |X u ω - X v ω| ^ p) P :=
    fun u v => integrable_abs_sub_rpow_of_isKolmogorovProcess hX u v
  have hbound : ∀ u v, ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ (M : ℝ) * dist u v ^ q :=
    fun u v => integral_abs_sub_rpow_le_of_isKolmogorovProcess hX u v
  have hsum : ∑' n : ℕ, P (badSetPi X r (n + 1) n) ≠ ∞ :=
    tsum_measure_badSetPi_ne_top P hp M.coe_nonneg hc0 hθ hint hbound
  have hgood := ae_exists_notMem_badSetPi P hsum
  refine ⟨fun z ω => dlimPi (fun u => X u ω) z, fun z => ?_, fun z => ?_, ?_⟩
  · exact Measurable.limsup fun n => hX.measurable (dtruncPi n z)
  · obtain ⟨ns, hns, hns'⟩ := (tendstoInMeasure_dtruncPi hX z).exists_seq_tendsto_ae
    filter_upwards [hgood, hns'] with ω h1 h2
    obtain ⟨n₀, hn₀⟩ := h1
    have hb := dyadicIncBoundPi_of_notMem hn₀
    have hzn : ∀ i, |z i| ≤ ((max n₀ ⌈‖z‖⌉₊ : ℕ) : ℝ) := by
      intro i
      have h1 : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have h2 : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈‖z‖⌉₊ : ℕ) : ℝ) ≤ ((max n₀ ⌈‖z‖⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (le_max_right _ _)
      linarith
    have hlim := tendsto_dtruncPi hb (fun n => (hrpos n).le) hrsum (le_max_left n₀ ⌈‖z‖⌉₊) hzn
    exact tendsto_nhds_unique h2 (hlim.comp hns.tendsto_atTop)
  · filter_upwards [hgood] with ω hω
    obtain ⟨n₀, hn₀⟩ := hω
    exact continuous_dlimPi (dyadicIncBoundPi_of_notMem hn₀) (fun n => (hrpos n).le) hrsum


/-- The sup distance of the space-time coordinates read off a point of
`Fin (d+1) → ℝ` is at most the distance of the points. -/
theorem LatticeProb.edist_prod_cons_le {d : ℕ} (u v : Fin (d + 1) → ℝ) :
    edist ((u 0, fun j : Fin d => u j.succ) : ℝ × (Fin d → ℝ))
      (v 0, fun j : Fin d => v j.succ) ≤ edist u v := by
  rw [Prod.edist_eq]
  refine max_le (edist_le_pi_edist u v 0) ?_
  refine edist_pi_le_iff.2 fun j => ?_
  exact edist_le_pi_edist u v j.succ

/-- Assembling a time and a space coordinate into a point of `Fin (d+1) → ℝ` is
continuous. -/
theorem LatticeProb.continuous_finCons {d : ℕ} :
    Continuous (fun z : ℝ × (Fin d → ℝ) => (Fin.cons z.1 z.2 : Fin (d + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]
    fun_prop
  · intro j
    simp only [Fin.cons_succ]
    fun_prop

/-- **Kolmogorov-Chentsov over a space-time index set.**  A process indexed by
`ℝ × (Fin d → ℝ)` whose increments satisfy the Kolmogorov condition with
exponent `q > d + 1` has a modification whose sample paths are continuous. -/
theorem LatticeProb.exists_continuous_modification_spaceTime {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {M : ℝ≥0}
    {X : ℝ × (Fin d → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (hq : ((d : ℝ) + 1) < q) :
    ∃ Y : ℝ × (Fin d → ℝ) → Ω → ℝ, (∀ z, Measurable (Y z)) ∧ (∀ z, X z =ᵐ[P] Y z) ∧
      ∀ᵐ ω ∂P, Continuous fun z => Y z ω := by
  have hX'K : IsKolmogorovProcess
      (fun u : Fin (d + 1) → ℝ => X (u 0, fun j : Fin d => u j.succ)) P p q M := by
    refine ⟨fun s t => hX.measurablePair _ _, fun s t => ?_, hX.p_pos, hX.q_pos⟩
    refine (hX.kolmogorovCondition _ _).trans ?_
    gcongr
    · exact hX.q_pos.le
    · exact edist_prod_cons_le s t
  have hq' : ((d + 1 : ℕ) : ℝ) < q := by push_cast; linarith
  obtain ⟨Y', hY'meas, hY'mod, hY'cont⟩ := exists_continuous_modification_pi hX'K hq'
  refine ⟨fun z ω => Y' (Fin.cons z.1 z.2) ω, fun z => hY'meas _, fun z => ?_, ?_⟩
  · have h := hY'mod (Fin.cons z.1 z.2)
    have hz : ((Fin.cons z.1 z.2 : Fin (d + 1) → ℝ) 0,
        fun j : Fin d => (Fin.cons z.1 z.2 : Fin (d + 1) → ℝ) j.succ) = z := by
      simp
    rw [hz] at h
    exact h
  · filter_upwards [hY'cont] with ω hω
    exact hω.comp continuous_finCons


/-- The quantitative modulus theorem on a box, with Mathlib's Kolmogorov
condition as the hypothesis: the modulus `δ` is produced from the parameters
alone, before the probability space and the process. -/
theorem LatticeProb.kolmogorovModulusPi_of_kolmogorovProcess (k : ℕ) (a b : Fin k → ℝ)
    (p q : ℝ) (M : ℝ≥0) (hp : 0 < p) (hq : (k : ℝ) < q) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ, IsKolmogorovProcess X P p q M →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < δ ∧ η < |X u ω - X v ω|}
            ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, h⟩ := kolmogorovModulusPi k a b p q (M : ℝ) hp hq ε η hε hη
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P hP X hX hcont
  exact h P hP X hX.measurable
    (fun u _ v _ => integrable_abs_sub_rpow_of_isKolmogorovProcess hX u v)
    (fun u _ v _ => integral_abs_sub_rpow_le_of_isKolmogorovProcess hX u v) hcont


/-- The samples that avoid the dyadic bad events from some level on. -/
def LatticeProb.goodSetPi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : (Fin k → ℝ) → Ω → ℝ) (r : ℕ → ℝ) : Set Ω :=
  ⋃ n₀ : ℕ, ⋂ n, ⋂ _ : n₀ ≤ n, (badSetPi X r (n + 1) n)ᶜ

theorem LatticeProb.mem_goodSetPi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {X : (Fin k → ℝ) → Ω → ℝ} {r : ℕ → ℝ} {ω : Ω} :
    ω ∈ goodSetPi X r ↔ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ω ∉ badSetPi X r (n + 1) n := by
  simp [goodSetPi]

theorem LatticeProb.measurableSet_goodSetPi {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {X : (Fin k → ℝ) → Ω → ℝ} {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (hmeas : ∀ (n : ℕ) (j : Fin k → ℤ), Measurable (fun ω => X (gridPt n j) ω)) :
    MeasurableSet (goodSetPi X r) := by
  refine MeasurableSet.iUnion fun n₀ => MeasurableSet.iInter fun n => ?_
  refine MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_badSetPi hr (n + 1) n (hmeas n)).compl

/-- **Kolmogorov-Chentsov in finite dimension, with every path continuous.**  Setting
the chained limit to zero off the measurable set where the dyadic increment bounds
hold from some level on gives a modification whose every sample path, not merely
almost every one, is continuous. -/
theorem LatticeProb.exists_continuous_modification_pi_all {k : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {M : ℝ≥0}
    {X : (Fin k → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (hq : (k : ℝ) < q) :
    ∃ Y : (Fin k → ℝ) → Ω → ℝ, (∀ z, Measurable (Y z)) ∧ (∀ z, X z =ᵐ[P] Y z) ∧
      ∀ ω, Continuous fun z => Y z ω := by
  classical
  have hp := hX.p_pos
  obtain ⟨c, hc0, hc1, hθ⟩ := exists_incr_exponent_pi k hp hq
  set r : ℕ → ℝ := fun n => c ^ n with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => pow_pos hc0 n
  have hrsum : Summable r := summable_geometric_of_lt_one hc0.le hc1
  have hint : ∀ u v, Integrable (fun ω => |X u ω - X v ω| ^ p) P :=
    fun u v => integrable_abs_sub_rpow_of_isKolmogorovProcess hX u v
  have hbound : ∀ u v, ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ (M : ℝ) * dist u v ^ q :=
    fun u v => integral_abs_sub_rpow_le_of_isKolmogorovProcess hX u v
  have hsum : ∑' n : ℕ, P (badSetPi X r (n + 1) n) ≠ ∞ :=
    tsum_measure_badSetPi_ne_top P hp M.coe_nonneg hc0 hθ hint hbound
  have hgood := ae_exists_notMem_badSetPi P hsum
  have hGmeas : MeasurableSet (goodSetPi X r) :=
    measurableSet_goodSetPi (fun n => (hrpos n).le) (fun n j => hX.measurable _)
  have hGae : ∀ᵐ ω ∂P, ω ∈ goodSetPi X r := by
    filter_upwards [hgood] with ω hω
    exact mem_goodSetPi.mpr hω
  refine ⟨fun z ω => if ω ∈ goodSetPi X r then dlimPi (fun u => X u ω) z else 0,
    fun z => ?_, fun z => ?_, ?_⟩
  · exact Measurable.ite hGmeas (Measurable.limsup fun n => hX.measurable (dtruncPi n z))
      measurable_const
  · obtain ⟨ns, hns, hns'⟩ := (tendstoInMeasure_dtruncPi hX z).exists_seq_tendsto_ae
    filter_upwards [hgood, hGae, hns'] with ω h1 hG h2
    obtain ⟨n₀, hn₀⟩ := h1
    have hb := dyadicIncBoundPi_of_notMem hn₀
    have hzn : ∀ i, |z i| ≤ ((max n₀ ⌈‖z‖⌉₊ : ℕ) : ℝ) := by
      intro i
      have h1 : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have h2 : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈‖z‖⌉₊ : ℕ) : ℝ) ≤ ((max n₀ ⌈‖z‖⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (le_max_right _ _)
      linarith
    have hlim := tendsto_dtruncPi hb (fun n => (hrpos n).le) hrsum (le_max_left n₀ ⌈‖z‖⌉₊) hzn
    have hEq := tendsto_nhds_unique h2 (hlim.comp hns.tendsto_atTop)
    rw [if_pos hG]
    exact hEq
  · intro ω
    by_cases hω : ω ∈ goodSetPi X r
    · simp only [if_pos hω]
      obtain ⟨n₀, hn₀⟩ := mem_goodSetPi.mp hω
      exact continuous_dlimPi (dyadicIncBoundPi_of_notMem hn₀) (fun n => (hrpos n).le) hrsum
    · simp only [if_neg hω]
      exact continuous_const

/-- The space-time form with every path continuous. -/
theorem LatticeProb.exists_continuous_modification_spaceTime_all {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {M : ℝ≥0}
    {X : ℝ × (Fin d → ℝ) → Ω → ℝ}
    (hX : IsKolmogorovProcess X P p q M) (hq : ((d : ℝ) + 1) < q) :
    ∃ Y : ℝ × (Fin d → ℝ) → Ω → ℝ, (∀ z, Measurable (Y z)) ∧ (∀ z, X z =ᵐ[P] Y z) ∧
      ∀ ω, Continuous fun z => Y z ω := by
  have hX'K : IsKolmogorovProcess
      (fun u : Fin (d + 1) → ℝ => X (u 0, fun j : Fin d => u j.succ)) P p q M := by
    refine ⟨fun s t => hX.measurablePair _ _, fun s t => ?_, hX.p_pos, hX.q_pos⟩
    refine (hX.kolmogorovCondition _ _).trans ?_
    gcongr
    · exact hX.q_pos.le
    · exact edist_prod_cons_le s t
  have hq' : ((d + 1 : ℕ) : ℝ) < q := by push_cast; linarith
  obtain ⟨Y', hY'meas, hY'mod, hY'cont⟩ := exists_continuous_modification_pi_all hX'K hq'
  refine ⟨fun z ω => Y' (Fin.cons z.1 z.2) ω, fun z => hY'meas _, fun z => ?_, ?_⟩
  · have h := hY'mod (Fin.cons z.1 z.2)
    have hz : ((Fin.cons z.1 z.2 : Fin (d + 1) → ℝ) 0,
        fun j : Fin d => (Fin.cons z.1 z.2 : Fin (d + 1) → ℝ) j.succ) = z := by
      simp
    rw [hz] at h
    exact h
  · intro ω
    exact (hY'cont ω).comp continuous_finCons

end
