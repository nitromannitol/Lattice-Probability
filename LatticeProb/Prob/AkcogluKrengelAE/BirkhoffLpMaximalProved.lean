/-
# Wiener's one-parameter `Lᵖ` maximal theorem (`LatticeProb.BirkhoffLpMaximal`)

This file proves `BirkhoffLpMaximal`, one of the two named gaps of
`LatticeProb/Prob/AkcogluKrengelAE/BallMaximalLp.lean` (the one-parameter strong `Lᵖ`
maximal / Marcinkiewicz interpolation).

Route:

* the `ℝ≥0∞` layer cake `lintegral_rpow_layer_cake` and the elementary inner integral
  `lintegral_Ioi_cond_rpow_eq`;
* the normalised weak-type `(1,1)` bound for `birkhoffMax` (`birkhoffMax_weakType`), obtained
  from the library's maximal ergodic theorem in its **restricted** form
  (`maximalSet_restricted_le`, extracted from the proof of `maximal_inequality`) by truncating
  `f` and passing to the limit with `birkhoffMax_iSup_min`;
* Tonelli + Hölder + the `ℝ≥0∞` algebra (`marcinkiewicz_abstract`) give the `Lᵖ` bound;
* monotone convergence (`lintegral_iSup`) removes the truncation.

Everything is `sorry`-free; the only axioms are the standard three.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BallMaximalLp

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LatticeProb

noncomputable section

/-! ### Reusable layer-cake helpers (copied verbatim from `wip/MomentsDefs.lean`) -/

/-- The half-line integral of `t ^ (q - 1)` diverges for `q > 0`. -/
theorem lintegral_Ioi_rpow_sub_one_eq_top {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) = ⊤ := by
  by_contra h
  have hmeas : Measurable fun t : ℝ => t ^ (q - 1) := measurable_id.pow_const _
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t : ℝ => t ^ (q - 1) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => Real.rpow_nonneg ht.le _
  have hint : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioi 0) volume :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 h)⟩
  have h1 := (integrableOn_Ioi_rpow_iff (s := q - 1) (t := 1) one_pos).1
    (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  linarith

/-- Layer cake formula for `ℝ≥0∞`-valued functions and an arbitrary measure. -/
theorem lintegral_rpow_layer_cake {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ENNReal} (hX : Measurable X) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, X ω ^ q ∂μ = ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0 : ℝ),
      μ {ω | ENNReal.ofReal t < X ω} * ENNReal.ofReal (t ^ (q - 1)) := by
  by_cases h : μ {ω | X ω = ⊤} = 0
  · have hae : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
      rw [ae_iff]
      simpa using h
    have h1 : ∫⁻ ω, X ω ^ q ∂μ = ∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ q) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le, ENNReal.ofReal_toReal hω]
    rw [h1, lintegral_rpow_eq_lintegral_meas_lt_mul μ
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hX.ennreal_toReal.aemeasurable hq]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hset : μ {a | t < (X a).toReal} = μ {ω | ENNReal.ofReal t < X ω} := by
      refine measure_congr ?_
      filter_upwards [hae] with ω hω
      exact propext (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hω).symm
    rw [hset]
  · have hmeasT : MeasurableSet {ω | X ω = ⊤} := measurableSet_eq_fun hX measurable_const
    have hL : ∫⁻ ω, X ω ^ q ∂μ = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ENNReal) = ⊤ * μ {ω | X ω = ⊤} := (ENNReal.top_mul h).symm
        _ = ∫⁻ ω, {ω | X ω = ⊤}.indicator (fun _ => (⊤ : ENNReal)) ω ∂μ :=
          (lintegral_indicator_const hmeasT ⊤).symm
        _ ≤ ∫⁻ ω, X ω ^ q ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : X ω = ⊤
          · simp [Set.indicator, hω, ENNReal.top_rpow_of_pos hq]
          · simp [Set.indicator, hω]
    have hmeasG : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (q - 1)) :=
      (measurable_id.pow_const _).ennreal_ofReal
    rw [hL]
    refine (eq_top_iff.2 ?_).symm
    calc (⊤ : ENNReal)
        = ENNReal.ofReal q * (μ {ω | X ω = ⊤} * ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (q - 1))) := by
          rw [lintegral_Ioi_rpow_sub_one_eq_top hq, ENNReal.mul_top h,
            ENNReal.mul_top (ENNReal.ofReal_pos.2 hq).ne']
      _ = ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {ω | X ω = ⊤} * ENNReal.ofReal (t ^ (q - 1)) := by
          rw [lintegral_const_mul _ hmeasG]
      _ ≤ _ := by
          refine mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_) _
          refine mul_le_mul_left (measure_mono fun ω hω => ?_) _
          simp only [Set.mem_setOf_eq] at hω ⊢
          rw [hω]
          exact ENNReal.ofReal_lt_top

/-! ### Interval integrals -/

theorem lintegral_Ioo_rpow_eq {s r : ℝ} (hs : 0 ≤ s) (hr : -1 < r) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (s ^ (r + 1) / (r + 1)) := by
  have hIntU : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hInt : IntegrableOn (fun t : ℝ => t ^ r) (Ioo 0 s) volume :=
    hIntU.1.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 s)] (fun t : ℝ => t ^ r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le r
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

theorem lintegral_Ioi_Iio_rpow {s r : ℝ} (hs : 0 ≤ s) (hr : -1 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (Iio s).indicator (fun _ => (1:ℝ≥0∞)) t
      = ENNReal.ofReal (s ^ (r + 1) / (r + 1)) := by
  rw [show (fun t : ℝ => ENNReal.ofReal (t ^ r) *
        (Iio s).indicator (fun _ => (1:ℝ≥0∞)) t)
        = (Iio s).indicator (fun t => ENNReal.ofReal (t ^ r)) from by
    funext t; by_cases h : t < s <;> simp [Set.indicator, h]]
  rw [setLIntegral_indicator measurableSet_Iio,
    show Iio s ∩ Ioi (0:ℝ) = Ioo 0 s from by ext t; simp [Ioo, and_comm],
    lintegral_Ioo_rpow_eq hs hr]

/-- Pointwise value of the `Ioi 0` integral of `t^(p-2)` on `t < gN x`. -/
theorem lintegral_Ioi_cond_rpow_eq {Ω : Type*} [MeasurableSpace Ω]
    (gN : Ω → ℝ≥0∞) (hgNlt : ∀ x, gN x < ∞) (p : ℝ) (hp : 1 < p) (x : Ω) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (if ENNReal.ofReal t < gN x then (1:ℝ≥0∞) else 0)
      = ENNReal.ofReal (1/(p-1)) * gN x ^ (p-1) := by
  have hs : 0 ≤ (gN x).toReal := ENNReal.toReal_nonneg
  have hr : -1 < p - 2 := by linarith
  have hx : gN x ≠ ∞ := ne_of_lt (hgNlt x)
  have hcongr : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (if ENNReal.ofReal t < gN x then (1:ℝ≥0∞) else 0)
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (Iio ((gN x).toReal)).indicator (fun _ => (1:ℝ≥0∞)) t := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.indicator_apply]
    by_cases h : ENNReal.ofReal t < gN x
    · have htlt : t < (gN x).toReal := (ENNReal.ofReal_lt_iff_lt_toReal ht.le hx).1 h
      simp [h, htlt]
    · have htge : ¬ t < (gN x).toReal := fun htlt =>
        h ((ENNReal.ofReal_lt_iff_lt_toReal ht.le hx).2 htlt)
      simp [h, htge]
  rw [hcongr, lintegral_Ioi_Iio_rpow hs hr]
  rw [show p - 2 + 1 = p - 1 by ring]
  have hpm : 0 < p - 1 := by linarith
  rw [show (gN x).toReal ^ (p - 1) / (p - 1) = (gN x).toReal ^ (p-1) * (1/(p-1)) by
    rw [div_eq_mul_one_div]]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs (p-1)),
    ← ENNReal.ofReal_rpow_of_nonneg hs hpm.le, ENNReal.ofReal_toReal hx]
  ring

/-- Pointwise iSup of truncated powers. -/
theorem iSup_min_rpow (a : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (⨆ N : ℕ, (min a (N:ℝ≥0∞)) ^ p) = a ^ p := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro N; exact ENNReal.rpow_le_rpow (min_le_left _ _) (by linarith)
  · intro w hw
    rcases eq_or_ne a ∞ with rfl | ha
    · have hwtop : w < (⨆ N : ℕ, (N:ℝ≥0∞)) := by
        rw [ENNReal.iSup_natCast]
        rwa [ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < p)] at hw
      rw [lt_iSup_iff] at hwtop
      obtain ⟨N, hN⟩ := hwtop
      refine ⟨N, lt_of_lt_of_le hN ?_⟩
      have hmin : min (⊤ : ℝ≥0∞) (N:ℝ≥0∞) = (N:ℝ≥0∞) := min_eq_right le_top
      rw [hmin]
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0; simp
      · calc (N:ℝ≥0∞) = (N:ℝ≥0∞) ^ (1:ℝ) := (ENNReal.rpow_one _).symm
          _ ≤ (N:ℝ≥0∞) ^ p :=
              ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hNpos) hp
    · obtain ⟨N, hN⟩ := exists_nat_ge a.toReal
      refine ⟨N, ?_⟩
      have haN : a ≤ (N:ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal ha]
        simpa using ENNReal.ofReal_le_ofReal hN
      rwa [min_eq_left haN]


/-! ## The Birkhoff maximal function and the named statements -/

-- The general-`p` layer cake is already in Mathlib (real-valued `f`):
#check @MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
#check @MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul

/-- The one-parameter maximal function `Mf x = sup_N (N : ℝ≥0∞)⁻¹ * Σ_{k<N} f(T^[k] x)`. -/
noncomputable def birkhoffMax {Ω : Type*} [MeasurableSpace Ω] (T : Ω → Ω) (f : Ω → ℝ≥0∞) :
    Ω → ℝ≥0∞ :=
  fun x => ⨆ (N : ℕ), (N : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range N, f (T^[k] x)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ≥0∞}

/-- Pointwise `iSup` of truncations at a natural-number level. -/
lemma iSup_min_natCast (a : ℝ≥0∞) : (⨆ N : ℕ, min a (N:ℝ≥0∞)) = a := by
  apply le_antisymm
  · exact iSup_le fun N => min_le_left _ _
  · rcases eq_or_ne a ∞ with rfl | ha
    · simpa only [min_top_left, ENNReal.iSup_natCast] using le_top
    · obtain ⟨N, hN⟩ := exists_nat_ge a.toReal
      refine le_iSup_of_le N (le_min le_rfl ?_)
      rw [← ENNReal.ofReal_toReal ha]
      simpa using ENNReal.ofReal_le_ofReal hN

omit [MeasurableSpace Ω] in
lemma iSup_add_iSup_of_monotone {A B : ℕ → ℝ≥0∞} (hA : Monotone A) (hB : Monotone B) :
    (⨆ i, A i) + (⨆ j, B j) = ⨆ k, (A k + B k) := by
  rw [ENNReal.iSup_add]
  simp_rw [ENNReal.add_iSup]
  apply le_antisymm
  · apply iSup_le; intro i
    apply iSup_le; intro j
    exact le_iSup_of_le (max i j)
      (add_le_add (hA (le_max_left i j)) (hB (le_max_right i j)))
  · apply iSup_le; intro k
    exact le_iSup_of_le k (le_iSup_of_le k le_rfl)

omit [MeasurableSpace Ω] in
lemma Finset.sum_iSup_of_monotone {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ≥0∞)
    (hg : ∀ k, Monotone (g k)) :
    (∑ k ∈ s, ⨆ M, g k M) = ⨆ M, ∑ k ∈ s, g k M := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      simp_rw [Finset.sum_insert ha]
      rw [iSup_add_iSup_of_monotone (hg a)
          (fun M N hMN => Finset.sum_le_sum fun k _ => hg k hMN)]

/-- Truncating the function truncates the maximal function, the suprema recovering it. -/
lemma birkhoffMax_iSup_min (T : Ω → Ω) (f : Ω → ℝ≥0∞) :
    birkhoffMax T f = fun x => ⨆ M : ℕ, birkhoffMax T (fun x => min (f x) (M:ℝ≥0∞)) x := by
  funext x
  simp only [birkhoffMax]
  rw [iSup_comm]
  congr 1
  funext N
  rw [← ENNReal.mul_iSup]
  congr 1
  rw [show (∑ k ∈ Finset.range N, f (T^[k] x))
        = ∑ k ∈ Finset.range N, ⨆ M : ℕ, min (f (T^[k] x)) (M:ℝ≥0∞) from
      Finset.sum_congr rfl (fun k _ => (iSup_min_natCast _).symm)]
  rw [Finset.sum_iSup_of_monotone (s := Finset.range N)
      (g := fun k M => min (f (T^[k] x)) (M:ℝ≥0∞))
      (fun k M N hMN => min_le_min le_rfl (by exact_mod_cast hMN))]

omit [MeasurableSpace Ω] in
theorem maxBirkhoff_pos_iff (T : Ω → Ω) (g : Ω → ℝ) (N : ℕ) (x : Ω) :
    0 < maxBirkhoff T g N x ↔ ∃ n ≤ N, 0 < birkhoffSum T g n x := by
  induction N with
  | zero =>
      constructor
      · intro hx; exact absurd hx (by simp [maxBirkhoff])
      · rintro ⟨n, hn, hnpos⟩
        interval_cases n
        simp [birkhoffSum] at hnpos
  | succ N ih =>
      rw [maxBirkhoff_succ, lt_max_iff, ih]
      constructor
      · rintro (⟨n, hn, hpos⟩ | hpos)
        · exact ⟨n, by omega, hpos⟩
        · exact ⟨N+1, le_rfl, hpos⟩
      · rintro ⟨n, hn, hpos⟩
        rcases Nat.lt_or_ge n (N+1) with hlt | hge
        · exact Or.inl ⟨n, by omega, hpos⟩
        · refine Or.inr ?_
          have hne : n = N+1 := by omega
          rw [hne] at hpos
          exact hpos

omit [MeasurableSpace Ω] in
theorem birkhoffMax_term (T : Ω → Ω) (h : Ω → ℝ) (hnn : ∀ x, 0 ≤ h x) (N : ℕ) (x : Ω) :
    (N : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range N, ENNReal.ofReal (h (T^[k] x))
      = ENNReal.ofReal (bAvg T h N x) := by
  cases N with
  | zero => simp [bAvg, birkhoffSum]
  | succ n =>
      have hn : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn _)]
      have hNinv : (((n+1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (((n+1 : ℕ) : ℝ)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]
      rw [hNinv, ← ENNReal.ofReal_mul (inv_nonneg.mpr hn.le)]
      congr 1
      simp only [bAvg, birkhoffSum, div_eq_mul_inv]
      ring

omit [MeasurableSpace Ω] in
theorem maximalSet_eq_bAvg (T : Ω → Ω) (h : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    maximalSet T h c = {x | ∃ n : ℕ, c < bAvg T h n x} := by
  ext x
  simp only [maximalSet, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨N, hN⟩
    rw [maxBirkhoff_pos_iff] at hN
    obtain ⟨n, -, hn⟩ := hN
    have hn1 : 1 ≤ n := by
      by_contra h
      push Not at h
      have : n = 0 := by omega
      subst this
      simp [birkhoffSum] at hn
    refine ⟨n, ?_⟩
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [bAvg, lt_div_iff₀ hn0]
    rw [birkhoffSum_sub_const] at hn
    linarith
  · rintro ⟨n, hn⟩
    have hn1 : 1 ≤ n := by
      by_contra h
      push Not at h
      have : n = 0 := by omega
      subst this
      simp [bAvg, birkhoffSum] at hn
      linarith
    refine ⟨n, ?_⟩
    rw [maxBirkhoff_pos_iff]
    refine ⟨n, le_rfl, ?_⟩
    rw [birkhoffSum_sub_const, bAvg] at *
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [lt_div_iff₀ hn0] at hn
    linarith

/-- The restricted form of the maximal inequality: `c · μ{E} ≤ ∫_E |f|` on the maximal set. -/
theorem maximalSet_restricted_le [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {h : Ω → ℝ} (hfm : Measurable h) (hint : Integrable h μ) (hnn : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal c * μ (maximalSet T h c) ≤
      ∫⁻ x in maximalSet T h c, ENNReal.ofReal (h x) ∂μ := by
  set g : Ω → ℝ := fun y => h y - c with hg
  have hgm : Measurable g := hfm.sub measurable_const
  have hgi : Integrable g μ := hint.sub (integrable_const c)
  set E : ℕ → Set Ω := fun N => {x | 0 < maxBirkhoff T g N x} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxBirkhoff hT.measurable hgm N)
  have hmono : Monotone E := monotone_maximalSet_aux T h c
  have hstep : ∀ N, ENNReal.ofReal c * μ (E N) ≤ ∫⁻ x in E N, ENNReal.ofReal (h x) ∂μ := by
    intro N
    have h0 := maximal_ergodic hT hgm hgi N
    have hsplit : ∫ x in E N, g x ∂μ = (∫ x in E N, h x ∂μ) - c * (μ (E N)).toReal := by
      rw [hg]
      rw [integral_sub hint.integrableOn (integrable_const c), setIntegral_const,
        smul_eq_mul, measureReal_def]
      ring
    rw [hsplit] at h0
    have hcle : c * (μ (E N)).toReal ≤ ∫ x in E N, h x ∂μ := by linarith
    have h2 : ENNReal.ofReal (∫ x in E N, h x ∂μ)
        = ∫⁻ x in E N, ENNReal.ofReal (h x) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Filter.Eventually.of_forall hnn)
    have h3 : μ (E N) = ENNReal.ofReal ((μ (E N)).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    calc ENNReal.ofReal c * μ (E N)
        = ENNReal.ofReal c * ENNReal.ofReal ((μ (E N)).toReal) := by conv_lhs => rw [h3]
      _ = ENNReal.ofReal (c * (μ (E N)).toReal) := (ENNReal.ofReal_mul hc.le).symm
      _ ≤ ENNReal.ofReal (∫ x in E N, h x ∂μ) := ENNReal.ofReal_le_ofReal hcle
      _ = ∫⁻ x in E N, ENNReal.ofReal (h x) ∂μ := h2
  have hsuplim : (⨆ N, μ (E N)) = μ (maximalSet T h c) :=
    iSup_eq_of_tendsto (fun m n hmn => measure_mono (hmono hmn))
      (by rw [maximalSet]; exact tendsto_measure_iUnion_atTop hmono)
  calc ENNReal.ofReal c * μ (maximalSet T h c)
      = ENNReal.ofReal c * (⨆ N, μ (E N)) := by rw [hsuplim]
    _ = ⨆ N, ENNReal.ofReal c * μ (E N) := ENNReal.mul_iSup _ _
    _ ≤ ⨆ N, ∫⁻ x in E N, ENNReal.ofReal (h x) ∂μ := iSup_le fun N => le_iSup_of_le N (hstep N)
    _ ≤ ∫⁻ x in maximalSet T h c, ENNReal.ofReal (h x) ∂μ := by
        refine iSup_le fun N => ?_
        exact lintegral_mono_set (fun x hx => mem_iUnion.mpr ⟨N, hx⟩)

theorem marcinkiewicz_abstract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g f : Ω → ℝ≥0∞) (p : ℝ) (hp : 1 < p)
    (hg : Measurable g) (hf : Measurable f)
    (hweak : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < g x} ≤
        ∫⁻ x, ({x | ENNReal.ofReal t < g x}.indicator f) x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ x, f x ^ p ∂μ := by
  have hCpos : 0 < (p / (p - 1)) ^ p :=
    Real.rpow_pos_of_pos (by positivity) p
  by_cases hB : ∫⁻ x, f x ^ p ∂μ = ∞
  · have hC : ENNReal.ofReal ((p / (p - 1)) ^ p) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hCpos).ne'
    rw [hB, ENNReal.mul_top hC]
    exact le_top
  have key : ∀ N : ℕ, ∫⁻ x, (min (g x) (N:ℝ≥0∞)) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ x, f x ^ p ∂μ := by
    intro N
    let gN : Ω → ℝ≥0∞ := fun x => min (g x) (N:ℝ≥0∞)
    have hgNmeas : Measurable gN := hg.min measurable_const
    have hgNlt : ∀ x, gN x < ∞ := fun x =>
      lt_of_le_of_lt (min_le_right _ _) (by simp)
    have hgNpow_meas : Measurable (fun x => gN x ^ (p - 1)) :=
      (ENNReal.continuous_rpow_const (y := p - 1)).measurable.comp hgNmeas
    have hweakN : ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t * μ {x | ENNReal.ofReal t < gN x} ≤
          ∫⁻ x, ({x | ENNReal.ofReal t < gN x}.indicator f) x ∂μ := by
      intro t ht
      by_cases htN : t < (N : ℝ)
      · have hset : {x | ENNReal.ofReal t < gN x} = {x | ENNReal.ofReal t < g x} := by
          ext x
          simp only [gN, Set.mem_setOf_eq]
          constructor
          · intro h; exact lt_of_lt_of_le h (min_le_left _ _)
          · intro h
            refine lt_min h ?_
            rw [ENNReal.ofReal_lt_iff_lt_toReal ht.le (by simp)]
            simpa using htN
        rw [hset]; exact hweak t ht
      · have hset : {x | ENNReal.ofReal t < gN x} = ∅ := by
          ext x
          simp only [gN, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          have h2 : ENNReal.ofReal t < (N : ℝ≥0∞) := lt_of_lt_of_le h (min_le_right _ _)
          rw [ENNReal.ofReal_lt_iff_lt_toReal ht.le (by simp)] at h2
          rw [ENNReal.toReal_natCast] at h2
          exact absurd h2 (not_lt.mpr (le_of_not_gt htN))
        rw [hset]; simp
    have hinner : ∀ x : Ω,
        ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            ({y : Ω | ENNReal.ofReal t < gN y}.indicator f) x
          = ENNReal.ofReal (1/(p-1)) * (f x * gN x ^ (p-1)) := by
      intro x
      have hψ : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p-2)) *
          (if ENNReal.ofReal t < gN x then (1:ℝ≥0∞) else 0)) := by
        refine ((measurable_id.pow_const (p-2)).ennreal_ofReal).mul ?_
        rw [show (fun t : ℝ => if ENNReal.ofReal t < gN x then (1:ℝ≥0∞) else 0)
            = ({t : ℝ | ENNReal.ofReal t < gN x}.indicator (fun _ => (1:ℝ≥0∞))) from by
              funext t; simp only [Set.indicator_apply, Set.mem_setOf_eq]]
        exact measurable_const.indicator
          (measurableSet_lt measurable_id.ennreal_ofReal measurable_const)
      have hstep : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            ({y : Ω | ENNReal.ofReal t < gN y}.indicator f) x
          = f x * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            (if ENNReal.ofReal t < gN x then (1:ℝ≥0∞) else 0) := by
        rw [← lintegral_const_mul (f x) hψ]
        refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        by_cases h : ENNReal.ofReal t < gN x
        · simp only [h, if_true]; ring
        · simp only [h, if_false, mul_zero]
      rw [hstep, lintegral_Ioi_cond_rpow_eq gN hgNlt p hp x]
      ring
    have hpt : ∀ t : ℝ, 0 < t →
        μ {x | ENNReal.ofReal t < gN x} * ENNReal.ofReal (t ^ (p-1)) ≤
          ENNReal.ofReal (t ^ (p-2)) *
            ∫⁻ x, ({x | ENNReal.ofReal t < gN x}.indicator f) x ∂μ := by
      intro t ht
      have hfact : ENNReal.ofReal (t ^ (p-1)) =
          ENNReal.ofReal t * ENNReal.ofReal (t ^ (p-2)) := by
        rw [← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht 1 (p-2), Real.rpow_one]
      calc μ {x | ENNReal.ofReal t < gN x} * ENNReal.ofReal (t ^ (p-1))
          = ENNReal.ofReal (t ^ (p-2)) *
              (ENNReal.ofReal t * μ {x | ENNReal.ofReal t < gN x}) := by
            rw [hfact]; ring
        _ ≤ ENNReal.ofReal (t ^ (p-2)) *
              ∫⁻ x, ({x | ENNReal.ofReal t < gN x}.indicator f) x ∂μ := by
            gcongr
            exact hweakN t ht
    have hφ : AEMeasurable (Function.uncurry (fun (t : ℝ) (x : Ω) =>
          ENNReal.ofReal (t ^ (p-2)) * ({y : Ω | ENNReal.ofReal t < gN y}.indicator f) x))
        ((volume.restrict (Ioi (0:ℝ))).prod μ) := by
      apply Measurable.aemeasurable
      have heq : Function.uncurry (fun (t : ℝ) (x : Ω) =>
            ENNReal.ofReal (t ^ (p-2)) * ({y : Ω | ENNReal.ofReal t < gN y}.indicator f) x)
          = fun z : ℝ × Ω => ENNReal.ofReal (z.1 ^ (p-2)) *
              ({y : Ω | ENNReal.ofReal z.1 < gN y}.indicator f) z.2 := by
        funext z; rfl
      rw [heq]
      have hset : MeasurableSet {z : ℝ × Ω | ENNReal.ofReal z.1 < gN z.2} :=
        measurableSet_lt (measurable_fst.ennreal_ofReal) (hgNmeas.comp measurable_snd)
      exact ((measurable_fst.pow_const (p-2)).ennreal_ofReal).mul
        ((hf.comp measurable_snd).indicator hset)
    have hstep1 :
        ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < gN x} * ENNReal.ofReal (t ^ (p-1))
          ≤ ENNReal.ofReal (1/(p-1)) * ∫⁻ x, f x * gN x ^ (p-1) ∂μ := by
      calc ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < gN x} * ENNReal.ofReal (t ^ (p-1))
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
                ∫⁻ x, ({x | ENNReal.ofReal t < gN x}.indicator f) x ∂μ :=
              setLIntegral_mono' measurableSet_Ioi fun t ht => hpt t ht
        _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal (t ^ (p-2)) *
                ({x | ENNReal.ofReal t < gN x}.indicator f) x ∂μ := by
              refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
              exact (lintegral_const_mul _
                (hf.indicator (measurableSet_lt measurable_const hgNmeas))).symm
        _ = ∫⁻ x, (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
                ({y : Ω | ENNReal.ofReal t < gN y}.indicator f) x) ∂μ :=
              lintegral_lintegral_swap hφ
        _ = ∫⁻ x, ENNReal.ofReal (1/(p-1)) * (f x * gN x ^ (p-1)) ∂μ := by
              refine lintegral_congr fun x => ?_
              exact hinner x
        _ = ENNReal.ofReal (1/(p-1)) * ∫⁻ x, f x * gN x ^ (p-1) ∂μ := by
              rw [show (fun x : Ω => ENNReal.ofReal (1/(p-1)) * (f x * gN x ^ (p-1)))
                  = fun x : Ω => ENNReal.ofReal (1/(p-1)) * (f * fun x => gN x ^ (p-1)) x by
                    funext x; rw [Pi.mul_apply]]
              exact lintegral_const_mul _ (hf.mul hgNpow_meas)
    have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.aemeasurable
      hgNpow_meas.aemeasurable
    have hqpow : (fun x => (gN x ^ (p-1)) ^ (p/(p-1))) = fun x => gN x ^ p := by
      funext x
      rw [← ENNReal.rpow_mul, mul_comm (p - 1) (p / (p - 1)),
        div_mul_cancel₀ p (by linarith : p - 1 ≠ 0)]
    rw [hqpow] at hHolder
    set S := ∫⁻ x, f x * gN x ^ (p-1) ∂μ with hS
    set X := ∫⁻ x, gN x ^ p ∂μ with hX
    set Y := ∫⁻ x, f x ^ p ∂μ with hY
    set K := ENNReal.ofReal (p/(p-1)) with hK
    have hcomb : X ≤ K * S := by
      rw [hX, hK, hS]
      calc ∫⁻ x, gN x ^ p ∂μ
          = ENNReal.ofReal p * ∫⁻ t in Ioi (0:ℝ),
              μ {x | ENNReal.ofReal t < gN x} * ENNReal.ofReal (t ^ (p-1)) :=
              lintegral_rpow_layer_cake hgNmeas (by linarith)
        _ ≤ ENNReal.ofReal p *
              (ENNReal.ofReal (1/(p-1)) * ∫⁻ x, f x * gN x ^ (p-1) ∂μ) := by
              gcongr
        _ = ENNReal.ofReal (p/(p-1)) * ∫⁻ x, f x * gN x ^ (p-1) ∂μ := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p)]
              congr 1
              ring_nf
    have hHolder' : S ≤ Y ^ (1/p) * X ^ (1/(p/(p-1))) := by
      have h1 : ∫⁻ a, (f * fun x => gN x ^ (p-1)) a ∂μ = S := by
        rw [hS]; exact lintegral_congr (fun a => by rw [Pi.mul_apply])
      have h2 : Y ^ (1/p) * X ^ (1/(p/(p-1)))
          = (∫⁻ x, f x ^ p ∂μ) ^ (1/p) * (∫⁻ x, gN x ^ p ∂μ) ^ (1/(p/(p-1))) := by
        rw [hY, hX]
      rw [← h1, ← h2]
      exact hHolder
    have hmain : X ≤ K * (Y ^ (1/p) * X ^ (1/(p/(p-1)))) := by
      calc X ≤ K * S := hcomb
        _ ≤ K * (Y ^ (1/p) * X ^ (1/(p/(p-1)))) := by
              gcongr
    by_cases hX0 : X = 0
    · rw [hX0]; exact zero_le
    · have hXtop : X ≠ ∞ := by
        rw [hX]
        have hle : ∫⁻ x, gN x ^ p ∂μ ≤ (N:ℝ≥0∞)^p * μ univ := by
          rw [← lintegral_const]
          exact lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right _ _) (by linarith : (0:ℝ) ≤ p)
        rw [measure_univ, mul_one] at hle
        exact ne_of_lt (lt_of_le_of_lt hle
          (ENNReal.rpow_lt_top_of_nonneg (by linarith : (0:ℝ) ≤ p) (by simp)))
      have hpne : p ≠ 0 := by linarith
      have hone : 1/p + 1/(p/(p-1)) = 1 := by
        rw [one_div, one_div]
        exact hpq.inv_add_inv_eq_one
      have hXsplit : X = X^(1/p) * X^(1/(p/(p-1))) := by
        rw [← ENNReal.rpow_add _ _ hX0 hXtop, hone, ENNReal.rpow_one]
      have hqpos : 0 < 1/(p/(p-1)) := by positivity
      have hXq_ne0 : X^(1/(p/(p-1))) ≠ 0 := by
        intro h
        rw [ENNReal.rpow_eq_zero_iff] at h
        rcases h with ⟨hXz, _⟩ | ⟨hXz, hlt⟩
        · exact hX0 hXz
        · exact absurd hlt (not_lt.mpr (by positivity))
      have hXq_lt : X^(1/(p/(p-1))) < ∞ :=
        ENNReal.rpow_lt_top_of_nonneg hqpos.le hXtop
      have hcancel : X^(1/p) ≤ K * Y^(1/p) := by
        have hchain : X^(1/p) * X^(1/(p/(p-1))) ≤
            K * Y^(1/p) * X^(1/(p/(p-1))) := by
          calc X^(1/p) * X^(1/(p/(p-1))) = X := hXsplit.symm
            _ ≤ K * (Y^(1/p) * X^(1/(p/(p-1)))) := hmain
            _ = K * Y^(1/p) * X^(1/(p/(p-1))) := by rw [← mul_assoc]
        exact (ENNReal.mul_le_mul_iff_left hXq_ne0 (ne_of_lt hXq_lt)).1 hchain
      have h1 : (X^(1/p))^p = X := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hpne, ENNReal.rpow_one]
      have h2 : (K * Y^(1/p))^p = K^p * Y := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ p), ← ENNReal.rpow_mul,
            one_div_mul_cancel hpne, ENNReal.rpow_one]
      have hKp : K ^ p = ENNReal.ofReal ((p / (p - 1)) ^ p) := by
        rw [hK, ← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ p/(p-1))
              (by linarith : (0:ℝ) ≤ p)]
      have hpow := ENNReal.rpow_le_rpow hcancel (by linarith : (0:ℝ) ≤ p)
      rw [h1, h2, hKp] at hpow
      exact hpow
  have hconv : ∫⁻ x, g x ^ p ∂μ =
      ⨆ N : ℕ, ∫⁻ x, (min (g x) (N:ℝ≥0∞)) ^ p ∂μ := by
    rw [← lintegral_iSup]
    · congr 1
      funext x
      exact (iSup_min_rpow (g x) hp.le).symm
    · intro N
      exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp
        (hg.min measurable_const)
    · intro M N hMN x
      exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hMN)) (by linarith)
  rw [hconv]
  exact ciSup_le key

/-- Measurability of the Birkhoff maximal function. -/
theorem measurable_birkhoffMax {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω} {f : Ω → ℝ≥0∞}
    (hT : Measurable T) (hf : Measurable f) : Measurable (birkhoffMax T f) := by
  refine Measurable.iSup fun N => ?_
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k))


/-! ## The `ℝ≥0∞`-valued weak type and the strong `Lᵖ` maximal -/

theorem birkhoffMax_mono {f₁ f₂ : Ω → ℝ≥0∞} (h : f₁ ≤ f₂) :
    birkhoffMax T f₁ ≤ birkhoffMax T f₂ := by
  intro x
  simp only [birkhoffMax]
  refine iSup_le fun N => ?_
  exact le_iSup_of_le N (mul_le_mul' (le_refl _) (Finset.sum_le_sum fun k _ => h _))

/-- The `ℝ≥0∞` normalised weak-type bound for `birkhoffMax`, obtained from the pin's maximal
ergodic theorem (`maximalSet_restricted_le`) by truncating `f` at each natural level and passing
to the limit with `birkhoffMax_iSup_min`. -/
theorem birkhoffMax_weakType {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < birkhoffMax T f x} ≤
        ∫⁻ x, ({x | ENNReal.ofReal t < birkhoffMax T f x}.indicator f) x ∂μ := by
  intro t ht
  let fM : ℕ → Ω → ℝ≥0∞ := fun M x => min (f x) (M:ℝ≥0∞)
  have hfMmeas : ∀ M, Measurable (fM M) := fun M => hf.min measurable_const
  have hMbound : ∀ M, ENNReal.ofReal t * μ {x | ENNReal.ofReal t < birkhoffMax T (fM M) x} ≤
      ∫⁻ x, ({x | ENNReal.ofReal t < birkhoffMax T (fM M) x}.indicator f) x ∂μ := by
    intro M
    set h : Ω → ℝ := fun x => (fM M x).toReal with hh
    have hfin : ∀ x, fM M x ≠ ∞ :=
      fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (min_le_right _ _)
    have hnn : 0 ≤ h := fun x => ENNReal.toReal_nonneg
    have heq : (fun x => ENNReal.ofReal (h x)) = fM M :=
      funext fun x => ENNReal.ofReal_toReal (hfin x)
    have hmeas : Measurable h := (hfMmeas M).ennreal_toReal
    have hint : Integrable h μ := by
      refine Integrable.of_bound hmeas.aestronglyMeasurable (M:ℝ) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
      calc (fM M x).toReal ≤ ((M:ℝ≥0∞)).toReal :=
            ENNReal.toReal_mono (ENNReal.natCast_ne_top M) (min_le_right _ _)
        _ = (M:ℝ) := ENNReal.toReal_natCast M
    have hset : maximalSet T h t = {x | ENNReal.ofReal t < birkhoffMax T (fM M) x} := by
      have hMeq : fM M = fun x => ENNReal.ofReal (h x) := heq.symm
      rw [maximalSet_eq_bAvg T h ht, hMeq]
      ext x
      simp only [Set.mem_setOf_eq, birkhoffMax]
      rw [lt_iSup_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, by
          rw [birkhoffMax_term T h hnn n x]
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hn⟩
      · rintro ⟨n, hn⟩
        rw [birkhoffMax_term T h hnn n x] at hn
        exact ⟨n, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp hn⟩
    have hEmeas : MeasurableSet {x | ENNReal.ofReal t < birkhoffMax T (fM M) x} :=
      hset ▸ measurableSet_maximalSet hT.measurable hmeas t
    have hbound := maximalSet_restricted_le hT hmeas hint hnn ht
    rw [hset] at hbound
    calc ENNReal.ofReal t * μ {x | ENNReal.ofReal t < birkhoffMax T (fM M) x}
        ≤ ∫⁻ x in {x | ENNReal.ofReal t < birkhoffMax T (fM M) x}, ENNReal.ofReal (h x) ∂μ :=
          hbound
      _ = ∫⁻ x in {x | ENNReal.ofReal t < birkhoffMax T (fM M) x}, fM M x ∂μ := by rw [heq]
      _ ≤ ∫⁻ x in {x | ENNReal.ofReal t < birkhoffMax T (fM M) x}, f x ∂μ :=
            setLIntegral_mono' hEmeas (fun x _ => min_le_left _ _)
      _ = ∫⁻ x, ({x | ENNReal.ofReal t < birkhoffMax T (fM M) x}.indicator f) x ∂μ := by
            rw [lintegral_indicator hEmeas]
  set E : ℕ → Set Ω := fun M => {x | ENNReal.ofReal t < birkhoffMax T (fM M) x} with hE
  have hEmono : Monotone E := by
    intro M N hMN x hx
    have hx' : ENNReal.ofReal t < birkhoffMax T (fM M) x := by
      simpa only [hE, Set.mem_setOf_eq] using hx
    have hgoal : ENNReal.ofReal t < birkhoffMax T (fM N) x :=
      lt_of_lt_of_le hx' (birkhoffMax_mono (fun y => min_le_min le_rfl (by exact_mod_cast hMN)) x)
    simpa only [hE, Set.mem_setOf_eq] using hgoal
  have hEunion : (⋃ M, E M) = {x | ENNReal.ofReal t < birkhoffMax T f x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, hE]
    constructor
    · rintro ⟨M, hM⟩
      exact lt_of_lt_of_le hM (birkhoffMax_mono (fun y => min_le_left _ _) x)
    · intro hx
      have hsup : birkhoffMax T f x = ⨆ M, birkhoffMax T (fM M) x :=
        congr_fun (birkhoffMax_iSup_min T f) x
      rw [hsup, lt_iSup_iff] at hx
      obtain ⟨M, hM⟩ := hx
      exact ⟨M, hM⟩
  have hEsup : (⨆ M, μ (E M)) = μ {x | ENNReal.ofReal t < birkhoffMax T f x} := by
    refine iSup_eq_of_tendsto (fun m n hmn => measure_mono (hEmono hmn)) ?_
    have := tendsto_measure_iUnion_atTop (μ := μ) hEmono
    rwa [hEunion] at this
  calc ENNReal.ofReal t * μ {x | ENNReal.ofReal t < birkhoffMax T f x}
      = ENNReal.ofReal t * (⨆ M, μ (E M)) := by rw [hEsup]
    _ = ⨆ M, ENNReal.ofReal t * μ (E M) := ENNReal.mul_iSup _ _
    _ ≤ ⨆ M, ∫⁻ x, (E M).indicator f x ∂μ := iSup_le fun M => le_iSup_of_le M (hMbound M)
    _ ≤ ∫⁻ x, ({x | ENNReal.ofReal t < birkhoffMax T f x}.indicator f) x ∂μ := by
        refine iSup_le fun M => ?_
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ E M
        · have hxbig : x ∈ {y | ENNReal.ofReal t < birkhoffMax T f y} := by
            rw [← hEunion]; exact Set.mem_iUnion.mpr ⟨M, hx⟩
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxbig]
        · rw [Set.indicator_of_notMem hx]; exact zero_le

/-- **Wiener's maximal theorem**, in the exact form isolated by the library as
`LatticeProb.BirkhoffLpMaximal`: the one-parameter strong `Lᵖ` maximal inequality. -/
theorem birkhoffLpMaximal : BirkhoffLpMaximal := by
  intro p hp
  refine ⟨(p / (p - 1)) ^ p, by positivity, ?_⟩
  intro Ω _ μ hprob T hT f hf
  exact marcinkiewicz_abstract μ (birkhoffMax T f) f p hp
    (measurable_birkhoffMax hT.measurable hf) hf (birkhoffMax_weakType μ hT hf)

#print axioms birkhoffLpMaximal
#print axioms birkhoffMax_weakType

end

end LatticeProb
