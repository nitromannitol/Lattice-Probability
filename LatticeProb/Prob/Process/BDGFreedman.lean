import Mathlib

/-!
# Discrete peeling bound and Doob's Lᵖ inequality for the continuous Burkholder–Davis–Gundy bound

Ported from the vertex-reinforced walk development. The module collects the discrete inputs of the
upper half of the Burkholder–Davis–Gundy inequality for continuous martingales: the peeling
summation bound `peelingSummationBound_holds` for `p ≥ 2` in Burkholder–Rosenthal form, and Doob's
Lᵖ maximal inequality `doobMaximalLp_holds`. Both are proved here. Their auxiliary lemmas live in
the namespace `LatticeProb.Process.RandomizedFreedman`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Process

section Freedman

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The predictable quadratic variation `V k = ∑_{i<k} E[(M_{i+1} - M_i)^2 | F_i]`. -/
noncomputable def condQvar (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω

theorem measurable_condQvar (P : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) :
    Measurable[m0] (condQvar P ℱ M k) :=
  Finset.measurable_sum _ fun i _ =>
    ((stronglyMeasurable_condExp (m := ℱ i)).mono (ℱ.le i)).measurable

/-- Increments bounded by `b` from a start at `0` bound `|M j|` by `j b`. -/
theorem abs_le_of_increments {M : ℕ → Ω → ℝ} (hM0 : ∀ ω, M 0 ω = 0) {b : ℝ} {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |M (i + 1) ω - M i ω| ≤ b) :
    ∀ j, j ≤ n → ∀ ω, |M j ω| ≤ j * b := by
  intro j
  induction j with
  | zero => intro _ ω; simp [hM0 ω]
  | succ j ih =>
      intro hj ω
      have hjn : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have h1 := ih (le_of_lt hjn) ω
      have h2 := hinc j hjn ω
      have h3 : M (j + 1) ω = M j ω + (M (j + 1) ω - M j ω) := by ring
      calc |M (j + 1) ω| = |M j ω + (M (j + 1) ω - M j ω)| := by rw [← h3]
        _ ≤ |M j ω| + |M (j + 1) ω - M j ω| := abs_add_le _ _
        _ ≤ j * b + b := add_le_add h1 h2
        _ = ((j : ℝ) + 1) * b := by ring
        _ = ((j + 1 : ℕ) : ℝ) * b := by push_cast; ring

end Freedman

end LatticeProb.Process

namespace LatticeProb.Process.RandomizedFreedman

noncomputable section

section DoobCopy

open Set

/-! ### Layer cake for `ℝ≥0∞`-valued functions, non-strict level sets -/

/-- The half-line integral of `t ^ (q - 1)` diverges for `q > 0`. -/
private lemma lintegral_Ioi_rpow_sub_one_eq_top {q : ℝ} (hq : 0 < q) :
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

/-- Layer cake for `ℝ≥0∞`-valued functions with non-strict level sets. -/
private theorem lintegral_rpow_layer_cake_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ENNReal} (hX : Measurable X) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, X ω ^ q ∂μ = ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0 : ℝ),
      μ {ω | ENNReal.ofReal t ≤ X ω} * ENNReal.ofReal (t ^ (q - 1)) := by
  by_cases h : μ {ω | X ω = ⊤} = 0
  · have hae : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
      rw [ae_iff]
      simpa using h
    have h1 : ∫⁻ ω, X ω ^ q ∂μ = ∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ q) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le, ENNReal.ofReal_toReal hω]
    rw [h1, lintegral_rpow_eq_lintegral_meas_le_mul μ
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hX.ennreal_toReal.aemeasurable hq]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hset : μ {a | t ≤ (X a).toReal} = μ {ω | ENNReal.ofReal t ≤ X ω} := by
      refine measure_congr ?_
      filter_upwards [hae] with ω hω
      exact propext (ENNReal.ofReal_le_iff_le_toReal hω).symm
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
          simp only [Set.mem_ofPred_eq] at hω ⊢
          rw [hω]
          exact le_top

/-! ### Interval integrals -/

private theorem lintegral_Ioc_rpow_eq {s r : ℝ} (hs : 0 ≤ s) (hr : -1 < r) :
    ∫⁻ t in Ioc (0:ℝ) s, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (s ^ (r + 1) / (r + 1)) := by
  have hIntU : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hInt : IntegrableOn (fun t : ℝ => t ^ r) (Ioc 0 s) volume := hIntU.1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 s)] (fun t : ℝ => t ^ r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le r
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hs, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

private theorem lintegral_Ioi_Iic_rpow {s r : ℝ} (hs : 0 ≤ s) (hr : -1 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (Iic s).indicator (fun _ => (1:ℝ≥0∞)) t
      = ENNReal.ofReal (s ^ (r + 1) / (r + 1)) := by
  rw [show (fun t : ℝ => ENNReal.ofReal (t ^ r) *
        (Iic s).indicator (fun _ => (1:ℝ≥0∞)) t)
        = (Iic s).indicator (fun t => ENNReal.ofReal (t ^ r)) from by
    funext t; by_cases h : t ≤ s <;> simp [Set.indicator, h]]
  rw [lintegral_indicator measurableSet_Iic]
  have hmeas : (volume.restrict (Ioi (0:ℝ))).restrict (Iic s) = volume.restrict (Ioc (0:ℝ) s) := by
    rw [Measure.restrict_restrict (s := Iic s) (t := Ioi (0:ℝ)) measurableSet_Iic]
    congr 1
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]
    exact and_comm
  rw [hmeas]
  exact lintegral_Ioc_rpow_eq hs hr

/-- Pointwise value of the `Ioi 0` integral of `t^(p-2)` on `t ≤ gN x`. -/
private theorem lintegral_Ioi_cond_rpow_eq_le {Ω : Type*} [MeasurableSpace Ω]
    (gN : Ω → ℝ≥0∞) (hgNlt : ∀ x, gN x < ∞) (p : ℝ) (hp : 1 < p) (x : Ω) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (if ENNReal.ofReal t ≤ gN x then (1:ℝ≥0∞) else 0)
      = ENNReal.ofReal (1/(p-1)) * gN x ^ (p-1) := by
  have hs : 0 ≤ (gN x).toReal := ENNReal.toReal_nonneg
  have hr : -1 < p - 2 := by linarith
  have hx : gN x ≠ ∞ := ne_of_lt (hgNlt x)
  have hcongr : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (if ENNReal.ofReal t ≤ gN x then (1:ℝ≥0∞) else 0)
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
        (Iic ((gN x).toReal)).indicator (fun _ => (1:ℝ≥0∞)) t := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.indicator_apply]
    by_cases h : ENNReal.ofReal t ≤ gN x
    · have htle : t ≤ (gN x).toReal := (ENNReal.ofReal_le_iff_le_toReal hx).1 h
      simp [h, htle]
    · have htge : ¬ t ≤ (gN x).toReal := fun htle =>
        h ((ENNReal.ofReal_le_iff_le_toReal hx).2 htle)
      simp [h, htge]
  rw [hcongr, lintegral_Ioi_Iic_rpow hs hr]
  rw [show p - 2 + 1 = p - 1 by ring]
  have hpm : 0 < p - 1 := by linarith
  rw [show (gN x).toReal ^ (p - 1) / (p - 1) = (gN x).toReal ^ (p-1) * (1/(p-1)) by
    rw [div_eq_mul_one_div]]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs (p-1)),
    ← ENNReal.ofReal_rpow_of_nonneg hs hpm.le, ENNReal.ofReal_toReal hx]
  ring

/-- Pointwise iSup of truncated powers. -/
private theorem iSup_min_rpow (a : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
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

/-! ### The Marcinkiewicz layer-cake upgrade (non-strict level sets) -/

/-- **Marcinkiewicz upgrade.**  A weak-type `(1,1)` level bound for `g` implies the strong `Lᵖ`
bound with constant `(p/(p-1))ᵖ`, for `p > 1` and `ℝ≥0∞`-valued functions. -/
private theorem marcinkiewicz_abstract_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g f : Ω → ℝ≥0∞) (p : ℝ) (hp : 1 < p)
    (hg : Measurable g) (hf : Measurable f)
    (hweak : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ g x} ≤
        ∫⁻ x, ({x | ENNReal.ofReal t ≤ g x}.indicator f) x ∂μ) :
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
        ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ gN x} ≤
          ∫⁻ x, ({x | ENNReal.ofReal t ≤ gN x}.indicator f) x ∂μ := by
      intro t ht
      by_cases htN : t ≤ (N : ℝ)
      · have hset : {x | ENNReal.ofReal t ≤ gN x} = {x | ENNReal.ofReal t ≤ g x} := by
          ext x
          simp only [gN, Set.mem_ofPred_eq]
          constructor
          · intro h; exact le_trans h (min_le_left _ _)
          · intro h
            refine le_min h ?_
            rw [ENNReal.ofReal_le_iff_le_toReal (by simp)]
            simpa using htN
        rw [hset]; exact hweak t ht
      · have hset : {x | ENNReal.ofReal t ≤ gN x} = ∅ := by
          ext x
          refine ⟨fun hx => absurd hx ?_, fun hx => absurd hx (Set.notMem_empty x)⟩
          simp only [gN, Set.mem_ofPred_eq]
          intro h
          have h2 : ENNReal.ofReal t ≤ (N : ℝ≥0∞) := le_trans h (min_le_right _ _)
          rw [ENNReal.ofReal_le_iff_le_toReal (by simp)] at h2
          rw [ENNReal.toReal_natCast] at h2
          exact absurd h2 (not_le.mpr (lt_of_not_ge htN))
        rw [hset]; simp
    have hinner : ∀ x : Ω,
        ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            ({y : Ω | ENNReal.ofReal t ≤ gN y}.indicator f) x
          = ENNReal.ofReal (1/(p-1)) * (f x * gN x ^ (p-1)) := by
      intro x
      have hψ : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p-2)) *
          (if ENNReal.ofReal t ≤ gN x then (1:ℝ≥0∞) else 0)) := by
        refine ((measurable_id.pow_const (p-2)).ennreal_ofReal).mul ?_
        rw [show (fun t : ℝ => if ENNReal.ofReal t ≤ gN x then (1:ℝ≥0∞) else 0)
            = ({t : ℝ | ENNReal.ofReal t ≤ gN x}.indicator (fun _ => (1:ℝ≥0∞))) from by
              funext t; simp only [Set.indicator_apply, Set.mem_ofPred_eq]]
        exact measurable_const.indicator
          (measurableSet_le measurable_id.ennreal_ofReal measurable_const)
      have hstep : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            ({y : Ω | ENNReal.ofReal t ≤ gN y}.indicator f) x
          = f x * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
            (if ENNReal.ofReal t ≤ gN x then (1:ℝ≥0∞) else 0) := by
        rw [← lintegral_const_mul (f x) hψ]
        refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        by_cases h : ENNReal.ofReal t ≤ gN x
        · simp only [h, ite_true]; ring
        · simp only [h, ↓reduceIte, mul_zero]
      rw [hstep, lintegral_Ioi_cond_rpow_eq_le gN hgNlt p hp x]
      ring
    have hpt : ∀ t : ℝ, 0 < t →
        μ {x | ENNReal.ofReal t ≤ gN x} * ENNReal.ofReal (t ^ (p-1)) ≤
          ENNReal.ofReal (t ^ (p-2)) *
            ∫⁻ x, ({x | ENNReal.ofReal t ≤ gN x}.indicator f) x ∂μ := by
      intro t ht
      have hfact : ENNReal.ofReal (t ^ (p-1)) =
          ENNReal.ofReal t * ENNReal.ofReal (t ^ (p-2)) := by
        rw [← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht 1 (p-2), Real.rpow_one]
      calc μ {x | ENNReal.ofReal t ≤ gN x} * ENNReal.ofReal (t ^ (p-1))
          = ENNReal.ofReal (t ^ (p-2)) *
              (ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ gN x}) := by
            rw [hfact]; ring
        _ ≤ ENNReal.ofReal (t ^ (p-2)) *
              ∫⁻ x, ({x | ENNReal.ofReal t ≤ gN x}.indicator f) x ∂μ := by
            gcongr
            exact hweakN t ht
    have hφ : AEMeasurable (Function.uncurry (fun (t : ℝ) (x : Ω) =>
          ENNReal.ofReal (t ^ (p-2)) * ({y : Ω | ENNReal.ofReal t ≤ gN y}.indicator f) x))
        ((volume.restrict (Ioi (0:ℝ))).prod μ) := by
      apply Measurable.aemeasurable
      have heq : Function.uncurry (fun (t : ℝ) (x : Ω) =>
            ENNReal.ofReal (t ^ (p-2)) * ({y : Ω | ENNReal.ofReal t ≤ gN y}.indicator f) x)
          = fun z : ℝ × Ω => ENNReal.ofReal (z.1 ^ (p-2)) *
              ({y : Ω | ENNReal.ofReal z.1 ≤ gN y}.indicator f) z.2 := by
        funext z; rfl
      rw [heq]
      have hset : MeasurableSet {z : ℝ × Ω | ENNReal.ofReal z.1 ≤ gN z.2} :=
        measurableSet_le (measurable_fst.ennreal_ofReal) (hgNmeas.comp measurable_snd)
      exact ((measurable_fst.pow_const (p-2)).ennreal_ofReal).mul
        ((hf.comp measurable_snd).indicator hset)
    have hstep1 :
        ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t ≤ gN x} * ENNReal.ofReal (t ^ (p-1))
          ≤ ENNReal.ofReal (1/(p-1)) * ∫⁻ x, f x * gN x ^ (p-1) ∂μ := by
      calc ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t ≤ gN x} * ENNReal.ofReal (t ^ (p-1))
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
                ∫⁻ x, ({x | ENNReal.ofReal t ≤ gN x}.indicator f) x ∂μ :=
              setLIntegral_mono' measurableSet_Ioi fun t ht => hpt t ht
        _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal (t ^ (p-2)) *
                ({x | ENNReal.ofReal t ≤ gN x}.indicator f) x ∂μ := by
              refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
              exact (lintegral_const_mul _
                (hf.indicator (measurableSet_le measurable_const hgNmeas))).symm
        _ = ∫⁻ x, (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-2)) *
                ({y : Ω | ENNReal.ofReal t ≤ gN y}.indicator f) x) ∂μ :=
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
              μ {x | ENNReal.ofReal t ≤ gN x} * ENNReal.ofReal (t ^ (p-1)) :=
              lintegral_rpow_layer_cake_le hgNmeas (by linarith)
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

/-! ### The martingale maximal function -/

/-- `|X|` is a submartingale for a martingale `X` with integrable values (conditional Jensen for
the convex function `|·|`, via `MeasureTheory.norm_condExp_le`). -/
private lemma submartingale_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) (hint : ∀ i, Integrable (X i) P) :
    Submartingale (fun k ω => |X k ω|) ℱ P := by
  refine ⟨fun k => (hM.1 k).norm, ?_, fun k => (hint k).norm⟩
  intro i j hij
  have h := hM.2 i j hij
  have hJ := norm_condExp_le (μ := P) (m := ℱ i) (X j)
  filter_upwards [h, hJ] with ω hh hJω
  rw [hh] at hJω
  simpa only [Real.norm_eq_abs] using hJω

/-- Conversion of a real set integral of a nonnegative integrable function into the `ℝ≥0∞`
set integral of `ofReal`. -/
private lemma ofReal_setIntegral_eq_setLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → ℝ) (hh_nn : ∀ ω, 0 ≤ h ω) (hh_int : Integrable h P) {s : Set Ω}
    (_hs : MeasurableSet s) :
    ENNReal.ofReal (∫ ω in s, h ω ∂P) = ∫⁻ ω in s, ENNReal.ofReal (h ω) ∂P :=
  ofReal_integral_eq_lintegral_ofReal (μ := P.restrict s) hh_int.integrableOn
    (Eventually.of_forall hh_nn)

/-- `ofReal` commutes with the nonempty `Finset.sup'` of reals. -/
private lemma ofReal_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ENNReal.ofReal (s.sup' hs f) = s.sup' hs (fun i => ENNReal.ofReal (f i)) := by
  apply le_antisymm
  · refine Finset.sup'_induction hs f
      (p := fun a => ENNReal.ofReal a ≤ s.sup' hs (fun i => ENNReal.ofReal (f i))) ?_ ?_
    · intro a₁ _ a₂ _
      change ENNReal.ofReal (max a₁ a₂) ≤ s.sup' hs (fun i => ENNReal.ofReal (f i))
      rw [ENNReal.ofReal_max]
      exact max_le ‹_› ‹_›
    · intro b hb
      exact Finset.le_sup' (fun i => ENNReal.ofReal (f i)) hb
  · exact Finset.sup'_le hs _ fun i hi => ENNReal.ofReal_le_ofReal (Finset.le_sup' f hi)

/-- Identification of the `Finset.sup'` maximal with the `iSup` maximal. -/
private lemma sup'_range_eq_iSup (n : ℕ) (f : ℕ → ℝ≥0∞) :
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f = ⨆ k ≤ n, f k := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro k hk
    exact le_iSup_of_le k (le_iSup_of_le (by simpa [Finset.mem_range] using hk) le_rfl)
  · refine iSup_le fun k => iSup_le fun hk => ?_
    exact Finset.le_sup' f (by simp only [Finset.mem_range]; omega)

/-- The weak-type `(1,1)` level bound for the maximal function, in the non-strict `ℝ≥0∞`
form consumed by `marcinkiewicz_abstract_le`. -/
private lemma weakType_maximal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hM : Martingale X ℱ P) (hint : ∀ i, Integrable (X i) P) :
    ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * P {ω | ENNReal.ofReal t ≤
        ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => |X k ω|))} ≤
        ∫⁻ ω in {ω | ENNReal.ofReal t ≤
          ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => |X k ω|))}, ENNReal.ofReal |X n ω| ∂P := by
  set M : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |X k ω|) with hMdef
  have hMmeas : Measurable M := by
    rw [hMdef]
    have h := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k _ => ((hM.1 k).measurable.mono (ℱ.le k) le_rfl).abs)
    convert h using 1
    funext ω; rw [Finset.sup'_apply]
  have hMnn : ∀ ω, 0 ≤ M ω := by
    intro ω; rw [hMdef]
    exact le_trans (abs_nonneg _) (Finset.le_sup' (s := Finset.range (n + 1))
      (fun k => |X k ω|) (b := 0) (by simp))
  intro t ht
  have htnn : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.le
  have hcoe : (t.toNNReal : ℝ≥0∞) = ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_coe_nnreal (p := t.toNNReal), htnn]
  have hw := maximal_ineq (submartingale_abs P ℱ X hM hint) (fun _ => abs_nonneg _)
    (ε := t.toNNReal) n
  rw [htnn, hcoe] at hw
  have hset : {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (M ω)} = {ω | t ≤ M ω} := by
    ext ω; simp only [Set.mem_ofPred_eq]
    exact ENNReal.ofReal_le_ofReal_iff (hMnn ω)
  rw [hset]
  rw [← ofReal_setIntegral_eq_setLIntegral P (fun ω => |X n ω|) (fun _ => abs_nonneg _)
    (hint n).abs (measurableSet_le measurable_const hMmeas)]
  exact hw

/-! ### `DoobMaximalLp` -/

/-- **Doob's general-`p` maximal inequality for discrete real martingales from zero.** -/
def DoobMaximalLp : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (n : ℕ),
      Martingale X ℱ P → (∀ ω, X 0 ω = 0) →
        ∫⁻ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) ^ p ∂P ≤
          ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal |X n ω| ^ p ∂P

/-- **`DoobMaximalLp` holds**, with the sharp constant `(p/(p-1))^p`.  The identification
`⨆ k≤n ofReal|X k| = ofReal (sup' |X k|)` reduces the maximal to the real maximal of the
submartingale `|X|`, and the pin's `maximal_ineq` supplies the weak-type hypothesis of the
Marcinkiewicz upgrade. -/
theorem doobMaximalLp_holds : DoobMaximalLp := by
  intro p hp
  refine ⟨(p / (p - 1)) ^ p, by positivity, ?_⟩
  intro Ω _ P _ ℱ X n hM h0
  have hint : ∀ i, Integrable (X i) P := fun i => hM.integrable i
  have hbridge : ∀ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) =
      ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |X k ω|)) := by
    intro ω
    rw [ofReal_sup' Finset.nonempty_range_add_one]
    exact (sup'_range_eq_iSup n (fun k => ENNReal.ofReal |X k ω|)).symm
  rw [show (∫⁻ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) ^ p ∂P) =
      ∫⁻ ω, (ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |X k ω|))) ^ p ∂P from by
    apply lintegral_congr; intro ω; rw [hbridge ω]]
  refine marcinkiewicz_abstract_le P
    (fun ω => ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => |X k ω|)))
    (fun ω => ENNReal.ofReal |X n ω|) p hp ?_ ?_ ?_
  · have h := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k _ => ((hM.1 k).measurable.mono (ℱ.le k) le_rfl).abs)
    convert h.ennreal_ofReal using 1
    funext ω; rw [Finset.sup'_apply]
  · exact ((hM.1 n).measurable.mono (ℱ.le n) le_rfl).abs.ennreal_ofReal
  · intro t ht
    have hmeas : MeasurableSet {x : Ω | ENNReal.ofReal t ≤
        ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => |X k x|))} := by
      have h := Finset.measurable_sup' (s := Finset.range (n + 1))
        Finset.nonempty_range_add_one
        (fun k _ => ((hM.1 k).measurable.mono (ℱ.le k) le_rfl).abs)
      have hg : Measurable (fun x => ENNReal.ofReal ((Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k => |X k x|))) := by
        convert h.ennreal_ofReal using 1
        funext ω; rw [Finset.sup'_apply]
      exact measurableSet_le measurable_const hg
    rw [lintegral_indicator hmeas (fun x => ENNReal.ofReal |X n x|)]
    exact weakType_maximal P ℱ X n hM hint t ht

end DoobCopy

/-- The constant in the scalar Taylor-type bound. -/
def powK (p : ℝ) : ℝ := (2 : ℝ) ^ p * (p ^ 2 + p + 1)

lemma powK_pos {p : ℝ} (hp : 2 ≤ p) : 0 < powK p := by
  unfold powK
  have : (0 : ℝ) < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  positivity

lemma two_rpow_ge_one {p : ℝ} (hp : 2 ≤ p) : (1 : ℝ) ≤ (2 : ℝ) ^ p :=
  Real.one_le_rpow (by norm_num) (by linarith)

/-- Normalised scalar bound: `|1+s|^p ≤ 1 + p s + K (s² + |s|^p)`. -/
lemma pow_one_add_le {p : ℝ} (hp : 2 ≤ p) (s : ℝ) :
    |1 + s| ^ p ≤ 1 + p * s + powK p * (s ^ 2 + |s| ^ p) := by
  have hp0 : 0 < p := by linarith
  have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ p := two_rpow_ge_one hp
  have hK : powK p = (2 : ℝ) ^ p * (p ^ 2 + p + 1) := rfl
  have hspow : 0 ≤ |s| ^ p := Real.rpow_nonneg (abs_nonneg s) p
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  by_cases hs : 1 ≤ |s|
  · -- large `|s|`
    have h1 : |1 + s| ≤ 2 * |s| := by
      calc |1 + s| ≤ |1| + |s| := abs_add_le _ _
        _ = 1 + |s| := by simp
        _ ≤ 2 * |s| := by linarith
    have h2 : |1 + s| ^ p ≤ (2 * |s|) ^ p := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
    have h3 : (2 * |s|) ^ p = (2 : ℝ) ^ p * |s| ^ p := Real.mul_rpow (by norm_num) (abs_nonneg _)
    have h4 : |s| ≤ |s| ^ p := by
      have := Real.rpow_le_rpow_of_exponent_le hs (show (1 : ℝ) ≤ p by linarith)
      simpa using this
    have h5 : -(p * |s|) ≤ p * s := by
      have := neg_abs_le s
      nlinarith
    have h6 : (2 : ℝ) ^ p + p ≤ powK p := by
      rw [hK]
      have : (0 : ℝ) ≤ (2 : ℝ) ^ p * p ^ 2 := by positivity
      have h7 : p ≤ (2 : ℝ) ^ p * p := by nlinarith
      nlinarith
    have h8 : p * |s| ≤ p * |s| ^ p := mul_le_mul_of_nonneg_left h4 hp0.le
    have h9 : powK p * s ^ 2 ≥ 0 := mul_nonneg (powK_pos hp).le hs2
    have h10 : ((2 : ℝ) ^ p + p) * |s| ^ p ≤ powK p * |s| ^ p :=
      mul_le_mul_of_nonneg_right h6 hspow
    nlinarith
  · replace hs := not_le.mp hs
    have hs1 : -1 < s := by
      have := neg_abs_le s
      linarith
    have hs2' : s < 1 := by
      have := le_abs_self s
      linarith
    have hpos : 0 < 1 + s := by linarith
    rw [abs_of_pos hpos]
    have hexp : (1 + s) ^ p ≤ Real.exp (p * s) := by
      rw [Real.rpow_def_of_pos hpos]
      apply Real.exp_le_exp.mpr
      have := Real.log_le_sub_one_of_pos hpos
      nlinarith
    have hKp : p ^ 2 ≤ powK p := by
      rw [hK]
      have : (0 : ℝ) ≤ (2 : ℝ) ^ p * (p + 1) := by positivity
      nlinarith
    have hKs : 0 ≤ powK p * |s| ^ p := mul_nonneg (powK_pos hp).le hspow
    by_cases hps : |p * s| ≤ 1
    · have := Real.abs_exp_sub_one_sub_id_le hps
      have h1 : Real.exp (p * s) ≤ 1 + p * s + (p * s) ^ 2 := by
        have := (abs_le.mp this).2
        linarith
      have h2 : (p * s) ^ 2 = p ^ 2 * s ^ 2 := by ring
      have h3 : p ^ 2 * s ^ 2 ≤ powK p * s ^ 2 := mul_le_mul_of_nonneg_right hKp hs2
      nlinarith
    · replace hps := not_le.mp hps
      rcases lt_trichotomy s 0 with hneg | hzero | hposs
      · -- s < 0
        have h1 : (1 + s) ^ p ≤ 1 := Real.rpow_le_one hpos.le (by linarith) hp0.le
        have hps' : 1 < -(p * s) := by
          rw [abs_of_neg (by nlinarith)] at hps
          linarith
        have h4 : p ≤ powK p * (-s) := by
          have : p ^ 2 ≤ powK p := hKp
          nlinarith
        have h5 : 0 ≤ p * s + powK p * s ^ 2 := by
          nlinarith
        nlinarith
      · subst hzero
        norm_num at hps
      · have h1 : (1 + s) ^ p ≤ (2 : ℝ) ^ p :=
          Real.rpow_le_rpow hpos.le (by linarith) hp0.le
        have hps' : 1 < p * s := by
          rw [abs_of_pos (by positivity)] at hps
          exact hps
        have h2 : (2 : ℝ) ^ p ≤ powK p * s ^ 2 := by
          rw [hK]
          have h3 : 1 ≤ p ^ 2 * s ^ 2 := by nlinarith
          have h4 : (0 : ℝ) < (2 : ℝ) ^ p := by linarith
          nlinarith
        nlinarith

lemma abs_rpow_eq_mul_sq {p : ℝ} (x : ℝ) (hx : x ≠ 0) : |x| ^ p = |x| ^ (p - 2) * x ^ 2 := by
  have hpos : 0 < |x| := abs_pos.mpr hx
  have : p = (p - 2) + 2 := by ring
  calc |x| ^ p = |x| ^ ((p - 2) + 2) := by rw [← this]
    _ = |x| ^ (p - 2) * |x| ^ (2 : ℝ) := Real.rpow_add hpos _ _
    _ = |x| ^ (p - 2) * x ^ 2 := by rw [Real.rpow_two, sq_abs]

/-- The scalar Taylor-type bound for `|x + d|^p`, `p ≥ 2`. -/
theorem pow_add_le {p : ℝ} (hp : 2 ≤ p) (x d : ℝ) :
    |x + d| ^ p ≤ |x| ^ p + p * (|x| ^ (p - 2) * x) * d +
      powK p * (|x| ^ (p - 2) * d ^ 2 + |d| ^ p) := by
  have hp0 : 0 < p := by linarith
  have hKpos : 0 < powK p := powK_pos hp
  by_cases hx : x = 0
  · subst hx
    simp only [zero_add, abs_zero, mul_zero, zero_mul, add_zero]
    have h1 : 0 ≤ (0 : ℝ) ^ (p - 2) * d ^ 2 := mul_nonneg (Real.rpow_nonneg le_rfl _) (sq_nonneg _)
    have h2 : 0 ≤ |d| ^ p := Real.rpow_nonneg (abs_nonneg d) p
    have h3 : (1 : ℝ) ≤ powK p := by
      unfold powK
      have := two_rpow_ge_one hp
      nlinarith [sq_nonneg p]
    have h4 : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp0.ne'
    rw [h4, zero_add]
    nlinarith
  · have hxpos : 0 < |x| := abs_pos.mpr hx
    set s : ℝ := d / x with hs
    have hd : d = x * s := by rw [hs]; field_simp
    have hnorm := pow_one_add_le hp s
    have hxd : x + d = x * (1 + s) := by rw [hd]; ring
    have h1 : |x + d| ^ p = |x| ^ p * |1 + s| ^ p := by
      rw [hxd, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have h2 : |d| ^ p = |x| ^ p * |s| ^ p := by
      rw [hd, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    have h3 : |x| ^ (p - 2) * d ^ 2 = |x| ^ p * s ^ 2 := by
      rw [abs_rpow_eq_mul_sq (p := p) x hx, hd]; ring
    have h4 : |x| ^ (p - 2) * x * d = |x| ^ p * s := by
      rw [abs_rpow_eq_mul_sq (p := p) x hx, hd]; ring
    have hxp : 0 ≤ |x| ^ p := Real.rpow_nonneg (abs_nonneg x) p
    have h5 := mul_le_mul_of_nonneg_left hnorm hxp
    calc |x + d| ^ p = |x| ^ p * |1 + s| ^ p := h1
      _ ≤ |x| ^ p * (1 + p * s + powK p * (s ^ 2 + |s| ^ p)) := h5
      _ = |x| ^ p + p * (|x| ^ (p - 2) * x * d) +
            powK p * (|x| ^ (p - 2) * d ^ 2 + |d| ^ p) := by
          rw [h4, h3, h2]; ring
      _ = |x| ^ p + p * (|x| ^ (p - 2) * x) * d +
            powK p * (|x| ^ (p - 2) * d ^ 2 + |d| ^ p) := by ring

/-- Weighted Young inequality: `a^(p-2) v ≤ τ a^p + τ^(-(p-2)/2) v^(p/2)` for `p ≥ 2`. -/
theorem young_pow {p : ℝ} (hp : 2 ≤ p) {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) {τ : ℝ}
    (hτ : 0 < τ) :
    a ^ (p - 2) * v ≤ τ * a ^ p + τ ^ (-((p - 2) / 2)) * v ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have hw1 : 0 ≤ (p - 2) / p := div_nonneg (by linarith) hp0.le
  have hw2 : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
  have hw : (p - 2) / p + 2 / p = 1 := by field_simp; ring
  have hp1 : 0 ≤ τ * a ^ p := mul_nonneg hτ.le (Real.rpow_nonneg ha _)
  have hp2 : 0 ≤ τ ^ (-((p - 2) / 2)) * v ^ (p / 2) :=
    mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.rpow_nonneg hv _)
  have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 hp2 hw
  have e1 : (τ * a ^ p) ^ ((p - 2) / p) = τ ^ ((p - 2) / p) * a ^ (p - 2) := by
    rw [Real.mul_rpow hτ.le (Real.rpow_nonneg ha _), ← Real.rpow_mul ha]
    congr 2
    field_simp
  have e2 : (τ ^ (-((p - 2) / 2)) * v ^ (p / 2)) ^ (2 / p) = τ ^ (-((p - 2) / p)) * v := by
    rw [Real.mul_rpow (Real.rpow_nonneg hτ.le _) (Real.rpow_nonneg hv _),
      ← Real.rpow_mul hτ.le, ← Real.rpow_mul hv]
    have h1 : -((p - 2) / 2) * (2 / p) = -((p - 2) / p) := by field_simp
    have h2 : p / 2 * (2 / p) = 1 := by field_simp
    rw [h1, h2, Real.rpow_one]
  have e3 : τ ^ ((p - 2) / p) * τ ^ (-((p - 2) / p)) = 1 := by
    rw [← Real.rpow_add hτ]; simp
  have e4 : (τ * a ^ p) ^ ((p - 2) / p) * (τ ^ (-((p - 2) / 2)) * v ^ (p / 2)) ^ (2 / p)
      = a ^ (p - 2) * v := by
    rw [e1, e2]
    calc τ ^ ((p - 2) / p) * a ^ (p - 2) * (τ ^ (-((p - 2) / p)) * v)
        = (τ ^ ((p - 2) / p) * τ ^ (-((p - 2) / p))) * (a ^ (p - 2) * v) := by ring
      _ = a ^ (p - 2) * v := by rw [e3, one_mul]
  rw [e4] at h
  have hle1 : (p - 2) / p ≤ 1 := by linarith
  have hle2 : 2 / p ≤ 1 := by linarith
  calc a ^ (p - 2) * v ≤ (p - 2) / p * (τ * a ^ p) + 2 / p *
        (τ ^ (-((p - 2) / 2)) * v ^ (p / 2)) := h
    _ ≤ 1 * (τ * a ^ p) + 1 * (τ ^ (-((p - 2) / 2)) * v ^ (p / 2)) :=
        add_le_add (mul_le_mul_of_nonneg_right hle1 hp1) (mul_le_mul_of_nonneg_right hle2 hp2)
    _ = _ := by ring

/-- The one-step conditional variance `E[(X_{i+1} - X_i)² | ℱ_i]`. -/
def incVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  P[fun ω' => (X (i + 1) ω' - X i ω') ^ 2 | ℱ i]

/-- A bounded measurable real function is integrable on a probability space. -/
lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using h ω)

/-- The martingale difference `X (i+1) - X i` has zero conditional mean given `ℱ i`. -/
lemma condExp_diff_ae_zero {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} (hM : Martingale X ℱ P)
    (i : ℕ) : P[fun ω => X (i + 1) ω - X i ω | ℱ i] =ᵐ[P] 0 := by
  have h3 := condExp_sub (μ := P) (hM.integrable (i + 1)) (hM.integrable i) (ℱ i)
  have h1 : P[X (i + 1) | ℱ i] =ᵐ[P] X i := hM.condExp_ae_eq (Nat.le_succ i)
  have h2 : P[X i | ℱ i] = X i :=
    condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyMeasurable i) (hM.integrable i)
  filter_upwards [h3, h1] with ω e3 e1
  show P[X (i + 1) - X i | ℱ i] ω = 0
  rw [e3]
  simp only [Pi.sub_apply]
  rw [e1, h2, sub_self]

/-- A bounded increment satisfies `|d|^p ≤ b^(p-2) d²` for `p ≥ 2`. -/
lemma abs_rpow_le_mul_sq {p b : ℝ} (hp : 2 ≤ p) (d : ℝ) (hd : |d| ≤ b) :
    |d| ^ p ≤ b ^ (p - 2) * d ^ 2 := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) hd
  by_cases h0 : d = 0
  · subst h0
    have : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
    simp only [abs_zero, this]
    have : 0 ≤ b ^ (p - 2) := Real.rpow_nonneg hb0 _
    simp
  · rw [abs_rpow_eq_mul_sq (p := p) d h0]
    have : |d| ^ (p - 2) ≤ b ^ (p - 2) := Real.rpow_le_rpow (abs_nonneg _) hd hp2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- One step of the discrete Itô-type bound for `|X|^p`. -/
theorem step_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    {p b B : ℝ} (hp : 2 ≤ p) (i : ℕ) (hB0 : 0 ≤ B)
    (hB : ∀ ω, |X i ω| ≤ B) (hinc : ∀ ω, |X (i + 1) ω - X i ω| ≤ b) :
    ∫ ω, |X (i + 1) ω| ^ p ∂P ≤ ∫ ω, |X i ω| ^ p ∂P
      + powK p * ∫ ω, |X i ω| ^ (p - 2) *
          incVar P ℱ X i ω ∂P
      + powK p * b ^ (p - 2) * ∫ ω, incVar P ℱ X i ω ∂P := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hKpos : 0 < powK p := by
    unfold powK
    have : (0 : ℝ) < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hXm : ∀ j, Measurable (X j) := fun j => ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  set d : Ω → ℝ := fun ω => X (i + 1) ω - X i ω with hd
  have hdm : Measurable d := (hXm (i + 1)).sub (hXm i)
  set a : Ω → ℝ := fun ω => |X i ω| ^ (p - 2) with ha
  have ham : Measurable a := (hXm i).abs.pow_const _
  have ha_bdd : ∀ ω, |a ω| ≤ B ^ (p - 2) := by
    intro ω
    rw [ha]
    simp only
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hB ω) hp2
  have hBy : ∀ ω, |X (i + 1) ω| ≤ B + b := by
    intro ω
    have h1 : X (i + 1) ω = X i ω + (X (i + 1) ω - X i ω) := by ring
    calc |X (i + 1) ω| = |X i ω + (X (i + 1) ω - X i ω)| := by rw [← h1]
      _ ≤ |X i ω| + |X (i + 1) ω - X i ω| := abs_add_le _ _
      _ ≤ B + b := add_le_add (hB ω) (hinc ω)
  have hdI : Integrable d P := integrable_of_abs_le hdm hinc
  have hIq : Integrable (fun ω => d ω ^ 2) P := by
    refine integrable_of_abs_le (C := b ^ 2) (hdm.pow_const 2) fun ω => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hinc ω)).1 (abs_le.mp (hinc ω)).2
  have hIx : Integrable (fun ω => |X i ω| ^ p) P := by
    refine integrable_of_abs_le (C := B ^ p) ((hXm i).abs.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hB ω) hp0.le
  have hIy : Integrable (fun ω => |X (i + 1) ω| ^ p) P := by
    refine integrable_of_abs_le (C := (B + b) ^ p) ((hXm (i + 1)).abs.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hBy ω) hp0.le
  have hIh : Integrable (fun ω => a ω * d ω ^ 2) P :=
    hIq.bdd_mul ham.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using ha_bdd ω)
  have hIg : Integrable (fun ω => (a ω * X i ω) * d ω) P := by
    refine hdI.bdd_mul (ham.mul (hXm i)).aestronglyMeasurable
      (c := B ^ (p - 2) * B) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ha_bdd ω) (hB ω) (abs_nonneg _) (Real.rpow_nonneg hB0 _)
  -- pointwise bound
  have hpt : ∀ ω, |X (i + 1) ω| ^ p ≤ |X i ω| ^ p + p * ((a ω * X i ω) * d ω)
      + powK p * (a ω * d ω ^ 2) + powK p * b ^ (p - 2) * d ω ^ 2 := by
    intro ω
    have h1 := pow_add_le hp (X i ω) (d ω)
    have h2 : X i ω + d ω = X (i + 1) ω := by rw [hd]; ring
    rw [h2] at h1
    have h3 := abs_rpow_le_mul_sq hp (d ω) (hinc ω)
    have h4 : powK p * |d ω| ^ p ≤ powK p * (b ^ (p - 2) * d ω ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hKpos.le
    have h5 : p * (|X i ω| ^ (p - 2) * X i ω) * d ω = p * ((a ω * X i ω) * d ω) := by
      rw [ha]; ring
    have h6 : powK p * (|X i ω| ^ (p - 2) * d ω ^ 2 + |d ω| ^ p)
        = powK p * (a ω * d ω ^ 2) + powK p * |d ω| ^ p := by rw [ha]; ring
    nlinarith
  have hI2 := hIg.const_mul p
  have hI3 := hIh.const_mul (powK p)
  have hI4 := hIq.const_mul (powK p * b ^ (p - 2))
  have hS12 : Integrable (fun ω => |X i ω| ^ p + p * ((a ω * X i ω) * d ω)) P := hIx.add hI2
  have hS123 : Integrable (fun ω => |X i ω| ^ p + p * ((a ω * X i ω) * d ω)
      + powK p * (a ω * d ω ^ 2)) P := hS12.add hI3
  have hS1234 : Integrable (fun ω => |X i ω| ^ p + p * ((a ω * X i ω) * d ω)
      + powK p * (a ω * d ω ^ 2) + powK p * b ^ (p - 2) * d ω ^ 2) P := hS123.add hI4
  have hR : ∫ ω, (|X i ω| ^ p + p * ((a ω * X i ω) * d ω) + powK p * (a ω * d ω ^ 2)
        + powK p * b ^ (p - 2) * d ω ^ 2) ∂P
      = ∫ ω, |X i ω| ^ p ∂P + p * ∫ ω, (a ω * X i ω) * d ω ∂P
        + powK p * ∫ ω, a ω * d ω ^ 2 ∂P + powK p * b ^ (p - 2) * ∫ ω, d ω ^ 2 ∂P := by
    rw [integral_add hS123 hI4, integral_add hS12 hI3,
      integral_add hIx hI2, integral_const_mul, integral_const_mul, integral_const_mul]
  have hmono : ∫ ω, |X (i + 1) ω| ^ p ∂P ≤ ∫ ω, (|X i ω| ^ p + p * ((a ω * X i ω) * d ω)
      + powK p * (a ω * d ω ^ 2) + powK p * b ^ (p - 2) * d ω ^ 2) ∂P :=
    integral_mono hIy hS1234 hpt
  -- the three identities
  have hSMa : StronglyMeasurable[ℱ i] a :=
    (continuous_abs.rpow_const (fun _ => Or.inr hp2)).comp_stronglyMeasurable
      (hM.stronglyMeasurable i)
  have hSM : StronglyMeasurable[ℱ i] (fun ω => a ω * X i ω) :=
    hSMa.mul (hM.stronglyMeasurable i)
  have hg0 : ∫ ω, (a ω * X i ω) * d ω ∂P = 0 := by
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hSM
      (g := d) (by exact hIg) hdI
    have h2 := condExp_diff_ae_zero hM i
    calc ∫ ω, (a ω * X i ω) * d ω ∂P = ∫ ω, P[(fun ω => a ω * X i ω) * d | ℱ i] ω ∂P :=
          (integral_condExp (ℱ.le i)).symm
      _ = ∫ ω, 0 ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [h1, h2] with ω e1 e2
          rw [e1]
          simp only [Pi.mul_apply]
          have : P[d | ℱ i] ω = 0 := e2
          rw [this, mul_zero]
      _ = 0 := integral_zero _ _
  have hh : ∫ ω, a ω * d ω ^ 2 ∂P = ∫ ω, a ω *
      incVar P ℱ X i ω ∂P := by
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hSMa
      (g := fun ω => d ω ^ 2) (by exact hIh) hIq
    calc ∫ ω, a ω * d ω ^ 2 ∂P = ∫ ω, P[a * (fun ω => d ω ^ 2) | ℱ i] ω ∂P :=
          (integral_condExp (ℱ.le i)).symm
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h1] with ω e1
          rw [e1]
          rfl
  have hq : ∫ ω, d ω ^ 2 ∂P = ∫ ω, incVar P ℱ X i ω ∂P :=
    (integral_condExp (ℱ.le i) (f := fun ω => d ω ^ 2)).symm
  calc ∫ ω, |X (i + 1) ω| ^ p ∂P ≤ _ := hmono
    _ = _ := hR
    _ = _ := by rw [hg0, hh, hq]; ring

/-- Summation of the one-step bound. -/
theorem moment_sum_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    (h0 : ∀ ω, X 0 ω = 0) {p b : ℝ} (hp : 2 ≤ p) (hb : 0 < b) {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) (m : ℕ) (hm : m ≤ n) :
    ∫ ω, |X m ω| ^ p ∂P ≤
      powK p * ∑ i ∈ Finset.range m, ∫ ω, |X i ω| ^ (p - 2) *
          incVar P ℱ X i ω ∂P
      + powK p * b ^ (p - 2) * ∑ i ∈ Finset.range m,
          ∫ ω, incVar P ℱ X i ω ∂P := by
  have hp0 : 0 < p := by linarith
  induction m with
  | zero =>
      simp only [h0, abs_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      rw [Real.zero_rpow hp0.ne']
      simp
  | succ m ih =>
      have hmn : m < n := hm
      have ih' := ih hmn.le
      have hbd := abs_le_of_increments h0 hinc m hmn.le
      have hB0 : 0 ≤ (m : ℝ) * b := by positivity
      have hstep := step_integral_le P ℱ X hM hp m hB0 hbd (hinc m hmn)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith [hstep, ih']

/-- The one-step conditional variances lie in `[0, b²]` almost surely. -/
theorem incVar_ae_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    {b : ℝ} {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) :
    ∀ᵐ ω ∂P, ∀ i, i < n → 0 ≤ incVar P ℱ X i ω ∧ incVar P ℱ X i ω ≤ b ^ 2 := by
  have hXm : ∀ j, Measurable (X j) := fun j =>
    ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  refine ae_all_iff.mpr fun i => ?_
  by_cases hi : i < n
  · have hdm : Measurable (fun ω => (X (i + 1) ω - X i ω) ^ 2) :=
      ((hXm (i + 1)).sub (hXm i)).pow_const 2
    have hdI : Integrable (fun ω => (X (i + 1) ω - X i ω) ^ 2) P := by
      refine integrable_of_abs_le (C := b ^ 2) hdm fun ω => ?_
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp (hinc i hi ω)).1 (abs_le.mp (hinc i hi ω)).2
    have h1 := condExp_nonneg (μ := P) (m := ℱ i)
      (f := fun ω => (X (i + 1) ω - X i ω) ^ 2) (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    have h2 := condExp_mono (μ := P) (m := ℱ i) hdI (integrable_const (b ^ 2))
      (Filter.Eventually.of_forall fun ω =>
        sq_le_sq' (abs_le.mp (hinc i hi ω)).1 (abs_le.mp (hinc i hi ω)).2)
    have h3 := condExp_const (μ := P) (ℱ.le i) (b ^ 2)
    filter_upwards [h1, h2] with ω e1 e2
    intro _
    refine ⟨by simpa [incVar] using e1, ?_⟩
    rw [h3] at e2
    simpa [incVar] using e2
  · exact Filter.Eventually.of_forall fun ω h => absurd h hi

/-- The conditional quadratic variation lies in `[0, n b²]` almost surely. -/
theorem condQvar_ae_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    {b : ℝ} {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) :
    ∀ᵐ ω ∂P, 0 ≤ condQvar P ℱ X n ω ∧ condQvar P ℱ X n ω ≤ n * b ^ 2 := by
  filter_upwards [incVar_ae_bounds P ℱ X hM hinc] with ω hω
  have hsum : condQvar P ℱ X n ω = ∑ i ∈ Finset.range n, incVar P ℱ X i ω := rfl
  rw [hsum]
  refine ⟨Finset.sum_nonneg fun i hi => (hω i (Finset.mem_range.mp hi)).1, ?_⟩
  calc ∑ i ∈ Finset.range n, incVar P ℱ X i ω ≤ ∑ i ∈ Finset.range n, b ^ 2 :=
        Finset.sum_le_sum fun i hi => (hω i (Finset.mem_range.mp hi)).2
    _ = n * b ^ 2 := by simp

/-- Nonnegative powers of the conditional quadratic variation are integrable. -/
theorem integrable_condQvar_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) {b : ℝ} {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => condQvar P ℱ X n ω ^ q) P := by
  refine Integrable.of_bound ((measurable_condQvar P ℱ X n).pow_const _).aestronglyMeasurable
    (((n : ℝ) * b ^ 2) ^ q) ?_
  filter_upwards [condQvar_ae_bounds P ℱ X hM hinc] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hω.1 _)]
  exact Real.rpow_le_rpow hω.1 hω.2 hq

/-- Real-analytic core: the `L^p` Itô-type bound before absorption. -/
theorem moment_bound_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    (h0 : ∀ ω, X 0 ω = 0) {p b D τ : ℝ} (hp : 2 ≤ p) (hb : 0 < b) (hτ : 0 < τ) {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b)
    (hDoob : ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |X k ω|)) ^ p ∂P ≤ D * ∫ ω, |X n ω| ^ p ∂P) :
    ∫ ω, |X n ω| ^ p ∂P ≤ powK p * τ * D * ∫ ω, |X n ω| ^ p ∂P
      + powK p * (τ ^ (-((p - 2) / 2)) + 1) * ∫ ω, condQvar P ℱ X n ω ^ (p / 2) ∂P
      + powK p * b ^ p := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hK := powK_pos hp
  have hb0 : 0 ≤ b := hb.le
  have hXm : ∀ j, Measurable (X j) := fun j =>
    ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  set M : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |X k ω|) with hMdef
  have hbd : ∀ k, k ≤ n → ∀ ω, |X k ω| ≤ k * b := abs_le_of_increments h0 hinc
  have hMle : ∀ k, k ≤ n → ∀ ω, |X k ω| ≤ M ω := fun k hk ω =>
    Finset.le_sup' (fun k => |X k ω|) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => le_trans (abs_nonneg _) (hMle 0 (Nat.zero_le _) ω)
  have hMbd : ∀ ω, M ω ≤ n * b := fun ω => Finset.sup'_le _ _ (fun k hk => by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc |X k ω| ≤ k * b := hbd k hk' ω
      _ ≤ n * b := by
        have : (k : ℝ) ≤ n := by exact_mod_cast hk'
        nlinarith)
  have hMm : Measurable M := by
    have h := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k _ => (hXm k).abs)
    convert h using 1
    funext ω
    rw [Finset.sup'_apply]
  set V : Ω → ℝ := condQvar P ℱ X n with hVdef
  have hVsum : ∀ ω, V ω = ∑ i ∈ Finset.range n, incVar P ℱ X i ω := fun ω => rfl
  have hσI : ∀ i, Integrable (incVar P ℱ X i) P := fun i => integrable_condExp
  have hσ_ae : ∀ᵐ ω ∂P, ∀ i, i < n → 0 ≤ incVar P ℱ X i ω ∧ incVar P ℱ X i ω ≤ b ^ 2 :=
    incVar_ae_bounds P ℱ X hM hinc
  have hV_ae : ∀ᵐ ω ∂P, 0 ≤ V ω ∧ V ω ≤ n * b ^ 2 := condQvar_ae_bounds P ℱ X hM hinc
  have hVm : Measurable V := measurable_condQvar P ℱ X n
  have hVI : Integrable V P := by
    have : V = fun ω => ∑ i ∈ Finset.range n, incVar P ℱ X i ω := funext hVsum
    rw [this]
    exact integrable_finsetSum _ fun i _ => hσI i
  have hTI : ∀ i, i < n → Integrable (fun ω => |X i ω| ^ (p - 2) * incVar P ℱ X i ω) P := by
    intro i hi
    refine (hσI i).bdd_mul ((hXm i).abs.pow_const _).aestronglyMeasurable
      (c := ((i : ℝ) * b) ^ (p - 2)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hbd i hi.le ω) hp2
  have hmsum := moment_sum_bound P ℱ X hM h0 hp hb hinc n le_rfl
  have hSa : ∑ i ∈ Finset.range n, ∫ ω, |X i ω| ^ (p - 2) * incVar P ℱ X i ω ∂P
      = ∫ ω, ∑ i ∈ Finset.range n, |X i ω| ^ (p - 2) * incVar P ℱ X i ω ∂P :=
    (integral_finsetSum _ fun i hi => hTI i (Finset.mem_range.mp hi)).symm
  have hSc : ∑ i ∈ Finset.range n, ∫ ω, incVar P ℱ X i ω ∂P = ∫ ω, V ω ∂P := by
    have : V = fun ω => ∑ i ∈ Finset.range n, incVar P ℱ X i ω := funext hVsum
    rw [this]
    exact (integral_finsetSum _ fun i _ => hσI i).symm
  have hMVI : Integrable (fun ω => M ω ^ (p - 2) * V ω) P := by
    refine hVI.bdd_mul ((hMm.pow_const _).aestronglyMeasurable)
      (c := ((n : ℝ) * b) ^ (p - 2)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hM0 ω) _)]
    exact Real.rpow_le_rpow (hM0 ω) (hMbd ω) hp2
  have hMpI : Integrable (fun ω => M ω ^ p) P := by
    refine integrable_of_abs_le (C := ((n : ℝ) * b) ^ p) (hMm.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (hM0 ω) _)]
    exact Real.rpow_le_rpow (hM0 ω) (hMbd ω) hp0.le
  have hVpI : Integrable (fun ω => V ω ^ (p / 2)) P :=
    integrable_condQvar_rpow P ℱ X hM hinc (by linarith)
  have hd_ae : ∀ᵐ ω ∂P, ∑ i ∈ Finset.range n, |X i ω| ^ (p - 2) * incVar P ℱ X i ω
      ≤ M ω ^ (p - 2) * V ω := by
    filter_upwards [hσ_ae] with ω hω
    rw [hVsum ω, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hMle i hi'.le ω) hp2) (hω i hi').1
  have he_ae : ∀ᵐ ω ∂P, M ω ^ (p - 2) * V ω ≤
      τ * M ω ^ p + τ ^ (-((p - 2) / 2)) * V ω ^ (p / 2) := by
    filter_upwards [hV_ae] with ω hω
    exact young_pow hp (hM0 ω) hω.1 hτ
  have hf_ae : ∀ᵐ ω ∂P, b ^ (p - 2) * V ω ≤ b ^ p + V ω ^ (p / 2) := by
    filter_upwards [hV_ae] with ω hω
    have := young_pow hp hb0 hω.1 (zero_lt_one' ℝ)
    simpa using this
  have hIa : ∫ ω, ∑ i ∈ Finset.range n, |X i ω| ^ (p - 2) * incVar P ℱ X i ω ∂P
      ≤ τ * ∫ ω, M ω ^ p ∂P + τ ^ (-((p - 2) / 2)) * ∫ ω, V ω ^ (p / 2) ∂P := by
    calc _ ≤ ∫ ω, M ω ^ (p - 2) * V ω ∂P := by
          refine integral_mono_ae ?_ hMVI hd_ae
          have : (fun ω => ∑ i ∈ Finset.range n, |X i ω| ^ (p - 2) * incVar P ℱ X i ω)
              = fun ω => ∑ i ∈ Finset.range n, |X i ω| ^ (p - 2) * incVar P ℱ X i ω := rfl
          exact integrable_finsetSum _ fun i hi => hTI i (Finset.mem_range.mp hi)
      _ ≤ ∫ ω, (τ * M ω ^ p + τ ^ (-((p - 2) / 2)) * V ω ^ (p / 2)) ∂P :=
          integral_mono_ae hMVI ((hMpI.const_mul τ).add (hVpI.const_mul _)) he_ae
      _ = _ := by
          rw [integral_add (hMpI.const_mul τ) (hVpI.const_mul _), integral_const_mul,
            integral_const_mul]
  have hIb : b ^ (p - 2) * ∫ ω, V ω ∂P ≤ b ^ p + ∫ ω, V ω ^ (p / 2) ∂P := by
    calc b ^ (p - 2) * ∫ ω, V ω ∂P = ∫ ω, b ^ (p - 2) * V ω ∂P := (integral_const_mul _ _).symm
      _ ≤ ∫ ω, (b ^ p + V ω ^ (p / 2)) ∂P :=
          integral_mono_ae (hVI.const_mul _) ((integrable_const _).add hVpI) hf_ae
      _ = b ^ p + ∫ ω, V ω ^ (p / 2) ∂P := by
          rw [integral_add (integrable_const _) hVpI]
          simp
  have hMp : τ * ∫ ω, M ω ^ p ∂P ≤ τ * (D * ∫ ω, |X n ω| ^ p ∂P) :=
    mul_le_mul_of_nonneg_left hDoob hτ.le
  rw [hSa] at hmsum
  rw [hSc] at hmsum
  have h1 := mul_le_mul_of_nonneg_left hIa hK.le
  have h2 := mul_le_mul_of_nonneg_left hMp hK.le
  have h3 := mul_le_mul_of_nonneg_left hIb hK.le
  nlinarith [hmsum, h1, h2, h3]

/-- Real-valued form of Doob's `L^p` maximal inequality. -/
theorem doob_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (hM : Martingale X ℱ P)
    (h0 : ∀ ω, X 0 ω = 0) {p b D : ℝ} (hp : 0 ≤ p) (hb : 0 < b) (hD : 0 ≤ D) {n : ℕ}
    (hinc : ∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b)
    (hDoob : ∫⁻ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) ^ p ∂P ≤
      ENNReal.ofReal D * ∫⁻ ω, ENNReal.ofReal |X n ω| ^ p ∂P) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => |X k ω|)) ^ p ∂P ≤ D * ∫ ω, |X n ω| ^ p ∂P := by
  have hb0 : 0 ≤ b := hb.le
  have hXm : ∀ j, Measurable (X j) := fun j =>
    ((hM.stronglyMeasurable j).mono (ℱ.le j)).measurable
  set M : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |X k ω|) with hMdef
  have hbd : ∀ k, k ≤ n → ∀ ω, |X k ω| ≤ k * b := abs_le_of_increments h0 hinc
  have hMle : ∀ k, k ≤ n → ∀ ω, |X k ω| ≤ M ω := fun k hk ω =>
    Finset.le_sup' (fun k => |X k ω|) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => le_trans (abs_nonneg _) (hMle 0 (Nat.zero_le _) ω)
  have hMbd : ∀ ω, M ω ≤ n * b := fun ω => Finset.sup'_le _ _ (fun k hk => by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc |X k ω| ≤ k * b := hbd k hk' ω
      _ ≤ n * b := by
        have : (k : ℝ) ≤ n := by exact_mod_cast hk'
        nlinarith)
  have hMm : Measurable M := by
    have h := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k _ => (hXm k).abs)
    convert h using 1
    funext ω
    rw [Finset.sup'_apply]
  have hMpI : Integrable (fun ω => M ω ^ p) P := by
    refine integrable_of_abs_le (C := ((n : ℝ) * b) ^ p) (hMm.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (hM0 ω) _)]
    exact Real.rpow_le_rpow (hM0 ω) (hMbd ω) hp
  have hXnI : Integrable (fun ω => |X n ω| ^ p) P := by
    refine integrable_of_abs_le (C := ((n : ℝ) * b) ^ p) ((hXm n).abs.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hbd n le_rfl ω) hp
  have hbridge : ∀ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) = ENNReal.ofReal (M ω) := by
    intro ω
    rw [hMdef]
    simp only
    rw [ofReal_sup' Finset.nonempty_range_add_one]
    exact (sup'_range_eq_iSup n (fun k => ENNReal.ofReal |X k ω|)).symm
  have hL : ENNReal.ofReal (∫ ω, M ω ^ p ∂P) = ∫⁻ ω, (⨆ k ≤ n, ENNReal.ofReal |X k ω|) ^ p ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hMpI
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hM0 ω) _)]
    refine lintegral_congr fun ω => ?_
    rw [hbridge ω, ENNReal.ofReal_rpow_of_nonneg (hM0 ω) hp]
  have hR : ENNReal.ofReal (∫ ω, |X n ω| ^ p ∂P) = ∫⁻ ω, ENNReal.ofReal |X n ω| ^ p ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hXnI
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp]
  have hXn0 : 0 ≤ ∫ ω, |X n ω| ^ p ∂P :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  rw [← hL, ← hR, ← ENNReal.ofReal_mul hD] at hDoob
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hD hXn0)).mp hDoob

/-- **The terminal moment bound with randomised variance proxy** (the peeling summation bound,
equivalently the Burkholder–Rosenthal inequality for `p ≥ 2`): for a martingale `X` from `0` with
increments bounded by `b`,
`E |X_n|^p ≤ C_p (E (condQvar X n)^{p/2} + b^p)`.  The two dyadic-band hypotheses are
tautologies and are not used. -/
def PeelingSummationBound : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ) (n : ℕ) {b : ℝ}, 0 < b →
      Martingale X ℱ P → (∀ ω, X 0 ω = 0) →
      (∀ i, i < n → ∀ ω, |X (i + 1) ω - X i ω| ≤ b) →
      (∀ k : ℕ, P {ω | condQvar P ℱ X n ω < (2 : ℝ) ^ k} ≤
        P {ω | condQvar P ℱ X n ω < (2 : ℝ) ^ (k + 1)}) →
      (∀ k : ℕ, {ω | condQvar P ℱ X n ω ≤ (2 : ℝ) ^ (k + 1)} ⊆
        {ω | condQvar P ℱ X n ω < (2 : ℝ) ^ (k + 2)}) →
        ∫⁻ ω, ENNReal.ofReal (|X n ω|) ^ p ∂P ≤
          ENNReal.ofReal C *
            (∫⁻ ω, ENNReal.ofReal (condQvar P ℱ X n ω) ^ (p / 2) ∂P + ENNReal.ofReal (b ^ p))

/-- **`PeelingSummationBound` holds.**  The proof is the discrete Itô-type estimate for `|X|^p`
(`pow_add_le`), summed along the martingale (`moment_sum_bound`), combined with Young's inequality,
Doob's `L^p` maximal inequality (`doobMaximalLp_holds`) and absorption of the maximal term. -/
theorem peelingSummationBound_holds : PeelingSummationBound := by
  intro p hp
  have hp0 : 0 < p := by linarith
  obtain ⟨D, hDpos, hD⟩ := doobMaximalLp_holds p (by linarith)
  have hK : 0 < powK p := powK_pos hp
  set τ : ℝ := 1 / (2 * powK p * D) with hτdef
  have hτ : 0 < τ := by positivity
  have hμ : 0 ≤ τ ^ (-((p - 2) / 2)) := Real.rpow_nonneg hτ.le _
  refine ⟨2 * powK p * (τ ^ (-((p - 2) / 2)) + 1), by positivity, ?_⟩
  intro Ω _ P _ ℱ X n b hb hM h0 hinc _ _
  have hDoob := doob_real P ℱ X hM h0 hp0.le hb hDpos.le hinc (hD P ℱ X n hM h0)
  have hcore := moment_bound_core P ℱ X hM h0 hp hb hτ hinc hDoob
  have hhalf : powK p * τ * D = 1 / 2 := by
    rw [hτdef]
    field_simp
  rw [hhalf] at hcore
  set A : ℝ := ∫ ω, |X n ω| ^ p ∂P with hA
  set B : ℝ := ∫ ω, condQvar P ℱ X n ω ^ (p / 2) ∂P with hB
  have hVpI : Integrable (fun ω => condQvar P ℱ X n ω ^ (p / 2)) P :=
    integrable_condQvar_rpow P ℱ X hM hinc (by linarith)
  have hVae : ∀ᵐ ω ∂P, 0 ≤ condQvar P ℱ X n ω := by
    filter_upwards [condQvar_ae_bounds P ℱ X hM hinc] with ω hω using hω.1
  have hB0 : 0 ≤ B := integral_nonneg_of_ae (by
    filter_upwards [hVae] with ω hω using Real.rpow_nonneg hω _)
  have hbp : 0 ≤ b ^ p := Real.rpow_nonneg hb.le _
  have hAle : A ≤ 2 * powK p * (τ ^ (-((p - 2) / 2)) + 1) * (B + b ^ p) := by
    have h1 : 0 ≤ powK p * τ ^ (-((p - 2) / 2)) * B := by positivity
    have h2 : 0 ≤ powK p * b ^ p := by positivity
    nlinarith [hcore]
  have hXnI : Integrable (fun ω => |X n ω| ^ p) P := by
    have hXm : Measurable (X n) := ((hM.stronglyMeasurable n).mono (ℱ.le n)).measurable
    refine integrable_of_abs_le (C := ((n : ℝ) * b) ^ p) (hXm.abs.pow_const p) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (abs_le_of_increments h0 hinc n le_rfl ω) hp0.le
  have hL : ∫⁻ ω, ENNReal.ofReal (|X n ω|) ^ p ∂P = ENNReal.ofReal A := by
    rw [hA, ofReal_integral_eq_lintegral_ofReal hXnI
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
  have hRV : ∫⁻ ω, ENNReal.ofReal (condQvar P ℱ X n ω) ^ (p / 2) ∂P = ENNReal.ofReal B := by
    rw [hB, ofReal_integral_eq_lintegral_ofReal hVpI
      (by filter_upwards [hVae] with ω hω using Real.rpow_nonneg hω _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hVae] with ω hω
    rw [ENNReal.ofReal_rpow_of_nonneg hω (by linarith)]
  rw [hL, hRV, ← ENNReal.ofReal_add hB0 hbp,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hAle


end

end LatticeProb.Process.RandomizedFreedman
