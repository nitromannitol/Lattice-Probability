import LatticeProb.Prob.Process.BDGSkeleton

/-!
# Square-function bounds and the Burkholder–Davis–Gundy inequality for continuous martingales

Ported from the vertex-reinforced walk development. The square-function maximal bound for exponents
`p ≥ 2` and `1 < p < 2`, the lower and full-sum assembly of the stopped skeleton, and the main
theorem `burkholderDavisGundy_holds`, which proves the Burkholder–Davis–Gundy inequality for
continuous martingales in terminal-value form.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process.StoppedSkeleton.StoppedLp

noncomputable section

/-- The stopped process at a finite stopping time `ρ` is the process read at `min u (ρ ω)`. -/
theorem stoppedProcess_coe {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => (ρ ω : WithTop ℝ≥0)) u ω = X (min u (ρ ω)) ω := by
  show X (min (u : WithTop ℝ≥0) (ρ ω : WithTop ℝ≥0)).untopA ω = _
  rw [← WithTop.coe_min]
  rfl

/-- If `ρ` is the clipped time `min τ t` and `u ≤ t`, then the stopped process at time `u` is the
process read at `min u (ρ ω)`. -/
theorem stoppedProcess_eq_of_clip {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    {t u : ℝ≥0} (hu : u ≤ t) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0)) (ω : Ω) :
    stoppedProcess X τ u ω = X (min u (ρ ω)) ω := by
  have h : min (u : WithTop ℝ≥0) (τ ω) = ((min u (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_min, hρ ω, min_comm (τ ω), ← min_assoc,
      min_eq_left (WithTop.coe_le_coe.2 hu)]
  show X (min (u : WithTop ℝ≥0) (τ ω)).untopA ω = _
  rw [h]
  rfl

/-- The dyadic upper approximations of the clipped stopping time `min τ t` are stopping times. -/
theorem isStoppingTime_dyUp_clip {Ω : Type} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (t : ℝ≥0) (ρ : Ω → ℝ≥0) (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0))
    (m : ℕ) :
    IsStoppingTime ℱ fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have hρst : IsStoppingTime ℱ fun ω => (ρ ω : ℝ≥0∞) := by
    have h := hτ.min_const t
    have e : (fun ω => (ρ ω : WithTop ℝ≥0)) = fun ω => min (τ ω) (t : WithTop ℝ≥0) := funext hρ
    rw [← e] at h
    exact h
  exact LatticeProb.isStoppingTime_dyUp hρst m

/-- The clipped stopping time `min τ t` is finite: it is the coercion of a nonnegative real. -/
theorem exists_clip {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    ∃ ρ : Ω → ℝ≥0, ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0) := by
  have hex : ∀ ω, ∃ r : ℝ≥0, (r : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0) := fun ω =>
    WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
  choose ρ hρ using hex
  exact ⟨ρ, hρ⟩

/-- Pointwise along each path, the stopped process at the dyadic upper approximations of the clipped
time `min τ t` converges, at time `t`, to the stopped process at `τ`, by path continuity. -/
theorem tendsto_stoppedProcess_dyUp {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (hcont : ∀ ω, Continuous fun t => X t ω) {t : ℝ≥0} (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0)) (ω : Ω) :
    Tendsto (fun m : ℕ => stoppedProcess X
      (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) t ω) atTop
      (𝓝 (stoppedProcess X τ t ω)) := by
  simp_rw [stoppedProcess_coe X (fun ω => LatticeProb.dyUp _ (ρ ω)) t ω]
  rw [stoppedProcess_eq_of_clip X τ le_rfl ρ hρ ω]
  exact ((hcont ω).continuousAt.tendsto).comp
    (tendsto_const_nhds.min (LatticeProb.tendsto_dyUp (ρ ω)))

/-- Stopping at a countably valued stopping time does not increase the `Lᵖ` norm at a fixed time
`u`, and the stopped process is almost everywhere strongly measurable there. Optional sampling
identifies the stopped process at time `u` with a conditional expectation of `X u`. -/
theorem eLpNorm_stoppedProcess_le_of_countable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (hX : Martingale X ℱ P) (σ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime ℱ σ)
    (hcount : (Set.range σ).Countable) (u : ℝ≥0) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    AEStronglyMeasurable (stoppedProcess X σ u) P ∧
      eLpNorm (stoppedProcess X σ u) q P ≤ eLpNorm (X u) q P := by
  have hτ : IsStoppingTime ℱ (fun ω => min (u : WithTop ℝ≥0) (σ ω)) :=
    (isStoppingTime_const ℱ u).min hσ
  have hle : ∀ ω, min (u : WithTop ℝ≥0) (σ ω) ≤ u := fun ω => min_le_left _ _
  have hcm : (Set.range fun ω => min (u : WithTop ℝ≥0) (σ ω)).Countable := by
    refine (hcount.image fun a => min (u : WithTop ℝ≥0) a).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hae : stoppedProcess X σ u =ᵐ[P] P[X u | hτ.measurableSpace] :=
    hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hle hcm
  refine ⟨?_, ?_⟩
  · exact ((stronglyMeasurable_condExp (f := X u) (μ := P)).mono
      (hτ.measurableSpace_le_of_le hle)).aestronglyMeasurable.congr hae.symm
  · rw [eLpNorm_congr_ae hae]
    exact eLpNorm_condExp_le_eLpNorm (X u) hq

/-- The `Lᵖ` norm of a path-continuous martingale stopped at any stopping time is at most that of
`X t`, in `eLpNorm` form, for an exponent `q ≥ 1`. -/
theorem eLpNorm_stoppedProcess_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (hX : Martingale X ℱ P) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (stoppedProcess X τ t) q P ≤ eLpNorm (X t) q P := by
  obtain ⟨ρ, hρ⟩ := exists_clip τ t
  have hσ : ∀ m : ℕ, IsStoppingTime ℱ
      fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0) :=
    fun m => isStoppingTime_dyUp_clip ℱ τ hτ t ρ hρ m
  have hb := fun m : ℕ => eLpNorm_stoppedProcess_le_of_countable P ℱ X hX _ (hσ m)
    (LatticeProb.countable_range_dyUp m ρ) t hq
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => stoppedProcess X
      (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) t ω) atTop
      (𝓝 (stoppedProcess X τ t ω)) :=
    Eventually.of_forall fun ω => tendsto_stoppedProcess_dyUp X τ hcont ρ hρ ω
  exact Lp.eLpNorm_le_of_ae_tendsto (C := eLpNorm (X t) q P)
    (Eventually.of_forall fun m => (hb m).2) (fun m => (hb m).1)
    (aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hb m).1) hlim) hlim

/-- The stopped process of a path-continuous martingale is a.e. strongly measurable. -/
theorem aestronglyMeasurable_stoppedProcess {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (hX : Martingale X ℱ P) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    AEStronglyMeasurable (stoppedProcess X τ t) P := by
  obtain ⟨ρ, hρ⟩ := exists_clip τ t
  have hσ : ∀ m : ℕ, IsStoppingTime ℱ
      fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0) :=
    fun m => isStoppingTime_dyUp_clip ℱ τ hτ t ρ hρ m
  have hb := fun m : ℕ => eLpNorm_stoppedProcess_le_of_countable P ℱ X hX _ (hσ m)
    (LatticeProb.countable_range_dyUp m ρ) t hq
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => stoppedProcess X
      (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) t ω) atTop
      (𝓝 (stoppedProcess X τ t ω)) :=
    Eventually.of_forall fun ω => tendsto_stoppedProcess_dyUp X τ hcont ρ hρ ω
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hb m).1) hlim

/-- **Stopping a continuous martingale contracts `Lᵖ`, `p ≥ 1`.** -/
theorem stoppedLpContraction_holds : StoppedLpContraction := by
  intro Ω inst P hP ℱ X τ hX hcont hτ t p hp
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hq : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h := eLpNorm_stoppedProcess_le P ℱ X τ hX hcont hτ t hq
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hnetop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hS := aestronglyMeasurable_stoppedProcess P ℱ X τ hX hcont hτ t hq
  have hXt : AEStronglyMeasurable (X t) P :=
    ((hX.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hS,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hXt, ENNReal.toReal_ofReal hp0.le] at h
  have h' := (ENNReal.rpow_le_rpow_iff (one_div_pos.2 hp0)).1 h
  simpa only [Real.enorm_eq_ofReal_abs] using h'

end

end LatticeProb.Process.StoppedSkeleton.StoppedLp

namespace LatticeProb.Process.StoppedSkeleton.FullSum

noncomputable section

/-- The last grid time `t_{2^n}` is `T`. -/
theorem gridT_last (T : ℝ≥0) (n : ℕ) : gridT T n (2 ^ n) = T := by
  simp [gridT]

/-- Consecutive grid times differ by `T / 2^n`. -/
theorem gridT_succ_sub (T : ℝ≥0) (n k : ℕ) :
    ((gridT T n (k + 1) : ℝ≥0) : ℝ) - ((gridT T n k : ℝ≥0) : ℝ) = (T : ℝ) / 2 ^ n := by
  simp only [gridT, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat]
  push_cast
  ring

/-- The grid times are monotone in the index. -/
theorem gridT_mono (T : ℝ≥0) (n : ℕ) : Monotone (gridT T n) := by
  intro i j hij
  unfold gridT
  have : ((i : ℕ) : ℝ≥0) ≤ ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
  gcongr

/-- Grid times with index at most `2^n` do not exceed `T`. -/
theorem gridT_le (T : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 ^ n) : gridT T n k ≤ T :=
  (gridT_mono T n hk).trans_eq (gridT_last T n)

/-- The running sum of squared grid increments is monotone in the index. -/
theorem gridSq_mono (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : Monotone (gridSq f T n) := by
  intro k l hkl
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl) fun _ _ _ => sq_nonneg _

/-- If `t ≤ r` then `min t r` reads back as `t`. -/
theorem untopA_min_of_le {t : ℝ≥0} {r : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ r) :
    (min (t : WithTop ℝ≥0) r).untopA = t := by
  rw [min_eq_left h]
  exact WithTop.untopD_coe _ _

/-- Under the modulus condition and the bound `gridSq ≤ L` the skeleton stop is `⊤`: no grid
interval contains an oscillation hit, and the running sum never exceeds `L`. -/
theorem skelStop_eq_top {f : ℝ≥0 → ℝ} {T : ℝ≥0} {n : ℕ} {b L : ℝ}
    (hmod : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n → |f s - f t| < b)
    (hgs : gridSq f T n (2 ^ n) ≤ L) : skelStop f T n b L = ⊤ := by
  have hosc : ∀ k, k < 2 ^ n → oscHit f T n b k = ⊤ := by
    intro k hk
    unfold oscHit
    rw [ite_eq_right]
    rintro ⟨s, hs1, hs2, hs3⟩
    have hsT : s ≤ T := hs2.trans (gridT_le T n (k + 1) (Nat.succ_le_of_lt hk))
    have htT : gridT T n k ≤ T := gridT_le T n k hk.le
    have habs : |(s : ℝ) - ((gridT T n k : ℝ≥0) : ℝ)| ≤ (T : ℝ) / 2 ^ n := by
      have e1 : ((gridT T n k : ℝ≥0) : ℝ) ≤ s := by exact_mod_cast hs1
      have e2 : (s : ℝ) ≤ ((gridT T n (k + 1) : ℝ≥0) : ℝ) := by exact_mod_cast hs2
      have e3 := gridT_succ_sub T n k
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact absurd (hmod s _ hsT htT habs) (not_lt.2 hs3)
  have hosc' : oscStop f T n b = ⊤ := by
    unfold oscStop
    rw [Finset.inf_eq_top_iff]
    intro k hk
    exact hosc k (Finset.mem_range.1 hk)
  have hgrid' : gridStop f T n L = ⊤ := by
    unfold gridStop
    rw [Finset.inf_eq_top_iff]
    intro k hk
    have hle : gridSq f T n k ≤ L :=
      (gridSq_mono f T n (Nat.le_of_lt_succ (Finset.mem_range.1 hk))).trans hgs
    exact ite_eq_right (not_lt.2 hle)
  unfold skelStop
  rw [hosc', hgrid']
  exact min_self _

/-- When the skeleton stop is `⊤`, the stopped skeleton at the index `k` is the path at the grid
time `t_{min k 2^n}`. -/
theorem skelVal_of_stop_top (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) (k : ℕ)
    (h : skelStop f T n b L = ⊤) :
    skelVal f T n b L k = f (gridT T n (min k (2 ^ n))) := by
  unfold skelVal
  rw [h, untopA_min_of_le le_top]

/-- On the good event the square sum of the stopped skeleton is the full sum of squared grid
increments. -/
theorem skeletonFullSum_holds : SkeletonFullSum := by
  intro f _ T n b L _ _ hmod hgs
  have hr := skelStop_eq_top hmod hgs
  have hsum : ∑ i ∈ Finset.range (2 ^ n),
      (skelVal f T n b L (i + 1) - skelVal f T n b L i) ^ 2 =
        ∑ i ∈ Finset.range (2 ^ n), (f (gridT T n (i + 1)) - f (gridT T n i)) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [skelVal_of_stop_top f T n b L (i + 1) hr, skelVal_of_stop_top f T n b L i hr,
      min_eq_left (Nat.succ_le_of_lt hi), min_eq_left hi.le]
  rw [hsum]
  rfl

end

end LatticeProb.Process.StoppedSkeleton.FullSum

namespace LatticeProb.Process.BdgUpperContinuous.LowerAssembly

noncomputable section

/-- The coordinate of a one-dimensional vector-valued martingale is a real martingale. -/
theorem martingale_coord_zero {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 m0} {M : ℝ≥0 → Ω → Fin 1 → ℝ} (hM : Martingale M ℱ P) :
    Martingale (fun t ω => M t ω 0) ℱ P := by
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · exact (continuous_apply (0 : Fin 1)).comp_stronglyMeasurable (hM.1 t)
  · have h1 : (fun ω => (P[M j | ℱ i]) ω 0) =ᵐ[P] P[fun ω => M j ω 0 | ℱ i] :=
      ContinuousLinearMap.comp_condExp_comm (hM.integrable j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    filter_upwards [h1, hM.2 i j hij] with ω h1ω h2ω
    rw [← h1ω, h2ω]

/-- The dyadic grid times `t_k = T k / 2^n` are monotone in the index `k`. -/
theorem gridT_monotone (T : ℝ≥0) (n : ℕ) : Monotone (LatticeProb.Process.StoppedSkeleton.gridT T n) := by
  intro i j hij
  unfold LatticeProb.Process.StoppedSkeleton.gridT
  exact mul_le_mul_right (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) zero_le) T

/-- The capped grid times `t_{min k 2^n}` are monotone in the index `k`. -/
theorem cappedGridT_monotone (T : ℝ≥0) (n : ℕ) :
    Monotone fun k : ℕ => LatticeProb.Process.StoppedSkeleton.gridT T n (min k (2 ^ n)) :=
  fun _ _ hij => gridT_monotone T n (min_le_min_right _ hij)

/-- The last dyadic grid time `t_{2^n} = T 2^n / 2^n` is `T`. -/
theorem gridT_two_pow (T : ℝ≥0) (n : ℕ) : LatticeProb.Process.StoppedSkeleton.gridT T n (2 ^ n) = T := by
  unfold LatticeProb.Process.StoppedSkeleton.gridT
  rw [Nat.cast_pow, Nat.cast_ofNat, div_self (pow_ne_zero n two_ne_zero), mul_one]

/-- **The stopped dyadic skeleton for the lower bound, from its five components**: optional
stopping for continuous martingales, the localising time being a stopping time, the path
bookkeeping of the skeleton, the full-sum identity on the good event, and the `Lᵖ` contraction of
stopping. -/
theorem stoppedDyadicSkeletonLower_of_components
    (hOST : LatticeProb.Process.StoppedSkeleton.ContinuousStoppedMartingale)
    (hStop : LatticeProb.Process.StoppedSkeleton.SkeletonStopIsStoppingTime)
    (hPath : LatticeProb.Process.StoppedSkeleton.SkeletonPathFacts)
    (hFull : LatticeProb.Process.StoppedSkeleton.SkeletonFullSum)
    (hLp : LatticeProb.Process.StoppedSkeleton.StoppedLpContraction) : StoppedDyadicSkeletonLower := by
  intro Ω _ P _ ℱ M T hM hcont h0 n b L hb hL
  let X : ℝ≥0 → Ω → ℝ := fun t ω => M t ω 0
  have hX : Martingale X ℱ P := martingale_coord_zero hM
  have hXcont : ∀ ω, Continuous fun t => X t ω :=
    fun ω => (continuous_apply (0 : Fin 1)).comp (hcont ω)
  have hτ := hStop ℱ X hX.1 hXcont T n b L
  have hY := hOST P ℱ X _ hX hXcont hτ
  let g : ℕ → ℝ≥0 := fun k => LatticeProb.Process.StoppedSkeleton.gridT T n (min k (2 ^ n))
  have hg : Monotone g := cappedGridT_monotone T n
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨fun k => ℱ (g k), fun _ _ hij => ℱ.mono (hg hij), fun k => ℱ.le _⟩
  refine ⟨𝒢, fun k ω => LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L k,
    ⟨fun k => hY.1 (g k), fun i j hij => hY.2 (g i) (g j) (hg hij)⟩, ?_, ?_, ?_, ?_⟩
  · intro ω
    have h := (hPath (fun t => X t ω) (hXcont ω) T n hb hL).1
    show LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L 0 = 0
    rw [h]
    show M 0 ω 0 = 0
    simp [h0 ω]
  · intro i hi ω
    exact (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.1 i hi
  · intro p hp
    have hmin : min (2 ^ n) (2 ^ n) = 2 ^ n := min_self _
    have hgT : LatticeProb.Process.StoppedSkeleton.gridT T n (min (2 ^ n) (2 ^ n)) = T := by
      rw [hmin]
      exact gridT_two_pow T n
    have h := hLp P ℱ X _ hX hXcont hτ T hp
    have hlhs : ∀ ω, LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L (2 ^ n) =
        stoppedProcess X (fun ω => LatticeProb.Process.StoppedSkeleton.skelStop (fun t => X t ω) T n b L) T
          ω := by
      intro ω
      have h2 := LatticeProb.Process.StoppedSkeleton.skelVal_eq_stoppedProcess X T n b L (2 ^ n) ω
      rw [hgT] at h2
      exact h2
    calc ∫⁻ ω, ENNReal.ofReal |LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L (2 ^ n)| ^ p
          ∂P
        = ∫⁻ ω, ENNReal.ofReal
            |stoppedProcess X
              (fun ω => LatticeProb.Process.StoppedSkeleton.skelStop (fun t => X t ω) T n b L) T ω| ^ p ∂P := by
          simp only [hlhs]
      _ ≤ ∫⁻ ω, ENNReal.ofReal |X T ω| ^ p ∂P := h
      _ = ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P := by
          simp only [X, Real.enorm_eq_ofReal_abs]
  · intro ω hmod hrc
    rw [LatticeProb.Process.StoppedSkeleton.realizedCovar_eq_gridSq] at hrc ⊢
    exact hFull (fun t => X t ω) (hXcont ω) T n hb hL hmod hrc

end

end LatticeProb.Process.BdgUpperContinuous.LowerAssembly

namespace LatticeProb.Process.BdgUpperContinuous.LowerPassage

noncomputable section

/-! ### The passage from the stopped skeleton to the lower half -/

/-- If `r j → x` and `S j = r j` for all large `j`, then `(ofReal (S j)) ^ q → (ofReal x) ^ q`
in `ℝ≥0∞`. -/
lemma tendsto_ofReal_rpow_of_eventually_eq {q : ℝ} {S r : ℕ → ℝ} {x : ℝ}
    (hr : Tendsto r atTop (𝓝 x)) (hev : ∀ᶠ j in atTop, S j = r j) :
    Tendsto (fun j => ENNReal.ofReal (S j) ^ q) atTop (𝓝 (ENNReal.ofReal x ^ q)) := by
  have hcont : Continuous fun y : ℝ => ENNReal.ofReal y ^ q :=
    ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal
  have h1 : Tendsto (fun j => ENNReal.ofReal (r j) ^ q) atTop (𝓝 (ENNReal.ofReal x ^ q)) :=
    (hcont.tendsto x).comp hr
  exact h1.congr' (hev.mono fun j hj => by simp only [hj])

/-- Pointwise liminf bound.  Along a sequence of levels `ns j → ∞`, suppose the realized sums
`rc j` converge to `x`, and that `S j = rc j` as soon as the modulus of continuity of `f` at the
scale `T / 2 ^ (ns j)` is below `b` and `rc j ≤ ns j`.  Then `(ofReal x) ^ q ≤ liminf (ofReal (S j)) ^ q`:
in fact `(ofReal (S j)) ^ q` converges to `(ofReal x) ^ q`. -/
lemma ofReal_rpow_le_liminf_of_sum {q : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (T : ℝ≥0) {b : ℝ} (hb : 0 < b)
    {rc S : ℕ → ℝ} {x : ℝ} (hrc : Tendsto rc atTop (𝓝 x))
    (hSum : ∀ j, (∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ (ns j) →
        |f s - f t| < b) → rc j ≤ (ns j : ℝ) → S j = rc j) :
    ENNReal.ofReal x ^ q ≤ liminf (fun j => ENNReal.ofReal (S j) ^ q) atTop := by
  have h1 : ∀ᶠ j in atTop, ∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ (ns j) →
      |f s - f t| < b := hns.eventually (eventually_modulus_lt hf T hb)
  have h2 : ∀ᶠ j in atTop, rc j ≤ (ns j : ℝ) := by
    have h3 : ∀ᶠ j in atTop, rc j < x + 1 := hrc.eventually (gt_mem_nhds (lt_add_one x))
    have h4 : ∀ᶠ j in atTop, x + 1 ≤ (ns j : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hns).eventually_ge_atTop (x + 1)
    filter_upwards [h3, h4] with j hj3 hj4 using (hj3.trans_le hj4).le
  have h5 : ∀ᶠ j in atTop, S j = rc j := by
    filter_upwards [h1, h2] with j hj1 hj2 using hSum j hj1 hj2
  exact (tendsto_ofReal_rpow_of_eventually_eq hrc h5).liminf_eq.symm.le

/-- Removing the bounded-increment term: if `X ≤ K (Y + ofReal (b ^ p))` for every `b > 0`, with
`K` finite, then `X ≤ K Y`. -/
lemma le_mul_of_forall_pos_le_mul_add {p : ℝ} (hp : 0 < p) {X Y K : ℝ≥0∞} (hK : K ≠ ∞)
    (h : ∀ b : ℝ, 0 < b → X ≤ K * (Y + ENNReal.ofReal (b ^ p))) : X ≤ K * Y := by
  have hb0 : Tendsto (fun b : ℝ => ENNReal.ofReal (b ^ p)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : ContinuousAt (fun b : ℝ => b ^ p) 0 :=
      Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
    have h2 : Tendsto (fun b : ℝ => b ^ p) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hp.ne'] using h1.tendsto
    have h3 := ENNReal.tendsto_ofReal
      (h2.mono_left nhdsWithin_le_nhds : Tendsto (fun b : ℝ => b ^ p) (𝓝[>] 0) (𝓝 0))
    simpa using h3
  have hlim : Tendsto (fun b : ℝ => K * (Y + ENNReal.ofReal (b ^ p))) (𝓝[>] (0 : ℝ))
      (𝓝 (K * (Y + 0))) :=
    ENNReal.Tendsto.const_mul (hb0.const_add Y) (Or.inr hK)
  have := ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun b hb => h b (Set.mem_Ioi.1 hb))
  simpa using this

/-- From `X ≤ ofReal C * Y` with `C > 0`, conclude `ofReal C⁻¹ * X ≤ Y`. -/
lemma ofReal_inv_mul_le {C : ℝ} (hC : 0 < C) {X Y : ℝ≥0∞} (h : X ≤ ENNReal.ofReal C * Y) :
    ENNReal.ofReal C⁻¹ * X ≤ Y := by
  have h0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hC).ne'
  calc ENNReal.ofReal C⁻¹ * X ≤ ENNReal.ofReal C⁻¹ * (ENNReal.ofReal C * Y) := by gcongr
    _ = Y := by
      rw [← mul_assoc, ENNReal.ofReal_inv_of_pos hC, ENNReal.inv_mul_cancel h0
        ENNReal.ofReal_ne_top, one_mul]

/-- **The bounded-increment estimate for the quadratic covariation.**  Let `rc_{ns j} → Q`
almost everywhere along a strictly increasing sequence of levels.  If the discrete lower bound
`E S^{p/2} ≤ C (E |Z_N|^p + b^p)` holds and the stopped dyadic skeleton exists, then for every
`b > 0`, `E Q^{p/2} ≤ C (E |M_T|^p + b^p)`.  Fatou's lemma is applied along the levels `ns j`,
with the square sums `S j` of the stopped skeletons at the truncation level `L = ns j`. -/
lemma lintegral_rpow_le_of_subseq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℝ} (hp : 1 < p) {C : ℝ}
    (hD' : ∀ (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b : ℝ}, 0 < b →
      Martingale Z 𝒢 P → (∀ ω, Z 0 ω = 0) →
      (∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) →
        ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P ≤
          ENNReal.ofReal C * (∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P + ENNReal.ofReal (b ^ p)))
    (hS : StoppedDyadicSkeletonLower)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
    (Q : Ω → Fin 1 → Fin 1 → ℝ) (hM : Martingale M ℱ P) (hcont : ∀ ω, Continuous fun t => M t ω)
    (h0 : ∀ ω, M 0 ω = 0) {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hae : ∀ᵐ ω ∂P,
      Tendsto (fun j => LatticeProb.Process.realizedCovar M T (ns j) ω 0 0) atTop (𝓝 (Q ω 0 0)))
    {b : ℝ} (hb : 0 < b) :
    ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
      ENNReal.ofReal C * (∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
  have hq0 : 0 < p / 2 := by linarith
  have hSn := fun j : ℕ =>
    hS P ℱ M T hM hcont h0 (ns j) hb (Nat.cast_nonneg (ns j) : (0 : ℝ) ≤ (ns j : ℝ))
  choose 𝒢 Z hZ using hSn
  have hZm : ∀ j k, Measurable (Z j k) := fun j k =>
    (((hZ j).1.stronglyMeasurable k).mono ((𝒢 j).le k)).measurable
  set F : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal (∑ i ∈ Finset.range (2 ^ ns j), (Z j (i + 1) ω - Z j i ω) ^ 2) ^ (p / 2)
    with hF
  have hF_meas : ∀ j, Measurable (F j) := fun j => by
    refine ((Finset.measurable_sum _ (fun i _ => ?_)).ennreal_ofReal).pow_const _
    exact ((hZm j (i + 1)).sub (hZm j i)).pow_const 2
  have hbound : ∀ j, ∫⁻ ω, F j ω ∂P ≤
      ENNReal.ofReal C * (∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
    intro j
    refine (hD' (𝒢 j) (Z j) (2 ^ ns j) hb (hZ j).1 (hZ j).2.1 (hZ j).2.2.1).trans ?_
    exact mul_le_mul' le_rfl (add_le_add ((hZ j).2.2.2.1 p hp.le) le_rfl)
  have hlow : ∀ᵐ ω ∂P, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ≤ liminf (fun j => F j ω) atTop := by
    filter_upwards [hae] with ω hω
    have hcontω : Continuous fun t => M t ω 0 := (continuous_apply 0).comp (hcont ω)
    exact ofReal_rpow_le_liminf_of_sum hns.tendsto_atTop hcontω T hb hω
      (fun j hm hr => (hZ j).2.2.2.2 ω hm hr)
  calc ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P
      ≤ ∫⁻ ω, liminf (fun j => F j ω) atTop ∂P := lintegral_mono_ae hlow
    _ ≤ liminf (fun j => ∫⁻ ω, F j ω ∂P) atTop := lintegral_liminf_le hF_meas
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

/-- **The lower half at one exponent from the stopped skeleton.**  If the discrete lower bound
with a bounded-increment term holds at `p > 1` and the stopped dyadic skeleton for the lower bound
exists, then `c E Q^{p/2} ≤ E |M_T|^p` for every continuous martingale `M` from `0` with
`HasQuadCovar P M T Q`.

Proof.  Fix `b > 0`.  Along a subsequence `ns j` of levels, `rc_{ns j} → Q` almost surely
(`HasQuadCovar` is convergence in probability).  For the stopped skeleton `Z^j` of level `ns j`
with truncation level `L = ns j`, the discrete bound gives
`E (S^j)^{p/2} ≤ C (E |M_T|^p + b^p)` for the square sums `S^j`.  Almost surely, for large `j`
the modulus condition holds (uniform continuity of the paths) and `rc_{ns j} ≤ ns j` (the
sequence `rc_{ns j}` is bounded and `ns j → ∞`), so `S^j = rc_{ns j}` eventually and
`(S^j)^{p/2} → Q^{p/2}`.  Fatou's lemma gives `E Q^{p/2} ≤ C (E |M_T|^p + b^p)`, and `b → 0`
removes the last term.  No limit in the truncation level is taken. -/
theorem bdgLowerAt_of_skeleton {p : ℝ} (hp : 1 < p) (hD : DiscreteLowerBoundedAt p)
    (hS : StoppedDyadicSkeletonLower) : BdgLowerAt p := by
  obtain ⟨C, hC, hD'⟩ := hD
  refine ⟨C⁻¹, inv_pos.2 hC, ?_⟩
  intro Ω _ P _ ℱ M T Q hM hcont h0 hQ
  obtain ⟨ns, hns, hae⟩ := (hasQuadCovar_coord hQ).exists_seq_tendsto_ae
  have key : ∀ b : ℝ, 0 < b → ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
      ENNReal.ofReal C * (∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P + ENNReal.ofReal (b ^ p)) := fun b hb =>
    lintegral_rpow_le_of_subseq P hp
      (fun 𝒢 Z N _ hb' hZ hZ0 hinc => hD' P 𝒢 Z N hb' hZ hZ0 hinc) hS ℱ M T Q hM hcont h0 hns
      hae hb
  exact ofReal_inv_mul_le hC
    (le_mul_of_forall_pos_le_mul_add (by linarith) ENNReal.ofReal_ne_top key)

end

end LatticeProb.Process.BdgUpperContinuous.LowerPassage


/-!
## The square function by the maximal function for `p ≥ 2`

Garsia–Neveu argument.  Write `q = p / 2`, `d_i = Z_{i+1} - Z_i`, `S_k = ∑_{i<k} d_i²` and
`M = max_{k ≤ N} |Z_k|`.  The weights `a_k = S_k^{q-1}` (with `a_0 = 0`) are predictable; by the
tangent-line inequality for `t ↦ t^q`, summation by parts and the orthogonality of martingale
increments against bounded predictable multipliers one gets `E S_N^q ≤ 8 q E[S_N^{q-1} M²]`, and
Hölder's inequality closes the estimate with the constant `(8 q)^q`.
-/

namespace LatticeProb.Process.StoppedSkeleton.SquareMaxHigh

noncomputable section

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

/-- `|Z_k| ≤ k b` for `k ≤ N`. -/
lemma abs_le_mul_of_increments {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ}
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω) :
    ∀ k, k ≤ N → |Z k ω| ≤ k * b := by
  intro k
  induction k with
  | zero => intro _; simp [hZ0]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hinc k (by omega) ω
    have h3 : |Z (k + 1) ω| ≤ |Z k ω| + |Z (k + 1) ω - Z k ω| := by
      calc |Z (k + 1) ω| = |Z k ω + (Z (k + 1) ω - Z k ω)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    push_cast
    linarith

/-- For a bounded `ℱ i`-measurable `g`, `g (X_{i+1} - X_i)` is integrable and has integral `0`. -/
lemma integral_mul_diff_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) (i : ℕ) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ i] g) {C : ℝ}
    (hgb : ∀ ω, |g ω| ≤ C) :
    Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P ∧
      ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P = 0 := by
  have hdI : Integrable (fun ω => X (i + 1) ω - X i ω) P :=
    (hM.integrable (i + 1)).sub (hM.integrable i)
  have hIh : Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P :=
    hdI.bdd_mul (hg.mono (ℱ.le i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb ω)
  refine ⟨hIh, ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hg
    (g := fun ω => X (i + 1) ω - X i ω) (by exact hIh) hdI
  have h2 := condExp_diff_ae_zero hM i
  calc ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P
      = ∫ ω, P[g * (fun ω => X (i + 1) ω - X i ω) | ℱ i] ω ∂P :=
        (integral_condExp (ℱ.le i)).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2] with ω e1 e2
        rw [e1]
        show g ω * P[fun ω => X (i + 1) ω - X i ω | ℱ i] ω = 0
        rw [e2]
        simp
    _ = 0 := integral_zero _ _


/-- A real function is measurable and bounded. -/
def BddMeas {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ ω, |f ω| ≤ C

namespace BddMeas

variable {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ}

/-- A bounded measurable function is integrable for a probability measure. -/
lemma integrable (P : Measure Ω) [IsProbabilityMeasure P] (hf : BddMeas f) : Integrable f P := by
  obtain ⟨hm, C, hC⟩ := hf
  exact integrable_of_abs_le hm hC

/-- Sum of bounded measurable functions. -/
lemma add (hf : BddMeas f) (hg : BddMeas g) : BddMeas (fun ω => f ω + g ω) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.add hgm, C + D, fun ω => (abs_add_le _ _).trans (add_le_add (hC ω) (hD ω))⟩

/-- Difference of bounded measurable functions. -/
lemma sub (hf : BddMeas f) (hg : BddMeas g) : BddMeas (fun ω => f ω - g ω) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.sub hgm, C + D, fun ω => (abs_sub _ _).trans (add_le_add (hC ω) (hD ω))⟩

/-- Product of bounded measurable functions. -/
lemma mul (hf : BddMeas f) (hg : BddMeas g) : BddMeas (fun ω => f ω * g ω) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, C * D, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC ω) (hD ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))

/-- A constant is bounded and measurable. -/
lemma const (r : ℝ) : BddMeas (fun _ : Ω => r) :=
  ⟨measurable_const, |r|, fun _ => le_rfl⟩

/-- Natural power of a bounded measurable function. -/
lemma pow (hf : BddMeas f) (n : ℕ) : BddMeas (fun ω => f ω ^ n) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.pow_const n, C ^ n, fun ω => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) n

/-- Nonnegative real power of a nonnegative bounded measurable function. -/
lemma rpow (hf : BddMeas f) (h0 : ∀ ω, 0 ≤ f ω) {r : ℝ} (hr : 0 ≤ r) :
    BddMeas (fun ω => f ω ^ r) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.pow_const r, C ^ r, fun ω => ?_⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (h0 ω) _)]
  have := hC ω
  rw [abs_of_nonneg (h0 ω)] at this
  exact Real.rpow_le_rpow (h0 ω) this hr

end BddMeas

/-- Summation by parts: if `a 0 = 0` and `T_k = ∑_{i<k} e_i`, then
`∑_{k<N} a_{k+1} e_k = ∑_{j<N} (a_{j+1} - a_j) (T_N - T_j)`. -/
lemma abel_sum (a e : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    ∑ k ∈ Finset.range N, a (k + 1) * e k =
      ∑ j ∈ Finset.range N,
        (a (j + 1) - a j) * (∑ i ∈ Finset.range N, e i - ∑ i ∈ Finset.range j, e i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : ∑ j ∈ Finset.range N, (a (j + 1) - a j) *
          (∑ i ∈ Finset.range (N + 1), e i - ∑ i ∈ Finset.range j, e i) =
        ∑ j ∈ Finset.range N, (a (j + 1) - a j) *
          (∑ i ∈ Finset.range N, e i - ∑ i ∈ Finset.range j, e i) + e N * a N := by
      have h2 : ∀ j ∈ Finset.range N, (a (j + 1) - a j) *
            (∑ i ∈ Finset.range (N + 1), e i - ∑ i ∈ Finset.range j, e i) =
          (a (j + 1) - a j) * (∑ i ∈ Finset.range N, e i - ∑ i ∈ Finset.range j, e i) +
            e N * (a (j + 1) - a j) := by
        intro j _
        rw [Finset.sum_range_succ]
        ring
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun j => a j) N, ha0, sub_zero]
    have h3 : ∑ j ∈ Finset.range (N + 1), (a (j + 1) - a j) *
          (∑ i ∈ Finset.range (N + 1), e i - ∑ i ∈ Finset.range j, e i) =
        ∑ j ∈ Finset.range N, (a (j + 1) - a j) *
          (∑ i ∈ Finset.range (N + 1), e i - ∑ i ∈ Finset.range j, e i) +
        (a (N + 1) - a N) * (∑ i ∈ Finset.range (N + 1), e i - ∑ i ∈ Finset.range N, e i) :=
      Finset.sum_range_succ _ _
    rw [h3, h1, Finset.sum_range_succ (fun k => a (k + 1) * e k) N, ih,
      Finset.sum_range_succ e N]
    ring

/-- Tangent-line inequality for `t ↦ t ^ q`, `q ≥ 1`: `x^q - y^q ≤ q x^(q-1) (x - y)` for
`0 ≤ y ≤ x`. -/
lemma rpow_sub_rpow_le {q : ℝ} (hq : 1 ≤ q) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ q - y ^ q ≤ q * x ^ (q - 1) * (x - y) := by
  rcases eq_or_lt_of_le (hy.trans hxy) with hx | hx
  · have hy0 : y = 0 := le_antisymm (hx ▸ hxy) hy
    subst hy0
    rw [← hx]
    have hq0 : q ≠ 0 := by linarith
    simp [Real.zero_rpow hq0]
  · have hs : -1 ≤ y / x - 1 := by
      have : 0 ≤ y / x := div_nonneg hy hx.le
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hq
    have h1 : 1 + (y / x - 1) = y / x := by ring
    rw [h1, Real.div_rpow hy hx.le] at hb
    have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx _
    have h3 : x ^ q * (1 + q * (y / x - 1)) ≤ y ^ q := by
      have := mul_le_mul_of_nonneg_left hb hxq.le
      rwa [mul_div_cancel₀ _ hxq.ne'] at this
    have h2 : x ^ q = x ^ (q - 1) * x := by
      rw [← Real.rpow_add_one hx.ne']
      congr 1
      ring
    have h4 : x ^ q * (y / x - 1) = x ^ (q - 1) * (y - x) := by
      rw [h2]
      field_simp
    have h5 : x ^ q * (1 + q * (y / x - 1)) = x ^ q + q * (x ^ (q - 1) * (y - x)) := by
      rw [mul_add, mul_one, mul_left_comm, h4]
    nlinarith [h3, h5]

/-- Pointwise Garsia–Neveu tangent bound: for a nondecreasing nonnegative sequence `s` from `0`,
`s_N^q ≤ q ∑_{k<N} s_{k+1}^(q-1) (s_{k+1} - s_k)`. -/
lemma rpow_le_sum_tangent (s : ℕ → ℝ) (hs0 : s 0 = 0) (hmono : ∀ k, s k ≤ s (k + 1))
    (hnn : ∀ k, 0 ≤ s k) {q : ℝ} (hq : 1 ≤ q) (N : ℕ) :
    s N ^ q ≤ q * ∑ k ∈ Finset.range N, s (k + 1) ^ (q - 1) * (s (k + 1) - s k) := by
  have hq0 : q ≠ 0 := by linarith
  have htel : s N ^ q = ∑ k ∈ Finset.range N, (s (k + 1) ^ q - s k ^ q) := by
    rw [Finset.sum_range_sub (fun k => s k ^ q) N, hs0, Real.zero_rpow hq0, sub_zero]
  rw [htel, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := rpow_sub_rpow_le hq (hnn k) (hmono k)
  linarith

/-- Bounds for the running sum of squared increments: `0 ≤ S_k ≤ k b²` for `k ≤ N`. -/
lemma sq_sum_bounds {Ω : Type*} {Z : ℕ → Ω → ℝ} (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2) {N : ℕ} {b : ℝ}
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω) :
    ∀ k, k ≤ N → 0 ≤ S k ω ∧ S k ω ≤ k * b ^ 2 := by
  intro k hk
  rw [hS]
  refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
  calc ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 ≤ ∑ i ∈ Finset.range k, b ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h := hinc i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk) ω
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    _ = k * b ^ 2 := by simp

/-- Measurability with respect to the filtration: `S_k` is `𝒢 k`-strongly measurable. -/
lemma sq_sum_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P)
    (S : ℕ → Ω → ℝ) (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    (k : ℕ) : StronglyMeasurable[𝒢 k] (S k) := by
  have h : Measurable[𝒢 k] (S k) := by
    have : S k = fun ω => ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 := funext (hS k)
    rw [this]
    refine Finset.measurable_sum _ fun i hi => ?_
    have hik : i + 1 ≤ k := Finset.mem_range.mp hi
    have h1 : Measurable[𝒢 k] (Z (i + 1)) :=
      ((hM.stronglyMeasurable (i + 1)).mono (𝒢.mono hik)).measurable
    have h2 : Measurable[𝒢 k] (Z i) :=
      ((hM.stronglyMeasurable i).mono (𝒢.mono (by omega))).measurable
    exact (h1.sub h2).pow_const 2
  exact h.stronglyMeasurable

/-- `Z_k` is bounded and measurable for `k ≤ N`. -/
lemma bddMeas_Z {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P) (hZ0 : ∀ ω, Z 0 ω = 0) {N : ℕ} {b : ℝ}
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {k : ℕ} (hk : k ≤ N) :
    BddMeas (Z k) :=
  ⟨((hM.stronglyMeasurable k).mono (𝒢.le k)).measurable, k * b,
    fun ω => abs_le_mul_of_increments hZ0 hinc ω k hk⟩

/-- `S_k` is bounded and measurable for `k ≤ N`. -/
lemma bddMeas_S {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2) {N : ℕ} {b : ℝ}
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {k : ℕ} (hk : k ≤ N) :
    BddMeas (S k) :=
  ⟨((sq_sum_stronglyMeasurable 𝒢 hM S hS k).mono (𝒢.le k)).measurable, k * b ^ 2, fun ω => by
    obtain ⟨h0, h1⟩ := sq_sum_bounds S hS hinc ω k hk
    rwa [abs_of_nonneg h0]⟩


/-- **Orthogonality of the square sum against a bounded predictable multiplier.**  For `c` bounded
and `𝒢 j`-measurable and `j ≤ n ≤ N`,
`E[c (S_n - S_j)] = E[c (Z_n - Z_j)²]`. -/
lemma orthogonality_sq_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ)
    (hM : Martingale Z 𝒢 P) (hZ0 : ∀ ω, Z 0 ω = 0) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    {j : ℕ} {c : Ω → ℝ} (hc : StronglyMeasurable[𝒢 j] c) {C : ℝ} (hcb : ∀ ω, |c ω| ≤ C) :
    ∀ n, j ≤ n → n ≤ N →
      ∫ ω, c ω * (S n ω - S j ω) ∂P = ∫ ω, c ω * (Z n ω - Z j ω) ^ 2 ∂P := by
  have hBc : BddMeas c := ⟨(hc.mono (𝒢.le j)).measurable, C, hcb⟩
  intro n hjn
  induction n, hjn using Nat.le_induction with
  | base =>
    intro _
    simp
  | succ n hjn ih =>
    intro hn1
    have hnN : n ≤ N := by omega
    have hjN : j ≤ N := by omega
    have ih' := ih hnN
    have hBd : BddMeas (fun ω => Z (n + 1) ω - Z n ω) :=
      (bddMeas_Z hM hZ0 hinc hn1).sub (bddMeas_Z hM hZ0 hinc hnN)
    have hBe : BddMeas (fun ω => Z n ω - Z j ω) :=
      (bddMeas_Z hM hZ0 hinc hnN).sub (bddMeas_Z hM hZ0 hinc hjN)
    have hBS : BddMeas (fun ω => S n ω - S j ω) :=
      (bddMeas_S hM S hS hinc hnN).sub (bddMeas_S hM S hS hinc hjN)
    have hBd2 := hBd.pow 2
    have hBe2 := hBe.pow 2
    have hcm : StronglyMeasurable[𝒢 n] c := hc.mono (𝒢.mono hjn)
    have hgm : StronglyMeasurable[𝒢 n] (fun ω => 2 * c ω * (Z n ω - Z j ω)) :=
      (hcm.const_mul 2).mul ((hM.stronglyMeasurable n).sub
        ((hM.stronglyMeasurable j).mono (𝒢.mono hjn)))
    have hBg : BddMeas (fun ω => 2 * c ω * (Z n ω - Z j ω)) :=
      ((BddMeas.const 2).mul hBc).mul hBe
    obtain ⟨_, Cg, hCg⟩ := hBg
    have h0 := (integral_mul_diff_eq_zero P 𝒢 Z hM n hgm hCg).2
    have hSs : ∀ ω, S (n + 1) ω = S n ω + (Z (n + 1) ω - Z n ω) ^ 2 := fun ω => by
      rw [hS, hS, Finset.sum_range_succ]
    have e1 : ∫ ω, c ω * (S (n + 1) ω - S j ω) ∂P =
        ∫ ω, c ω * (S n ω - S j ω) ∂P + ∫ ω, c ω * (Z (n + 1) ω - Z n ω) ^ 2 ∂P := by
      rw [← integral_add ((hBc.mul hBS).integrable P) ((hBc.mul hBd2).integrable P)]
      congr 1
      funext ω
      rw [hSs ω]
      ring
    have e2 : ∫ ω, c ω * (Z (n + 1) ω - Z j ω) ^ 2 ∂P =
        ∫ ω, c ω * (Z n ω - Z j ω) ^ 2 ∂P +
          ∫ ω, 2 * c ω * (Z n ω - Z j ω) * (Z (n + 1) ω - Z n ω) ∂P +
          ∫ ω, c ω * (Z (n + 1) ω - Z n ω) ^ 2 ∂P := by
      have hB2 : BddMeas (fun ω => 2 * c ω * (Z n ω - Z j ω) * (Z (n + 1) ω - Z n ω)) :=
        (((BddMeas.const 2).mul hBc).mul hBe).mul hBd
      rw [← integral_add ((hBc.mul hBe2).integrable P) (hB2.integrable P),
        ← integral_add (((hBc.mul hBe2).add hB2).integrable P) ((hBc.mul hBd2).integrable P)]
      congr 1
      funext ω
      ring
    rw [e1, e2]
    linarith [ih', h0]


/-- If `|x| ≤ m` and `|y| ≤ m` then `(x - y)² ≤ 4 m²`. -/
lemma sq_sub_le_four {x y m : ℝ} (hx : |x| ≤ m) (hy : |y| ≤ m) : (x - y) ^ 2 ≤ 4 * m ^ 2 := by
  have h := (abs_sub x y).trans (add_le_add hx hy)
  have h' := abs_le.mp h
  calc (x - y) ^ 2 ≤ (m + m) ^ 2 := sq_le_sq' h'.1 h'.2
    _ = 4 * m ^ 2 := by ring

/-- **One term of the summation by parts.**  For a nondecreasing family `a` of predictable,
bounded weights and `j < N`,
`E[(a_{j+1} - a_j) (S_N - S_j)] ≤ 8 E[(a_{j+1} - a_j) M²]`, where `M` dominates `|Z_k|`, `k ≤ N`. -/
lemma sq_sum_step {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    (a : ℕ → Ω → ℝ) (hamono : ∀ k ω, a k ω ≤ a (k + 1) ω)
    (ham : ∀ k, k ≤ N → StronglyMeasurable[𝒢 k] (a k)) {Ca : ℝ}
    (haC : ∀ k, k ≤ N → ∀ ω, |a k ω| ≤ Ca)
    (M : Ω → ℝ) (hMm : Measurable M) {CM : ℝ} (hMC : ∀ ω, |M ω| ≤ CM)
    (hMZ : ∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω) {j : ℕ} (hj : j < N) :
    ∫ ω, (a (j + 1) ω - a j ω) * (S N ω - S j ω) ∂P ≤
      ∫ ω, (a (j + 1) ω - a j ω) * (8 * M ω ^ 2) ∂P := by
  have hBa : ∀ k, k ≤ N → BddMeas (a k) := fun k hk =>
    ⟨((ham k hk).mono (𝒢.le k)).measurable, Ca, haC k hk⟩
  have hBα : BddMeas (fun ω => a (j + 1) ω - a j ω) := (hBa (j + 1) hj).sub (hBa j hj.le)
  have hαsm : StronglyMeasurable[𝒢 (j + 1)] (fun ω => a (j + 1) ω - a j ω) :=
    (ham (j + 1) hj).sub ((ham j hj.le).mono (𝒢.mono (Nat.le_succ j)))
  have hBM : BddMeas M := ⟨hMm, CM, hMC⟩
  have hBd : BddMeas (fun ω => Z (j + 1) ω - Z j ω) :=
    (bddMeas_Z hM hZ0 hinc hj).sub (bddMeas_Z hM hZ0 hinc hj.le)
  have hBe : BddMeas (fun ω => Z N ω - Z (j + 1) ω) :=
    (bddMeas_Z hM hZ0 hinc le_rfl).sub (bddMeas_Z hM hZ0 hinc hj)
  have hBSS : BddMeas (fun ω => S N ω - S (j + 1) ω) :=
    (bddMeas_S hM S hS hinc le_rfl).sub (bddMeas_S hM S hS hinc hj)
  have hBSj : BddMeas (fun ω => S N ω - S j ω) :=
    (bddMeas_S hM S hS hinc le_rfl).sub (bddMeas_S hM S hS hinc hj.le)
  have hBd2 := hBd.pow 2
  have hBe2 := hBe.pow 2
  have hBM2 := (BddMeas.const (8 : ℝ)).mul (hBM.pow 2)
  have hI1 := (hBα.mul hBd2).integrable P
  have hI2 := (hBα.mul hBSS).integrable P
  have hI3 := (hBα.mul hBe2).integrable P
  obtain ⟨Cα, hCα⟩ := hBα.2
  have horth := orthogonality_sq_sum P 𝒢 Z hM hZ0 S hS hinc hαsm hCα N (Nat.succ_le_of_lt hj)
    le_rfl
  have hSs : ∀ ω, S (j + 1) ω = S j ω + (Z (j + 1) ω - Z j ω) ^ 2 := fun ω => by
    rw [hS, hS, Finset.sum_range_succ]
  calc ∫ ω, (a (j + 1) ω - a j ω) * (S N ω - S j ω) ∂P
      = ∫ ω, ((a (j + 1) ω - a j ω) * (Z (j + 1) ω - Z j ω) ^ 2 +
          (a (j + 1) ω - a j ω) * (S N ω - S (j + 1) ω)) ∂P := by
        congr 1
        funext ω
        rw [hSs ω]
        ring
    _ = ∫ ω, (a (j + 1) ω - a j ω) * (Z (j + 1) ω - Z j ω) ^ 2 ∂P +
          ∫ ω, (a (j + 1) ω - a j ω) * (S N ω - S (j + 1) ω) ∂P := integral_add hI1 hI2
    _ = ∫ ω, (a (j + 1) ω - a j ω) * (Z (j + 1) ω - Z j ω) ^ 2 ∂P +
          ∫ ω, (a (j + 1) ω - a j ω) * (Z N ω - Z (j + 1) ω) ^ 2 ∂P := by rw [horth]
    _ = ∫ ω, ((a (j + 1) ω - a j ω) * (Z (j + 1) ω - Z j ω) ^ 2 +
          (a (j + 1) ω - a j ω) * (Z N ω - Z (j + 1) ω) ^ 2) ∂P := (integral_add hI1 hI3).symm
    _ ≤ ∫ ω, (a (j + 1) ω - a j ω) * (8 * M ω ^ 2) ∂P := by
        refine integral_mono (hI1.add hI3) ((hBα.mul hBM2).integrable P) fun ω => ?_
        have hα0 : 0 ≤ a (j + 1) ω - a j ω := sub_nonneg.mpr (hamono j ω)
        have h1 := sq_sub_le_four (hMZ (j + 1) hj ω) (hMZ j hj.le ω)
        have h2 := sq_sub_le_four (hMZ N le_rfl ω) (hMZ (j + 1) hj ω)
        have h3 : (Z (j + 1) ω - Z j ω) ^ 2 + (Z N ω - Z (j + 1) ω) ^ 2 ≤ 8 * M ω ^ 2 := by
          linarith
        calc (a (j + 1) ω - a j ω) * (Z (j + 1) ω - Z j ω) ^ 2 +
              (a (j + 1) ω - a j ω) * (Z N ω - Z (j + 1) ω) ^ 2
            = (a (j + 1) ω - a j ω) *
                ((Z (j + 1) ω - Z j ω) ^ 2 + (Z N ω - Z (j + 1) ω) ^ 2) := by ring
          _ ≤ (a (j + 1) ω - a j ω) * (8 * M ω ^ 2) := mul_le_mul_of_nonneg_left h3 hα0

/-- **Summation by parts and orthogonality.**  For a nondecreasing family `a` from `0` of
predictable bounded weights, `E ∑_{k<N} a_{k+1} (Z_{k+1} - Z_k)² ≤ E[a_N · 8 M²]`. -/
lemma sq_sum_key {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    (a : ℕ → Ω → ℝ) (ha0 : ∀ ω, a 0 ω = 0) (hamono : ∀ k ω, a k ω ≤ a (k + 1) ω)
    (ham : ∀ k, k ≤ N → StronglyMeasurable[𝒢 k] (a k)) {Ca : ℝ}
    (haC : ∀ k, k ≤ N → ∀ ω, |a k ω| ≤ Ca)
    (M : Ω → ℝ) (hMm : Measurable M) {CM : ℝ} (hMC : ∀ ω, |M ω| ≤ CM)
    (hMZ : ∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω) :
    ∫ ω, ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 ∂P ≤
      ∫ ω, a N ω * (8 * M ω ^ 2) ∂P := by
  have hBa : ∀ k, k ≤ N → BddMeas (a k) := fun k hk =>
    ⟨((ham k hk).mono (𝒢.le k)).measurable, Ca, haC k hk⟩
  have hBM : BddMeas M := ⟨hMm, CM, hMC⟩
  have hBM2 := (BddMeas.const (8 : ℝ)).mul (hBM.pow 2)
  have hBα : ∀ j, j < N → BddMeas (fun ω => a (j + 1) ω - a j ω) := fun j hj =>
    (hBa (j + 1) hj).sub (hBa j hj.le)
  have hpt : ∀ ω, ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 =
      ∑ j ∈ Finset.range N, (a (j + 1) ω - a j ω) * (S N ω - S j ω) := by
    intro ω
    have h := abel_sum (fun k => a k ω) (fun k => (Z (k + 1) ω - Z k ω) ^ 2) (ha0 ω) N
    simpa only [← hS] using h
  calc ∫ ω, ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 ∂P
      = ∫ ω, ∑ j ∈ Finset.range N, (a (j + 1) ω - a j ω) * (S N ω - S j ω) ∂P := by
        congr 1
        funext ω
        exact hpt ω
    _ = ∑ j ∈ Finset.range N, ∫ ω, (a (j + 1) ω - a j ω) * (S N ω - S j ω) ∂P := by
        refine integral_finsetSum _ fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        exact ((hBα j hj').mul ((bddMeas_S hM S hS hinc le_rfl).sub
          (bddMeas_S hM S hS hinc hj'.le))).integrable P
    _ ≤ ∑ j ∈ Finset.range N, ∫ ω, (a (j + 1) ω - a j ω) * (8 * M ω ^ 2) ∂P :=
        Finset.sum_le_sum fun j hj =>
          sq_sum_step P 𝒢 Z hM hZ0 S hS hinc a hamono ham haC M hMm hMC hMZ
            (Finset.mem_range.mp hj)
    _ = ∫ ω, ∑ j ∈ Finset.range N, (a (j + 1) ω - a j ω) * (8 * M ω ^ 2) ∂P := by
        refine (integral_finsetSum _ fun j hj => ?_).symm
        exact ((hBα j (Finset.mem_range.mp hj)).mul hBM2).integrable P
    _ = ∫ ω, a N ω * (8 * M ω ^ 2) ∂P := by
        congr 1
        funext ω
        rw [← Finset.sum_mul, Finset.sum_range_sub (fun k => a k ω) N, ha0 ω, sub_zero]


/-- For a bounded measurable nonnegative `f`, `E (ofReal f)^q = ofReal (E f^q)`. -/
lemma lintegral_ofReal_rpow_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (h0 : ∀ ω, 0 ≤ f ω)
    (hC : ∀ ω, f ω ≤ C) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ q ∂P = ENNReal.ofReal (∫ ω, f ω ^ q ∂P) := by
  have hI : Integrable (fun ω => f ω ^ q) P := by
    refine integrable_of_abs_le (C := C ^ q) (hf.pow_const q) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (h0 ω) _)]
    exact Real.rpow_le_rpow (h0 ω) (hC ω) hq
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (h0 ω) _)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (h0 ω) hq]

/-- The real-variable end of the Garsia–Neveu argument: from `J ≤ q H` and
`H ≤ J^{1-1/q} K^{1/q}` conclude `J ≤ q^q K`. -/
lemma garsia_final {q J K H : ℝ} (hq : 1 < q) (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K)
    (hH : H ≤ J ^ (1 - q⁻¹) * K ^ q⁻¹) (hJH : J ≤ q * H) : J ≤ q ^ q * K := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le hJ0 with hJ | hJ
  · rw [← hJ]
    positivity
  · have h1 : J ≤ q * (J ^ (1 - q⁻¹) * K ^ q⁻¹) :=
      hJH.trans (mul_le_mul_of_nonneg_left hH hq0.le)
    have hJe : J = J ^ q⁻¹ * J ^ (1 - q⁻¹) := by
      rw [← Real.rpow_add hJ]
      simp
    have hpos : 0 < J ^ (1 - q⁻¹) := Real.rpow_pos_of_pos hJ _
    have h2 : J ^ q⁻¹ ≤ q * K ^ q⁻¹ := by
      have h3 : J ^ q⁻¹ * J ^ (1 - q⁻¹) ≤ (q * K ^ q⁻¹) * J ^ (1 - q⁻¹) := by
        calc J ^ q⁻¹ * J ^ (1 - q⁻¹) = J := hJe.symm
          _ ≤ q * (J ^ (1 - q⁻¹) * K ^ q⁻¹) := h1
          _ = (q * K ^ q⁻¹) * J ^ (1 - q⁻¹) := by ring
      exact le_of_mul_le_mul_right h3 hpos
    have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hJ.le _) h2 hq0.le
    rw [Real.rpow_inv_rpow hJ.le hq0.ne', Real.mul_rpow hq0.le (Real.rpow_nonneg hK0 _),
      Real.rpow_inv_rpow hK0 hq0.ne'] at h3
    exact h3

/-- `ofReal` commutes with the nonempty `Finset.sup'` of reals. -/
lemma ofReal_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
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
lemma sup'_range_eq_iSup (n : ℕ) (f : ℕ → ℝ≥0∞) :
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f = ⨆ k ≤ n, f k := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro k hk
    exact le_iSup_of_le k (le_iSup_of_le (by simpa [Finset.mem_range] using hk) le_rfl)
  · refine iSup_le fun k => iSup_le fun hk => ?_
    exact Finset.le_sup' f (by simp only [Finset.mem_range]; omega)

/-- **The Hölder step of the Garsia–Neveu argument.**  For bounded measurable nonnegative `s`, `g`
and `q ≥ 1`, from `E s^q ≤ q E[s^{q-1} g]` one gets `E s^q ≤ q^q E g^q`. -/
lemma garsia_holder {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q : ℝ} (hq : 1 ≤ q) {s g : Ω → ℝ} (hsm : Measurable s) (hgm : Measurable g)
    (hs0 : ∀ ω, 0 ≤ s ω) (hg0 : ∀ ω, 0 ≤ g ω) {Cs Cg : ℝ} (hsC : ∀ ω, s ω ≤ Cs)
    (hgC : ∀ ω, g ω ≤ Cg)
    (hmain : ∫ ω, s ω ^ q ∂P ≤ q * ∫ ω, s ω ^ (q - 1) * g ω ∂P) :
    ∫ ω, s ω ^ q ∂P ≤ q ^ q * ∫ ω, g ω ^ q ∂P := by
  have hq0 : 0 < q := by linarith
  have hK0 : 0 ≤ ∫ ω, g ω ^ q ∂P := integral_nonneg fun ω => Real.rpow_nonneg (hg0 ω) _
  have hJ0 : 0 ≤ ∫ ω, s ω ^ q ∂P := integral_nonneg fun ω => Real.rpow_nonneg (hs0 ω) _
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · have hq1' : q = 1 := hq1.symm
    have hdiff : q - 1 = 0 := by linarith
    have h1 : ∫ ω, s ω ^ (q - 1) * g ω ∂P = ∫ ω, g ω ^ q ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show s ω ^ (q - 1) * g ω = g ω ^ q
      rw [hdiff, Real.rpow_zero, one_mul, hq1', Real.rpow_one]
    rw [h1, hq1'] at hmain
    simpa [hq1'] using hmain
  · have hpq : (q.conjExponent).HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
    have hp'pos : 0 < q.conjExponent := hpq.pos
    have hf0 : 0 ≤ᵐ[P] fun ω => s ω ^ (q - 1) :=
      Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hs0 ω) _
    have hg0' : 0 ≤ᵐ[P] g := Filter.Eventually.of_forall fun ω => hg0 ω
    have hfL : MemLp (fun ω => s ω ^ (q - 1)) (ENNReal.ofReal q.conjExponent) P := by
      refine MemLp.of_bound (hsm.pow_const _).aestronglyMeasurable (Cs ^ (q - 1))
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hs0 ω) _)]
      exact Real.rpow_le_rpow (hs0 ω) (hsC ω) (by linarith)
    have hgL : MemLp g (ENNReal.ofReal q) P := by
      refine MemLp.of_bound hgm.aestronglyMeasurable Cg (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
      exact hgC ω
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0' hfL hgL
    have hpow : ∀ ω, (s ω ^ (q - 1)) ^ q.conjExponent = s ω ^ q := fun ω => by
      rw [← Real.rpow_mul (hs0 ω)]
      congr 1
      unfold Real.conjExponent
      field_simp
    simp only [hpow, one_div] at hH
    have hinv : q.conjExponent⁻¹ = 1 - q⁻¹ := by
      have := hpq.inv_add_inv_eq_one
      linarith
    rw [hinv] at hH
    exact garsia_final hq1 hJ0 hK0 hH hmain


/-- The predictable weights `a_0 = 0`, `a_k = S_k^{q-1}` for `k ≥ 1`: they are nondecreasing in
`k`, `a_k` is `𝒢 k`-measurable, and `|a_k| ≤ (N b²)^{q-1}` for `k ≤ N`. -/
lemma sq_sum_weights {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P)
    (S : ℕ → Ω → ℝ) (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {q : ℝ} (hq : 1 ≤ q) :
    ∃ a : ℕ → Ω → ℝ, (∀ ω, a 0 ω = 0) ∧ (∀ k ω, a (k + 1) ω = S (k + 1) ω ^ (q - 1)) ∧
      (∀ k ω, a k ω ≤ a (k + 1) ω) ∧ (∀ k, k ≤ N → StronglyMeasurable[𝒢 k] (a k)) ∧
      (∀ k, k ≤ N → ∀ ω, |a k ω| ≤ ((N : ℝ) * b ^ 2) ^ (q - 1)) := by
  have hq1 : 0 ≤ q - 1 := by linarith
  have hSs : ∀ k ω, S (k + 1) ω = S k ω + (Z (k + 1) ω - Z k ω) ^ 2 := fun k ω => by
    rw [hS, hS, Finset.sum_range_succ]
  have hSnn : ∀ k ω, 0 ≤ S k ω := fun k ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSmono : ∀ k ω, S k ω ≤ S (k + 1) ω := fun k ω => by
    rw [hSs]
    nlinarith [sq_nonneg (Z (k + 1) ω - Z k ω)]
  refine ⟨fun k ω => if k = 0 then 0 else S k ω ^ (q - 1), fun ω => by simp,
    fun k ω => by simp, ?_, ?_, ?_⟩
  · intro k ω
    cases k with
    | zero => simpa using Real.rpow_nonneg (hSnn 1 ω) _
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact Real.rpow_le_rpow (hSnn _ ω) (hSmono (k + 1) ω) hq1
  · intro k _
    cases k with
    | zero => simpa using stronglyMeasurable_const (b := (0 : ℝ))
    | succ k =>
      have h : Measurable[𝒢 (k + 1)] (S (k + 1)) :=
        (sq_sum_stronglyMeasurable 𝒢 hM S hS (k + 1)).measurable
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact (h.pow_const (q - 1)).stronglyMeasurable
  · intro k hk ω
    cases k with
    | zero =>
      simpa using Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) * b ^ 2) (q - 1)
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [abs_of_nonneg (Real.rpow_nonneg (hSnn _ ω) _)]
      have h := (sq_sum_bounds S hS hinc ω (k + 1) hk).2
      have hkN : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
      exact Real.rpow_le_rpow (hSnn _ ω) (by nlinarith [sq_nonneg b]) hq1

/-- **The Garsia–Neveu inequality for the square sum.**  For `q ≥ 1` and `N ≥ 1`,
`E S_N^q ≤ q E[S_N^{q-1} · 8 M²]`, where `M` dominates `|Z_k|`, `k ≤ N`. -/
lemma sq_sum_rpow_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} (hN : 1 ≤ N) {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    (M : Ω → ℝ) (hMm : Measurable M) {CM : ℝ} (hMC : ∀ ω, |M ω| ≤ CM)
    (hMZ : ∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, S N ω ^ q ∂P ≤ q * ∫ ω, S N ω ^ (q - 1) * (8 * M ω ^ 2) ∂P := by
  have hq0 : 0 < q := by linarith
  obtain ⟨a, ha0, haS, hamono, ham, haC⟩ := sq_sum_weights 𝒢 hM S hS hinc hq
  have hSs : ∀ k ω, S (k + 1) ω = S k ω + (Z (k + 1) ω - Z k ω) ^ 2 := fun k ω => by
    rw [hS, hS, Finset.sum_range_succ]
  have hSnn : ∀ k ω, 0 ≤ S k ω := fun k ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSmono : ∀ k ω, S k ω ≤ S (k + 1) ω := fun k ω => by
    rw [hSs]
    nlinarith [sq_nonneg (Z (k + 1) ω - Z k ω)]
  have hS0 : ∀ ω, S 0 ω = 0 := fun ω => by simp [hS]
  have haN : ∀ ω, a N ω = S N ω ^ (q - 1) := fun ω => by
    obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [hN']
    exact haS N' ω
  have hBS : ∀ k, k ≤ N → BddMeas (S k) := fun k hk => bddMeas_S hM S hS hinc hk
  have hBa : ∀ k, k ≤ N → BddMeas (a k) := fun k hk =>
    ⟨((ham k hk).mono (𝒢.le k)).measurable, _, haC k hk⟩
  have hBd2 : ∀ k, k < N → BddMeas (fun ω => (Z (k + 1) ω - Z k ω) ^ 2) := fun k hk =>
    ((bddMeas_Z hM hZ0 hinc hk).sub (bddMeas_Z hM hZ0 hinc hk.le)).pow 2
  have hIsum : Integrable (fun ω => q * ∑ k ∈ Finset.range N,
      a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2) P :=
    (integrable_finsetSum _ fun k hk =>
      (((hBa (k + 1) (Finset.mem_range.mp hk)).mul
        (hBd2 k (Finset.mem_range.mp hk))).integrable P)).const_mul q
  have hpt : ∀ ω, S N ω ^ q ≤
      q * ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 := by
    intro ω
    have h := rpow_le_sum_tangent (fun k => S k ω) (hS0 ω) (fun k => hSmono k ω)
      (fun k => hSnn k ω) hq N
    refine h.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : S (k + 1) ω - S k ω = (Z (k + 1) ω - Z k ω) ^ 2 := by rw [hSs]; ring
    simp only [e, haS]
  have hkey := sq_sum_key P 𝒢 Z hM hZ0 S hS hinc a ha0 hamono ham haC M hMm hMC hMZ
  calc ∫ ω, S N ω ^ q ∂P
      ≤ ∫ ω, q * ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 ∂P :=
        integral_mono (((hBS N le_rfl).rpow (fun ω => hSnn N ω) hq0.le).integrable P) hIsum hpt
    _ = q * ∫ ω, ∑ k ∈ Finset.range N, a (k + 1) ω * (Z (k + 1) ω - Z k ω) ^ 2 ∂P :=
        integral_const_mul _ _
    _ ≤ q * ∫ ω, a N ω * (8 * M ω ^ 2) ∂P := mul_le_mul_of_nonneg_left hkey hq0.le
    _ = q * ∫ ω, S N ω ^ (q - 1) * (8 * M ω ^ 2) ∂P := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show a N ω * (8 * M ω ^ 2) = S N ω ^ (q - 1) * (8 * M ω ^ 2)
        rw [haN]

/-- **Real form of the comparison.**  For `q ≥ 1` and `N ≥ 1`,
`E S_N^q ≤ q^q E (8 M²)^q`. -/
lemma sq_sum_rpow_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) (S : ℕ → Ω → ℝ)
    (hS : ∀ k ω, S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2)
    {N : ℕ} (hN : 1 ≤ N) {b : ℝ} (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    (M : Ω → ℝ) (hMm : Measurable M) {CM : ℝ} (hMC : ∀ ω, |M ω| ≤ CM)
    (hMZ : ∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, S N ω ^ q ∂P ≤ q ^ q * ∫ ω, (8 * M ω ^ 2) ^ q ∂P := by
  have hSnn : ∀ ω, 0 ≤ S N ω := fun ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmain := sq_sum_rpow_le P 𝒢 Z hM hZ0 S hS hN hinc M hMm hMC hMZ hq
  refine garsia_holder P hq (s := S N) (g := fun ω => 8 * M ω ^ 2)
    (bddMeas_S hM S hS hinc le_rfl).1 (measurable_const.mul (hMm.pow_const 2)) hSnn
    (fun ω => by positivity) (Cs := (N : ℝ) * b ^ 2)
    (fun ω => (sq_sum_bounds S hS hinc ω N le_rfl).2) (Cg := 8 * CM ^ 2) ?_ hmain
  intro ω
  have h1 : M ω ^ 2 ≤ CM ^ 2 := by
    rw [← sq_abs (M ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMC ω) 2
  linarith


/-- **The maximal function.**  For a martingale `Z` from `0` with increments at most `b` on
`i < N`, `M = max_{k ≤ N} |Z_k|` is a bounded measurable function dominating each `|Z_k|`,
`k ≤ N`, and the `ℝ≥0∞`-valued supremum `⨆ k ≤ N, ofReal |Z_k|` is `ofReal M`. -/
lemma maximal_function_facts {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ} (hM : Martingale Z 𝒢 P)
    (hZ0 : ∀ ω, Z 0 ω = 0) {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) :
    ∃ M : Ω → ℝ, Measurable M ∧ (∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω) ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω, M ω ≤ N * b) ∧
      ∀ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) = ENNReal.ofReal (M ω) := by
  obtain ⟨M, hMdef⟩ : ∃ M : Ω → ℝ, ∀ ω, M ω =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => |Z k ω|) :=
    ⟨fun ω => _, fun _ => rfl⟩
  have hZm : ∀ k, Measurable (Z k) := fun k =>
    ((hM.stronglyMeasurable k).mono (𝒢.le k)).measurable
  have hMm : Measurable M := by
    have h := Finset.measurable_sup' (s := Finset.range (N + 1)) Finset.nonempty_range_add_one
      (f := fun k => fun ω => |Z k ω|) (fun k _ => (hZm k).abs)
    have hfun : M = (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => fun ω => |Z k ω|) := by
      funext ω
      rw [hMdef, Finset.sup'_apply]
    rw [hfun]
    exact h
  have hMZ : ∀ k, k ≤ N → ∀ ω, |Z k ω| ≤ M ω := fun k hk ω => by
    rw [hMdef]
    exact Finset.le_sup' (fun k => |Z k ω|) (Finset.mem_range.mpr (by omega))
  refine ⟨M, hMm, hMZ, fun ω => (abs_nonneg _).trans (hMZ 0 (Nat.zero_le _) ω), fun ω => ?_,
    fun ω => ?_⟩
  · rw [hMdef]
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    refine (abs_le_mul_of_increments hZ0 hinc ω k hk').trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hb.le
  · rw [hMdef, ofReal_sup', sup'_range_eq_iSup N (fun k => ENNReal.ofReal |Z k ω|)]

/-- For nonnegative `M`, `E (8 M²)^{p/2} = 8^{p/2} E M^p`. -/
lemma integral_rpow_eight_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : Ω → ℝ}
    (hM0 : ∀ ω, 0 ≤ M ω) (p : ℝ) :
    ∫ ω, (8 * M ω ^ 2) ^ (p / 2) ∂P = 8 ^ (p / 2) * ∫ ω, M ω ^ p ∂P := by
  have hpt : ∀ ω, (8 * M ω ^ 2) ^ (p / 2) = 8 ^ (p / 2) * M ω ^ p := fun ω => by
    have h2 : ((2 : ℕ) : ℝ) * (p / 2) = p := by push_cast; ring
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← Real.rpow_natCast (M ω) 2,
      ← Real.rpow_mul (hM0 ω), h2]
  simp_rw [hpt]
  exact integral_const_mul _ _

/-- **The square function is bounded by the maximal function for `p ≥ 2`** (Garsia–Neveu).
For every discrete real martingale `Z` from `0` with increments at most `b` on `i < N`,
`E (∑_{i<N} (Z_{i+1} - Z_i)²)^{p/2} ≤ (4 p)^{p/2} E (max_{k ≤ N} |Z_k|)^p`; the term `b^p` of
`SquareMaximalBoundedAt` is not needed. -/
theorem squareMaximalBoundedAt_ge_two {p : ℝ} (hp : 2 ≤ p) : SquareMaximalBoundedAt p := by
  have hq : 1 ≤ p / 2 := by linarith
  have hC0 : 0 < (8 * (p / 2)) ^ (p / 2) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨(8 * (p / 2)) ^ (p / 2), hC0, ?_⟩
  intro Ω _ P _ 𝒢 Z N b hb hM hZ0 hinc
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∀ ω, ENNReal.ofReal (∑ i ∈ Finset.range 0, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) =
        0 := fun ω => by
      simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < p / 2)]
    simp only [h0, lintegral_zero]
    exact zero_le
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℝ, ∀ k ω,
      S k ω = ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) ^ 2 := ⟨fun k ω => _, fun _ _ => rfl⟩
  obtain ⟨M, hMm, hMZ, hM0, hMb, hconv⟩ := maximal_function_facts hM hZ0 hb hinc
  have hSnn : ∀ ω, 0 ≤ S N ω := fun ω => by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hreal := sq_sum_rpow_bound P 𝒢 Z hM hZ0 S hS hN hinc M hMm (CM := N * b)
    (fun ω => by rw [abs_of_nonneg (hM0 ω)]; exact hMb ω) hMZ hq
  have hL1 : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P =
      ∫⁻ ω, ENNReal.ofReal (S N ω) ^ (p / 2) ∂P :=
    lintegral_congr fun ω => by rw [hS]
  have hL : ∫⁻ ω, ENNReal.ofReal (S N ω) ^ (p / 2) ∂P =
      ENNReal.ofReal (∫ ω, S N ω ^ (p / 2) ∂P) :=
    lintegral_ofReal_rpow_eq (bddMeas_S hM S hS hinc le_rfl).1 hSnn
      (fun ω => (sq_sum_bounds S hS hinc ω N le_rfl).2) (by linarith)
  have hR : ∫⁻ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) ^ p ∂P =
      ENNReal.ofReal (∫ ω, M ω ^ p ∂P) := by
    have h1 : ∫⁻ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) ^ p ∂P =
        ∫⁻ ω, ENNReal.ofReal (M ω) ^ p ∂P := lintegral_congr fun ω => by rw [hconv]
    rw [h1]
    exact lintegral_ofReal_rpow_eq hMm hM0 hMb (by linarith)
  have hJ : ∫ ω, S N ω ^ (p / 2) ∂P ≤ (8 * (p / 2)) ^ (p / 2) * ∫ ω, M ω ^ p ∂P := by
    calc ∫ ω, S N ω ^ (p / 2) ∂P ≤ (p / 2) ^ (p / 2) * ∫ ω, (8 * M ω ^ 2) ^ (p / 2) ∂P := hreal
      _ = (8 * (p / 2)) ^ (p / 2) * ∫ ω, M ω ^ p ∂P := by
        rw [integral_rpow_eight_sq P hM0 p,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by linarith : (0 : ℝ) ≤ p / 2)]
        ring
  rw [hL1, hL, hR]
  calc ENNReal.ofReal (∫ ω, S N ω ^ (p / 2) ∂P)
      ≤ ENNReal.ofReal ((8 * (p / 2)) ^ (p / 2) * ∫ ω, M ω ^ p ∂P) :=
        ENNReal.ofReal_le_ofReal hJ
    _ = ENNReal.ofReal ((8 * (p / 2)) ^ (p / 2)) * ENNReal.ofReal (∫ ω, M ω ^ p ∂P) :=
        ENNReal.ofReal_mul hC0.le
    _ ≤ ENNReal.ofReal ((8 * (p / 2)) ^ (p / 2)) *
          (ENNReal.ofReal (∫ ω, M ω ^ p ∂P) + ENNReal.ofReal (b ^ p)) := by
        gcongr
        exact le_self_add

end

end LatticeProb.Process.StoppedSkeleton.SquareMaxHigh

namespace LatticeProb.Process.BdgUpperContinuous

noncomputable section

/-- **The discrete lower Burkholder bound with a bounded-increment term** from the discrete
square-function bound `E S^{p/2} ≤ C₁ (E (max_k |Z_k|)^p + b^p)`, for `p > 1`.  Doob's `Lᵖ`
maximal inequality `E (max_{k ≤ N} |Z_k|)^p ≤ C_D E |Z_N|^p` replaces the maximal function by the
terminal value, and the two constants combine into `C₁ max(C_D, 1)`. -/
theorem discreteLowerBoundedAt_of_squareMaximal {p : ℝ} (hp : 1 < p)
    (h : LatticeProb.Process.StoppedSkeleton.SquareMaximalBoundedAt p) : DiscreteLowerBoundedAt p := by
  obtain ⟨C₁, hC₁, h₁⟩ := h
  obtain ⟨D, hD, hD'⟩ := LatticeProb.Process.RandomizedFreedman.doobMaximalLp_holds p hp
  refine ⟨C₁ * max D 1, mul_pos hC₁ (lt_max_of_lt_right one_pos), ?_⟩
  intro Ω _ P _ 𝒢 Z N b hb hM h0 hinc
  calc ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
      ≤ ENNReal.ofReal C₁ *
          (∫⁻ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) ^ p ∂P + ENNReal.ofReal (b ^ p)) :=
        h₁ P 𝒢 Z N hb hM h0 hinc
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal D * ∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
        have hmax := hD' P 𝒢 Z N hM h0
        gcongr
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (max D 1) *
          (∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P + ENNReal.ofReal (b ^ p))) := by
        rw [mul_add (ENNReal.ofReal (max D 1))]
        have hDM : ENNReal.ofReal D ≤ ENNReal.ofReal (max D 1) :=
          ENNReal.ofReal_le_ofReal (le_max_left D 1)
        have h1M : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max D 1) := ENNReal.one_le_ofReal.2 (le_max_right D 1)
        have hB : ENNReal.ofReal (b ^ p) ≤ ENNReal.ofReal (max D 1) * ENNReal.ofReal (b ^ p) :=
          le_mul_of_one_le_left zero_le h1M
        gcongr
    _ = ENNReal.ofReal (C₁ * max D 1) *
          (∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
        rw [ENNReal.ofReal_mul hC₁.le, mul_assoc]

/-- **The stopped dyadic skeleton for the lower bound** holds: the five component statements
(optional stopping for continuous martingales, the stopping-time property of the localising time,
the path bookkeeping, the full-sum identity on the good event and the `Lᵖ` contraction of stopping)
are proved. -/
theorem stoppedDyadicSkeletonLower_holds : StoppedDyadicSkeletonLower :=
  LowerAssembly.stoppedDyadicSkeletonLower_of_components
    (LatticeProb.Process.StoppedSkeleton.ContinuousOST.continuousStoppedMartingale_of_countable
      LatticeProb.Process.StoppedSkeleton.CountableOST.countableRangeStoppedIntegral_holds)
    LatticeProb.Process.StoppedSkeleton.StoppingTime.skeletonStopIsStoppingTime_holds
    LatticeProb.Process.StoppedSkeleton.PathFacts.skeletonPathFacts_holds
    LatticeProb.Process.StoppedSkeleton.FullSum.skeletonFullSum_holds
    LatticeProb.Process.StoppedSkeleton.StoppedLp.stoppedLpContraction_holds

/-- **The lower half of the Burkholder–Davis–Gundy statement at the exponent `p`** from the
discrete square-function bound at `p`. -/
theorem bdgLowerAt_of_squareMaximal {p : ℝ} (hp : 1 < p)
    (h : LatticeProb.Process.StoppedSkeleton.SquareMaximalBoundedAt p) : BdgLowerAt p :=
  LowerPassage.bdgLowerAt_of_skeleton hp (discreteLowerBoundedAt_of_squareMaximal hp h)
    stoppedDyadicSkeletonLower_holds

/-- The Burkholder–Davis–Gundy statement, from the discrete square-function bound for
`p ≥ 2` (the range `1 < p < 2` is proved). -/
theorem burkholderDavisGundy_of_high
    (hHigh : ∀ p : ℝ, 2 ≤ p → LatticeProb.Process.StoppedSkeleton.SquareMaximalBoundedAt p) :
    ∀ p : ℝ, 1 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
          (Q : Ω → Fin 1 → Fin 1 → ℝ),
          Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
          LatticeProb.Process.HasQuadCovar P M T Q →
            ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
                ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ∧
              ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ≤ ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P := by
  intro p hp
  have hLow : BdgLowerAt p := by
    by_cases h2 : 2 ≤ p
    · exact bdgLowerAt_of_squareMaximal hp (hHigh p h2)
    · exact bdgLowerAt_of_squareMaximal hp
        (LatticeProb.Process.StoppedSkeleton.SquareMaxLow.squareMaximalBoundedAt_lt_two hp (lt_of_not_ge h2))
  have hUp : BdgUpperAt p := burkholderDavisGundyUpper_holds p hp
  obtain ⟨c, hc, hL⟩ := hLow
  obtain ⟨C, hC, hU⟩ := hUp
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ P _ ℱ M T Q hM hcont h0 hQ
  exact ⟨hL P ℱ M T Q hM hcont h0 hQ, hU P ℱ M T Q hM hcont h0 hQ⟩

/-- **The Burkholder–Davis–Gundy statement holds.** -/
theorem burkholderDavisGundy_holds :
    ∀ p : ℝ, 1 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
          (Q : Ω → Fin 1 → Fin 1 → ℝ),
          Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
          LatticeProb.Process.HasQuadCovar P M T Q →
            ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
                ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ∧
              ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ≤ ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P :=
  burkholderDavisGundy_of_high fun _ hp =>
    LatticeProb.Process.StoppedSkeleton.SquareMaxHigh.squareMaximalBoundedAt_ge_two hp

end

end LatticeProb.Process.BdgUpperContinuous
