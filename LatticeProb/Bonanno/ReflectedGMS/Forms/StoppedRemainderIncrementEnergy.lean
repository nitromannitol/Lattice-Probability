/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderIncrementEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyCoreAgreement
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyStationaryIsometry
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPairIncrement
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupEnergyBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedDynkinFullDomain

/-!
# Zero energy of the full-domain remainder along uniform partitions (unstopped, stationary)

`Forms/FullEnergyZeroEnergy` shows `E_m[R_t²]/t → 0` for the remainder
`R = (u(X) − u(X_0)) − M` of a full-domain vector `U`, at time `0` only.  The stopped
vanishing statement of `Forms/StoppedRemainderVanishing` needs the *partition* form: for the
uniform grid `t_k = k t / n` of `[0, t]`,

`Σ_{k < n} E_m[(R_{t_{k+1}} − R_{t_k})²] → 0`  as `n → ∞`,

under the unnormalized stationary speed law `reflectedSpeedLaw PF m`.  This module proves it.

* `remainderIncrement_sq_integral_le`: `E_m[(R_t − R_s)²] ≤ 8 (t − s) 𝓔(U)` for every `s ≤ t`,
  from the stationary pair law (`StationaryPairIncrement.integral_sq_sub_unweight_shift`), the
  semigroup deficit bound and the exact stationary increment isometry of the martingale part.
* `remainderIncrement_core_sq_integral_le`: for a resolvent-core vector the remainder increment
  is the drift occupation over `[s, t]`, bounded by `(t − s) · 2K`, so its stationary second
  moment is `O((t − s)²)`.
* `remainderIncrement_partition_sum_tendsto_zero`: split `U = (U − Q_j) + Q_j` along the
  canonical core approximation; the first part contributes `16 t 𝓔(U − Q_j)`, the second
  `O(1/n)`.

Nothing here is stopped, and nothing here uses local harmonicity.  The speed `m` is generic
and summable, as everywhere in the fast-side modules; the consumer instantiates it at the
summable fast speed.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The increments -/

/-- The raw vertex-path increment of `W` over `[s, t]`, with `none` read as `0`. -/
noncomputable def rawPathIncrement (G : ConductanceGraph V) (m : V → ℝ)
    (PF : ProcessFamily V) (W : hilbertDomain G m) (s t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  (PF.X t ω).elim 0 (unweight m (valueInclusion G m W)) -
    (PF.X s ω).elim 0 (unweight m (valueInclusion G m W))

/-- The increment over `[s, t]` of the full-domain remainder `u(X) − u(X_0) − M`. -/
noncomputable def remainderIncrement (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V)
    (W : hilbertDomain G m) (s t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  rawPathIncrement G m PF W s t ω -
    (fullEnergyMartingaleLimit G m hm PF default W t ω -
      fullEnergyMartingaleLimit G m hm PF default W s ω)

theorem rawPathIncrement_sub (G : ConductanceGraph V) (m : V → ℝ)
    (PF : ProcessFamily V) (W₁ W₂ : hilbertDomain G m) (s t : ℝ≥0) (ω : PF.Ω) :
    rawPathIncrement G m PF (W₁ - W₂) s t ω =
      rawPathIncrement G m PF W₁ s t ω - rawPathIncrement G m PF W₂ s t ω := by
  have hdecode (q : Option V) :
      q.elim 0 (unweight m (valueInclusion G m (W₁ - W₂))) =
        q.elim 0 (unweight m (valueInclusion G m W₁)) -
          q.elim 0 (unweight m (valueInclusion G m W₂)) := by
    cases q with
    | none => simp
    | some x =>
      simp only [Option.elim_some, map_sub, unweight, lp.coeFn_sub, Pi.sub_apply, sub_div]
  simp only [rawPathIncrement, hdecode]
  ring

/-- The uniform grid `k t / n` on `[0, t]`. -/
noncomputable def uniformGrid (t : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * t / n

theorem uniformGrid_le_succ (t : ℝ≥0) (n k : ℕ) :
    uniformGrid t n k ≤ uniformGrid t n (k + 1) := by
  unfold uniformGrid
  gcongr
  exact_mod_cast Nat.le_succ k

theorem uniformGrid_succ_sub (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    ((uniformGrid t n (k + 1) : ℝ≥0) : ℝ) - (uniformGrid t n k : ℝ) = (t : ℝ) / n := by
  unfold uniformGrid
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp
  ring

/-- The uniform-partition square sum of the remainder increments of `U` on `[0, t]`. -/
noncomputable def remainderPartitionSquareSum (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V)
    (U : hilbertDomain G m) (t : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    ∫ ω, (remainderIncrement G m hm PF default U (uniformGrid t n k) (uniformGrid t n (k + 1)) ω)
      ^ 2 ∂reflectedSpeedLaw PF m

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V)

include h hG hm hmsum

/-! ## The stationary increment bound for a general full-domain vector -/

theorem remainderIncrement_memLp_two (W : hilbertDomain G m) (s t : ℝ≥0) :
    MemLp (remainderIncrement G m hm PF default W s t) 2 (reflectedSpeedLaw PF m) :=
  ((memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m W) t).sub
    (memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m W) s)).sub
    ((fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw h hG hm hmsum default W t).sub
      (fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw h hG hm hmsum default W s))

/-- **Stationary second moment of a remainder increment**: `E_m[(R_t − R_s)²] ≤ 8 (t−s) 𝓔(W)`. -/
theorem remainderIncrement_sq_integral_le (W : hilbertDomain G m) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (remainderIncrement G m hm PF default W s t ω) ^ 2 ∂reflectedSpeedLaw PF m) ≤
      8 * ((t : ℝ) - s) * G.Energy (unweight m (valueInclusion G m W)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let P := reflectedSpeedLaw PF m
  let A : PF.Ω → ℝ := rawPathIncrement G m PF W s t
  let D : PF.Ω → ℝ := fun ω ↦ fullEnergyMartingaleLimit G m hm PF default W t ω -
    fullEnergyMartingaleLimit G m hm PF default W s ω
  have hA2 : MemLp A 2 P :=
    (memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m W) t).sub
      (memLp_two_reflected_unweight_speedLaw h hG hm hmsum (valueInclusion G m W) s)
  have hD2 : MemLp D 2 P :=
    (fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw h hG hm hmsum default W t).sub
      (fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw h hG hm hmsum default W s)
  have hAi : Integrable (fun ω ↦ (A ω) ^ 2) P := hA2.integrable_sq
  have hDi : Integrable (fun ω ↦ (D ω) ^ 2) P := hD2.integrable_sq
  have hADi : Integrable (fun ω ↦ (A ω - D ω) ^ 2) P := (hA2.sub hD2).integrable_sq
  have hb : (∫ ω, (A ω - D ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (A ω) ^ 2 ∂P) + 2 * (∫ ω, (D ω) ^ 2 ∂P) := by
    calc
      _ ≤ ∫ ω, 2 * (A ω) ^ 2 + 2 * (D ω) ^ 2 ∂P := by
        apply integral_mono_ae hADi ((hAi.const_mul 2).add (hDi.const_mul 2))
        filter_upwards [] with ω
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (A ω + D ω)]
      _ = _ := by
        rw [integral_add (hAi.const_mul 2) (hDi.const_mul 2), integral_const_mul,
          integral_const_mul]
  -- the raw increment: stationary pair law + semigroup deficit
  have hAsq : (∫ ω, (A ω) ^ 2 ∂P) =
      2 * (‖valueInclusion G m W‖ ^ 2 -
        ⟪valueInclusion G m W, fullFormSemigroup G m (t - s) (valueInclusion G m W)⟫_ℝ) := by
    have key := StationaryPairIncrement.integral_sq_sub_unweight_shift h hG hm hmsum
      (valueInclusion G m W) s (t - s)
    rw [add_tsub_cancel_of_le hst] at key
    exact key
  have hdef := fullFormSemigroup_quadratic_deficit_le_energy G m hm W (t - s)
  have hcoe : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - s := NNReal.coe_sub hst
  rw [hcoe] at hdef
  -- the martingale increment: exact stationary isometry
  have hDsq : (∫ ω, (D ω) ^ 2 ∂P) =
      2 * ((t : ℝ) - s) * G.Energy (unweight m (valueInclusion G m W)) :=
    fullEnergyMartingaleLimit_stationary_increment_energy h hG hm hmsum default W hst
  change (∫ ω, (A ω - D ω) ^ 2 ∂P) ≤ _
  rw [hAsq, hDsq] at hb
  nlinarith [hb, hdef]

/-! ## The core vectors: the remainder increment is the drift occupation over `[s, t]` -/

omit h hG hm hmsum in
theorem countableResolventCoreFeature_eq_unweight_valueInclusion
    (q : CountableResolventCoreIndex V) :
    countableResolventCoreFeature G m q =
      unweight m (valueInclusion G m (countableResolventCoreVector G m q)) := rfl

/-- Almost surely under every starting law, the remainder increment of a core vector over
`[s, t]` is the increment of its bounded drift occupation. -/
theorem remainderIncrement_core_ae_eq (q : CountableResolventCoreIndex V) (z : V)
    (s t : ℝ≥0) :
    remainderIncrement G m hm PF default (countableResolventCoreVector G m q) s t =ᵐ[PF.P z]
      fun ω ↦ boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω := by
  filter_upwards [countableResolventCore_fullEnergyRemainder_ae h hG hm hmsum default z q t,
    countableResolventCore_fullEnergyRemainder_ae h hG hm hmsum default z q s] with ω ht hs
  simp only [remainderIncrement, rawPathIncrement,
    ← countableResolventCoreFeature_eq_unweight_valueInclusion]
  have ht' : rawResolventCorePotential G m q (PF.X t ω) -
      rawResolventCorePotential G m q (PF.X 0 ω) -
      fullEnergyMartingaleLimit G m hm PF default (countableResolventCoreVector G m q) t ω =
      boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω := ht
  have hs' : rawResolventCorePotential G m q (PF.X s ω) -
      rawResolventCorePotential G m q (PF.X 0 ω) -
      fullEnergyMartingaleLimit G m hm PF default (countableResolventCoreVector G m q) s ω =
      boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω := hs
  simp only [rawResolventCorePotential] at ht' hs'
  linarith

omit h hG hmsum in
/-- The drift occupation increment over `[s, t]` is bounded by `(t − s) · 2K`. -/
theorem abs_boundedStateOccupationVersion_sub_le (q : CountableResolventCoreIndex V)
    {s t : ℝ≥0} (hst : s ≤ t) (ω : PF.Ω) :
    |boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω| ≤
      ((t : ℝ) - s) * (2 * countableResolventCoreBound q) := by
  have hf : ∃ C : ℝ, ∀ x, |resolventCoreDrift G m q x| ≤ C :=
    ⟨2 * countableResolventCoreBound q, fun x ↦ by
      simpa only [Real.norm_eq_abs] using norm_resolventCoreDrift_le G m hm q x⟩
  have key := stopped_boundedStateOccupationVersion_sub_eq_integral PF
    (resolventCoreDrift G m q) hf (fun _ ↦ (⊤ : WithTop ℝ≥0)) hst ω
  simp only [stoppedProcess_const_top, WithTop.coe_lt_top, ite_true] at key
  rw [key, ← Real.norm_eq_abs]
  have hts : (s : ℝ) ≤ t := NNReal.coe_le_coe.mpr hst
  have hvol : (volume : Measure ℝ) (Icc (s : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  calc
    ‖∫ r in Icc (s : ℝ) t,
        resolventCoreDrift G m q (Theorem16.dyadicLimit PF.X r.toNNReal ω)‖ ≤
        (2 * countableResolventCoreBound q) * (volume : Measure ℝ).real (Icc (s : ℝ) t) :=
      norm_setIntegral_le_of_norm_le_const hvol fun r _ ↦
        norm_resolventCoreDrift_le G m hm q _
    _ = ((t : ℝ) - s) * (2 * countableResolventCoreBound q) := by
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring

/-- **Stationary second moment of a core remainder increment**: quadratic in `t − s`. -/
theorem remainderIncrement_core_sq_integral_le (q : CountableResolventCoreIndex V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (remainderIncrement G m hm PF default (countableResolventCoreVector G m q) s t ω) ^ 2
        ∂reflectedSpeedLaw PF m) ≤
      (((t : ℝ) - s) * (2 * countableResolventCoreBound q)) ^ 2 *
        (reflectedSpeedLaw PF m).real Set.univ := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let P := reflectedSpeedLaw PF m
  let C : ℝ := ((t : ℝ) - s) * (2 * countableResolventCoreBound q)
  let B : PF.Ω → ℝ := fun ω ↦ boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω -
    boundedStateOccupationVersion PF (resolventCoreDrift G m q) s ω
  have hae : remainderIncrement G m hm PF default (countableResolventCoreVector G m q) s t
      =ᵐ[P] B := by
    apply (ae_reflectedSpeedLaw_iff PF m hm _).2
    intro z
    exact remainderIncrement_core_ae_eq h hG hm hmsum default q z s t
  have hBbound : ∀ ω, ‖B ω‖ ≤ C := fun ω ↦ by
    rw [Real.norm_eq_abs]
    exact abs_boundedStateOccupationVersion_sub_le hm q hst ω
  have hBmeas : AEStronglyMeasurable B P :=
    (((stronglyMeasurable_boundedStateOccupationVersion PF (resolventCoreDrift G m q) t).mono
      (PF.naturalFiltration.le t)).sub
      ((stronglyMeasurable_boundedStateOccupationVersion PF (resolventCoreDrift G m q) s).mono
        (PF.naturalFiltration.le s))).aestronglyMeasurable
  have hB2 : MemLp B 2 P := MemLp.of_bound hBmeas C (Eventually.of_forall hBbound)
  have hCnonneg : 0 ≤ C := by
    have hK : 0 ≤ 2 * countableResolventCoreBound q := by
      unfold countableResolventCoreBound Finsupp.sum
      positivity
    have hts : 0 ≤ (t : ℝ) - s := by
      have := NNReal.coe_le_coe.mpr hst
      linarith
    exact mul_nonneg hts hK
  calc
    (∫ ω, (remainderIncrement G m hm PF default (countableResolventCoreVector G m q) s t ω) ^ 2
        ∂reflectedSpeedLaw PF m) = ∫ ω, (B ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω]
    _ ≤ ∫ _ : PF.Ω, C ^ 2 ∂P := by
      apply integral_mono_ae hB2.integrable_sq (integrable_const (C ^ 2))
      filter_upwards [] with ω
      calc
        (B ω) ^ 2 = ‖B ω‖ ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
        _ ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg _) hCnonneg).2 (hBbound ω)
    _ = C ^ 2 * P.real Set.univ := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring

/-! ## The partition sums -/


omit h hG hmsum in
theorem energy_sub_core_tendsto_zero (U : hilbertDomain G m) :
    Tendsto (fun j : ℕ ↦ G.Energy (unweight m (valueInclusion G m
      (U - countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U j))))) atTop (𝓝 0) := by
  let Q : ℕ → hilbertDomain G m := fun j ↦ countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U j)
  let D : ℕ → hilbertDomain G m := fun j ↦ U - Q j
  have hQ : Tendsto Q atTop (𝓝 U) :=
    countableResolventCoreVector_tendsto_of_geometric_bound G m U (fullEnergyCoreIndex G m hm U)
      (fullEnergyCoreIndex_bound G m hm U)
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [D, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ U) atTop (𝓝 U)).sub hQ
  have hg := ((gradientInclusion G m).continuous.tendsto 0).comp hD
  have henergy : ∀ j, ‖gradientInclusion G m (D j)‖ ^ 2 =
      G.Energy (unweight m (valueInclusion G m (D j))) := fun j ↦ by
    rw [gradientInclusion_eq, weightedGradient_norm_sq]
  have := (hg.norm.pow 2)
  simp only [Function.comp_def, map_zero, norm_zero] at this
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at this
  exact this.congr fun j ↦ henergy j

/-- **Zero energy along uniform partitions**: the stationary square sums of the remainder
increments of `U` on the uniform grids of `[0, t]` tend to `0`. -/
theorem remainderPartitionSquareSum_tendsto_zero (U : hilbertDomain G m) (t : ℝ≥0) :
    Tendsto (remainderPartitionSquareSum G m hm PF default U t) atTop (𝓝 0) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let P := reflectedSpeedLaw PF m
  let mV : ℝ := P.real Set.univ
  let Q : ℕ → hilbertDomain G m := fun j ↦
    countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U j)
  let K : ℕ → ℝ := fun j ↦ 2 * countableResolventCoreBound (fullEnergyCoreIndex G m hm U j)
  let a : ℕ → ℝ := fun j ↦ 16 * (t : ℝ) * G.Energy (unweight m (valueInclusion G m (U - Q j)))
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_zero] using (energy_sub_core_tendsto_zero hm U).const_mul (16 * (t : ℝ))
  -- the one-increment bound after splitting `U = (U − Q_j) + Q_j`
  have hsplit : ∀ (j : ℕ) {s r : ℝ≥0}, s ≤ r →
      (∫ ω, (remainderIncrement G m hm PF default U s r ω) ^ 2 ∂P) ≤
        16 * ((r : ℝ) - s) * G.Energy (unweight m (valueInclusion G m (U - Q j))) +
          2 * (((r : ℝ) - s) * K j) ^ 2 * mV := by
    intro j s r hsr
    have hae : remainderIncrement G m hm PF default U s r =ᵐ[P]
        fun ω ↦ remainderIncrement G m hm PF default (U - Q j) s r ω +
          remainderIncrement G m hm PF default (Q j) s r ω := by
      apply (ae_reflectedSpeedLaw_iff PF m hm _).2
      intro z
      have hr := fullEnergyMartingaleLimit_add_ae h hG hm hmsum default z (U - Q j) (Q j) r
      have hs := fullEnergyMartingaleLimit_add_ae h hG hm hmsum default z (U - Q j) (Q j) s
      rw [sub_add_cancel] at hr hs
      filter_upwards [hr, hs] with ω hωr hωs
      simp only [Pi.add_apply] at hωr hωs
      have hraw : rawPathIncrement G m PF U s r ω =
          rawPathIncrement G m PF (U - Q j) s r ω + rawPathIncrement G m PF (Q j) s r ω := by
        rw [rawPathIncrement_sub]
        ring
      simp only [remainderIncrement, hωr, hωs, hraw]
      ring
    have h1 := remainderIncrement_memLp_two h hG hm hmsum default (U - Q j) s r
    have h2 := remainderIncrement_memLp_two h hG hm hmsum default (Q j) s r
    calc
      (∫ ω, (remainderIncrement G m hm PF default U s r ω) ^ 2 ∂P) =
          ∫ ω, (remainderIncrement G m hm PF default (U - Q j) s r ω +
            remainderIncrement G m hm PF default (Q j) s r ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hae] with ω hω
        rw [hω]
      _ ≤ ∫ ω, 2 * (remainderIncrement G m hm PF default (U - Q j) s r ω) ^ 2 +
            2 * (remainderIncrement G m hm PF default (Q j) s r ω) ^ 2 ∂P := by
        apply integral_mono_ae (h1.add h2).integrable_sq
          ((h1.integrable_sq.const_mul 2).add (h2.integrable_sq.const_mul 2))
        filter_upwards [] with ω
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (remainderIncrement G m hm PF default (U - Q j) s r ω -
          remainderIncrement G m hm PF default (Q j) s r ω)]
      _ = 2 * (∫ ω, (remainderIncrement G m hm PF default (U - Q j) s r ω) ^ 2 ∂P) +
            2 * ∫ ω, (remainderIncrement G m hm PF default (Q j) s r ω) ^ 2 ∂P := by
        rw [integral_add (h1.integrable_sq.const_mul 2) (h2.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * (8 * ((r : ℝ) - s) * G.Energy (unweight m (valueInclusion G m (U - Q j)))) +
            2 * ((((r : ℝ) - s) * K j) ^ 2 * mV) := by
        gcongr
        · exact remainderIncrement_sq_integral_le h hG hm hmsum default (U - Q j) hsr
        · exact remainderIncrement_core_sq_integral_le h hG hm hmsum default _ hsr
      _ = _ := by ring
  -- the partition sum bound: `a j + 2 t² K_j² mV / n`
  have hsum : ∀ (j : ℕ) {n : ℕ}, n ≠ 0 →
      remainderPartitionSquareSum G m hm PF default U t n ≤
        a j + 2 * ((t : ℝ) * K j) ^ 2 * mV / n := by
    intro j n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      remainderPartitionSquareSum G m hm PF default U t n ≤
          ∑ _k ∈ Finset.range n,
            (16 * ((t : ℝ) / n) * G.Energy (unweight m (valueInclusion G m (U - Q j))) +
              2 * (((t : ℝ) / n) * K j) ^ 2 * mV) := by
        apply Finset.sum_le_sum
        intro k _
        have := hsplit j (uniformGrid_le_succ t n k)
        rwa [uniformGrid_succ_sub t hn k] at this
      _ = a j + 2 * ((t : ℝ) * K j) ^ 2 * mV / n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hn'' : (n : ℝ) ≠ 0 := hn'.ne'
        simp only [a]
        field_simp
  have hnonneg : ∀ n, 0 ≤ remainderPartitionSquareSum G m hm PF default U t n := fun n ↦
    Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Eventually.of_forall fun n ↦ hb.trans_le (hnonneg n)
  · intro b hb
    obtain ⟨j, hj⟩ := (ha.eventually (gt_mem_nhds (half_pos hb))).exists
    have htail : Tendsto (fun n : ℕ ↦ 2 * ((t : ℝ) * K j) ^ 2 * mV / n) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * ((t : ℝ) * K j) ^ 2 * mV)).div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa using this
    filter_upwards [htail.eventually (gt_mem_nhds (half_pos hb)),
      eventually_ne_atTop 0] with n hn hn0
    calc
      remainderPartitionSquareSum G m hm PF default U t n ≤
          a j + 2 * ((t : ℝ) * K j) ^ 2 * mV / n := hsum j hn0
      _ < b / 2 + b / 2 := add_lt_add hj hn
      _ = b := by ring

end ReflectedGMS
