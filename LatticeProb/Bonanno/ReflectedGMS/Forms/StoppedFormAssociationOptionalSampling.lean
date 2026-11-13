/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedFormAssociationOptionalSampling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BoundedStopping
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Optional sampling at two stopping times, and clock changes of bounded martingales

The bracket clauses of the area-clock process are obtained, as in the manuscript
(`p:thm:martingale`: "time change a local martingale by the inverses of the increasing
adapted clock"), by transporting a *fast-clock* stopped martingale through the pathwise
homeomorphic time change `X_t = Y_{h(t)}`.  The martingale property of `t ↦ N_{h(t)}`
for the time-changed filtration is Doob's optional sampling theorem at the two
stopping times `h(s) ≤ h(t)`.  Mathlib's optional sampling
(`MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_of_countable_range`) is
available only for stopping times with countable range; the project's
`Limit/ConditionalStopping.bounded_stopping_condExp_of_const_le` handles one arbitrary
bounded stopping time against a deterministic time.  This module supplies the two
missing generic steps, for real martingales on `ℝ≥0` with almost surely right-continuous
paths:

* `setIntegral_stoppedValue_eq_of_le_of_le_const` — optional sampling at two bounded
  stopping times `ρ ≤ σ ≤ T`, in set-integral form on the stopped σ-algebra of `ρ`,
  by the upward grid approximations `Limit/StoppingApproximation.boundedGridApprox`
  (countable range, monotone in the stopping time) and the `L¹` convergence of
  `Limit/BoundedStopping.bounded_stopping_L1`;
* `setIntegral_stoppedValue_eq_of_le_of_bound` — the same for arbitrary finite stopping
  times `ρ ≤ σ` when the martingale is uniformly bounded, by truncation at integer
  horizons and dominated convergence;
* `martingale_stoppedValue_clock_of_bound` — **the clock change**: for a monotone family
  of finite `F`-stopping times `h t`, a bounded a.s. right-continuous `F`-martingale `N`
  and any filtration `G` with `G t` contained (up to null sets) in the stopped
  σ-algebra of `h t`, the process `t ↦ N_{h t}` is a `G`-martingale as soon as it is
  `G`-adapted.

Nothing here mentions the reflected walk or any speed measure; no `Summable` hypothesis
occurs.  Adaptedness of the time-changed process to the target filtration and the
inclusion of the target filtration in the stopped σ-algebras are hypotheses, discharged by
the consumers.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.StoppedFormAssociation

open ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Monotonicity of the grid approximations -/

/-- Upward grid rounding is monotone. -/
theorem upperGrid_mono (n : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) :
    upperGrid n x ≤ upperGrid n y := by
  unfold upperGrid
  have h1 : ((⌈x * ((n : ℝ≥0) + 1)⌉₊ : ℕ) : ℝ≥0) ≤ ((⌈y * ((n : ℝ≥0) + 1)⌉₊ : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right hxy zero_le)
  gcongr

/-- The capped grid approximation is monotone in the stopping time. -/
theorem boundedGridApprox_mono {ρ σ : Ω → WithTop ℝ≥0} (hρσ : ∀ ω, ρ ω ≤ σ ω)
    (T : ℝ≥0) (hσT : ∀ ω, σ ω ≤ T) (n : ℕ) (ω : Ω) :
    boundedGridApprox ρ T n ω ≤ boundedGridApprox σ T n ω := by
  have hσne : σ ω ≠ ⊤ := (lt_of_le_of_lt (hσT ω) (WithTop.coe_lt_top T)).ne
  have hu : (ρ ω).untopA ≤ (σ ω).untopA := WithTop.untopA_mono hσne (hρσ ω)
  unfold boundedGridApprox
  exact min_le_min (WithTop.coe_le_coe.2 (upperGrid_mono n hu)) le_rfl

/-! ## Optional sampling at two bounded stopping times -/

/-- **Optional sampling at two bounded stopping times, set-integral form.**  For an
a.s. right-continuous real martingale `N`, stopping times `ρ ≤ σ ≤ T`, and an event
`B` of the stopped σ-algebra of `ρ`, the set integrals of `N_σ` and `N_ρ` over `B`
agree.  The grid approximations from above have countable range, so mathlib's
discrete optional sampling applies to them; the two `L¹` limits are
`bounded_stopping_L1`. -/
theorem setIntegral_stoppedValue_eq_of_le_of_le_const
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime F ρ) (hσ : IsStoppingTime F σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (T : ℝ≥0) (hσT : ∀ ω, σ ω ≤ T)
    {B : Set Ω} (hB : MeasurableSet[hρ.measurableSpace] B) :
    ∫ ω in B, stoppedValue N σ ω ∂P = ∫ ω in B, stoppedValue N ρ ω ∂P := by
  have hρT : ∀ ω, ρ ω ≤ T := fun ω => (hρσ ω).trans (hσT ω)
  have hBm : MeasurableSet B := hρ.measurableSpace_le B hB
  obtain ⟨hρnI, hρI, hρL1⟩ := bounded_stopping_L1 hN hρ T hρT hr
  obtain ⟨hσnI, hσI, hσL1⟩ := bounded_stopping_L1 hN hσ T hσT hr
  have hstep : ∀ n : ℕ,
      ∫ ω in B, stoppedValue N (boundedGridApprox σ T n) ω ∂P =
        ∫ ω in B, stoppedValue N (boundedGridApprox ρ T n) ω ∂P := by
    intro n
    have hρn := isStoppingTime_boundedGridApprox hρ T hρT n
    have hσn := isStoppingTime_boundedGridApprox hσ T hσT n
    have hle : boundedGridApprox ρ T n ≤ boundedGridApprox σ T n :=
      fun ω => boundedGridApprox_mono hρσ T hσT n ω
    have hce := hN.stoppedValue_ae_eq_condExp_of_le_of_countable_range hσn hρn hle
      (fun ω => (boundedGridApprox_bounds T hσT n ω).2)
      (finite_range_boundedGridApprox T hσT n).countable
      (finite_range_boundedGridApprox T hρT n).countable
    have hBn : MeasurableSet[hρn.measurableSpace] B :=
      hρ.measurableSpace_mono hρn (fun ω => (boundedGridApprox_bounds T hρT n ω).1) B hB
    calc ∫ ω in B, stoppedValue N (boundedGridApprox σ T n) ω ∂P
        = ∫ ω in B,
            (P[stoppedValue N (boundedGridApprox σ T n) | hρn.measurableSpace]) ω ∂P :=
          (setIntegral_condExp hρn.measurableSpace_le (hσnI n) hBn).symm
      _ = ∫ ω in B, stoppedValue N (boundedGridApprox ρ T n) ω ∂P :=
          setIntegral_congr_ae hBm (hce.mono fun ω hω _ => hω.symm)
  have hσlim := tendsto_setIntegral_of_L1' _ (Eventually.of_forall hσnI) hσL1 B
  have hρlim := tendsto_setIntegral_of_L1' _ (Eventually.of_forall hρnI) hρL1 B
  exact tendsto_nhds_unique hσlim (hρlim.congr fun n => (hstep n).symm)

/-! ## Optional sampling at finite stopping times, for a bounded martingale -/

/-- **Optional sampling at two finite stopping times for a uniformly bounded
martingale.**  Truncate both stopping times at integer horizons, apply the bounded
statement on the event `B ∩ {ρ ≤ T}` of the truncated stopped σ-algebra, and let the
horizon tend to infinity by dominated convergence. -/
theorem setIntegral_stoppedValue_eq_of_le_of_bound
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {C : ℝ} (hC : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ C)
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime F ρ) (hσ : IsStoppingTime F σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (hσfin : ∀ ω, σ ω ≠ ⊤)
    {B : Set Ω} (hB : MeasurableSet[hρ.measurableSpace] B) :
    ∫ ω in B, stoppedValue N σ ω ∂P = ∫ ω in B, stoppedValue N ρ ω ∂P := by
  have hBm : MeasurableSet B := hρ.measurableSpace_le B hB
  -- truncated stopping times and truncated events
  let ρT : ℕ → Ω → WithTop ℝ≥0 := fun T ω => min (ρ ω) ((T : ℝ≥0) : WithTop ℝ≥0)
  let σT : ℕ → Ω → WithTop ℝ≥0 := fun T ω => min (σ ω) ((T : ℝ≥0) : WithTop ℝ≥0)
  let BT : ℕ → Set Ω := fun T => B ∩ {ω | ρ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0)}
  have hρT : ∀ T : ℕ, IsStoppingTime F (ρT T) := fun T => hρ.min_const (T : ℝ≥0)
  have hσT : ∀ T : ℕ, IsStoppingTime F (σT T) := fun T => hσ.min_const (T : ℝ≥0)
  have hBT : ∀ T : ℕ, MeasurableSet[(hρT T).measurableSpace] (BT T) := fun T =>
    (hρ.measurableSet_inter_le_const_iff B (T : ℝ≥0)).1
      (hB.inter (hρ.measurableSet_le' (T : ℝ≥0)))
  have hBTm : ∀ T : ℕ, MeasurableSet (BT T) := fun T =>
    (hρT T).measurableSpace_le _ (hBT T)
  have hstep : ∀ T : ℕ,
      ∫ ω in BT T, stoppedValue N (σT T) ω ∂P = ∫ ω in BT T, stoppedValue N (ρT T) ω ∂P :=
    fun T => setIntegral_stoppedValue_eq_of_le_of_le_const hN hr (hρT T) (hσT T)
      (fun ω => min_le_min (hρσ ω) le_rfl) (T : ℝ≥0) (fun ω => min_le_right _ _) (hBT T)
  -- integrability of the truncated stopped values
  have hσTI : ∀ T : ℕ, Integrable (stoppedValue N (σT T)) P := fun T =>
    (bounded_stopping_L1 hN (hσT T) (T : ℝ≥0) (fun ω => min_le_right _ _) hr).2.1
  have hρTI : ∀ T : ℕ, Integrable (stoppedValue N (ρT T)) P := fun T =>
    (bounded_stopping_L1 hN (hρT T) (T : ℝ≥0) (fun ω => min_le_right _ _) hr).2.1
  -- the pointwise limits of the truncated indicator processes
  have hσev : ∀ ω, ∀ᶠ T : ℕ in atTop,
      B.indicator (stoppedValue N σ) ω = (BT T).indicator (stoppedValue N (σT T)) ω := by
    intro ω
    obtain ⟨T₀, hT₀⟩ := exists_nat_ge (σ ω).untopA
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hσle : σ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := by
      rw [← WithTop.untopA_le_iff (hσfin ω)]
      exact hT₀.trans (by exact_mod_cast hT)
    have hσeq : σT T ω = σ ω := min_eq_left hσle
    have hmem : ω ∈ BT T ↔ ω ∈ B := by
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, (hρσ ω).trans hσle⟩
    by_cases hωB : ω ∈ B
    · rw [indicator_of_mem (hmem.2 hωB), indicator_of_mem hωB]
      simp only [stoppedValue, hσeq]
    · rw [indicator_of_notMem (fun h => hωB (hmem.1 h)), indicator_of_notMem hωB]
  have hρev : ∀ ω, ∀ᶠ T : ℕ in atTop,
      B.indicator (stoppedValue N ρ) ω = (BT T).indicator (stoppedValue N (ρT T)) ω := by
    intro ω
    obtain ⟨T₀, hT₀⟩ := exists_nat_ge (σ ω).untopA
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hσle : σ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := by
      rw [← WithTop.untopA_le_iff (hσfin ω)]
      exact hT₀.trans (by exact_mod_cast hT)
    have hρle : ρ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := (hρσ ω).trans hσle
    have hρeq : ρT T ω = ρ ω := min_eq_left hρle
    have hmem : ω ∈ BT T ↔ ω ∈ B := by
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, hρle⟩
    by_cases hωB : ω ∈ B
    · rw [indicator_of_mem (hmem.2 hωB), indicator_of_mem hωB]
      simp only [stoppedValue, hρeq]
    · rw [indicator_of_notMem (fun h => hωB (hmem.1 h)), indicator_of_notMem hωB]
  -- dominated convergence for both sides
  have hbound : ∀ (τ : Ω → WithTop ℝ≥0) (S : Set Ω),
      ∀ᵐ ω ∂P, ‖S.indicator (stoppedValue N τ) ω‖ ≤ C := by
    intro τ S
    filter_upwards [hC] with ω hω
    refine (norm_indicator_le_norm_self _ _).trans ?_
    rw [Real.norm_eq_abs]
    exact hω _
  have hσlim : Tendsto (fun T : ℕ => ∫ ω, (BT T).indicator (stoppedValue N (σT T)) ω ∂P)
      atTop (𝓝 (∫ ω, B.indicator (stoppedValue N σ) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun T => ((hσTI T).indicator (hBTm T)).aestronglyMeasurable)
      (integrable_const C) (fun T => hbound (σT T) (BT T)) ?_
    exact Eventually.of_forall fun ω => tendsto_const_nhds.congr' (hσev ω)
  have hρlim : Tendsto (fun T : ℕ => ∫ ω, (BT T).indicator (stoppedValue N (ρT T)) ω ∂P)
      atTop (𝓝 (∫ ω, B.indicator (stoppedValue N ρ) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun T => ((hρTI T).indicator (hBTm T)).aestronglyMeasurable)
      (integrable_const C) (fun T => hbound (ρT T) (BT T)) ?_
    exact Eventually.of_forall fun ω => tendsto_const_nhds.congr' (hρev ω)
  have hstep' : ∀ T : ℕ,
      ∫ ω, (BT T).indicator (stoppedValue N (σT T)) ω ∂P =
        ∫ ω, (BT T).indicator (stoppedValue N (ρT T)) ω ∂P := by
    intro T
    rw [integral_indicator (hBTm T), integral_indicator (hBTm T)]
    exact hstep T
  have hlim := tendsto_nhds_unique hσlim (hρlim.congr fun T => (hstep' T).symm)
  rwa [integral_indicator hBm, integral_indicator hBm] at hlim

/-! ## Clock change of a bounded martingale -/

/-- **Clock change of a bounded martingale, with the target filtration contained in the
stopped σ-algebras up to null sets.**  `h t` is a monotone family of finite
`F`-stopping times.  If every event of `G t` agrees almost surely with an event of the
stopped σ-algebra of `h t`, and the time-changed process `t ↦ N_{h t}` is `G`-adapted,
then it is a `G`-martingale. -/
theorem martingale_stoppedValue_clock_of_bound_of_ae
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {C : ℝ} (hC : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ C)
    {h : ℝ≥0 → Ω → WithTop ℝ≥0} (hh : ∀ t, IsStoppingTime F (h t))
    (hmono : ∀ ω, Monotone (fun t => h t ω)) (hfin : ∀ t ω, h t ω ≠ ⊤)
    {G : Filtration ℝ≥0 m}
    (hG : ∀ (t : ℝ≥0) (B : Set Ω), MeasurableSet[G t] B →
      ∃ B' : Set Ω, MeasurableSet[(hh t).measurableSpace] B' ∧ B =ᵐ[P] B')
    (hadapt : StronglyAdapted G (fun t ω => stoppedValue N (h t) ω)) :
    Martingale (fun t ω => stoppedValue N (h t) ω) G P := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  have hint : ∀ u, Integrable (fun ω => stoppedValue N (h u) ω) P := by
    intro u
    refine Integrable.of_bound ((hadapt u).mono (G.le u)).aestronglyMeasurable C ?_
    filter_upwards [hC] with ω hω
    rw [Real.norm_eq_abs]
    exact hω _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  obtain ⟨B', hB', hBB'⟩ := hG s B hB
  rw [setIntegral_congr_set hBB', setIntegral_congr_set hBB']
  exact (setIntegral_stoppedValue_eq_of_le_of_bound hN hr hC (hh s) (hh t)
    (fun ω => hmono ω hst) (hfin t) hB').symm

end ReflectedGMS.StoppedFormAssociation
