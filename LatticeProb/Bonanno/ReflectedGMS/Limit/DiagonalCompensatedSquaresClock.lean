/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DiagonalCompensatedSquaresClock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationOptionalSampling
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalMartingaleCombination

/-!
# Step (a) of bracket atom 2: the clock change of a *dominated* compensated square

Atom 1 time-changes the stopped fast potential `P^τ`, which is **bounded**, with
`StoppedFormAssociation.martingale_stoppedValue_clock_of_bound_of_ae`.  The compensated square
`(P^τ)² − ⟨U⟩^τ` of atom 2 is **not** bounded: `⟨U⟩^τ_t = ∫₀^{t∧τ} Γ(U)(Y_s) ds` grows with the
time spent inside the region, which is not bounded uniformly in the sample.  (Correction to the
brief: "the bound comes from atom 1's exit bound plus the bracket bound" — there is no uniform
bracket bound.)  What is true is that it is **dominated by an integrable variable**:

`|(P^τ_t)² − ⟨U⟩^τ_t| ≤ C² + sup_k ⟨U⟩^τ_k`,  `E sup_k ⟨U⟩^τ_k ≤ C² · P(Ω)`,

because the martingale property gives `E ⟨U⟩^τ_t = E (P^τ_t)² − E (P^τ_0)² ≤ C²` and the
occupation is increasing (monotone convergence).  This file proves:

* `setIntegral_stoppedValue_eq_of_le_of_dom` / `martingale_stoppedValue_clock_of_dom_of_ae` — the
  optional sampling and clock change of `StoppedFormAssociationOptionalSampling`, with the uniform
  bound replaced by an integrable dominating variable (same proof: truncation at integer horizons
  and dominated convergence);
* `exists_integrable_dom_of_compensatedSquare` — the domination above;
* `martingale_of_clock_two` — the generic core of atom 2: if `W = c₁ + N₁ ∘ h` and
  `Z = c + a·(N₁ ∘ h) + N₂ ∘ h` almost surely at every time, with `N₁` bounded and `N₂` dominated
  martingales, then `Z` is a martingale of the target filtration.  (The square of the area-side
  coordinate is `(u(start) + P^τ ∘ h)²`, so both the fast potential and the fast compensated
  square are needed.)

Nothing here mentions the reflected walk; no `Summable` hypothesis occurs.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.DiagonalCompensatedSquaresClock

open ReflectedGMS.MartingaleLimit ReflectedGMS.StoppedFormAssociation

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Optional sampling at finite stopping times, for a dominated martingale -/

/-- **Optional sampling at two finite stopping times for a martingale dominated by an integrable
variable.**  The proof of `setIntegral_stoppedValue_eq_of_le_of_bound`, with the constant bound
replaced by the dominating variable in the dominated convergence step. -/
theorem setIntegral_stoppedValue_eq_of_le_of_dom
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {g : Ω → ℝ} (hg : Integrable g P) (hd : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ g ω)
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime F ρ) (hσ : IsStoppingTime F σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (hσfin : ∀ ω, σ ω ≠ ⊤)
    {B : Set Ω} (hB : MeasurableSet[hρ.measurableSpace] B) :
    ∫ ω in B, stoppedValue N σ ω ∂P = ∫ ω in B, stoppedValue N ρ ω ∂P := by
  have hBm : MeasurableSet B := hρ.measurableSpace_le B hB
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
  have hσTI : ∀ T : ℕ, Integrable (stoppedValue N (σT T)) P := fun T =>
    (bounded_stopping_L1 hN (hσT T) (T : ℝ≥0) (fun ω => min_le_right _ _) hr).2.1
  have hρTI : ∀ T : ℕ, Integrable (stoppedValue N (ρT T)) P := fun T =>
    (bounded_stopping_L1 hN (hρT T) (T : ℝ≥0) (fun ω => min_le_right _ _) hr).2.1
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
  have hbound : ∀ (τ : Ω → WithTop ℝ≥0) (S : Set Ω),
      ∀ᵐ ω ∂P, ‖S.indicator (stoppedValue N τ) ω‖ ≤ g ω := by
    intro τ S
    filter_upwards [hd] with ω hω
    refine (norm_indicator_le_norm_self _ _).trans ?_
    rw [Real.norm_eq_abs]
    exact hω _
  have hσlim : Tendsto (fun T : ℕ => ∫ ω, (BT T).indicator (stoppedValue N (σT T)) ω ∂P)
      atTop (𝓝 (∫ ω, B.indicator (stoppedValue N σ) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence g
      (fun T => ((hσTI T).indicator (hBTm T)).aestronglyMeasurable)
      hg (fun T => hbound (σT T) (BT T)) ?_
    exact Eventually.of_forall fun ω => tendsto_const_nhds.congr' (hσev ω)
  have hρlim : Tendsto (fun T : ℕ => ∫ ω, (BT T).indicator (stoppedValue N (ρT T)) ω ∂P)
      atTop (𝓝 (∫ ω, B.indicator (stoppedValue N ρ) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence g
      (fun T => ((hρTI T).indicator (hBTm T)).aestronglyMeasurable)
      hg (fun T => hbound (ρT T) (BT T)) ?_
    exact Eventually.of_forall fun ω => tendsto_const_nhds.congr' (hρev ω)
  have hstep' : ∀ T : ℕ,
      ∫ ω, (BT T).indicator (stoppedValue N (σT T)) ω ∂P =
        ∫ ω, (BT T).indicator (stoppedValue N (ρT T)) ω ∂P := by
    intro T
    rw [integral_indicator (hBTm T), integral_indicator (hBTm T)]
    exact hstep T
  have hlim := tendsto_nhds_unique hσlim (hρlim.congr fun T => (hstep' T).symm)
  rwa [integral_indicator hBm, integral_indicator hBm] at hlim

/-- **Clock change of a dominated martingale**, with the target filtration contained in the
stopped σ-algebras up to null sets. -/
theorem martingale_stoppedValue_clock_of_dom_of_ae
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {g : Ω → ℝ} (hg : Integrable g P) (hd : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ g ω)
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
    refine hg.mono' ((hadapt u).mono (G.le u)).aestronglyMeasurable ?_
    filter_upwards [hd] with ω hω
    rw [Real.norm_eq_abs]
    exact hω _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  obtain ⟨B', hB', hBB'⟩ := hG s B hB
  rw [setIntegral_congr_set hBB', setIntegral_congr_set hBB']
  exact (setIntegral_stoppedValue_eq_of_le_of_dom hN hr hg hd (hh s) (hh t)
    (fun ω => hmono ω hst) (hfin t) hB').symm

/-! ## Domination of a compensated square -/

/-- An increasing process stays increasing when stopped. -/
theorem monotone_stoppedProcess {A : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hA : Monotone (fun t => A t ω)) : Monotone (fun t => stoppedProcess A τ t ω) := by
  intro s t hst
  simp only [stoppedProcess]
  apply hA
  have hne : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
  exact WithTop.untopA_mono hne (min_le_min_right _ (WithTop.coe_le_coe.2 hst))

/-- A stopped process at time `0` is the process at time `0`. -/
theorem stoppedProcess_zero {β : Type*} (A : ℝ≥0 → Ω → β) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stoppedProcess A τ 0 ω = A 0 ω := by
  simp only [stoppedProcess]
  have h0 : min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω) = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
    min_eq_left (by simp)
  rw [h0]
  rfl

/-- **An increasing compensator of the square of a bounded process is dominated.**  If
`X² − A` is a martingale, `|X| ≤ C`, and `A ≥ 0` is increasing with `A₀ = 0`, then
`|X_t² − A_t| ≤ g` for one integrable `g` and every `t`. -/
theorem exists_integrable_dom_of_compensatedSquare
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {X A : ℝ≥0 → Ω → ℝ}
    (hM : Martingale (fun t ω => X t ω ^ 2 - A t ω) F P)
    (hXm : ∀ t, AEStronglyMeasurable (X t) P)
    {C : ℝ} (hX : ∀ᵐ ω ∂P, ∀ t, |X t ω| ≤ C)
    (hA0 : ∀ ω, A 0 ω = 0) (hAnn : ∀ t ω, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂P, Monotone (fun t => A t ω)) :
    ∃ g : Ω → ℝ, Integrable g P ∧ ∀ᵐ ω ∂P, ∀ t, |X t ω ^ 2 - A t ω| ≤ g ω := by
  have hsq : ∀ᵐ ω ∂P, ∀ t, X t ω ^ 2 ≤ C ^ 2 := by
    filter_upwards [hX] with ω hω
    intro t
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω t) 2
  have hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) P := by
    intro t
    refine (integrable_const (C ^ 2)).mono' ((hXm t).pow 2) ?_
    filter_upwards [hsq] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω t
  have hAeq : ∀ t, A t = fun ω => X t ω ^ 2 - (X t ω ^ 2 - A t ω) := by
    intro t
    funext ω
    ring
  have hAint : ∀ t, Integrable (A t) P := by
    intro t
    rw [hAeq t]
    exact (hX2 t).sub (hM.integrable t)
  -- the mean of the compensator
  have hmean : ∀ t, ∫ ω, A t ω ∂P ≤ ∫ _ω, C ^ 2 ∂P := by
    intro t
    have hE : ∫ ω, (X 0 ω ^ 2 - A 0 ω) ∂P = ∫ ω, (X t ω ^ 2 - A t ω) ∂P := by
      have := hM.setIntegral_eq (zero_le) MeasurableSet.univ (i := 0) (j := t)
      simpa only [Measure.restrict_univ] using this
    have h0 : ∫ ω, (X 0 ω ^ 2 - A 0 ω) ∂P = ∫ ω, X 0 ω ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hA0 ω, sub_zero]
    have hAt : ∫ ω, A t ω ∂P = ∫ ω, X t ω ^ 2 ∂P - ∫ ω, (X t ω ^ 2 - A t ω) ∂P := by
      conv_lhs => rw [hAeq t]
      exact integral_sub (hX2 t) (hM.integrable t)
    have hnn : 0 ≤ ∫ ω, X 0 ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have hle : ∫ ω, X t ω ^ 2 ∂P ≤ ∫ _ω, C ^ 2 ∂P :=
      integral_mono_ae (hX2 t) (integrable_const _) (hsq.mono fun ω hω => hω t)
    rw [hAt, ← hE, h0]
    linarith
  -- the supremum along integer times
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ k : ℕ, ENNReal.ofReal (A k ω) with hSdef
  have hSm : AEMeasurable S P :=
    AEMeasurable.iSup fun k => (hAint k).1.aemeasurable.ennreal_ofReal
  have hlin : ∫⁻ ω, S ω ∂P ≤ ENNReal.ofReal (∫ _ω, C ^ 2 ∂P) := by
    rw [hSdef, lintegral_iSup' (fun k => (hAint k).1.aemeasurable.ennreal_ofReal) ?_]
    · refine iSup_le fun k => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hAint k)
        (Eventually.of_forall fun ω => hAnn k ω)]
      exact ENNReal.ofReal_le_ofReal (hmean k)
    · filter_upwards [hAmono] with ω hω
      intro a b hab
      exact ENNReal.ofReal_le_ofReal (hω (by exact_mod_cast hab))
  have hSfin : ∫⁻ ω, S ω ∂P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hSlt : ∀ᵐ ω ∂P, S ω < ∞ := ae_lt_top' hSm hSfin
  refine ⟨fun ω => C ^ 2 + (S ω).toReal,
    (integrable_const _).add (integrable_toReal_of_lintegral_ne_top hSm hSfin), ?_⟩
  filter_upwards [hsq, hAmono, hSlt] with ω hXω hmω hSω
  intro t
  obtain ⟨k, hk⟩ := exists_nat_ge t
  have hAk : A t ω ≤ (S ω).toReal := by
    calc A t ω ≤ A k ω := hmω hk
      _ = (ENNReal.ofReal (A k ω)).toReal := (ENNReal.toReal_ofReal (hAnn k ω)).symm
      _ ≤ (S ω).toReal := ENNReal.toReal_mono hSω.ne
          (le_iSup (fun k : ℕ => ENNReal.ofReal (A k ω)) k)
  calc |X t ω ^ 2 - A t ω| ≤ |X t ω ^ 2| + |A t ω| := abs_sub _ _
    _ = X t ω ^ 2 + A t ω := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hAnn t ω)]
    _ ≤ C ^ 2 + (S ω).toReal := add_le_add (hXω t) hAk

/-! ## The generic core of atom 2 -/

/-- **The clock-change core of atom 2.**  `N₁` a bounded and `N₂` a dominated right-continuous
`F`-martingale, `h` a monotone finite family of `F`-stopping times whose stopped σ-algebras contain
`G` up to null sets, `G` containing the null events.  If the `G`-adapted processes `W`, `Z`
satisfy `W_t = c₁ + N₁(h t)` and `Z_t = c + a·N₁(h t) + N₂(h t)` almost surely at every time,
then `Z` is a `G`-martingale. -/
theorem martingale_of_clock_two {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 m} {N₁ N₂ : ℝ≥0 → Ω → ℝ}
    (hN₁ : Martingale N₁ F P) (hr₁ : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N₁ t ω))
    {C : ℝ} (hC : ∀ᵐ ω ∂P, ∀ t, |N₁ t ω| ≤ C)
    (hN₂ : Martingale N₂ F P) (hr₂ : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N₂ t ω))
    {g : Ω → ℝ} (hg : Integrable g P) (hd : ∀ᵐ ω ∂P, ∀ t, |N₂ t ω| ≤ g ω)
    {h : ℝ≥0 → Ω → WithTop ℝ≥0} (hh : ∀ t, IsStoppingTime F (h t))
    (hmono : ∀ ω, Monotone (fun t => h t ω)) (hfin : ∀ t ω, h t ω ≠ ⊤)
    (hG : ∀ (t : ℝ≥0) (B : Set Ω), MeasurableSet[G t] B →
      ∃ B' : Set Ω, MeasurableSet[(hh t).measurableSpace] B' ∧ B =ᵐ[P] B')
    (hnullG : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[G t] A)
    {W Z : ℝ≥0 → Ω → ℝ} (hW : StronglyAdapted G W) (hZ : StronglyAdapted G Z) (c₁ c a : ℝ)
    (hWN : ∀ t, ∀ᵐ ω ∂P, W t ω = c₁ + stoppedValue N₁ (h t) ω)
    (hZN : ∀ t, ∀ᵐ ω ∂P,
      Z t ω = c + a * stoppedValue N₁ (h t) ω + stoppedValue N₂ (h t) ω) :
    Martingale Z G P := by
  have hA1 : StronglyAdapted G (fun t ω => stoppedValue N₁ (h t) ω) := by
    intro t
    have hsub : StronglyMeasurable[G t] (fun ω => W t ω - c₁) :=
      (hW t).sub stronglyMeasurable_const
    refine LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events (G.le t)
      (hnullG t) hsub ?_
    filter_upwards [hWN t] with ω hω
    rw [hω]
    ring
  have hA2 : StronglyAdapted G (fun t ω => stoppedValue N₂ (h t) ω) := by
    intro t
    have hm : StronglyMeasurable[G t]
        (fun ω => Z t ω - c - a * (W t ω - c₁)) :=
      (((hZ t).sub stronglyMeasurable_const).sub
        (stronglyMeasurable_const.mul ((hW t).sub stronglyMeasurable_const)))
    refine LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events (G.le t)
      (hnullG t) hm ?_
    filter_upwards [hWN t, hZN t] with ω hω1 hω2
    rw [hω2, hω1]
    ring
  have hM1 : Martingale (fun t ω => stoppedValue N₁ (h t) ω) G P :=
    martingale_stoppedValue_clock_of_bound_of_ae hN₁ hr₁ hC hh hmono hfin hG hA1
  have hM2 : Martingale (fun t ω => stoppedValue N₂ (h t) ω) G P :=
    martingale_stoppedValue_clock_of_dom_of_ae hN₂ hr₂ hg hd hh hmono hfin hG hA2
  have hsum : Martingale ((fun _ _ => c) + a • (fun t ω => stoppedValue N₁ (h t) ω) +
      fun t ω => stoppedValue N₂ (h t) ω) G P :=
    ((martingale_const G P c).add (hM1.smul a)).add hM2
  refine hsum.congr hZ fun t => ?_
  filter_upwards [hZN t] with ω hω
  rw [hω]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end ReflectedGMS.DiagonalCompensatedSquaresClock
