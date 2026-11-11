import LatticeProb.LQG.LocalMeasureKernel4

/-!
# Local decoder: the two statements and the rooted clause 2

The two statements of the local decoder in the LatticeProb predicates, with the same binders and conclusions:
`LocalMeasureKernelStmtLP`, the kernel of the local mean-zero observation (unrooted and rooted clauses), and
`LocalLQGDecoderCommonFrozenLP`, the common local decoder. Their proofs are `localMeasureKernelStmt_lp` and
`localLQGDecoderCommonFrozen_lp`. The rooted clause 2 is proved for `rootedMeanZeroObs`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG

universe u

namespace LatticeProb.LocalMeasureKernel

namespace LocalDecoderCommon

section Rooted2

open scoped CompactlySupported

/-- The LatticeProb form of the local measure kernel statement, with the same binders and conclusion. -/
def LocalMeasureKernelStmtLP (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  0 < γ → γ < 2 → 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1 →
  (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ, Measurable κ ∧
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (localMeanZeroObs α (ball c₂ r₂) (hC ω))).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μ ω).restrict (ball c₂ r₂)) ∧
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))

/-- The LatticeProb form of the common local decoder statement, with the same binders and conclusion. -/
def LocalLQGDecoderCommonFrozenLP : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (c₂ : ℂ) (r₂ : ℝ), 0 < r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ K : ProbabilityTheory.Kernel ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ,
    ProbabilityTheory.IsSFiniteKernel K ∧
    (∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = c • (μ ω).restrict (ball c₂ r₂)) ∧
    (∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (z : ℂ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μz : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ (fun ω => rootedCircleAverage α₀ γ z (hcirc ω)) μz →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC ω)) = c • (μz ω).restrict (ball c₂ r₂))

/-- The kernel `κ` of `LocalMeasureKernelStmtLP`, with the countable decoder
of `exists_localDecoder` and the compact exhaustion of the disc; both clauses (unrooted and rooted) are proved here. -/
theorem localMeasureKernelStmt_lp (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : LocalMeasureKernelStmtLP γ c₁ c₂ r₁ r₂ := by
  intro hγ0 hγ2 hr1 hr2 hsub1 hsub2 h0
  obtain ⟨d, decode, hdm, hdec⟩ := exists_localDecoder c₂ hr2
  obtain ⟨K, hKc, hKs⟩ := ball_exhaustion c₂ r₂
  obtain ⟨T⟩ := exists_testFamilyX K hKc
  have h0b : (0 : ℂ) ∉ ball c₂ r₂ := fun h => h0 (ball_subset_closedBall h)
  have hdm' : Measurable fun y => decode (fun n => localCoord c₂ hr2 (d n) y) :=
    hdm.comp (measurable_pi_iff.mpr fun n => measurable_localCoord c₂ hr2 (d n))
  refine ⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr2 (d n) y)),
    measurable_kernelMeas γ hKs T _ hdm', ?_, ?_⟩
  · intro α _ Ω _ P _ hC hcirc μ hGFF hμ
    exact clauseA_unrooted γ α hr2 h0b hGFF μ hμ d decode hKs T hdec
  · intro α _ Ω _ P _ hC hcirc hGFF
    refine Filter.Eventually.of_forall fun z => ?_
    intro μz hμz
    exact clauseA_rooted hGFF γ α c₂ hr2 h0b z μz hμz d decode hKs T hdec

/-! ### Rooted clause 2 (without the logarithmic cut-off): the field `h - γ log|· - z|` -/

/-- The rooted shift `w ↦ -γ log|w - z|` (`rootedCircleAverage`, `rootedMeanZeroObs`). -/
noncomputable def rootShift0 (γ : ℝ) (z w : ℂ) : ℝ := -γ * Real.log ‖w - z‖

/-- The observation of `rootedMeanZeroObs` is the pairing of `h - γ log|·-z|` (algebra). -/
theorem rootedMeanZeroObs_eq (γ α₀ : ℝ) (φ : ℂ → ℝ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    fieldPairing α₀ hC φ - γ * ∫ w, Real.log ‖w - z‖ * φ w =
      fieldPairing α₀ hC φ + ∫ w, rootShift0 γ z w * φ w := by
  have h : ∫ w, rootShift0 γ z w * φ w = -γ * ∫ w, Real.log ‖w - z‖ * φ w := by
    rw [← integral_const_mul]
    congr 1
    funext w
    simp only [rootShift0]
    ring
  rw [h]
  ring

/-- The circle average of `-γ log|·-z|` (no linearity needed). -/
theorem circleAverage_rootShift0 (γ : ℝ) {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (rootShift0 γ z) x r = -γ * Real.log (max r ‖x - z‖) := by
  have h := Real.circleAverage_smul (a := -γ) (f := fun w => Real.log ‖w - z‖) (c := x) (R := r)
  have hfun : ((-γ) • fun w : ℂ => Real.log ‖w - z‖) = fun w : ℂ => -γ * Real.log ‖w - z‖ := by
    funext w
    rfl
  rw [hfun, smul_eq_mul] at h
  have e : rootShift0 γ z = fun w : ℂ => -γ * Real.log ‖w - z‖ := rfl
  rw [e, h, circleAverage_log_norm_sub_eq x z hr]

theorem integrable_rootShift0_mul_bump (γ : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => rootShift0 γ z w * bumpRho c hR w := by
  have h1 := (integrable_bump_mul_log_sub c hR z).const_mul (-γ)
  refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [rootShift0]
  ring

theorem integrable_circleApprox_mul_rootShift0 {r : ℝ} (hr : 0 < r) (γ : ℝ) (x z : ℂ) (j : ℕ) :
    Integrable fun y => circleApprox hr x j y * rootShift0 γ z y := by
  have hδ : 0 < r * approxEta r j := mul_pos hr (approxEta_pos hr j)
  have i1 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log ‖y - z‖ :=
    integrable_unitCircleDensity_mul_log hr.le hδ x z
  refine (i1.const_mul (-γ)).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [rootShift0, circleApprox]
  ring

/-- Deterministic limit, no cut-off: the annular averages of `-γ log|·-z|` converge. -/
theorem tendsto_circleApprox_rootShift0 (γ : ℝ) {r : ℝ} (hr : 0 < r) (x z : ℂ) (N : ℕ) :
    Tendsto (fun j : ℕ => ∫ y, circleApprox hr x (j + N) y * rootShift0 γ z y) atTop
      (𝓝 (Real.circleAverage (rootShift0 γ z) x r)) := by
  have hδ : ∀ j : ℕ, 0 < r * approxEta r (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
  have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j → r * approxEta r (j + N) ≤ r * η := by
    intro η hη
    obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := r) hη
    exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
  have hL := tendsto_unitCircleDensity_mul_log (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x z
  rw [circleAverage_rootShift0 γ hr z x]
  refine (hL.const_mul (-γ)).congr fun j => ?_
  have e : ∫ y, circleApprox hr x (j + N) y * rootShift0 γ z y =
      -γ * ∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [rootShift0, circleApprox]
    ring
  exact e.symm

/-- The rooted observation of `h - γ log|·-z|` on the mean-zero tests of `D`. -/
noncomputable def rootedObs0 (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α hC φ.1 + ∫ w, rootShift0 γ z w * φ.1 w

theorem ae_tendsto_localRooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w))) := by
  have hρ := integrable_rootShift0_mul_bump γ c hR z
  have hD : Tendsto (fun j : ℕ => ∫ w, rootShift0 γ z w * localTest c hR p j w) atTop
      (𝓝 (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w)) := by
    have hsplit : ∀ j : ℕ, (∫ w, rootShift0 γ z w * localTest c hR p j w) =
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift0 γ z w) -
          ∫ w, rootShift0 γ z w * bumpRho c hR w := by
      intro j
      rw [← integral_sub (integrable_circleApprox_mul_rootShift0 (localParam_radius_pos p) γ p.1.2 z _) hρ]
      congr 1
      funext w
      simp only [localTest, Pi.sub_apply]
      ring
    have hfun : (fun j : ℕ => ∫ w, rootShift0 γ z w * localTest c hR p j w) = fun j : ℕ =>
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift0 γ z w) -
          ∫ w, rootShift0 γ z w * bumpRho c hR w := funext hsplit
    rw [hfun]
    exact (tendsto_circleApprox_rootShift0 γ (localParam_radius_pos p) p.1.2 z (localShift c p)).sub_const _
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  have hobs : ∀ j : ℕ, obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j) =
      obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift0 γ z w * localTest c hR p j w := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte, rootedObs0, localMeanZeroObs]
  have heq : (fun j => obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j)) =
      fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift0 γ z w * localTest c hR p j w := funext hobs
  rw [heq]
  exact hω.add hD

/-- The rooted circle profile of `h - γ log|·-z|`: `hc0 r x = h^ℂ_r(x) + circleAverage(-γ log|·-z|)(x,r)`. -/
noncomputable def rootedHc0 (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hcirc r x + Real.circleAverage (rootShift0 γ z) x r

theorem rootedCircleAverage_eq_fieldCircleAverage (γ α₀ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (x : ℂ) : rootedCircleAverage α₀ γ z hcirc r x = fieldCircleAverage α₀ (rootedHc0 γ z hcirc) r x := by
  unfold rootedCircleAverage fieldCircleAverage rootedHc0
  rw [circleAverage_rootShift0 γ hr z x, circleAverage_log_norm_sub_eq x z hr]
  ring

theorem continuous_rootedHc0 (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ε)) :
    ∀ ε : ℝ, 0 < ε → Continuous (rootedHc0 γ z hcirc ε) := fun ε hε => by
  have h2 : Continuous fun x : ℂ => Real.circleAverage (rootShift0 γ z) x ε := by
    have hfun : (fun x : ℂ => Real.circleAverage (rootShift0 γ z) x ε) =
        fun x : ℂ => -γ * Real.log (max ε ‖x - z‖) :=
      funext fun x => circleAverage_rootShift0 γ hε z x
    rw [hfun]
    exact continuous_const.mul
      ((continuous_const.max (continuous_id.sub continuous_const).norm).log fun x => (lt_max_of_lt_left hε).ne')
  exact (hcont ε hε).add h2

/-- The γ-LQG limit property is invariant under changing the circle profile at positive radii (only the dyadic scales
enter `lqgApprox`). -/
theorem isLQGLimit_congr {γ : ℝ} {f g : ℝ → ℂ → ℝ} (h : ∀ r : ℝ, 0 < r → ∀ x : ℂ, f r x = g r x) {m : Measure ℂ}
    (hm : IsLQGLimit γ f m) : IsLQGLimit γ g m := by
  refine ⟨hm.isLocallyFiniteMeasure, fun φ hφc hφs => ?_⟩
  have hfg : ∀ k : ℕ, lqgApprox γ g (dyadicScale k) = lqgApprox γ f (dyadicScale k) := by
    intro k
    unfold lqgApprox
    congr 1
    funext x
    rw [← h (dyadicScale k) (ProfileDerived.dyadicScale_pos k) x]
  simp only [hfg]
  exact hm.tendsto_integral φ hφc hφs

theorem ae_localCoord_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (rootedObs0 γ α (ball c R) (hC ω) z) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) := by
  filter_upwards [ae_tendsto_localRooted0 hGFF γ α c hR h0 z p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

theorem ae_decode_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w)) ∧
      decode (fun n => localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z)) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) (d n).1.2 (d n).1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) :=
    ae_all_iff.2 fun n => ae_localCoord_rooted0 hGFF γ α c hR h0 z (d n)
  filter_upwards [hGFF.ae_continuousOn_circle, hco] with ω hω hωn
  have hpos : ∀ p : LocalParam c R, 0 < p.1.1 := fun p => localParam_radius_pos p
  have hmem : ∀ p : LocalParam c R, ((p.1.1, p.1.2) : ℝ × ℂ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
    fun p => ⟨hpos p, Set.mem_univ _⟩
  have hpair : Continuous fun p : LocalParam c R => ((p.1.1, p.1.2) : ℝ × ℂ) :=
    (continuous_fst.comp continuous_subtype_val).prodMk (continuous_snd.comp continuous_subtype_val)
  have hcirc_c : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 :=
    hω.comp_continuous hpair hmem
  have hlog : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hA : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2 - z‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp ((continuous_snd.comp continuous_subtype_val).sub continuous_const)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hrsEq : (fun p : LocalParam c R => Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1) = fun p =>
      -γ * Real.log (max p.1.1 ‖p.1.2 - z‖) :=
    funext fun p => circleAverage_rootShift0 γ (hpos p) z p.1.2
  have hrs : Continuous fun p : LocalParam c R => Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 := by
    rw [hrsEq]
    exact continuous_const.mul hA
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) +
      (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) :=
    (((hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const).add (hrs.sub continuous_const))
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z)) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

theorem rootedMeanZeroObs_eq_rootedObs0 (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    rootedMeanZeroObs α γ D z hC = rootedObs0 γ α D hC z :=
  funext fun φ => rootedMeanZeroObs_eq γ α φ.1 hC z

/-- Clause 2 (rooted, almost surely): the kernel of `rootedMeanZeroObs` (the observation of
`h - γ log|·-z|`) is a positive multiple of the rooted γ-LQG measure `μz` on the disc. -/
theorem clauseA_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (μz : Ω → Measure ℂ)
    (hμz : IsLQGMeasure P γ (fun ω => rootedCircleAverage α γ z (hcirc ω)) μz)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (rootedMeanZeroObs α γ (ball c R) z (hC ω))).restrict (ball c R) =
        ENNReal.ofReal a • (μz ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (rootedHc0 γ z (hcirc ω))) (μz ω) := by
    filter_upwards [hμz] with ω hω
    exact isLQGLimit_congr (fun r hr x => rootedCircleAverage_eq_fieldCircleAverage γ α z (hcirc ω) hr x) hω
  filter_upwards [ae_decode_rooted0 hGFF γ α c hR h0 z d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (rootedHc0 γ z (hcirc ω) ε) := by
    refine continuous_rootedHc0 γ z (hcirc ω) fun ε hε => ?_
    have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x : ℂ => (⟨hε, Set.mem_univ x⟩ : (ε, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
    exact h
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) (rootedMeanZeroObs α γ (ball c R) z (hC ω)) p =
        fieldCircleAverage α (rootedHc0 γ z (hcirc ω)) p.1.1 p.1.2 -
          (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift0 γ z w * bumpRho c hR w) := by
    intro p
    show decode (fun n => localCoord c hR (d n) (rootedMeanZeroObs α γ (ball c R) z (hC ω))) p = _
    rw [rootedMeanZeroObs_eq_rootedObs0, hGeq, hG p]
    unfold fieldCircleAverage rootedHc0
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
    ring
  exact kernelMeas_restrict_eq γ α
    (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift0 γ z w * bumpRho c hR w)
    hR (rootedHc0 γ z (hcirc ω)) hcont' (μz ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) (rootedMeanZeroObs α γ (ball c R) z (hC ω)) hF

/-- The kernel measure has total mass at most `1` (`κ(y)(ℂ) = (1+m)⁻¹ m ≤ 1`): the kernel is finite. -/
theorem kernelMeas_univ_le {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) : kernelMeas (γ := γ) hKs T decodeF y univ ≤ 1 := by
  unfold kernelMeas
  rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
    smul_eq_mul]
  rcases eq_or_ne (discDecoder (γ := γ) hKs T decodeF y univ) ⊤ with h | h
  · simp [h]
  · have h1 : (1 + discDecoder (γ := γ) hKs T decodeF y univ) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h⟩
    have h0 : (1 + discDecoder (γ := γ) hKs T decodeF y univ) ≠ 0 := by simp
    calc (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ * discDecoder (γ := γ) hKs T decodeF y univ
        ≤ (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ *
            (1 + discDecoder (γ := γ) hKs T decodeF y univ) :=
          by gcongr; exact le_add_self
      _ = 1 := ENNReal.inv_mul_cancel h0 h1

/-- The kernel measure is concentrated on the disc: `κ(y) = κ(y).restrict D`. -/
theorem kernelMeas_eq_restrict {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ}
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) :
    kernelMeas (γ := γ) hKs T decodeF y = (kernelMeas (γ := γ) hKs T decodeF y).restrict (ball c R) := by
  have hzero : kernelMeas (γ := γ) hKs T decodeF y (ball c R)ᶜ = 0 := by
    unfold kernelMeas
    rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe measurableSet_ball.compl]
    have hpre : (Subtype.val : ball c R → ℂ) ⁻¹' (ball c R)ᶜ = ∅ := by
      ext x
      exact ⟨fun h => absurd x.2 h, fun h => h.elim⟩
    rw [hpre, measure_empty, smul_zero]
  exact (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hzero)).symm

/-- For `LocalLQGDecoderCommonFrozenLP`: the single kernel `κ` (the same as in
`localMeasureKernelStmt_lp`) satisfies both clauses (unrooted and rooted) and is finite. -/
theorem localLQGDecoderCommonFrozen_lp : LocalLQGDecoderCommonFrozenLP := by
  intro γ _ _ c₂ r₂ hr₂ h0
  have h0b : (0 : ℂ) ∉ ball c₂ r₂ := fun h => h0 (ball_subset_closedBall h)
  obtain ⟨d, decode, hdm, hdec⟩ := exists_localDecoder c₂ hr₂
  obtain ⟨K, hKc, hKs⟩ := ball_exhaustion c₂ r₂
  obtain ⟨T⟩ := exists_testFamilyX K hKc
  have hdm' : Measurable fun y => decode (fun n => localCoord c₂ hr₂ (d n) y) :=
    hdm.comp (measurable_pi_iff.mpr fun n => measurable_localCoord c₂ hr₂ (d n))
  have hmK := measurable_kernelMeas γ hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)) hdm'
  refine ⟨⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)), hmK⟩, ?_, ?_, ?_⟩
  · have : ProbabilityTheory.IsFiniteKernel
        (⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)), hmK⟩ :
          ProbabilityTheory.Kernel _ ℂ) :=
      ⟨⟨1, ENNReal.one_lt_top, fun y => kernelMeas_univ_le γ hKs T
        (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)) y⟩⟩
    infer_instance
  · intro α₀ _ Ω _ P _ hC hcirc μ hGFF hμ
    filter_upwards [clauseA_unrooted γ α₀ hr₂ h0b hGFF μ hμ d decode hKs T hdec] with ω ⟨a, ha, hres⟩
    refine ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.2 ha, ENNReal.ofReal_lt_top, ?_⟩
    change kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y))
      (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = _
    rw [kernelMeas_eq_restrict, hres]
  · intro α₀ _ z Ω _ P _ hC hcirc μz hGFF hμz
    filter_upwards [clauseA_rooted0 hGFF γ α₀ c₂ hr₂ h0b z μz hμz d decode hKs T hdec] with ω ⟨a, ha, hres⟩
    refine ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.2 ha, ENNReal.ofReal_lt_top, ?_⟩
    change kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y))
      (rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC ω)) = _
    rw [kernelMeas_eq_restrict, hres]

end Rooted2

end LocalDecoderCommon

end LatticeProb.LocalMeasureKernel
