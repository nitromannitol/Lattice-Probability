import LatticeProb.LQG.LocalMeasureKernel3
import LatticeProb.LQG.MassFunctional

/-!
# Local decoder: rooted clauses

The rooted shift `rootShift`, the rooted observables `rootedObs` and `rootedHc` with their almost sure limits, and
`clauseA_rooted`. The observables `campbellReferenceObs`, `rootedCircleAverage` and `rootedMeanZeroObs` are defined in
this file. Statements and proofs use the names of the preceding layers.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG

universe u

namespace LatticeProb.LocalMeasureKernel

namespace LocalDecoderCommon

section Rooted

open scoped CompactlySupported

/-- The Campbell reference observation of the rooted field: the marked point `z` with the pairing
`fieldPairing α₀ hC φ` minus `γ ∫ (log|w - z| - log max(1,|w|)) φ(w) dw`. -/
noncomputable def campbellReferenceObs (γ α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) :=
  (z, fun φ => fieldPairing α₀ hC φ.1 - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w)

/-- The circle averages of the rooted field `h - γ log|· - z|`: `h_r(x) - γ` times the average of `log|· - z|`
over `∂B_r(x)`. -/
noncomputable def rootedCircleAverage (α₀ γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (x : ℂ) : ℝ :=
  fieldCircleAverage α₀ hcirc r x - γ * Real.circleAverage (fun w => Real.log ‖w - z‖) x r

/-- The mean-zero observation of the rooted field `h - γ log|· - z|` on `D`. -/
noncomputable def rootedMeanZeroObs (α₀ γ : ℝ) (D : Set ℂ) (z : ℂ) (hC : (ℂ → ℝ) → ℝ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α₀ hC φ.1 - γ * ∫ w, Real.log ‖w - z‖ * φ.1 w

/-- The real logarithm of the modulus is locally integrable on `ℂ`; the integrability on the balls is
`AffineDerived.integrableOn_log_norm_ball`. -/
theorem locallyIntegrable_log_norm_complex : LocallyIntegrable (fun w : ℂ => Real.log ‖w‖) volume := by
  intro x
  refine ⟨ball 0 (‖x‖ + 1), ?_, AffineDerived.integrableOn_log_norm_ball _⟩
  exact isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith [norm_nonneg x]))

/-- Clause A (unrooted), almost surely: for a whole-plane GFF `h^ℂ` and a γ-LQG measure `μ` of
`h^ℂ - α log|·|` (`IsLQGMeasureOfField`), the kernel `kernelMeas` of the local mean-zero observation is a positive
multiple of `μ` restricted to the disc. -/
theorem clauseA_unrooted (γ α : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (localMeanZeroObs α (ball c R) (hC ω))).restrict (ball c R) =
        ENNReal.ofReal a • (μ ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  filter_upwards [ae_decode_localCoord_eq hGFF α c hR h0 d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ω ε) := fun ε hε =>
    hcontω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, Set.mem_univ z⟩
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) (localMeanZeroObs α (ball c R) (hC ω)) p =
        fieldCircleAverage α (hcirc ω) p.1.1 p.1.2 - fieldPairing α (hC ω) (bumpRho c hR) := by
    intro p
    show decode (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) p = _
    rw [hGeq, hG p]
    unfold fieldCircleAverage
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
  exact kernelMeas_restrict_eq γ α (fieldPairing α (hC ω) (bumpRho c hR)) hR (hcirc ω) hcont' (μ ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) (localMeanZeroObs α (ball c R) (hC ω)) hF

/-! ### Rooted shift: the field `h + f_z`, `f_z(w) = -γ log|w-z| + γ log max(1,|w|)` -/

/-- The rooted shift `f_z(w) = -γ log|w - z| + γ log max(1,|w|)` (`campbellReferenceObs`). -/
noncomputable def rootShift (γ : ℝ) (z w : ℂ) : ℝ :=
  -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)

/-- The reference observation of `campbellReferenceObs` is the pairing of `h + f_z` (algebra; no integrability). -/
theorem campbellReferenceObs_eq (γ α₀ : ℝ) (φ : ℂ → ℝ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    fieldPairing α₀ hC φ - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w =
      fieldPairing α₀ hC φ + ∫ w, rootShift γ z w * φ w := by
  have h : ∫ w, rootShift γ z w * φ w = -γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w := by
    rw [← integral_const_mul]
    congr 1
    funext w
    simp only [rootShift]
    ring
  rw [h]
  ring

/-- The circle average of the rooted shift (linearity of `circleAverage` on the two summands). -/
theorem circleAverage_rootShift (γ : ℝ) {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (rootShift γ z) x r =
      -γ * Real.log (max r ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r := by
  have hL : CircleIntegrable (fun w => Real.log ‖w - z‖) x r := circleIntegrable_log_norm_sub_const r
  have hM : CircleIntegrable (fun w => Real.log (max 1 ‖w‖)) x r :=
    (((continuous_const.max continuous_norm).log fun w => (lt_max_of_lt_left one_pos).ne').continuousOn.circleIntegrable hr.le)
  have e1 : rootShift γ z = (fun w => -γ * Real.log ‖w - z‖) + (fun w => γ * Real.log (max 1 ‖w‖)) := rfl
  have hL1 : CircleIntegrable (fun w => -γ * Real.log ‖w - z‖) x r := IntervalIntegrable.const_mul hL (-γ)
  have hM1 : CircleIntegrable (fun w => γ * Real.log (max 1 ‖w‖)) x r := IntervalIntegrable.const_mul hM γ
  rw [e1, Real.circleAverage_add hL1 hM1]
  have e2 : Real.circleAverage (fun w => -γ * Real.log ‖w - z‖) x r =
      -γ * Real.circleAverage (fun w => Real.log ‖w - z‖) x r := by
    have h := Real.circleAverage_smul (a := -γ) (f := fun w => Real.log ‖w - z‖) (c := x) (R := r)
    have hfun : ((-γ) • fun w : ℂ => Real.log ‖w - z‖) = fun w : ℂ => -γ * Real.log ‖w - z‖ := by
      funext w
      rfl
    rw [hfun, smul_eq_mul] at h
    exact h
  have e3 : Real.circleAverage (fun w => γ * Real.log (max 1 ‖w‖)) x r =
      γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r := by
    have h := Real.circleAverage_smul (a := γ) (f := fun w => Real.log (max 1 ‖w‖)) (c := x) (R := r)
    have hfun : (γ • fun w : ℂ => Real.log (max 1 ‖w‖)) = fun w : ℂ => γ * Real.log (max 1 ‖w‖) := by
      funext w
      rfl
    rw [hfun, smul_eq_mul] at h
    exact h
  rw [e2, e3, circleAverage_log_norm_sub_eq x z hr]

/-- The logarithm of the local modulus `log max(1,|w|)` is continuous. -/
theorem continuous_log_max_one : Continuous fun w : ℂ => Real.log (max 1 ‖w‖) :=
  (continuous_const.max continuous_norm).log fun _ => (lt_max_of_lt_left one_pos).ne'

/-- Deterministic limit: the annular averages `∫ ψ_{j+N} f_z` of the rooted shift converge to the circle
average of `f_z` (the log singularity at `z` is handled by `tendsto_unitCircleDensity_mul_log`, the continuous part by
`tendsto_unitCircleDensity_mul_continuous`). -/
theorem tendsto_circleApprox_rootShift (γ : ℝ) {r : ℝ} (hr : 0 < r) (x z : ℂ) (N : ℕ) :
    Tendsto (fun j : ℕ => ∫ y, circleApprox hr x (j + N) y * rootShift γ z y) atTop
      (𝓝 (Real.circleAverage (rootShift γ z) x r)) := by
  have hδ : ∀ j : ℕ, 0 < r * approxEta r (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
  have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j → r * approxEta r (j + N) ≤ r * η := by
    intro η hη
    obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := r) hη
    exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
  have hL := tendsto_unitCircleDensity_mul_log (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x z
  have hM := tendsto_unitCircleDensity_mul_continuous (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x continuous_log_max_one
  have hLim := (hL.const_mul (-γ)).add (hM.const_mul γ)
  have hcirc : Real.circleAverage (rootShift γ z) x r =
      -γ * Real.log (max r ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r :=
    circleAverage_rootShift γ hr z x
  rw [hcirc]
  refine hLim.congr fun j => ?_
  have i1 : Integrable (fun y => unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y *
      Real.log ‖y - z‖) :=
    integrable_unitCircleDensity_mul_log hr.le (hδ j) x z
  have i2 : Integrable (fun y => unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y *
      Real.log (max 1 ‖y‖)) :=
    integrable_unitCircleDensity_mul hr.le (hδ j) x continuous_log_max_one
  have e1 : ∫ y, circleApprox hr x (j + N) y * rootShift γ z y =
      ∫ y, (-γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖))) := by
    congr 1
    funext y
    simp only [rootShift, circleApprox]
    ring
  have e2 : ∫ y, (-γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖))) =
      -γ * (∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖)) := by
    rw [integral_add (i1.const_mul (-γ)) (i2.const_mul γ), integral_const_mul, integral_const_mul]
  exact (e1.trans e2).symm

/-- The observation of the rooted field `h + f_z` on the mean-zero tests of `D` (the second component of
`campbellReferenceObs`, by `campbellReferenceObs_snd_eq_rootedObs`). -/
noncomputable def rootedObs (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α hC φ.1 + ∫ w, rootShift γ z w * φ.1 w

theorem campbellReferenceObs_snd_eq_rootedObs (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    (campbellReferenceObs γ α D hC z).2 = rootedObs γ α D hC z :=
  funext fun φ => campbellReferenceObs_eq γ α φ.1 hC z

/-- `bumpRho · log|· - z|` is integrable (the logarithmic singularity at `z` is locally integrable). -/
theorem integrable_bump_mul_log_sub (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => bumpRho c hR w * Real.log ‖w - z‖ := by
  have hcs : HasCompactSupport fun t : ℂ => bumpRho c hR (t + z) :=
    (bumpRho_isTest c hR).2.1.comp_homeomorph (Homeomorph.addRight z)
  have hl : LocallyIntegrable (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) volume :=
    (locallyIntegrable_log_norm_complex).continuous_mul
      ((bumpRho_isTest c hR).1.continuous.comp (continuous_id.add continuous_const))
  have hcs2 : HasCompactSupport (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) := hcs.mul_right
  have hg : Integrable (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
      (hl.integrableOn_isCompact hcs2.isCompact)
  have h2 := hg.comp_sub_right z
  simp only [sub_add_cancel] at h2
  exact h2

theorem integrable_rootShift_mul_bump (γ : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => rootShift γ z w * bumpRho c hR w := by
  have h1 := (integrable_bump_mul_log_sub c hR z).const_mul (-γ)
  have hc2 : Continuous fun w => bumpRho c hR w * Real.log (max 1 ‖w‖) :=
    (bumpRho_isTest c hR).1.continuous.mul continuous_log_max_one
  have h2 : Integrable fun w => bumpRho c hR w * Real.log (max 1 ‖w‖) :=
    hc2.integrable_of_hasCompactSupport (bumpRho_isTest c hR).2.1.mul_right
  refine (h1.add (h2.const_mul γ)).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply, rootShift]
  ring

theorem integrable_circleApprox_mul_rootShift {r : ℝ} (hr : 0 < r) (γ : ℝ) (x z : ℂ) (j : ℕ) :
    Integrable fun y => circleApprox hr x j y * rootShift γ z y := by
  have hδ : 0 < r * approxEta r j := mul_pos hr (approxEta_pos hr j)
  have i1 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log ‖y - z‖ :=
    integrable_unitCircleDensity_mul_log hr.le hδ x z
  have i2 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log (max 1 ‖y‖) :=
    integrable_unitCircleDensity_mul hr.le hδ x continuous_log_max_one
  refine ((i1.const_mul (-γ)).add (i2.const_mul γ)).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, rootShift, circleApprox]
  ring

/-- Almost surely: the coordinates of the rooted observation converge to the centred rooted circle profile
`h_r(x) - α log max(r,|x|) + (circle average of f_z) - (pairing of h and f_z with ρ)`. -/
theorem ae_tendsto_localRooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w))) := by
  have hρ := integrable_rootShift_mul_bump γ c hR z
  have hD : Tendsto (fun j : ℕ => ∫ w, rootShift γ z w * localTest c hR p j w) atTop
      (𝓝 (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w)) := by
    have hsplit : ∀ j : ℕ, (∫ w, rootShift γ z w * localTest c hR p j w) =
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift γ z w) -
          ∫ w, rootShift γ z w * bumpRho c hR w := by
      intro j
      rw [← integral_sub (integrable_circleApprox_mul_rootShift (localParam_radius_pos p) γ p.1.2 z _) hρ]
      congr 1
      funext w
      simp only [localTest, Pi.sub_apply]
      ring
    have hfun : (fun j : ℕ => ∫ w, rootShift γ z w * localTest c hR p j w) = fun j : ℕ =>
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift γ z w) -
          ∫ w, rootShift γ z w * bumpRho c hR w := funext hsplit
    rw [hfun]
    exact (tendsto_circleApprox_rootShift γ (localParam_radius_pos p) p.1.2 z (localShift c p)).sub_const _
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  have hobs : ∀ j : ℕ, obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j) =
      obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift γ z w * localTest c hR p j w := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte, rootedObs, localMeanZeroObs]
  have heq : (fun j => obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j)) =
      fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift γ z w * localTest c hR p j w := funext hobs
  rw [heq]
  exact hω.add hD

/-- Almost surely: the rooted circle coordinate of the observation of `h + f_z` at `p`. -/
theorem ae_localCoord_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (rootedObs γ α (ball c R) (hC ω) z) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) := by
  filter_upwards [ae_tendsto_localRooted hGFF γ α c hR h0 z p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

/-! ### Rooted clause A: the rooted profile `hc' r x = h_r(x) + circleAverage(f_z)(x,r)` -/

/-- The rooted circle profile of `h + f_z`: `hc' r x = h^ℂ_r(x) + circleAverage(f_z)(x,r)`. -/
noncomputable def rootedHc (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hcirc r x + Real.circleAverage (rootShift γ z) x r

theorem fieldCircleAverage_rootedHc (γ α : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) :
    fieldCircleAverage α (rootedHc γ z hcirc) =
      addCircleAverage (fieldCircleAverage α hcirc) (rootShift γ z) := by
  funext r x
  unfold fieldCircleAverage rootedHc addCircleAverage
  ring

/-- The circle average of the rooted shift is continuous in the centre (for a fixed positive radius). -/
theorem continuous_circleAverage_rootShift_centre (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x : ℂ => Real.circleAverage (rootShift γ z) x ε := by
  have hfun : (fun x : ℂ => Real.circleAverage (rootShift γ z) x ε) = fun x : ℂ =>
      -γ * Real.log (max ε ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x ε := by
    funext x
    exact circleAverage_rootShift γ hε z x
  rw [hfun]
  have h1 : Continuous fun x : ℂ => Real.log (max ε ‖x - z‖) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log fun x => (lt_max_of_lt_left hε).ne'
  have h2 : Continuous fun x : ℂ => Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x ε :=
    (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center continuous_log_max_one).comp (continuous_const.prodMk continuous_id)
  exact (continuous_const.mul h1).add (continuous_const.mul h2)

theorem continuous_rootedHc (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ε)) :
    ∀ ε : ℝ, 0 < ε → Continuous (rootedHc γ z hcirc ε) := fun ε hε =>
  (hcont ε hε).add (continuous_circleAverage_rootShift_centre γ z hε)

/-- Almost sure decoder identity, rooted: the decoded rooted observation is the continuous rooted profile
on `LocalParam c R`. -/
theorem ae_decode_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w)) ∧
      decode (fun n => localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z)) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) (d n).1.2 (d n).1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) :=
    ae_all_iff.2 fun n => ae_localCoord_rooted hGFF γ α c hR h0 z (d n)
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
  have hB : Continuous fun p : LocalParam c R =>
      Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) p.1.2 p.1.1 :=
    (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center continuous_log_max_one).comp hpair
  have hrsEq : (fun p : LocalParam c R => Real.circleAverage (rootShift γ z) p.1.2 p.1.1) = fun p =>
      -γ * Real.log (max p.1.1 ‖p.1.2 - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) p.1.2 p.1.1 :=
    funext fun p => circleAverage_rootShift γ (hpos p) z p.1.2
  have hrs : Continuous fun p : LocalParam c R => Real.circleAverage (rootShift γ z) p.1.2 p.1.1 := by
    rw [hrsEq]
    exact (continuous_const.mul hA).add (continuous_const.mul hB)
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) +
      (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) :=
    (((hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const).add (hrs.sub continuous_const))
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z)) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

/-- Clause A (rooted, almost surely): the kernel of the rooted observation `h + f_z` is a positive multiple
of the rooted γ-LQG measure `μz` on the disc. -/
theorem clauseA_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (μz : Ω → Measure ℂ)
    (hμz : IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
      (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (campbellReferenceObs γ α (ball c R) (hC ω) z).2).restrict (ball c R) =
        ENNReal.ofReal a • (μz ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (rootedHc γ z (hcirc ω))) (μz ω) := by
    filter_upwards [hμz] with ω hω
    rw [fieldCircleAverage_rootedHc]
    exact hω
  filter_upwards [ae_decode_rooted hGFF γ α c hR h0 z d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (rootedHc γ z (hcirc ω) ε) := by
    intro ε hε
    have hcirc_ε : Continuous (hcirc ω ε) := by
      have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x : ℂ => (⟨hε, Set.mem_univ x⟩ : (ε, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
      exact h
    exact continuous_rootedHc γ z (hcirc ω) (fun ε' hε' => by
      have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x : ℂ => (⟨hε', Set.mem_univ x⟩ : (ε', x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
      exact h) ε hε
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2) p =
        fieldCircleAverage α (rootedHc γ z (hcirc ω)) p.1.1 p.1.2 -
          (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift γ z w * bumpRho c hR w) := by
    intro p
    show decode (fun n => localCoord c hR (d n) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2)) p = _
    rw [campbellReferenceObs_snd_eq_rootedObs, hGeq, hG p]
    unfold fieldCircleAverage rootedHc
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
    ring
  exact kernelMeas_restrict_eq γ α (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift γ z w * bumpRho c hR w)
    hR (rootedHc γ z (hcirc ω)) hcont' (μz ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2) hF


end Rooted

end LocalDecoderCommon

end LatticeProb.LocalMeasureKernel
