import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.LQG.LQGMeasureDerived
import LatticeProb.Gauss.CameronMartinDerived2

/-! # Locality of the γ-LQG area measure (conditional form)

. The general LP statement of Fact 2.1 II (locality of the
γ-Liouville quantum gravity area measure, Duplantier-Sheffield 2011; Berestycki-Powell), in the form

  `LatticeProb.LQG.lqgLocality_of_circleLink`: under the circle-average link `LQGCircleAverageLink` (LP form, with the
  whole-plane GFF premise), `μ(U)` is a.s. equal to a `σ(h|_U)`-measurable variable for every open `U`.

The link is a hypothesis of this file. Its unconditional proof (`LQGCircleAverageLink` for every whole-plane GFF) is NOT
included here: the HB derivation `HarmonicBalls.lqgCircleAverageLocalityLink_derived`
(`FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean`) uses `wholePlaneCircleAverageLimit_derived`
(`FirstPass/S11u.lean`), which is not copied here. Everything else is proved here.

Contents: the definitions `LQGLocality` and `LQGCircleAverageLink`; the GFF pairing measurability `measurable_gff_pairing`;
the joint measurability of a modification of the circle averages (`LatticeProb.Gauss.IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage`,
the LP copy of `IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage`); the distance to the complement and
the exhaustion by cut-offs; the dyadic grid and the density integrals; the locality proof.

Sources: `HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean` (`measurable_gff_pairing`,
`lqgLocality_of_circleLink`), `HarmonicBalls/FirstPass/Phase2/LQGLocalityDerived.lean` (helpers),
`HarmonicBalls/Proofs/Sec5/CircleAverageMeasurability.lean` (joint measurability). Definitions reused:
`LatticeProb.LQG.IsLQGMeasureOfField` (`LatticeProb/LQG/LQGMeasure.lean`), `LatticeProb.Gauss.fieldSigmaAlgebra`
(`LatticeProb/Gauss/GFF.lean`), `LatticeProb.LQG.ProfileDerived.dyadicScale_pos` and `continuous_circleAverage_log_norm`
(`LatticeProb/LQG/LQGMeasureDerived.lean`).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.Gauss

/-- A whole-plane GFF has a modification whose circle averages are continuous
in the spatial variable at every positive radius and jointly measurable in the
spatial variable and the sample point. -/
theorem IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∃ H : Ω → ℝ → ℂ → ℝ,
      (∀ ω r, 0 < r → Continuous (H ω r)) ∧
      (∀ r, 0 < r → Measurable (fun p : ℂ × Ω => H p.2 r p.1)) ∧
      (∀ᵐ ω ∂P, ∀ r z, H ω r z = hcirc ω r z) := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hGFF.ae_continuousOn_circle)
  let H : Ω → ℝ → ℂ → ℝ := fun ω r z => if ω ∈ N then 0 else hcirc ω r z
  have hcont : ∀ ω r, 0 < r → Continuous (H ω r) := by
    intro ω r hr
    by_cases hω : ω ∈ N
    · simpa [H, hω] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
    · have hc : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
          (Ioi 0 ×ˢ univ) := by
        by_contra hnot
        exact hω (hNsub hnot)
      have h := hc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z : ℂ => ⟨hr, mem_univ z⟩)
      simpa [H, hω, Function.comp_def] using h
  have hmeas : ∀ r, 0 < r → Measurable (fun p : ℂ × Ω => H p.2 r p.1) := by
    intro r hr
    change Measurable (Function.uncurry (fun z ω => H ω r z))
    apply measurable_uncurry_of_continuous_of_measurable
    · exact fun ω => hcont ω r hr
    · intro z
      exact Measurable.ite hNmeas measurable_const (hGFF.measurable_circle r z hr)
  refine ⟨H, hcont, hmeas, ?_⟩
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNnull)
  filter_upwards [hae] with ω hω
  intro r z
  simp [H, hω]


end LatticeProb.Gauss

namespace LatticeProb.LQG

noncomputable section

/-- **Locality of the γ-LQG area measure** (Fact 2.1 II; Duplantier-Sheffield 2011, locality). Under whole-plane GFF,
for `0 < γ < 2` and `α₀ < lqgQ γ`, for every γ-LQG area measure `μ` of `h = h^ℂ - α₀ log |·|` and every open `U`, the mass
`μ(U)` is a.s. equal to a `σ(h|_U)`-measurable random variable (`fieldSigmaAlgebra α₀ hC U`). -/
def LQGLocality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ U : Set ℂ, IsOpen U →
      ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧ ∀ᵐ ω ∂P, μ ω U = Y ω

/-- **Circle-average locality link** (LP form of the link of Fact 2.1 II). For every open `U` and every closed ball
`closedBall z r ⊆ U` with `r > 0`, the circle average `fieldCircleAverage α₀ (hcirc ω) r z` is a.s. equal to a
`σ(h|_U)`-measurable random variable. Stated under the whole-plane GFF premise, which is needed: without it the claim is
false (a counterexample, recorded in `HarmonicBalls/FirstPass/Phase2/LQGLocalityDerived.lean`). Hypothesis of
`lqgLocality_of_circleLink`; not proved in this file. -/
def LQGCircleAverageLink {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ U →
    ∃ g : Ω → ℝ, Measurable[fieldSigmaAlgebra α₀ hC U] g ∧
      ∀ᵐ ω ∂P, fieldCircleAverage α₀ (hcirc ω) r z = g ω

/-- The σ-algebra `σ(h|_U)` contains the pairings `hC · φ` with test functions `φ` supported in `U`, up to the
deterministic shift `α₀ ∫ φ log|·|`: `ω ↦ hC ω φ` is `σ(h|_U)`-measurable. -/
theorem measurable_gff_pairing {Ω : Type*} [MeasurableSpace Ω] (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (U : Set ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction U φ) :
    @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => hC ω φ) := by
  have h1 : MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) φ) inferInstance ≤
      fieldSigmaAlgebra α₀ hC U := by
    unfold fieldSigmaAlgebra
    exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ) =>
      MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) ψ) inferInstance) φ hφ
  have h2 : @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => fieldPairing α₀ (hC ω) φ) :=
    Measurable.of_comap_le h1
  have h3 := h2.add_const (α₀ * ∫ x, φ x * Real.log ‖x‖)
  convert h3 using 1
  funext ω
  simp [fieldPairing]


open Classical in
/-- Distance from `z` to `Uᶜ`, with the convention `1 + ‖z‖` when `U = ℂ` (`infDist _ ∅ = 0` in Mathlib). -/
def dCompl (U : Set ℂ) (z : ℂ) : ℝ :=
  if (Uᶜ).Nonempty then Metric.infDist z Uᶜ else 1 + ‖z‖

lemma dCompl_continuous (U : Set ℂ) : Continuous (dCompl U) := by
  unfold dCompl
  split_ifs
  · exact Metric.continuous_infDist_pt _
  · exact continuous_const.add continuous_norm

lemma dCompl_nonneg (U : Set ℂ) (z : ℂ) : 0 ≤ dCompl U z := by
  unfold dCompl
  split_ifs
  · exact Metric.infDist_nonneg
  · have := norm_nonneg z
    linarith

lemma dCompl_pos_of_mem {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : 0 < dCompl U z := by
  unfold dCompl
  split_ifs with h
  · exact (hU.isClosed_compl.notMem_iff_infDist_pos h).mp (by simpa using hz)
  · have := norm_nonneg z
    linarith

lemma dCompl_eq_zero_of_notMem {U : Set ℂ} {z : ℂ} (hz : z ∉ U) : dCompl U z = 0 := by
  have h : (Uᶜ).Nonempty := ⟨z, by simpa using hz⟩
  unfold dCompl
  simp only [h, ↓reduceIte]
  exact Metric.infDist_zero_of_mem (by simpa using hz)

lemma ball_subset_of_lt_dCompl {U : Set ℂ} {z : ℂ} {ε : ℝ} (h : ε < dCompl U z) :
    Metric.closedBall z ε ⊆ U := by
  intro w hw
  by_contra hwU
  have hw' : w ∈ Uᶜ := hwU
  unfold dCompl at h
  split_ifs at h with hne
  · have h1 := Metric.infDist_le_dist_of_mem (x := z) hw'
    have h2 : dist w z ≤ ε := hw
    rw [dist_comm] at h1
    linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne] at hw'
    exact hw'

/-! ### Exhaustion of an open set by cut-offs -/

/-- `f_n(z) = min(1, max(0, n·dCompl U z − 1)) · min(1, max(0, n − |z|))`: continuous, `0 ≤ f_n ≤ 1_U`,
increasing in `n`, supported in `closedBall 0 n`, and `f_n(z) ≠ 0` forces `1/n < dCompl U z`. -/
def exhaustFn (U : Set ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  min 1 (max 0 ((n : ℝ) * dCompl U z - 1)) * min 1 (max 0 ((n : ℝ) - ‖z‖))

lemma exhaustFn_continuous (U : Set ℂ) (n : ℕ) : Continuous (exhaustFn U n) := by
  unfold exhaustFn
  exact (continuous_const.min (continuous_const.max
      ((continuous_const.mul (dCompl_continuous U)).sub continuous_const))).mul
    (continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm)))

lemma exhaustFn_nonneg (U : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ exhaustFn U n z :=
  mul_nonneg (le_min zero_le_one (le_max_left _ _)) (le_min zero_le_one (le_max_left _ _))

lemma exhaustFn_le_one (U : Set ℂ) (n : ℕ) (z : ℂ) : exhaustFn U n z ≤ 1 :=
  by unfold exhaustFn; simpa using mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min zero_le_one (le_max_left _ _)) (zero_le_one : (0:ℝ) ≤ 1)

lemma exhaustFn_hasCompactSupport (U : Set ℂ) (n : ℕ) : HasCompactSupport (exhaustFn U n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) n) (fun z hz => ?_)
  by_contra h
  apply hz
  unfold exhaustFn at h
  have h2 : 0 < min 1 (max 0 ((n : ℝ) - ‖z‖)) := by
    refine lt_of_le_of_ne (le_min zero_le_one (le_max_left _ _)) fun h' => h ?_
    rw [← h', mul_zero]
  have h3 : 0 < (n : ℝ) - ‖z‖ :=
    (lt_max_iff.mp (lt_min_iff.mp h2).2).resolve_left (lt_irrefl 0)
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith

lemma exhaustFn_eq_zero_of_notMem (U : Set ℂ) (n : ℕ) {z : ℂ} (hz : z ∉ U) :
    exhaustFn U n z = 0 := by
  unfold exhaustFn
  rw [dCompl_eq_zero_of_notMem hz]
  simp

lemma lt_dCompl_of_exhaustFn_ne_zero {U : Set ℂ} {n : ℕ} {ε : ℝ} (hε : (n : ℝ) * ε ≤ 1) {z : ℂ}
    (hz : exhaustFn U n z ≠ 0) : ε < dCompl U z := by
  unfold exhaustFn at hz
  have h1 : 0 < min 1 (max 0 ((n : ℝ) * dCompl U z - 1)) := by
    refine lt_of_le_of_ne (le_min zero_le_one (le_max_left _ _)) fun h => hz ?_
    rw [← h, zero_mul]
  have h2 : 0 < (n : ℝ) * dCompl U z - 1 :=
    (lt_max_iff.mp (lt_min_iff.mp h1).2).resolve_left (lt_irrefl 0)
  by_contra hcon
  have hcon := not_lt.mp hcon
  have := mul_le_mul_of_nonneg_left hcon (Nat.cast_nonneg n)
  linarith

lemma exhaustFn_mono (U : Set ℂ) (z : ℂ) : Monotone fun n : ℕ => exhaustFn U n z := by
  intro n m hnm
  have hn : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 : (n : ℝ) * dCompl U z ≤ (m : ℝ) * dCompl U z :=
    mul_le_mul_of_nonneg_right hn (dCompl_nonneg U z)
  unfold exhaustFn
  exact mul_le_mul (min_le_min le_rfl (max_le_max le_rfl (by linarith)))
    (min_le_min le_rfl (max_le_max le_rfl (by linarith)))
    (le_min zero_le_one (le_max_left _ _)) (le_min zero_le_one (le_max_left _ _))

lemma exhaustFn_tendsto {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (exhaustFn U n z)) atTop (𝓝 (U.indicator 1 z)) := by
  by_cases hz : z ∈ U
  · have hd := dCompl_pos_of_mem hU hz
    rw [Set.indicator_of_mem hz, Pi.one_apply]
    obtain ⟨N, hN⟩ := exists_nat_ge (max (2 / dCompl U z) (‖z‖ + 1))
    have hN1 : 2 / dCompl U z ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
    have hN2 : ‖z‖ + 1 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
    have hev : ∀ n : ℕ, N ≤ n → ENNReal.ofReal (exhaustFn U n z) = 1 := by
      intro n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have a1 : 1 ≤ (n : ℝ) * dCompl U z - 1 := by
        have : 2 ≤ (n : ℝ) * dCompl U z := (div_le_iff₀ hd).mp (by linarith)
        linarith
      have a2 : 1 ≤ (n : ℝ) - ‖z‖ := by linarith
      unfold exhaustFn
      rw [min_eq_left (le_max_of_le_right a1), min_eq_left (le_max_of_le_right a2), mul_one,
        ENNReal.ofReal_one]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => (hev n hn).symm⟩)
  · have h0 : ∀ n : ℕ, ENNReal.ofReal (exhaustFn U n z) = 0 := fun n => by
      rw [exhaustFn_eq_zero_of_notMem U n hz, ENNReal.ofReal_zero]
    rw [Set.indicator_of_notMem hz]
    simp only [h0]
    exact tendsto_const_nhds

lemma tendsto_lintegral_exhaustFn (μ : Measure ℂ) {U : Set ℂ} (hU : IsOpen U) :
    Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂μ) atTop (𝓝 (μ U)) := by
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun n z => ENNReal.ofReal (exhaustFn U n z)) (F := U.indicator 1)
    (fun n => (ENNReal.measurable_ofReal.comp (exhaustFn_continuous U n).measurable).aemeasurable)
    (ae_of_all _ fun z n m hnm => ENNReal.ofReal_le_ofReal (exhaustFn_mono U z hnm))
    (ae_of_all _ fun z => exhaustFn_tendsto hU z)
  rwa [lintegral_indicator_one hU.measurableSet] at h

/-! ### Vague limits and the dyadic approximations -/

lemma lintegral_ofReal_eq_ofReal_integral_of_compact {ν : Measure ℂ} [IsLocallyFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (h0 : ∀ z, 0 ≤ f z) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂ν = ENNReal.ofReal (∫ z, f z ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hc)
    (ae_of_all _ h0)).symm

lemma tendsto_lintegral_of_isLQGLimit {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (h0 : ∀ z, 0 ≤ f z) :
    Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (f z) ∂(lqgApprox γ hε (dyadicScale k))) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂m)) := by
  have : IsLocallyFiniteMeasure m := hm.isLocallyFiniteMeasure
  have hloc : ∀ k : ℕ, IsLocallyFiniteMeasure (lqgApprox γ hε (dyadicScale k)) := fun k => by
    unfold lqgApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont k))))
  have key : (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (f z) ∂(lqgApprox γ hε (dyadicScale k))) =
      fun k : ℕ => ENNReal.ofReal (∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) :=
    funext fun k => lintegral_ofReal_eq_ofReal_integral_of_compact hf hc h0
  rw [key, lintegral_ofReal_eq_ofReal_integral_of_compact hf hc h0]
  exact ENNReal.tendsto_ofReal (hm.tendsto_integral f hf hc)

/-! ### Grid versions of a family of random variables (measurable in ω, continuous in z) -/

/-- Dyadic cell of level `N` containing `z`, as an index `(N, ⌊2^N re z⌋, ⌊2^N im z⌋)`. -/
def dyadicIdx (N : ℕ) (z : ℂ) : ℕ × ℤ × ℤ :=
  (N, ⌊(2 : ℝ) ^ N * z.re⌋, ⌊(2 : ℝ) ^ N * z.im⌋)

/-- Point `(a + i b) / 2^N` attached to the index `(N, a, b)`. -/
def dyadicPt (j : ℕ × ℤ × ℤ) : ℂ :=
  ⟨((j.2.1 : ℤ) : ℝ) / 2 ^ j.1, ((j.2.2 : ℤ) : ℝ) / 2 ^ j.1⟩

lemma measurable_dyadicIdx (N : ℕ) : Measurable (dyadicIdx N) := by
  unfold dyadicIdx
  exact measurable_const.prodMk
    ((Int.measurable_floor.comp (measurable_const.mul Complex.measurable_re)).prodMk
      (Int.measurable_floor.comp (measurable_const.mul Complex.measurable_im)))

lemma abs_floor_div_sub_le (x : ℝ) (N : ℕ) :
    |((⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) / 2 ^ N - x| ≤ 1 / 2 ^ N := by
  have ht : (0 : ℝ) < 2 ^ N := by positivity
  have h1 := Int.floor_le ((2 : ℝ) ^ N * x)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ N * x)
  have heq : ((⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) / 2 ^ N - x
      = (((⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) - 2 ^ N * x) / 2 ^ N := by
    field_simp
  rw [heq, abs_div, abs_of_pos ht]
  gcongr
  rw [abs_le]
  constructor <;> linarith

lemma tendsto_dyadicPt_idx (z : ℂ) :
    Tendsto (fun N : ℕ => dyadicPt (dyadicIdx N z)) atTop (𝓝 z) := by
  have hbound : ∀ N : ℕ, dist (dyadicPt (dyadicIdx N z)) z ≤ 2 * (1 / (2 : ℝ) ^ N) := by
    intro N
    rw [Complex.dist_eq]
    calc ‖dyadicPt (dyadicIdx N z) - z‖
        ≤ |(dyadicPt (dyadicIdx N z) - z).re| + |(dyadicPt (dyadicIdx N z) - z).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 / (2 : ℝ) ^ N + 1 / (2 : ℝ) ^ N := by
          apply add_le_add
          · simpa [dyadicPt, dyadicIdx] using abs_floor_div_sub_le z.re N
          · simpa [dyadicPt, dyadicIdx] using abs_floor_div_sub_le z.im N
      _ = 2 * (1 / (2 : ℝ) ^ N) := by ring
  have hlim : Tendsto (fun N : ℕ => 2 * (1 / (2 : ℝ) ^ N)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).const_mul 2
    rw [mul_zero] at h
    exact h.congr fun N => by rw [one_div_pow]
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun N => dist_nonneg) hbound hlim

/-- Grid version: if each `G(·, z)` on `W` is a.s. equal to a `m`-measurable `g_z`, with `G(ω, ·)`
continuous, then there is a jointly `m ⊗ Borel`-measurable `Ψ` equal to `G` a.s. on `W`
(limit over dyadic cells of the countably many versions `g_j`). -/
lemma exists_grid_version {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (G : Ω → ℂ → ℝ) (hGc : ∀ ω, Continuous (G ω)) (W : Set ℂ)
    (hW : IsOpen W)
    (hL : ∀ z ∈ W, ∃ g : Ω → ℝ, @Measurable Ω ℝ m _ g ∧ ∀ᵐ ω ∂P, G ω z = g ω) :
    ∃ Ψ : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (@Prod.instMeasurableSpace Ω ℂ m _) _ (fun p => Ψ p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ W, Ψ ω z = G ω z := by
  classical
  have hj : ∀ j : ℕ × ℤ × ℤ, ∃ g : Ω → ℝ, @Measurable Ω ℝ m _ g ∧
      (dyadicPt j ∈ W → ∀ᵐ ω ∂P, G ω (dyadicPt j) = g ω) := by
    intro j
    by_cases hjW : dyadicPt j ∈ W
    · obtain ⟨g, hgm, hg⟩ := hL _ hjW
      exact ⟨g, hgm, fun _ => hg⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h hjW⟩
  choose g hgm hgeq using hj
  have hgood : ∀ᵐ ω ∂P, ∀ j : ℕ × ℤ × ℤ, dyadicPt j ∈ W → G ω (dyadicPt j) = g j ω := by
    rw [ae_all_iff]
    intro j
    by_cases hjW : dyadicPt j ∈ W
    · filter_upwards [hgeq j hjW] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun ω h => absurd h hjW
  refine ⟨fun ω z => limsup (fun N : ℕ => g (dyadicIdx N z) ω) atTop, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    have hF : ∀ N : ℕ, Measurable (fun p : Ω × ℂ => g (dyadicIdx N p.2) p.1) := by
      intro N
      have h1 : Measurable (fun q : Ω × (ℕ × ℤ × ℤ) => g q.2 q.1) :=
        measurable_from_prod_countable_left (fun y => hgm y)
      have h2 : Measurable (fun p : Ω × ℂ => (p.1, dyadicIdx N p.2)) :=
        measurable_fst.prodMk ((measurable_dyadicIdx N).comp measurable_snd)
      exact h1.comp h2
    exact Measurable.limsup hF
  · filter_upwards [hgood] with ω hω
    intro z hz
    have hev : ∀ᶠ N in atTop, dyadicPt (dyadicIdx N z) ∈ W :=
      (tendsto_dyadicPt_idx z).eventually (hW.mem_nhds hz)
    have heq : ∀ᶠ N in atTop, G ω (dyadicPt (dyadicIdx N z)) = g (dyadicIdx N z) ω :=
      hev.mono fun N hN => hω _ hN
    have hlim : Tendsto (fun N : ℕ => g (dyadicIdx N z) ω) atTop (𝓝 (G ω z)) :=
      (((hGc ω).tendsto z).comp (tendsto_dyadicPt_idx z)).congr' (heq.mono fun N hN => hN)
    exact hlim.limsup_eq

/-! ### Measurability of the approximating integrals in the sub-σ-algebra -/

lemma measurable_lintegral_of_prod {Ω : Type*} (m : MeasurableSpace Ω) (F : Ω → ℂ → ℝ≥0∞)
    (hF : @Measurable (Ω × ℂ) ℝ≥0∞ (@Prod.instMeasurableSpace Ω ℂ m _) _ (fun p => F p.1 p.2)) :
    @Measurable Ω ℝ≥0∞ m _ (fun ω => ∫⁻ z, F ω z) := by
  let : MeasurableSpace Ω := m
  exact Measurable.lintegral_prod_right' hF

lemma measurable_density_prod {Ω : Type*} (m : MeasurableSpace Ω) (Φ : Ω → ℂ → ℝ)
    (hΦ : @Measurable (Ω × ℂ) ℝ (@Prod.instMeasurableSpace Ω ℂ m _) _ (fun p => Φ p.1 p.2))
    (c γ : ℝ) (f : ℂ → ℝ) (hf : Continuous f) :
    @Measurable (Ω × ℂ) ℝ≥0∞ (@Prod.instMeasurableSpace Ω ℂ m _) _
      (fun p => ENNReal.ofReal (c * Real.exp (γ * Φ p.1 p.2)) * ENNReal.ofReal (f p.2)) := by
  let : MeasurableSpace Ω := m
  exact (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hΦ)))).mul
    (ENNReal.measurable_ofReal.comp (hf.measurable.comp measurable_snd))

/-- The `n`-th cut-off integral of the `k`-th dyadic approximation, its density built from `Ψk`. -/
def densityIntegral {Ω : Type*} (γ : ℝ) (U : Set ℂ) (n k : ℕ) (Ψk : Ω → ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * Ψk ω z)) *
    ENNReal.ofReal (exhaustFn U n z)


/-- Fact 2.1 II (locality), with the circle-average link relativised to the whole-plane GFF premise. The proof is that of
`lqgMeasureLocality_of_circleLink` (`LQGLocalityDerived.lean:321`); the only use of the link is at `hWk`,
where `hGFF` is in scope. -/
theorem lqgLocality_of_circleLink {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hlink : IsWholePlaneGFF P hC hcirc → LQGCircleAverageLink P α₀ hC hcirc) :
    LQGLocality P γ α₀ hC hcirc := by
  unfold LQGLocality
  intro hGFF _ _ _ μ hμ U hU
  obtain ⟨H, hHc, _, hHae⟩ := hGFF.exists_jointlyMeasurable_circleAverage
  have hGc : ∀ (ω : Ω) (k : ℕ),
      Continuous (fun z => fieldCircleAverage α₀ (H ω) (dyadicScale k) z) := by
    intro ω k
    unfold fieldCircleAverage
    exact (hHc ω _ (ProfileDerived.dyadicScale_pos k)).sub
      (continuous_const.mul (ProfileDerived.continuous_circleAverage_log_norm (ProfileDerived.dyadicScale_pos k)))
  -- one grid version per dyadic scale, on the cells well inside `U`
  have hWk : ∀ k : ℕ, ∃ Ψ : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (@Prod.instMeasurableSpace Ω ℂ (fieldSigmaAlgebra α₀ hC U) _) _
        (fun p => Ψ p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ {z : ℂ | dyadicScale k < dCompl U z},
        Ψ ω z = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
    intro k
    obtain ⟨Ψ, hΨm, hΨ⟩ := exists_grid_version P (fieldSigmaAlgebra α₀ hC U)
      (fun ω z => fieldCircleAverage α₀ (H ω) (dyadicScale k) z) (fun ω => hGc ω k)
      {z : ℂ | dyadicScale k < dCompl U z} (isOpen_lt continuous_const (dCompl_continuous U))
      (by
        intro z hz
        obtain ⟨g, hgm, hg⟩ := hlink hGFF U hU (dyadicScale k) z (ProfileDerived.dyadicScale_pos k)
          (ball_subset_of_lt_dCompl hz)
        refine ⟨g, hgm, ?_⟩
        filter_upwards [hHae, hg] with ω hω1 hω2
        show fieldCircleAverage α₀ (H ω) (dyadicScale k) z = g ω
        rw [← hω2]
        simp only [fieldCircleAverage, hω1])
    exact ⟨Ψ, hΨm, hΨ⟩
  choose Ψ hΨm hΨ using hWk
  have hm : ∀ n k : ℕ, @Measurable Ω ℝ≥0∞ (fieldSigmaAlgebra α₀ hC U) _
      (densityIntegral γ U n k (Ψ k)) := by
    intro n k
    exact measurable_lintegral_of_prod (fieldSigmaAlgebra α₀ hC U)
      (fun ω z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * Ψ k ω z)) *
        ENNReal.ofReal (exhaustFn U n z))
      (measurable_density_prod (fieldSigmaAlgebra α₀ hC U) (Ψ k) (hΨm k)
        (dyadicScale k ^ (γ ^ 2 / 2)) γ (exhaustFn U n) (exhaustFn_continuous U n))
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hgood : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) ∧
      (∀ r z, H ω r z = hcirc ω r z) ∧
      ∀ k : ℕ, ∀ z ∈ {z : ℂ | dyadicScale k < dCompl U z},
        Ψ k ω z = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
    filter_upwards [hμ', hHae, ae_all_iff.mpr hΨ] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨fun ω => ⨆ n : ℕ, limsup (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop,
    Measurable.iSup fun n => Measurable.limsup fun k => hm n k, ?_⟩
  filter_upwards [hgood] with ω hω
  obtain ⟨h1, h2, h3⟩ := hω
  have hcontω : ∀ k : ℕ, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale k)) := by
    intro k
    have hfun : fieldCircleAverage α₀ (hcirc ω) (dyadicScale k)
        = fieldCircleAverage α₀ (H ω) (dyadicScale k) := by
      funext z
      simp only [fieldCircleAverage, h2]
    rw [hfun]
    exact hGc ω k
  have hstep : ∀ n : ℕ, Tendsto (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω))) := by
    intro n
    have hT := tendsto_lintegral_of_isLQGLimit h1 hcontω (exhaustFn_continuous U n)
      (exhaustFn_hasCompactSupport U n) (exhaustFn_nonneg U n)
    have hT0 : Tendsto (fun k : ℕ => dyadicScale k * n) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_const (n : ℝ)
      rw [zero_mul] at h
      exact h
    have hev := hT0.eventually (gt_mem_nhds zero_lt_one)
    refine hT.congr' ?_
    filter_upwards [hev] with k hk
    have hk' : (n : ℝ) * dyadicScale k ≤ 1 := by rw [mul_comm]; exact hk.le
    have hρ : Measurable (fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Real.measurable_exp.comp (measurable_const.mul (hcontω k).measurable)))
    have hfm : Measurable (fun z => ENNReal.ofReal (exhaustFn U n z)) :=
      ENNReal.measurable_ofReal.comp (exhaustFn_continuous U n).measurable
    unfold densityIntegral lqgApprox
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ hfm]
    apply lintegral_congr
    intro z
    simp only [Pi.mul_apply]
    by_cases hz : dyadicScale k < dCompl U z
    · have hfc : fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z
          = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
        simp only [fieldCircleAverage, h2]
      rw [h3 k z hz, hfc]
    · have hf0 : exhaustFn U n z = 0 := by
        by_contra hne
        exact hz (lt_dCompl_of_exhaustFn_ne_zero hk' hne)
      simp [hf0]
  have hμU := tendsto_lintegral_exhaustFn (μ ω) hU
  have hmono : Monotone (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω)) :=
    fun n m hnm => lintegral_mono fun z => ENNReal.ofReal_le_ofReal (exhaustFn_mono U z hnm)
  have hsup : μ ω U = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω) :=
    tendsto_nhds_unique hμU (tendsto_atTop_iSup hmono)
  show μ ω U = ⨆ n : ℕ, limsup (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop
  rw [hsup]
  exact iSup_congr fun n => ((hstep n).limsup_eq).symm


end

end LatticeProb.LQG
