/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.DualExistence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# GFF-K3, nodes E2 and E3: existence of dual-norm GFFs; a countable test family

* E2: `exists_dualGFF` (generic, from Riesz vectors in `GradSpace D` and the Gaussian Hilbert
  series), `exists_zeroGFFOn`, `exists_mixedGFF`.
* E3: `exists_testFamily`, the fixed family `testFamily`, `dualNormSq_eq_iSup_testFamily`,
  `measurable_dualNormSq_zeroSpace` (ℝ≥0∞-valued) and `measurable_zeroGFFTestCov`.
  The latter needs no finiteness of `dualCov` (node H3): `toReal` is measurable on `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

namespace QuantumZipper.K3

open GFFExist LQGDimension.ExistAsm

/-! ## E2 -/

theorem exists_dualGFF (D : Set ℂ) (V : Set (ℂ → ℝ)) (hV : IsDNSpace D V) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Measure ℂ → ℝ),
      IsProbabilityMeasure P ∧ (∀ μ, Measurable fun ω => X ω μ) ∧
      IsGaussianProcess (fun (μ : {μ // IsAdmissibleDual D V μ}) ω => X ω μ.1) P ∧
      (∀ μ, IsAdmissibleDual D V μ → ∫ ω, X ω μ ∂P = 0) ∧
      ∀ μ ν, IsAdmissibleDual D V μ → IsAdmissibleDual D V ν →
        cov[fun ω => X ω μ, fun ω => X ω ν; P] = dualCov D V μ ν := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : {μ // IsAdmissibleDual D V μ} → GradSpace D,
      v = fun μ => rieszVec D V μ.1 := ⟨_, rfl⟩
  obtain ⟨X, hXm, hX⟩ := gs_process_hilbert {μ // IsAdmissibleDual D V μ} v
  obtain ⟨F, hF⟩ : ∃ F : (ℕ → ℝ) → Measure ℂ → ℝ,
      F = fun ω μ => if h : IsAdmissibleDual D V μ then X ⟨μ, h⟩ ω else 0 := ⟨_, rfl⟩
  have hFX : ∀ (μ : Measure ℂ) (h : IsAdmissibleDual D V μ), (fun ω => F ω μ) = X ⟨μ, h⟩ := by
    intro μ h; funext ω; simp only [hF, h, ↓reduceDIte]
  have hlaw1 : ∀ μ : {μ // IsAdmissibleDual D V μ},
      HasLaw (X μ) (gaussianReal 0 (‖v μ‖ ^ 2).toNNReal) stdP :=
    fun μ => gs_comb4 hX ![μ, μ, μ, μ] ![1, 0, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])
  refine ⟨ℕ → ℝ, inferInstance, stdP, F, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro μ
    by_cases h : IsAdmissibleDual D V μ
    · rw [hFX μ h]; exact hXm _
    · have : (fun ω => F ω μ) = fun _ => 0 := by funext ω; simp only [hF, h, ↓reduceDIte]
      rw [this]; exact measurable_const
  · have e : (fun (μ : {μ // IsAdmissibleDual D V μ}) (ω : ℕ → ℝ) => F ω μ.1) = X := by
      funext μ ω; exact congrFun (hFX μ.1 μ.2) ω
    rw [e]
    exact gs_isGaussianProcess (fun t => (hXm t).aemeasurable)
      fun I c => ⟨_, hX (fun i : I => (i : {μ // IsAdmissibleDual D V μ})) c⟩
  · intro μ hμ
    rw [hFX μ hμ]
    exact gs_integral_eq_zero (hlaw1 ⟨μ, hμ⟩)
  · intro μ ν hμ hν
    rw [hFX μ hμ, hFX ν hν, dualCov_eq_inner_rieszVec hV hμ hν]
    have ev : ∀ μ' (h' : IsAdmissibleDual D V μ'), rieszVec D V μ' = v ⟨μ', h'⟩ := by
      intro μ' h'; rw [hv]
    rw [ev μ hμ, ev ν hν]
    refine gs_cov_eq (hlaw1 ⟨μ, hμ⟩) (hlaw1 ⟨ν, hν⟩) ?_
    exact gs_comb4 hX ![⟨μ, hμ⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩, ⟨μ, hμ⟩] ![1, 1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])

/-- **Non-vacuity of `IsZeroBoundaryGFFOn`.** -/
theorem exists_zeroGFFOn (U : Set ℂ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Measure ℂ → ℝ),
      IsProbabilityMeasure P ∧ IsZeroBoundaryGFFOn U X P := by
  obtain ⟨Ω, _, P, X, hP, h1, h2, h3, h4⟩ :=
    exists_dualGFF U (zeroSpace U) (isDNSpace_zeroSpace U)
  exact ⟨Ω, _, P, X, hP, ⟨h1, h2, h3, h4⟩⟩

/-- **Non-vacuity of `IsMixedGFF`.** -/
theorem exists_mixedGFF (D S : Set ℂ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Measure ℂ → ℝ),
      IsProbabilityMeasure P ∧ IsMixedGFF D S X P := by
  obtain ⟨Ω, _, P, X, hP, h1, h2, h3, h4⟩ :=
    exists_dualGFF D (mixedSpace D S) (isDNSpace_mixedSpace D S)
  exact ⟨Ω, _, P, X, hP, ⟨h1, h2, h3, h4⟩⟩

/-! ## E3: finite unions of rational-type balls -/

/-- Finite union of open balls with centers in a dense sequence and rational radii. -/
def rbO (s : Finset (ℕ × ℚ)) : Set ℂ := ⋃ p ∈ s, Metric.ball (denseSeq ℂ p.1) (p.2 : ℝ)

/-- The corresponding finite union of closed balls. -/
def rbK (s : Finset (ℕ × ℚ)) : Set ℂ := ⋃ p ∈ s, Metric.closedBall (denseSeq ℂ p.1) (p.2 : ℝ)

lemma rbO_subset_rbK (s : Finset (ℕ × ℚ)) : rbO s ⊆ rbK s :=
  biUnion_mono subset_rfl fun _ _ => Metric.ball_subset_closedBall

lemma isCompact_rbK (s : Finset (ℕ × ℚ)) : IsCompact (rbK s) :=
  s.isCompact_biUnion fun _ _ => isCompact_closedBall _ _

lemma exists_rb {C U : Set ℂ} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ s, C ⊆ rbO s ∧ rbK s ⊆ U := by
  have hball : ∀ z ∈ U, ∃ p : ℕ × ℚ, z ∈ Metric.ball (denseSeq ℂ p.1) (p.2 : ℝ) ∧
      Metric.closedBall (denseSeq ℂ p.1) (p.2 : ℝ) ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
    obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (half_pos hε)
    obtain ⟨n, hn⟩ := (denseRange_denseSeq ℂ).exists_dist_lt z hr0
    refine ⟨(n, r), hn, fun w hw => hεU ?_⟩
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have h1 := dist_triangle w (denseSeq ℂ n) z
    have h2 := dist_comm (denseSeq ℂ n) z
    simp only at hw hn
    linarith
  choose! p hp using hball
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun z : C => Metric.ball (denseSeq ℂ (p z).1) ((p z).2 : ℝ)) (fun _ => Metric.isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, (hp z (hCU hz)).1⟩)
  refine ⟨t.image fun z => p z.1, fun z hz => ?_, ?_⟩
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion₂.mpr ⟨p i.1, Finset.mem_image_of_mem _ hi, hzi⟩
  · refine iUnion₂_subset fun q hq => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact (hp i.1 (hCU i.2)).2

lemma exists_countable_approx (s : Finset (ℕ × ℚ)) :
    ∃ G : Set (ℂ → ℝ), G.Countable ∧ G ⊆ zeroSpace (rbO s) ∧
      ∀ f ∈ zeroSpace (rbO s), ∀ δ > 0, ∃ g ∈ G, ∀ z,
        |g z - f z| < δ ∧ ‖fderiv ℝ g z - fderiv ℝ f z‖ < δ := by
  have : CompactSpace (rbK s) := isCompact_iff_compactSpace.mp (isCompact_rbK s)
  let Φ : zeroSpace (rbO s) → C(rbK s, ℝ × (ℂ →L[ℝ] ℝ)) := fun x =>
    ⟨fun z => (x.1 z, fderiv ℝ x.1 z),
      (x.2.1.continuous.prodMk (x.2.1.continuous_fderiv smooth_ne_zero)).comp
        continuous_subtype_val⟩
  obtain ⟨c, hcsub, hcc, hdense⟩ :=
    (IsSeparable.of_subtype (Set.range Φ)).exists_countable_dense_subset
  have hpre : ∀ y : c, ∃ x, Φ x = y.1 := fun y => hcsub y.2
  choose pre hpre using hpre
  have := hcc.to_subtype
  refine ⟨Set.range fun y : c => (pre y).1, countable_range _, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact (pre y).2
  · intro f hf δ hδ
    have hmem : Φ ⟨f, hf⟩ ∈ closure c := hdense ⟨⟨f, hf⟩, rfl⟩
    have hmem' : Φ ⟨f, hf⟩ ∈ @closure C(rbK s, ℝ × (ℂ →L[ℝ] ℝ))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace c := hmem
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hmem' δ hδ
    refine ⟨(pre ⟨y, hy⟩).1, ⟨⟨y, hy⟩, rfl⟩, fun z => ?_⟩
    have hgy : Φ (pre ⟨y, hy⟩) = y := hpre ⟨y, hy⟩
    by_cases hz : z ∈ rbK s
    · have h1 := ContinuousMap.dist_apply_le_dist (f := Φ ⟨f, hf⟩) (g := y) ⟨z, hz⟩
      have h2 : dist ((Φ ⟨f, hf⟩) ⟨z, hz⟩) ((Φ (pre ⟨y, hy⟩)) ⟨z, hz⟩) < δ := by
        rw [hgy]; exact lt_of_le_of_lt h1 hdist
      change dist (f z, fderiv ℝ f z) ((pre ⟨y, hy⟩).1 z, fderiv ℝ (pre ⟨y, hy⟩).1 z) < δ at h2
      rw [Prod.dist_eq] at h2
      constructor
      · rw [← Real.dist_eq, dist_comm]; exact lt_of_le_of_lt (le_max_left _ _) h2
      · rw [← dist_eq_norm, dist_comm]; exact lt_of_le_of_lt (le_max_right _ _) h2
    · have hfz : z ∉ tsupport f := fun h => hz (rbO_subset_rbK s (hf.2.2 h))
      have hgz : z ∉ tsupport (pre ⟨y, hy⟩).1 :=
        fun h => hz (rbO_subset_rbK s ((pre ⟨y, hy⟩).2.2.2 h))
      have e1 : f z = 0 := by by_contra h; exact hfz (subset_tsupport f h)
      have e2 : (pre ⟨y, hy⟩).1 z = 0 := by by_contra h; exact hgz (subset_tsupport _ h)
      have e3 : fderiv ℝ f z = 0 := by
        by_contra h; exact hfz (support_fderiv_subset (𝕜 := ℝ) (f := f) h)
      have e4 : fderiv ℝ (pre ⟨y, hy⟩).1 z = 0 := by
        by_contra h; exact hgz (support_fderiv_subset (𝕜 := ℝ) (f := (pre ⟨y, hy⟩).1) h)
      rw [e1, e2, e3, e4]; simp [hδ]

lemma zeroSpace_sub {U : Set ℂ} {f g : ℂ → ℝ} (hf : f ∈ zeroSpace U) (hg : g ∈ zeroSpace U) :
    g - f ∈ zeroSpace U := by
  have : g - f = g + (-1 : ℝ) • f := by funext z; simp [sub_eq_add_neg]
  rw [this]
  exact (isDNSpace_zeroSpace U).add_mem _ hg _ ((isDNSpace_zeroSpace U).smul_mem _ _ hf)

/-- **E3, countable determining family.** -/
theorem exists_testFamily : ∃ F : ℕ → ℂ → ℝ, (∀ j, F j ∈ zeroSpace H) ∧
    ∀ U, IsOpen U → U ⊆ H → ∀ f ∈ zeroSpace U, ∀ ε > 0, ∃ j, tsupport (F j) ⊆ U ∧
      dirichletEnergyOn H (F j - f) < ε ∧ ∀ z, |F j z - f z| < ε := by
  choose G hGc hGsub hGapp using exists_countable_approx
  let A : Set (ℂ → ℝ) := insert 0 (⋃ s : Finset (ℕ × ℚ), ⋃ (_ : rbO s ⊆ H), G s)
  have hAc : A.Countable :=
    (countable_iUnion fun s => countable_iUnion fun _ => hGc s).insert 0
  obtain ⟨F, hF⟩ := hAc.exists_eq_range (insert_nonempty 0 _)
  refine ⟨F, fun j => ?_, ?_⟩
  · have hj : F j ∈ A := hF ▸ mem_range_self j
    rcases hj with h | h
    · rw [h]; exact (isDNSpace_zeroSpace H).zero_mem
    · obtain ⟨s, hs, hg⟩ : ∃ s, rbO s ⊆ H ∧ F j ∈ G s := by simpa using h
      have := hGsub s hg
      exact ⟨this.1, this.2.1, this.2.2.trans hs⟩
  · intro U hU hUH f hf ε hε
    obtain ⟨s, hsf, hsU⟩ := exists_rb hf.2.1 hU hf.2.2
    have hm0 : 0 ≤ (volume (rbK s)).toReal := ENNReal.toReal_nonneg
    set m := (volume (rbK s)).toReal with hm
    have hq0 : 0 < ε / (2 * (m + 1)) := by positivity
    have hq : ε / (2 * (m + 1)) * (2 * (m + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    set δ := min 1 (ε / (2 * (m + 1))) with hδdef
    have hδ : 0 < δ := lt_min one_pos hq0
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * (m + 1)) := min_le_right _ _
    have hfO : f ∈ zeroSpace (rbO s) := ⟨hf.1, hf.2.1, hsf⟩
    obtain ⟨g, hgG, hgclose⟩ := hGapp s f hfO δ hδ
    have hgO := hGsub s hgG
    have hgA : g ∈ A := by
      refine Or.inr (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨?_, hgG⟩⟩)
      exact (rbO_subset_rbK s).trans (hsU.trans hUH)
    rw [hF] at hgA
    obtain ⟨j, rfl⟩ := hgA
    have hgU : tsupport (F j) ⊆ U := hgO.2.2.trans ((rbO_subset_rbK s).trans hsU)
    refine ⟨j, hgU, ?_, fun z => (hgclose z).1.trans_le (hδ2.trans ?_)⟩
    · -- energy bound
      have hgH : F j ∈ zeroSpace H := ⟨hgO.1, hgO.2.1, hgU.trans hUH⟩
      have hfK : f ∈ zeroSpace (rbK s) := ⟨hf.1, hf.2.1, hsf.trans (rbO_subset_rbK s)⟩
      have hgK : F j ∈ zeroSpace (rbK s) := ⟨hgO.1, hgO.2.1, hgO.2.2.trans (rbO_subset_rbK s)⟩
      have hdK := zeroSpace_sub hfK hgK
      have hdH := zeroSpace_sub ⟨hf.1, hf.2.1, hf.2.2.trans hUH⟩ hgH
      have hEK : dirichletEnergyOn H (F j - f) = dirichletEnergyOn (rbK s) (F j - f) := by
        rw [energy_eq_of_tsupport_subset hdH.2.2, energy_eq_of_tsupport_subset hdK.2.2]
      rw [hEK]
      have hint : ‖∫ z in rbK s, ‖fderiv ℝ (F j - f) z‖ ^ 2‖ ≤ δ ^ 2 * volume.real (rbK s) := by
        refine norm_setIntegral_le_of_norm_le_const (isCompact_rbK s).measure_lt_top
          fun z _ => ?_
        rw [fderiv_sub (hgO.1.differentiable smooth_ne_zero z)
          (hf.1.differentiable smooth_ne_zero z), norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgclose z).2.le 2
      have hI : ∫ z in rbK s, ‖fderiv ℝ (F j - f) z‖ ^ 2 ≤ δ ^ 2 * m :=
        (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hint)
      have hI0 : 0 ≤ ∫ z in rbK s, ‖fderiv ℝ (F j - f) z‖ ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      have hpi : (2 * Real.pi)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
      have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.mpr (by positivity)
      unfold dirichletEnergyOn
      calc (2 * Real.pi)⁻¹ * ∫ z in rbK s, ‖fderiv ℝ (F j - f) z‖ ^ 2
          ≤ ∫ z in rbK s, ‖fderiv ℝ (F j - f) z‖ ^ 2 := by nlinarith
        _ ≤ δ ^ 2 * m := hI
        _ ≤ δ * m := by nlinarith
        _ ≤ ε / (2 * (m + 1)) * m := mul_le_mul_of_nonneg_right hδ2 hm0
        _ < ε := by nlinarith
    · exact div_le_self hε.le (by linarith)

/-- The fixed countable test family of E3. -/
def testFamily : ℕ → ℂ → ℝ := exists_testFamily.choose

lemma testFamily_mem (j : ℕ) : testFamily j ∈ zeroSpace H := exists_testFamily.choose_spec.1 j

lemma testFamily_approx {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace U) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, tsupport (testFamily j) ⊆ U ∧ dirichletEnergyOn H (testFamily j - f) < ε ∧
      ∀ z, |testFamily j z - f z| < ε :=
  exists_testFamily.choose_spec.2 U hU hUH f hf ε hε

/-- **E3.** The dual norm on `zeroSpace U` is a countable sup over the test family. -/
theorem dualNormSq_eq_iSup_testFamily {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hsupp : ∃ K, IsCompact K ∧ μ Kᶜ = 0) :
    dualNormSq U (zeroSpace U) μ =
      ⨆ j ∈ {j | tsupport (testFamily j) ⊆ U ∧ 0 < dirichletEnergyOn H (testFamily j)},
        ENNReal.ofReal ((∫ x, testFamily j x ∂μ) ^ 2 / dirichletEnergyOn H (testFamily j)) := by
  have hEUH : ∀ f : ℂ → ℝ, tsupport f ⊆ U → dirichletEnergyOn U f = dirichletEnergyOn H f :=
    fun f h => by
      rw [energy_eq_of_tsupport_subset h, energy_eq_of_tsupport_subset (h.trans hUH)]
  have hVH := isDNSpace_zeroSpace H
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    obtain ⟨hfU, hpos⟩ := hf
    have hfH : f ∈ zeroSpace H := ⟨hfU.1, hfU.2.1, hfU.2.2.trans hUH⟩
    choose J hJU hJE hJz using fun n : ℕ =>
      testFamily_approx hU hUH hfU (Nat.one_div_pos_of_nat (n := n) (α := ℝ))
    have hint : ∀ g ∈ zeroSpace H, Integrable g μ := fun g hg => integrable_of_mem hVH hsupp hg
    have hA : Tendsto (fun n => ∫ x, testFamily (J n) x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * μ.real univ) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (μ.real univ)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
      rw [← integral_sub (hint _ (testFamily_mem _)) (hint f hfH)]
      refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs]; exact (hJz n z).le
    have hE : ∀ g ∈ zeroSpace H, ‖gradFeat H g‖ ^ 2 = dirichletEnergyOn H g :=
      fun g hg => norm_gradFeat_sq (hVH.smooth g hg) (hVH.energy g hg)
    have hsub : ∀ g ∈ zeroSpace H, gradFeat H g - gradFeat H f = gradFeat H (g - f) := by
      intro g hg
      have : g - f = g + (-1 : ℝ) • f := by funext z; simp [sub_eq_add_neg]
      rw [this, gradFeat_add hVH hg (hVH.smul_mem _ f hfH), gradFeat_smul hVH _ hfH]
      simp [sub_eq_add_neg]
    have hN : Tendsto (fun n => ‖gradFeat H (testFamily (J n))‖) atTop
        (𝓝 ‖gradFeat H f‖) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun n : ℕ => √(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
      rw [Real.norm_eq_abs]
      calc |‖gradFeat H (testFamily (J n))‖ - ‖gradFeat H f‖|
          ≤ ‖gradFeat H (testFamily (J n)) - gradFeat H f‖ := abs_norm_sub_norm_le _ _
        _ = √(dirichletEnergyOn H (testFamily (J n) - f)) := by
          rw [hsub _ (testFamily_mem _), ← hE _ (zeroSpace_sub hfH (testFamily_mem _)),
            Real.sqrt_sq (norm_nonneg _)]
        _ ≤ √(1 / ((n : ℝ) + 1)) := Real.sqrt_le_sqrt (hJE n).le
    have hEn : Tendsto (fun n => dirichletEnergyOn H (testFamily (J n))) atTop
        (𝓝 (dirichletEnergyOn U f)) := by
      have h2 := hN.pow 2
      rw [hE f hfH, ← hEUH f hfU.2.2] at h2
      exact Tendsto.congr (fun n => hE _ (testFamily_mem _)) h2
    have hq := ENNReal.tendsto_ofReal ((hA.pow 2).div hEn hpos.ne')
    refine le_of_tendsto hq ?_
    filter_upwards [hEn.eventually (lt_mem_nhds hpos)] with n hn
    exact le_iSup₂ (f := fun j (_ : j ∈ {j | tsupport (testFamily j) ⊆ U ∧
        0 < dirichletEnergyOn H (testFamily j)}) =>
      ENNReal.ofReal ((∫ x, testFamily j x ∂μ) ^ 2 / dirichletEnergyOn H (testFamily j)))
      (J n) ⟨hJU n, hn⟩
  · refine iSup₂_le fun j hj => ?_
    have hmem : testFamily j ∈ zeroSpace U :=
      ⟨(testFamily_mem j).1, (testFamily_mem j).2.1, hj.1⟩
    rw [← hEUH _ hj.1]
    exact le_dualNormSq hmem (by rw [hEUH _ hj.1]; exact hj.2)

/-! ## E3: measurability -/

/-- Finite measures with compact support. -/
def IsGoodMeas (μ : Measure ℂ) : Prop := IsFiniteMeasure μ ∧ ∃ K, IsCompact K ∧ μ Kᶜ = 0

lemma IsGoodMeas.add {μ ν : Measure ℂ} (hμ : IsGoodMeas μ) (hν : IsGoodMeas ν) :
    IsGoodMeas (μ + ν) := by
  obtain ⟨hμf, K, hK, hKμ⟩ := hμ
  obtain ⟨hνf, K', hK', hKν⟩ := hν
  refine ⟨inferInstance, K ∪ K', hK.union hK', ?_⟩
  rw [Measure.add_apply, compl_union, measure_mono_null inter_subset_left hKμ,
    measure_mono_null inter_subset_right hKν, add_zero]

lemma isGoodMeas_withDensity {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    IsGoodMeas (volume.withDensity fun z => ENNReal.ofReal (g z)) := by
  refine ⟨isFiniteMeasure_withDensity_ofReal
    (hg.integrable_of_hasCompactSupport hgc).hasFiniteIntegral, tsupport g, hgc, ?_⟩
  have hs : MeasurableSet (tsupport g)ᶜ := (isClosed_tsupport g).measurableSet.compl
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 0) (fun z hz => by
    have : g z = 0 := by by_contra h; exact hz (subset_tsupport g h)
    simp [this])]
  simp

lemma isGoodMeas_testMeasPos (ρ : TestFun H) : IsGoodMeas (testMeasPos ρ.1) :=
  isGoodMeas_withDensity ρ.2.1.continuous ρ.2.2.1

lemma isGoodMeas_testMeasNeg (ρ : TestFun H) : IsGoodMeas (testMeasNeg ρ.1) :=
  isGoodMeas_withDensity (g := fun z => -ρ.1 z) ρ.2.1.continuous.neg ρ.2.2.1.neg

lemma measurable_biSup_events {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Ω → Prop)
    (hP : ∀ j, MeasurableSet {ω | P j ω}) (B : ℕ → Prop) (c : ℕ → ℝ≥0∞) :
    Measurable fun ω => ⨆ j ∈ {j | P j ω ∧ B j}, c j := by
  classical
  refine Measurable.iSup fun j => ?_
  by_cases hB : B j
  · have e : (fun ω => ⨆ (_ : j ∈ {j | P j ω ∧ B j}), c j) =
        Set.indicator {ω | P j ω} (fun _ => c j) := by
      funext ω
      by_cases hω : P j ω <;> simp [hω, hB]
    rw [e]; exact measurable_const.indicator (hP j)
  · have e : (fun ω => ⨆ (_ : j ∈ {j | P j ω ∧ B j}), c j) = fun _ => 0 := by
      funext ω; simp [hB]
    rw [e]; exact measurable_const

/-- **E3.** Measurability of the random dual norm, as an `ℝ≥0∞`-valued map. -/
theorem measurable_dualNormSq_zeroSpace {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Set ℂ}
    (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω})
    {μ : Measure ℂ} (hμ : IsGoodMeas μ) :
    Measurable fun ω => dualNormSq (U ω) (zeroSpace (U ω)) μ := by
  obtain ⟨hμf, hsupp⟩ := hμ
  have e : (fun ω => dualNormSq (U ω) (zeroSpace (U ω)) μ) = fun ω =>
      ⨆ j ∈ {j | tsupport (testFamily j) ⊆ U ω ∧ 0 < dirichletEnergyOn H (testFamily j)},
        ENNReal.ofReal ((∫ x, testFamily j x ∂μ) ^ 2 / dirichletEnergyOn H (testFamily j)) :=
    funext fun ω => dualNormSq_eq_iSup_testFamily (hU ω).1 (hU ω).2 hsupp
  rw [e]
  exact measurable_biSup_events (fun j ω => tsupport (testFamily j) ⊆ U ω) hE _ _

lemma measurable_dualCov_zeroSpace {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Set ℂ}
    (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω})
    {μ ν : Measure ℂ} (hμ : IsGoodMeas μ) (hν : IsGoodMeas ν) :
    Measurable fun ω => dualCov (U ω) (zeroSpace (U ω)) μ ν := by
  unfold dualCov
  exact (((ENNReal.measurable_toReal.comp (measurable_dualNormSq_zeroSpace hU hE (hμ.add hν))).sub
    (ENNReal.measurable_toReal.comp (measurable_dualNormSq_zeroSpace hU hE hμ))).sub
    (ENNReal.measurable_toReal.comp (measurable_dualNormSq_zeroSpace hU hE hν))).div_const 2

/-- **E3.** Measurability of the random test covariance (no finiteness of `dualCov` needed). -/
theorem measurable_zeroGFFTestCov {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Set ℂ}
    (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) (ρ σ : TestFun H) :
    Measurable fun ω => zeroGFFTestCov (U ω) ρ.1 σ.1 := by
  unfold zeroGFFTestCov
  have hp := isGoodMeas_testMeasPos ρ
  have hn := isGoodMeas_testMeasNeg ρ
  have hp' := isGoodMeas_testMeasPos σ
  have hn' := isGoodMeas_testMeasNeg σ
  exact (((measurable_dualCov_zeroSpace hU hE hp hp').sub
    (measurable_dualCov_zeroSpace hU hE hp hn')).sub
    (measurable_dualCov_zeroSpace hU hE hn hp')).add
    (measurable_dualCov_zeroSpace hU hE hn hn')

end QuantumZipper.K3
