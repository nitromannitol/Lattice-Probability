/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.CircleLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.Plane
import LatticeProb.Bonanno.HigherDimLFPP.Field.LawTransfer
import LatticeProb.Bonanno.HigherDimLFPP.Field.FiniteRange
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Measurable

/-!
# Law transfer for circle-average processes (packet P-X10, target T5)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2, Lemma A.1, last sentence
("Consequently these regularizations have the same fixed-parameter LFPP exponent"); planning audit
HA5, finding A2-2 and Details D12, Claim 5 (`CircleLawTransfer`); ruling H12.

`LQGDimension.IsGFFCircleAverage h P` fixes the finite-dimensional laws of `h` (centered Gaussian,
covariance `gffCircleCov`) and continuity in `z`, but not the probability space, and its values
are only a.e.-measurable.  We show that the law of `D^ξ_ε = LQGDimension.lfppDistance ξ (h ε ·)`
is the same for every such process:

* `TwoD.exists_measurable_modification`: a process with continuous paths on a separable Fréchet–Urysohn
  space and a.e.-measurable values has a modification with continuous paths and measurable values
  that agrees with it, almost surely, at every point simultaneously (one dense sequence and one
  null set);
* `map_modification_eq_of_isGFFCircleAverage`: these modifications (on `ℝ²`, through `cToR2`) have
  the same law on `ℝ² → ℝ` for any two circle-average processes (Gaussian finite-dimensional laws
  with the same covariance, `QuantumZipper.WedgeRes.map_eq_of_gaussian_vec`, and
  `LQGMetric.WhiteNoise.map_eq_of_forall_finset'`), hence on `C(ℝ², ℝ)`
  (`map_contField_eq_of_map_eq`, P-X2);
* `map_lfppDistance_eq_of_isGFFCircleAverage`: `D^ξ_ε` is a.e.-measurable and its law does not
  depend on the process (`lqg_lfppDistance_eq` and the Borel measurability of the frozen distance on
  `C(ℝ², ℝ)`, P-X1); `circleLawTransfer` is HA5's statement (distribution functions);
* `isLFPPExponent_iff_of_isGFFCircleAverage`: `LQGDimension.IsLFPPExponent h P ξ λ` depends only on
  the law (convergence in probability of `log D^ξ_ε / log ε` is a statement about the laws of the
  `D^ξ_ε`, ε > 0).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-! ### Measurable modifications -/

namespace TwoD

/-- **Measurable modifications of continuous processes**: if `t ↦ X t ω` is continuous for every
`ω` (on a separable Fréchet–Urysohn space `T`) and every `X t` is a.e.-measurable, there is `Y`
with continuous paths and measurable values such that a.s. `Y t = X t` for all `t`. -/
theorem exists_measurable_modification {T Ω : Type*} [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T] [FrechetUrysohnSpace T] [Nonempty T] [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ} (hc : ∀ ω, Continuous fun t => X t ω)
    (hm : ∀ t, AEMeasurable (X t) P) :
    ∃ Y : T → Ω → ℝ, (∀ ω, Continuous fun t => Y t ω) ∧ (∀ t, Measurable (Y t)) ∧
      ∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq T
  set m : ℕ → Ω → ℝ := fun k => (hm (u k)).mk (X (u k)) with hmdef
  have hmm : ∀ k, Measurable (m k) := fun k => (hm (u k)).measurable_mk
  have hmae : ∀ k, X (u k) =ᵐ[P] m k := fun k => (hm (u k)).ae_eq_mk
  set N : Set Ω := ⋃ k, {ω | X (u k) ω ≠ m k ω} with hN
  have hN0 : P N = 0 := measure_iUnion_null fun k => ae_iff.1 (hmae k)
  set N' : Set Ω := toMeasurable P N with hN'
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable P N
  have hN'0 : P N' = 0 := by rw [hN', measure_toMeasurable]; exact hN0
  have hNN' : N ⊆ N' := subset_toMeasurable P N
  refine ⟨fun t ω => N'ᶜ.indicator (fun ω => X t ω) ω, fun ω => ?_, fun t => ?_, ?_⟩
  · by_cases hω : ω ∈ N'
    · have : ω ∉ N'ᶜ := fun h => h hω
      simp only [indicator_of_notMem this]
      exact continuous_const
    · have : ω ∈ N'ᶜ := hω
      simp only [indicator_of_mem this]
      exact hc ω
  · have ht : t ∈ closure (range u) := by rw [hu.closure_range]; exact mem_univ t
    obtain ⟨x, hxu, hxt⟩ := mem_closure_iff_seq_limit.1 ht
    choose k hk using hxu
    refine measurable_of_tendsto_metrizable (f := fun n => N'ᶜ.indicator (m (k n)))
      (fun n => (hmm (k n)).indicator hN'm.compl) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ N'
    · have : ω ∉ N'ᶜ := fun h => h hω
      simp only [indicator_of_notMem this]
      exact tendsto_const_nhds
    · have hω' : ω ∈ N'ᶜ := hω
      have hagree : ∀ j, X (u j) ω = m j ω := by
        intro j
        by_contra hne
        exact hω (hNN' (mem_iUnion.2 ⟨j, hne⟩))
      simp only [indicator_of_mem hω']
      have hlim : Tendsto (fun n => X (x n) ω) atTop (𝓝 (X t ω)) :=
        ((hc ω).tendsto t).comp hxt
      refine hlim.congr fun n => ?_
      rw [← hk n, hagree]
  · filter_upwards [compl_mem_ae_iff.2 hN'0] with ω hω t
    simp only [indicator_of_mem hω]

end TwoD

open TwoD

/-! ### The law of the circle-average field -/

section Law

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {h : ℝ → ℂ → Ω → ℝ} {h' : ℝ → ℂ → Ω' → ℝ}

/-- A measurable modification of `x ↦ h_ε(cToR2⁻¹ x)` on `ℝ²`. -/
theorem exists_modification_of_isGFFCircleAverage (hG : LQGDimension.IsGFFCircleAverage h P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : Rd 2 → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ᵐ ω ∂P, ∀ x, Y x ω = h ε (cToR2.symm x) ω :=
  exists_measurable_modification
    (fun ω => (hG.continuous ε hε ω).comp cToR2.symm.continuous)
    fun x => hG.isGaussianProcess.aemeasurable ((⟨ε, hε⟩ : Ioi (0 : ℝ)), cToR2.symm x)

/-- Modifications of the circle-average field are Gaussian processes. -/
theorem isGaussianProcess_of_circleModification (hG : LQGDimension.IsGFFCircleAverage h P) {ε : ℝ}
    (hε : 0 < ε) {Y : Rd 2 → Ω → ℝ} (hY : ∀ᵐ ω ∂P, ∀ x, Y x ω = h ε (cToR2.symm x) ω) :
    IsGaussianProcess Y P :=
  (hG.isGaussianProcess.comp_right
    fun x : Rd 2 => ((⟨ε, hε⟩ : Ioi (0 : ℝ)), cToR2.symm x)).congr fun x => by
      filter_upwards [hY] with ω hω
      exact (hω x).symm

/-- **The law of the circle-average field does not depend on the process**: measurable
modifications of `x ↦ h_ε(cToR2⁻¹ x)` and `x ↦ h'_ε(cToR2⁻¹ x)` have the same law on
`ℝ² → ℝ` (product σ-algebra). -/
theorem map_modification_eq_of_isGFFCircleAverage (hG : LQGDimension.IsGFFCircleAverage h P)
    (hG' : LQGDimension.IsGFFCircleAverage h' P') {ε : ℝ} (hε : 0 < ε) {Y : Rd 2 → Ω → ℝ}
    {Y' : Rd 2 → Ω' → ℝ} (hYm : ∀ x, Measurable (Y x))
    (hY : ∀ᵐ ω ∂P, ∀ x, Y x ω = h ε (cToR2.symm x) ω) (hY'm : ∀ x, Measurable (Y' x))
    (hY' : ∀ᵐ ω ∂P', ∀ x, Y' x ω = h' ε (cToR2.symm x) ω) :
    P.map (fun ω x => Y x ω) = P'.map (fun ω x => Y' x ω) := by
  have := hG.isProbabilityMeasure
  have := hG'.isProbabilityMeasure
  have hYg := isGaussianProcess_of_circleModification hG hε hY
  have hY'g := isGaussianProcess_of_circleModification hG' hε hY'
  have hYae : ∀ x, Y x =ᵐ[P] h ε (cToR2.symm x) := fun x => by
    filter_upwards [hY] with ω hω using hω x
  have hY'ae : ∀ x, Y' x =ᵐ[P'] h' ε (cToR2.symm x) := fun x => by
    filter_upwards [hY'] with ω hω using hω x
  refine LQGMetric.WhiteNoise.map_eq_of_forall_finset' (measurable_pi_iff.2 hYm).aemeasurable
    (measurable_pi_iff.2 hY'm).aemeasurable fun I => ?_
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I) (U := fun i => Y i)
    (V := fun i => Y' i) (hYg.hasGaussianLaw I) (hY'g.hasGaussianLaw I) (fun i => hYm i)
    (fun i => hY'm i) (fun i => (hYg.hasGaussianLaw_eval i).memLp_two)
    (fun i => (hY'g.hasGaussianLaw_eval i).memLp_two)
    (fun i => by rw [integral_congr_ae (hYae i), hG.integral_eq_zero ε hε])
    (fun i => by rw [integral_congr_ae (hY'ae i), hG'.integral_eq_zero ε hε])
    fun i j => by
      rw [covariance_congr_ae (hYae i) (hYae j), covariance_congr_ae (hY'ae i) (hY'ae j),
        hG.covariance_eq ε hε ε hε, hG'.covariance_eq ε hε ε hε]

/-- The frozen LFPP distance is Borel measurable on `C(ℝ², ℝ)`. -/
theorem TwoD.measurable_lfppDistance_two_continuousMap (ξ : ℝ) :
    Measurable fun f : C(Rd 2, ℝ) => lfppDistance 2 ξ f :=
  measurable_lfppDistance (H := fun z (f : C(Rd 2, ℝ)) => f z) (fun f => f.continuous)
    (fun z => (continuous_eval_const z).measurable) ξ

/-- **HA5 D12, Claim 5** (target T5, law form): for two circle-average processes and `ε > 0`,
`D^ξ_ε = LQGDimension.lfppDistance ξ (h ε ·)` is a.e.-measurable and has the same law for both. -/
theorem map_lfppDistance_eq_of_isGFFCircleAverage (hG : LQGDimension.IsGFFCircleAverage h P)
    (hG' : LQGDimension.IsGFFCircleAverage h' P') (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (fun ω => LQGDimension.lfppDistance ξ fun z => h ε z ω) P ∧
      AEMeasurable (fun ω => LQGDimension.lfppDistance ξ fun z => h' ε z ω) P' ∧
      P.map (fun ω => LQGDimension.lfppDistance ξ fun z => h ε z ω) =
        P'.map (fun ω => LQGDimension.lfppDistance ξ fun z => h' ε z ω) := by
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_modification_of_isGFFCircleAverage hG hε
  obtain ⟨Y', hY'c, hY'm, hY'⟩ := exists_modification_of_isGFFCircleAverage hG' hε
  have hD : (fun ω => LQGDimension.lfppDistance ξ fun z => h ε z ω) =ᵐ[P]
      fun ω => lfppDistance 2 ξ fun x => Y x ω := by
    filter_upwards [hY] with ω hω
    rw [lqg_lfppDistance_eq]
    congr 1
    funext x
    exact (hω x).symm
  have hD' : (fun ω => LQGDimension.lfppDistance ξ fun z => h' ε z ω) =ᵐ[P']
      fun ω => lfppDistance 2 ξ fun x => Y' x ω := by
    filter_upwards [hY'] with ω hω
    rw [lqg_lfppDistance_eq]
    congr 1
    funext x
    exact (hω x).symm
  have hDm : Measurable fun ω => lfppDistance 2 ξ fun x => Y x ω :=
    measurable_lfppDistance hYc hYm ξ
  have hD'm : Measurable fun ω => lfppDistance 2 ξ fun x => Y' x ω :=
    measurable_lfppDistance hY'c hY'm ξ
  refine ⟨hDm.aemeasurable.congr hD.symm, hD'm.aemeasurable.congr hD'.symm, ?_⟩
  rw [Measure.map_congr hD, Measure.map_congr hD']
  have hlaw := map_contField_eq_of_map_eq hYc hYm hY'c hY'm
    (map_modification_eq_of_isGFFCircleAverage hG hG' hε hYm hY hY'm hY')
  have e1 : (fun ω => lfppDistance 2 ξ fun x => Y x ω) =
      (fun f : C(Rd 2, ℝ) => lfppDistance 2 ξ f) ∘ contField Y hYc := rfl
  have e2 : (fun ω => lfppDistance 2 ξ fun x => Y' x ω) =
      (fun f : C(Rd 2, ℝ) => lfppDistance 2 ξ f) ∘ contField Y' hY'c := rfl
  rw [e1, e2, ← Measure.map_map (TwoD.measurable_lfppDistance_two_continuousMap ξ)
    (measurable_contField hYc hYm),
    ← Measure.map_map (TwoD.measurable_lfppDistance_two_continuousMap ξ)
    (measurable_contField hY'c hY'm), hlaw]

/-- Probabilities of Borel events of `D^ξ_ε` agree for any two circle-average processes. -/
theorem measure_lfppDistance_mem_eq (hG : LQGDimension.IsGFFCircleAverage h P)
    (hG' : LQGDimension.IsGFFCircleAverage h' P') (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) {S : Set ℝ}
    (hS : MeasurableSet S) :
    P {ω | (LQGDimension.lfppDistance ξ fun z => h ε z ω) ∈ S} =
      P' {ω | (LQGDimension.lfppDistance ξ fun z => h' ε z ω) ∈ S} := by
  obtain ⟨hm, hm', hmap⟩ := map_lfppDistance_eq_of_isGFFCircleAverage hG hG' ξ hε
  have h1 := Measure.map_apply_of_aemeasurable hm hS
  have h2 := Measure.map_apply_of_aemeasurable hm' hS
  rw [hmap] at h1
  exact h1.symm.trans h2

/-- **The LFPP exponent depends only on the law** (target T5): for two circle-average processes
of the normalized whole-plane GFF (on any probability spaces), `λ` is an LFPP exponent at `ξ`
for one iff it is for the other. -/
theorem isLFPPExponent_iff_of_isGFFCircleAverage (hG : LQGDimension.IsGFFCircleAverage h P)
    (hG' : LQGDimension.IsGFFCircleAverage h' P') (ξ lam : ℝ) :
    LQGDimension.IsLFPPExponent h P ξ lam ↔ LQGDimension.IsLFPPExponent h' P' ξ lam := by
  unfold LQGDimension.IsLFPPExponent
  rw [tendstoInMeasure_iff_dist, tendstoInMeasure_iff_dist]
  have key : ∀ δ : ℝ, ∀ ε > (0 : ℝ),
      P {ω | δ ≤ dist (Real.log (LQGDimension.lfppDistance ξ fun z => h ε z ω) / Real.log ε) lam} =
        P' {ω | δ ≤
          dist (Real.log (LQGDimension.lfppDistance ξ fun z => h' ε z ω) / Real.log ε) lam} :=
    fun δ ε hε => measure_lfppDistance_mem_eq hG hG' ξ hε
      (S := {x : ℝ | δ ≤ dist (Real.log x / Real.log ε) lam})
      (measurableSet_le measurable_const
        ((Real.measurable_log.div_const _).dist measurable_const))
  constructor
  · intro H δ hδ
    refine (H δ hδ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact key δ ε hε
  · intro H δ hδ
    refine (H δ hδ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (key δ ε hε).symm

end Law

end HigherDimLFPP
