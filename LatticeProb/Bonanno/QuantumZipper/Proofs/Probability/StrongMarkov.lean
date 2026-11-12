/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.StrongMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping

/-!
Blueprint item L9 (`blueprint/SECTION5_BLUEPRINT.md`, §4).

Setting: `B : ℝ≥0 → Ω → ℝ` pre-Brownian with continuous paths, `𝓕` a filtration to which `B`
is adapted, and such that for every deterministic `t` the restarted process
`s ↦ B (t + s) - B t` is independent of `𝓕 t` (hypothesis `hind`; it follows from the
`hpast` hypothesis of `ItoLite.dynkin_additive`, see `indep_shift_of_le_past`).
A stopping time is given as `T : Ω → ℝ≥0` with `IsStoppingTime 𝓕 (fun ω ↦ (T ω : WithTop ℝ≥0))`
(so it is finite everywhere).

Main results:
* `StrongMarkov.map_restrict_smPath_eq` : for `A ∈ 𝓕_T`, the law of the restarted path
  `smPath B T` under `P|_A` is `P A •` (law of the path of `B`).
* `StrongMarkov.setIntegral_comp_smPath` / `setIntegral_fin_smShift` : the integral form
  `E[1_A Φ(B_{T+·} - B_T)] = P(A) E[Φ(B)]`, in particular for finitely many times.
* `StrongMarkov.isBrownianReal_smShift` : the restarted process is a Brownian motion.
* `StrongMarkov.indep_smPath`, `StrongMarkov.indepFun_smPath` : it is independent of `𝓕_T`.

Proof: dyadic approximation `T_m = ⌈2^m T⌉ / 2^m` from the right, the simple Markov property
at the countably many values of `T_m`, bounded continuous test functions and path continuity
to pass to the limit, then uniqueness of finite measures and of measures on cylinders.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace QuantumZipper
namespace StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The process restarted at the random time `T`: `s ↦ B (T + s) - B T`. -/
def smShift (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ :=
  B (T ω + s) ω - B (T ω) ω

/-- The path of the restarted process. -/
def smPath (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ := fun s => smShift B T s ω

/-! ### Measurability -/

lemma measurable_randomTime_eval (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    {T : Ω → ℝ≥0} (hT : Measurable T) : Measurable (fun ω => B (T ω) ω) :=
  (measurable_uncurry_of_continuous_of_measurable hBc hBm).comp (hT.prodMk measurable_id)

lemma measurable_smShift (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    {T : Ω → ℝ≥0} (hT : Measurable T) (s : ℝ≥0) : Measurable (smShift B T s) :=
  (measurable_randomTime_eval hBc hBm (hT.add_const s)).sub
    (measurable_randomTime_eval hBc hBm hT)

lemma measurable_smPath (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    {T : Ω → ℝ≥0} (hT : Measurable T) : Measurable (smPath B T) :=
  measurable_pi_iff.mpr fun s => measurable_smShift hBc hBm hT s

lemma measurable_path (hBm : ∀ t, Measurable (B t)) : Measurable (fun ω t => B t ω) :=
  measurable_pi_iff.mpr hBm

variable {𝓕 : Filtration ℝ≥0 mΩ}

lemma measurable_of_isStoppingTime {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) : Measurable T := by
  refine measurable_of_Iic fun u => ?_
  have h : MeasurableSet {ω | (T ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} := 𝓕.le u _ (hT u)
  convert h using 1
  ext ω
  show T ω ≤ u ↔ (T ω : WithTop ℝ≥0) ≤ u
  exact WithTop.coe_le_coe.symm

/-! ### Dyadic approximation from the right -/

/-- `T_m = ⌈2^m T⌉ / 2^m`. -/
noncomputable def dyadicTime (T : Ω → ℝ≥0) (m : ℕ) (ω : Ω) : ℝ≥0 :=
  ItoLite.dyadicCeil m (T ω)

lemma isStoppingTime_dyadicTime {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) (m : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (dyadicTime T m ω : WithTop ℝ≥0)) := by
  intro u
  have : {ω | (dyadicTime T m ω : WithTop ℝ≥0) ≤ u} =
      {ω | (T ω : WithTop ℝ≥0) ≤ (((⌊u * 2 ^ m⌋₊ : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    show (dyadicTime T m ω : WithTop ℝ≥0) ≤ u ↔ (T ω : WithTop ℝ≥0) ≤ _
    rw [WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact ItoLite.dyadicCeil_le_iff m _ u
  rw [this]
  exact 𝓕.mono (ItoLite.floor_div_le m u) _ (hT _)

/-! ### The simple Markov property at a deterministic time -/

lemma setIntegral_eq_of_indep [IsProbabilityMeasure P] {m₁ m₂ : MeasurableSpace Ω}
    (hind : Indep m₁ m₂ P) (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m₁] E)
    {g : Ω → ℝ} (hg : StronglyMeasurable[m₂] g) :
    ∫ ω in E, g ω ∂P = P.real E * ∫ ω, g ω ∂P := by
  have hEm : MeasurableSet[mΩ] E := h₁ _ hE
  rw [ItoLite.setIntegral_eq_integral_indicator_one_mul (m := mΩ) (P := P) hEm]
  have hf : StronglyMeasurable[m₁] (E.indicator (1 : Ω → ℝ)) :=
    (stronglyMeasurable_const.indicator hE)
  have hfg : IndepFun (E.indicator (1 : Ω → ℝ)) g P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hf.measurable.comap_le)
      hg.measurable.comap_le
  have hmul := hfg.integral_mul_eq_mul_integral (hf.mono h₁).aestronglyMeasurable
    (hg.mono h₂).aestronglyMeasurable
  simp only [Pi.mul_apply] at hmul
  rw [hmul, integral_indicator_one hEm]

/-! ### Main argument -/

section Main

variable [IsProbabilityMeasure P] {T : Ω → ℝ≥0}

omit [IsProbabilityMeasure P] in
lemma smPath_const_eq (t : ℝ≥0) (ω : Ω) :
    smPath B (fun _ => t) ω = fun s => B (t + s) ω - B t ω := rfl

/-- The discrete step: the identity holds at the dyadic approximations `T_m`. -/
theorem setIntegral_dyadicTime (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (m : ℕ) (I : Finset ℝ≥0)
    {F : (I → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) :
    ∫ ω in A, F (I.restrict (smPath B (dyadicTime T m) ω)) ∂P =
      P.real A * ∫ x, F x ∂(BrownianReal.projectiveFamily I) := by
  set c := ∫ x, F x ∂(BrownianReal.projectiveFamily I) with hc
  have hTm := isStoppingTime_dyadicTime hT m
  have hTmm : Measurable (dyadicTime T m) := measurable_of_isStoppingTime hTm
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  set d : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) / 2 ^ m with hd
  have h2 : (2 : ℝ≥0) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have hdinj : Function.Injective d := by
    intro i j hij
    simp only [hd] at hij
    exact_mod_cast (div_left_inj' h2).mp hij
  set E : ℕ → Set Ω := fun k => A ∩ {ω | dyadicTime T m ω = d k} with hE
  have hEF : ∀ k, MeasurableSet[𝓕 (d k)] (E k) := by
    intro k
    have h1 := hA.2 (d k)
    have h3 := hTm.measurableSet_eq (d k)
    have : E k = (A ∩ {ω | (T ω : WithTop ℝ≥0) ≤ d k}) ∩
        {ω | (dyadicTime T m ω : WithTop ℝ≥0) = d k} := by
      ext ω
      simp only [hE, Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe,
        WithTop.coe_inj]
      constructor
      · rintro ⟨hω, h⟩
        exact ⟨⟨hω, h ▸ ItoLite.le_dyadicCeil m (T ω)⟩, h⟩
      · rintro ⟨⟨hω, -⟩, h⟩
        exact ⟨hω, h⟩
    rw [this]
    exact h1.inter h3
  have hEm : ∀ k, MeasurableSet (E k) := fun k => 𝓕.le _ _ (hEF k)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij (hdinj ?_)
    exact hi.2.symm.trans hj.2
  have hU : A = ⋃ k, E k := by
    ext ω
    simp only [hE, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⌈T ω * 2 ^ m⌉₊, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  set f : Ω → ℝ := fun ω => F (I.restrict (smPath B (dyadicTime T m) ω)) with hf
  have hfm : StronglyMeasurable f :=
    ((hF.comp (Finset.measurable_restrict I)).comp
      (measurable_smPath hBc hBm hTmm)).stronglyMeasurable
  have hfi : IntegrableOn f (⋃ k, E k) P :=
    ItoLite.integrable_of_bound_abs hfm (fun ω => hFC _)
  have hci : IntegrableOn (fun _ : Ω => c) (⋃ k, E k) P := integrable_const c
  have hstep : ∀ k, ∫ ω in E k, f ω ∂P = ∫ ω in E k, c ∂P := by
    intro k
    have hcongr : ∫ ω in E k, f ω ∂P =
        ∫ ω in E k, F (I.restrict (smPath B (fun _ => d k) ω)) ∂P := by
      refine setIntegral_congr_fun (hEm k) fun ω hω => ?_
      simp only [hf]
      have : smPath B (dyadicTime T m) ω = smPath B (fun _ => d k) ω := by
        have h' : dyadicTime T m ω = d k := hω.2
        funext s; simp only [smPath, smShift, h']
      rw [this]
    have hgm : StronglyMeasurable[MeasurableSpace.comap (smPath B (fun _ => d k))
        MeasurableSpace.pi] (fun ω => F (I.restrict (smPath B (fun _ => d k) ω))) :=
      ((hF.comp (Finset.measurable_restrict I)).comp
        (comap_measurable (smPath B (fun _ => d k)))).stronglyMeasurable
    have hle : MeasurableSpace.comap (smPath B (fun _ => d k)) MeasurableSpace.pi ≤ mΩ :=
      (measurable_smPath hBc hBm measurable_const).comap_le
    rw [hcongr, setIntegral_eq_of_indep (hind (d k)) (𝓕.le _) hle (hEF k) hgm,
      setIntegral_const, smul_eq_mul]
    congr 1
    have hlaw := (hB.shift (d k)).hasLaw I
    have := hlaw.integral_comp (f := F) hF.aestronglyMeasurable
    simpa [Function.comp_def, smPath_const_eq] using this
  calc ∫ ω in A, f ω ∂P = ∫ ω in ⋃ k, E k, f ω ∂P := by rw [← hU]
    _ = ∑' k, ∫ ω in E k, f ω ∂P := integral_iUnion hEm hdisj hfi
    _ = ∑' k, ∫ ω in E k, c ∂P := by simp_rw [hstep]
    _ = ∫ ω in ⋃ k, E k, c ∂P := (integral_iUnion hEm hdisj hci).symm
    _ = P.real A * c := by rw [← hU, setIntegral_const, smul_eq_mul]

/-- The limit step: the identity at `T` for bounded continuous test functions. -/
theorem setIntegral_bcf (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (I : Finset ℝ≥0) (F : (I → ℝ) →ᵇ ℝ) :
    ∫ ω in A, F (I.restrict (smPath B T ω)) ∂P =
      P.real A * ∫ x, F x ∂(BrownianReal.projectiveFamily I) := by
  have hFC : ∀ x, |F x| ≤ ‖F‖ := fun x => by
    rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm x
  have hlim : Tendsto (fun m => ∫ ω in A, F (I.restrict (smPath B (dyadicTime T m) ω)) ∂P)
      atTop (𝓝 (∫ ω in A, F (I.restrict (smPath B T ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun m => ?_)
      (integrable_const _) (fun m => ae_of_all _ fun ω => F.norm_coe_le_norm _)
      (ae_of_all _ fun ω => ?_)
    · exact ((F.continuous.measurable.comp (Finset.measurable_restrict I)).comp
        (measurable_smPath hBc hBm (measurable_of_isStoppingTime
          (isStoppingTime_dyadicTime hT m)))).aestronglyMeasurable
    · refine (F.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      have hTm : Tendsto (fun m => dyadicTime T m ω) atTop (𝓝 (T ω)) :=
        ItoLite.tendsto_dyadicCeil (T ω)
      exact (((hBc ω).tendsto _).comp (hTm.add_const _)).sub (((hBc ω).tendsto _).comp hTm)
  have hconst : (fun m => ∫ ω in A, F (I.restrict (smPath B (dyadicTime T m) ω)) ∂P) =
      fun _ => P.real A * ∫ x, F x ∂(BrownianReal.projectiveFamily I) := by
    funext m
    exact setIntegral_dyadicTime hB hBc hBm hind hT hA m I F.continuous.measurable hFC
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Finite-dimensional form: the law of `(B_{T+s} - B_T)_{s ∈ I}` under `P|_A` is
`P A • projectiveFamily I`. -/
theorem map_restrict_finite_eq (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => I.restrict (smPath B T ω)) =
      P A • BrownianReal.projectiveFamily I := by
  have hgm : Measurable (fun ω => I.restrict (smPath B T ω)) :=
    (Finset.measurable_restrict I).comp
      (measurable_smPath hBc hBm (measurable_of_isStoppingTime hT))
  have : IsFiniteMeasure (BrownianReal.projectiveFamily I) := by
    rw [← (hB.hasLaw I).map_eq]; infer_instance
  have : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun F => ?_
  rw [integral_map hgm.aemeasurable F.continuous.aestronglyMeasurable, integral_smul_measure,
    setIntegral_bcf hB hBc hBm hind hT hA I F, smul_eq_mul, measureReal_def]

/-- **Strong Markov property**, law form: for `A ∈ 𝓕_T`, the law of the restarted path under
`P|_A` is `P A` times the law of the path of `B`. -/
theorem map_restrict_smPath_eq (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) :
    (P.restrict A).map (smPath B T) = P A • P.map (fun ω t => B t ω) := by
  have hsm := measurable_smPath hBc hBm (measurable_of_isStoppingTime hT)
  have hpm := measurable_path hBm
  refine ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
  · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
    have hsM := MeasurableSet.cylinder (α := fun _ : ℝ≥0 => ℝ) I hS
    have h1 := congrArg (fun μ : Measure (I → ℝ) => μ S)
      (map_restrict_finite_eq hB hBc hBm hind hT hA I)
    rw [Measure.map_apply (show Measurable (fun ω => I.restrict (smPath B T ω)) from
      (Finset.measurable_restrict I).comp hsm) hS, Measure.smul_apply,
      smul_eq_mul] at h1
    have hIm : Measurable (fun ω => I.restrict (fun t => B t ω)) :=
      (Finset.measurable_restrict I).comp hpm
    have h2 : P ((fun ω t => B t ω) ⁻¹' cylinder I S) = BrownianReal.projectiveFamily I S := by
      rw [← (hB.hasLaw I).map_eq, Measure.map_apply hIm hS]; rfl
    rw [Measure.map_apply hsm hsM, Measure.smul_apply, Measure.map_apply hpm hsM, smul_eq_mul,
      h2]
    exact h1
  · rw [Measure.map_apply hsm MeasurableSet.univ, Measure.smul_apply,
      Measure.map_apply hpm MeasurableSet.univ]
    simp

/-- The restarted process is a Brownian motion (L9 goal (2), first half). -/
theorem isBrownianReal_smShift (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (smShift B T) P where
  toIsPreBrownianReal := IsPreBrownianReal.mk' fun I =>
    { aemeasurable := ((Finset.measurable_restrict I).comp
        (measurable_smPath hBc hBm (measurable_of_isStoppingTime hT))).aemeasurable
      map_eq := by
        have := map_restrict_finite_eq hB hBc hBm hind hT
          (@MeasurableSet.univ Ω hT.measurableSpace) I
        rwa [Measure.restrict_univ, measure_univ, one_smul] at this }
  cont := ae_of_all _ fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const

/-- The restarted path is independent of `𝓕_T` (L9 goal (2), second half). -/
theorem indep_smPath (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) :
    Indep hT.measurableSpace (MeasurableSpace.comap (smPath B T) MeasurableSpace.pi) P := by
  have hsm := measurable_smPath hBc hBm (measurable_of_isStoppingTime hT)
  rw [Indep_iff]
  rintro t1 t2 ht1 ⟨c, hc, rfl⟩
  have h1 := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ c)
    (map_restrict_smPath_eq hB hBc hBm hind hT ht1)
  have h2 := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ c)
    (map_restrict_smPath_eq hB hBc hBm hind hT (@MeasurableSet.univ Ω hT.measurableSpace))
  simp only [Measure.map_apply hsm hc, Measure.smul_apply, smul_eq_mul, Measure.restrict_univ,
    measure_univ, one_mul] at h1 h2
  rw [Measure.restrict_apply (hsm hc)] at h1
  rw [Set.inter_comm, h1, h2]

/-- `IndepFun` form: every `𝓕_T`-measurable random variable is independent of the restarted
path. -/
theorem indepFun_smPath (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) {β : Type*} [MeasurableSpace β]
    {ξ : Ω → β} (hξ : Measurable[hT.measurableSpace] ξ) :
    IndepFun ξ (smPath B T) P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (indep_smPath hB hBc hBm hind hT) hξ.comap_le

end Main

/-! ### The `hpast` interface of `ItoLite.dynkin_additive` -/

/-- If `𝓕 t` is contained in the past of `B`, the simple Markov property gives `hind`. -/
theorem indep_shift_of_le_past (hB : IsPreBrownianReal B P)
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω)
      MeasurableSpace.pi) (t : ℝ≥0) :
    Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t)) MeasurableSpace.pi) P := by
  have h := hB.indepFun_shift t
  rw [IndepFun_iff_Indep] at h
  exact indep_of_indep_of_le_left h.symm (hpast t)

/-! ### The shifted filtration -/

end StrongMarkov
end QuantumZipper
