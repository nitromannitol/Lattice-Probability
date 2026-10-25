import LatticeProb.Prob.Cadlag.HalfLine.FiniteStopping
import LatticeProb.Prob.Cadlag.HalfLine.AldousHalfLine
import LatticeProb.External.BillingsleySkorokhod
import LatticeProb.Prob.Cadlag.HalfLine.RestrictionAsymptotic

/-!
# Finite-horizon stopping-increment tightness

Constant extension transports the raw finite stopping-increment condition to the half-line.
Asymptotic deterministic increment estimates control the terminal averaging rectangle, so
restriction recovers tightness of the full sequence of finite path laws.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal

noncomputable section

variable {E Ω : Type} [NormedAddCommGroup E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

/-- A tail bound for a bounded distance gives a real expectation bound, with no
integrability premise because the integrand is bounded by one. -/
theorem integral_boundedDistance_le_of_tail (P : ProbabilityMeasure Ω)
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g)
    {η b : ℝ} (hη : 0 ≤ η) (hb : 0 ≤ b)
    (htail : (P : Measure Ω) {w | η ≤ dist (f w) (g w)} ≤ ENNReal.ofReal b) :
    ∫ w, boundedDistance (f w) (g w) ∂P ≤ η + b := by
  let A := {w | η ≤ dist (f w) (g w)}
  have hA : MeasurableSet A := measurableSet_le measurable_const (hf.dist hg)
  have hF : Integrable (fun w => boundedDistance (f w) (g w)) (P : Measure Ω) :=
    Integrable.of_bound (continuous_boundedDistance.measurable.comp
      (hf.prodMk hg)).aestronglyMeasurable 1
      (ae_of_all _ fun w => norm_boundedDistance_le_one _ _)
  calc
    _ ≤ ∫ w, η + A.indicator (fun _ => (1 : ℝ)) w ∂P := by
      apply integral_mono hF ((integrable_const η).add
        ((integrable_const (1 : ℝ)).indicator hA))
      intro w
      dsimp only [Pi.add_apply]
      by_cases hw : w ∈ A
      · rw [Set.indicator_of_mem hw]
        exact (min_le_right _ _).trans (by linarith)
      · rw [Set.indicator_of_notMem hw, add_zero]
        exact (min_le_left _ _).trans (le_of_not_ge hw)
    _ = η + ((P : Measure Ω) A).toReal := by
      rw [integral_add (integrable_const η) ((integrable_const (1 : ℝ)).indicator hA),
        integral_const, integral_indicator hA, integral_const]
      simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
        measure_univ, ENNReal.toReal_one, one_mul, mul_one]
    _ ≤ η + b := by
      apply add_le_add_right
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail).trans_eq
        (ENNReal.toReal_ofReal hb)

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The extension is constant across the right averaging window. The left evaluation is
an original finite evaluation whenever the averaging width is below the horizon. -/
theorem constantExtension_cross_terminal {T : ℝ} (hT : 0 < T)
    {h s t : ℝ} (hhT : h < T) (hs : T - h < s) (hsT : s ≤ T) (ht : T < t)
    (x : Cadlag.D T E) :
    boundedDistance ((constantExtension hT x).1 s.toNNReal)
      ((constantExtension hT x).1 t.toNNReal) =
      boundedDistance (x.1 ⟨s, by linarith, hsT⟩) (x.1 ⟨T, hT.le, le_rfl⟩) := by
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := hT.le.trans ht.le
  rw [constantExtension_apply_of_le hT x (t := t.toNNReal) (by
    simpa only [Real.coe_toNNReal _ ht0] using ht.le)]
  apply congrArg (fun a => boundedDistance a (x.1 ⟨T, hT.le, le_rfl⟩))
  apply congrArg x.1
  exact Subtype.ext (by simp only [clampTime, Real.coe_toNNReal _ hs0, min_eq_left hsT])

/-- A uniform deterministic finite-increment tail estimate controls the full terminal
averaging rectangle of the constant-extension law. -/
theorem integral_averagedIncrement_constantExtension_le {T : ℝ} (hT : 0 < T)
    (P : ProbabilityMeasure (Cadlag.D T E)) {η b δ h : ℝ}
    (hη : 0 ≤ η) (hb : 0 ≤ b) (hh : 0 < h) (hhT : h < T) (hhδ : h ≤ δ)
    (htail : ∀ c : Icc (0 : ℝ) T, ∀ u : Time, (u : ℝ) ≤ δ →
      (P : Measure (Cadlag.D T E))
        {x | η ≤ dist (x.1 ⟨min ((c : ℝ) + u) T,
          le_min (add_nonneg c.2.1 u.2) hT.le, min_le_right _ _⟩) (x.1 c)} ≤
            ENNReal.ofReal b) :
    ∫ x, averagedIncrement ⟨T, hT.le⟩ h x
      ∂((P.map (measurable_constantExtension hT).aemeasurable :
        ProbabilityMeasure (D E)) : Measure (D E)) ≤ η + b := by
  apply integral_averagedIncrement_le _ ⟨T, hT.le⟩ hh
  intro s t hs hsT ht _
  change T - h < s at hs
  change s ≤ T at hsT
  change T < t at ht
  have hs0 : 0 ≤ s := by linarith
  let c : Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
  let u : Time := ⟨T - s, sub_nonneg.mpr hsT⟩
  have huδ : (u : ℝ) ≤ δ := (by change T - s ≤ h; linarith : (u : ℝ) ≤ h).trans hhδ
  have htime : (⟨min ((c : ℝ) + u) T,
      le_min (add_nonneg c.2.1 u.2) hT.le, min_le_right _ _⟩ : Icc (0 : ℝ) T) =
        ⟨T, hT.le, le_rfl⟩ := by
    apply Subtype.ext
    change min (s + (T - s)) T = T
    rw [show s + (T - s) = T by ring, min_self]
  have htail' := htail c u huδ
  rw [htime] at htail'
  simp_rw [dist_comm] at htail'
  have heval : Measurable (fun x : D E =>
      boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) :=
    continuous_boundedDistance.measurable.comp
      ((measurable_eval s.toNNReal).prodMk (measurable_eval t.toNNReal))
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_constantExtension hT).aemeasurable
      heval.aestronglyMeasurable]
  simp_rw [constantExtension_cross_terminal hT hhT hs hsT ht]
  exact integral_boundedDistance_le_of_tail P _ _
    (Cadlag.measurable_eval c) (Cadlag.measurable_eval ⟨T, hT.le, le_rfl⟩)
    hη hb htail'

omit [MeasurableSpace E] [BorelSpace E] in
/-- Restricting the extension law recovers each original probability law, including
any exceptional early law with a terminal jump. -/
theorem map_restrict_map_constantExtension {T : ℝ} (hT : 0 < T)
    (P : ProbabilityMeasure (Cadlag.D T E)) :
    (P.map (measurable_constantExtension hT).aemeasurable).map
      (measurable_restrict T).aemeasurable = P := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_restrict T) (measurable_constantExtension hT)]
  have hcomp : restrict T ∘ constantExtension (E := E) hT = id := by
    funext x
    exact restrict_constantExtension hT x
  rw [hcomp, Measure.map_id]

omit [SeparableSpace E] in
/-- Every marginal of the constant extension is an original marginal at a clamped time.
Tightness therefore supplies the rational-time compact sets for the half-line criterion. -/
theorem marginal_compactSets_constantExtension {T : ℝ} (hT : 0 < T)
    (P : ℕ → ProbabilityMeasure (Cadlag.D T E))
    (hmarginal : ∀ t : Icc (0 : ℝ) T,
      IsTightMeasureSet (range (fun n =>
        (((P n).map (Cadlag.measurable_eval t).aemeasurable) : Measure E)))) :
    ∀ η : ℝ, 0 < η → ∀ t : ℚ, 0 ≤ t →
      ∃ K : Set E, IsCompact K ∧ ∀ n,
        ENNReal.ofReal (1 - η) ≤ (P n : Measure (Cadlag.D T E))
          {x | (constantExtension hT x).1 (t : ℝ).toNNReal ∈ K} := by
  intro η hη t _
  let c := clampTime hT.le (t : ℝ).toNNReal
  obtain ⟨K, hK, hbound⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hmarginal c)
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  refine ⟨K, hK, fun n => ?_⟩
  let ν := (P n).map (Cadlag.measurable_eval c).aemeasurable
  have hcompl : (ν : Measure E) Kᶜ ≤ ENNReal.ofReal η := hbound _ ⟨n, rfl⟩
  have hlower : ENNReal.ofReal (1 - η) ≤ (ν : Measure E) K := by
    rw [ENNReal.ofReal_sub 1 hη.le, ENNReal.ofReal_one]
    apply tsub_le_iff_right.mpr
    calc
      1 = (ν : Measure E) K + (ν : Measure E) Kᶜ :=
        (prob_add_prob_compl hK.measurableSet).symm
      _ ≤ (ν : Measure E) K + ENNReal.ofReal η := add_le_add_right hcompl _
  change ENNReal.ofReal (1 - η) ≤
    (P n : Measure (Cadlag.D T E)) ((fun x => x.1 c) ⁻¹' K)
  simpa only [ν, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (Cadlag.measurable_eval c) hK.measurableSet] using hlower

omit [SeparableSpace E] in
/-- The finite full-sequence stopping hypothesis gives the half-line hypothesis for
constant extensions, by clipping every raw-natural stopping time. -/
theorem stoppingIncrementCondition_constantExtension {T : ℝ} (hT : 0 < T)
    (P : ℕ → ProbabilityMeasure (Cadlag.D T E))
    (h : ∀ η : ℝ, 0 < η → ∀ τ : ℕ → Cadlag.D T E → Icc (0 : ℝ) T,
      (∀ n, finiteIsStopping (τ n)) →
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
          (P n : Measure (Cadlag.D T E))
            {x | η ≤ dist (x.1 (clipFiniteTime (τ n x) u)) (x.1 (τ n x))}) atTop)
        (𝓝[>] 0) (𝓝 0)) :
    stoppingIncrementCondition P (fun _ => constantExtension hT) := by
  borelize E
  intro H hH η hη τ hτ
  have hf (n : ℕ) := finiteIsStopping_clampTime hT (τ n) (hτ n).2.2
  simpa only [constantExtension_apply_add, constantExtension_apply, clampTime_add] using
    h η hη (fun n x => clampTime hT.le (τ n x)) hf

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Full-sequence finite stopping control supplies one positive window and a tail index
uniformly over all finite stopping times and deterministic increments. -/
theorem exists_pos_eventually_finite_increment_bound {T : ℝ} (hT : 0 < T)
    (P : ℕ → ProbabilityMeasure (Cadlag.D T E))
    (h : ∀ η : ℝ, 0 < η → ∀ τ : ℕ → Cadlag.D T E → Icc (0 : ℝ) T,
      (∀ n, finiteIsStopping (τ n)) →
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
          (P n : Measure (Cadlag.D T E))
            {x | η ≤ dist (x.1 (clipFiniteTime (τ n x) u)) (x.1 (τ n x))}) atTop)
        (𝓝[>] 0) (𝓝 0))
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Cadlag.D T E → Icc (0 : ℝ) T, finiteIsStopping τ →
        ∀ u : Time, (u : ℝ) ≤ δ →
          (P n : Measure (Cadlag.D T E))
            {x | η ≤ dist (x.1 (clipFiniteTime (τ x) u)) (x.1 (τ x))} ≤ ε := by
  let S (_n : ℕ) := {τ : Cadlag.D T E → Icc (0 : ℝ) T // finiteIsStopping τ}
  have hnonempty : ∀ n, Nonempty (S n) :=
    fun _ => ⟨⟨fun _ => ⟨0, le_rfl, hT.le⟩, finiteIsStopping_zero hT⟩⟩
  let p (δ : ℝ) (n : ℕ) (τ : S n) : ℝ≥0∞ :=
    ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
      (P n : Measure (Cadlag.D T E))
        {x | η ≤ dist (x.1 (clipFiniteTime (τ.1 x) u)) (x.1 (τ.1 x))}
  obtain ⟨δ, hδ, N, hN⟩ :=
    @LatticeProb.exists_pos_eventually_forall_of_tendsto_choices S hnonempty p
    (fun n τ a b hab => iSup_le fun u => iSup_le fun hu =>
      le_iSup_of_le u (le_iSup_of_le (hu.trans hab) le_rfl))
    (fun σ => h η hη (fun n => (σ n).1) (fun n => (σ n).2)) ε hε
  refine ⟨δ, hδ, N, fun n hn τ hτ u hu => ?_⟩
  refine le_trans ?_ (hN n hn ⟨τ, hτ⟩).le
  exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)

/-- The finite stopping condition gives exactly the asymptotic terminal averaging bound
needed to restrict half-line subsequential limits. -/
theorem asymptotic_averagedIncrement_constantExtension {T : ℝ} (hT : 0 < T)
    (P : ℕ → ProbabilityMeasure (Cadlag.D T E))
    (h : ∀ η : ℝ, 0 < η → ∀ τ : ℕ → Cadlag.D T E → Icc (0 : ℝ) T,
      (∀ n, finiteIsStopping (τ n)) →
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
          (P n : Measure (Cadlag.D T E))
            {x | η ≤ dist (x.1 (clipFiniteTime (τ n x) u)) (x.1 (τ n x))}) atTop)
        (𝓝[>] 0) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∫ x, averagedIncrement ⟨T, hT.le⟩ h x
        ∂(((P n).map (measurable_constantExtension hT).aemeasurable :
          ProbabilityMeasure (D E)) : Measure (D E)) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, N, hN⟩ := exists_pos_eventually_finite_increment_bound hT P h hhalf
    (ENNReal.ofReal_pos.mpr hhalf)
  refine ⟨min δ T, lt_min hδ hT, fun r hr hrδ => ⟨N, fun n hn => ?_⟩⟩
  have hrT : r < T := hrδ.trans_le (min_le_right _ _)
  have hrd : r ≤ δ := (hrδ.trans_le (min_le_left _ _)).le
  have hbound := integral_averagedIncrement_constantExtension_le hT (P n)
    hhalf.le hhalf.le hr hrT hrd (fun c u hu =>
      hN n hn (fun _ => c) (finiteIsStopping_const c) u hu)
  exact hbound.trans_eq (by ring)

/-- The exact finite-horizon Aldous implication, from its raw-natural full-sequence
stopping condition and marginal tightness, modulo the two explicit cited inputs. -/
theorem isTightMeasureSet_of_finite_stoppingIncrementCondition [CompleteSpace E]
    (hEK : External.EthierKurtzRelativeCompactnessStopping)
    (hPol : External.BillingsleySkorokhodPolish) {T : ℝ} (hT : 0 < T)
    (P : ℕ → ProbabilityMeasure (Cadlag.D T E))
    (hmarginal : ∀ t : Icc (0 : ℝ) T,
      IsTightMeasureSet (range (fun n =>
        (((P n).map (Cadlag.measurable_eval t).aemeasurable) : Measure E))))
    (h : ∀ η : ℝ, 0 < η → ∀ τ : ℕ → Cadlag.D T E → Icc (0 : ℝ) T,
      (∀ n, finiteIsStopping (τ n)) →
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
          (P n : Measure (Cadlag.D T E))
            {x | η ≤ dist (x.1 (clipFiniteTime (τ n x) u)) (x.1 (τ n x))}) atTop)
        (𝓝[>] 0) (𝓝 0)) :
    IsTightMeasureSet (range (fun n => (P n : Measure (Cadlag.D T E)))) := by
  let μ : ℕ → ProbabilityMeasure (D E) :=
    fun n => (P n).map (measurable_constantExtension hT).aemeasurable
  have hcompact : IsCompact (closure (range μ)) :=
    isCompact_closure_range_map_of_stoppingIncrementCondition P
      (fun _ => constantExtension hT) hEK (fun _ => measurable_constantExtension hT)
      (marginal_compactSets_constantExtension hT P hmarginal)
      (stoppingIncrementCondition_constantExtension hT P h)
  obtain ⟨hsep, hcm⟩ := hPol E T hT
  have hrestrict := isTightMeasureSet_restrict_of_asymptotic_averagedIncrement
    ⟨T, hT.le⟩ hT hsep hcm μ hcompact
      (asymptotic_averagedIncrement_constantExtension hT P h)
  change IsTightMeasureSet {((((P n).map
    (measurable_constantExtension hT).aemeasurable).map
      (measurable_restrict T).aemeasurable : ProbabilityMeasure (Cadlag.D T E)) :
        Measure (Cadlag.D T E)) | n} at hrestrict
  simpa only [map_restrict_map_constantExtension, Set.range] using hrestrict

/-- The finite criterion applies to actual Dirac laws at constant paths, with zero stopped
increments for every raw-natural stopping sequence. -/
theorem isTightMeasureSet_finite_constantLaw [CompleteSpace E]
    (hEK : External.EthierKurtzRelativeCompactnessStopping)
    (hPol : External.BillingsleySkorokhodPolish) {T : ℝ} (hT : 0 < T) (a : E) :
    IsTightMeasureSet (range (fun _n : ℕ =>
      (Measure.dirac (Cadlag.const T a) : Measure (Cadlag.D T E)))) := by
  let P : ℕ → ProbabilityMeasure (Cadlag.D T E) :=
    fun _ => ⟨Measure.dirac (Cadlag.const T a), Measure.dirac.isProbabilityMeasure⟩
  apply isTightMeasureSet_of_finite_stoppingIncrementCondition hEK hPol hT P
  · intro t
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε hε
    refine ⟨{a}, isCompact_singleton, ?_⟩
    rintro _ ⟨n, rfl⟩
    change (((P n).map (Cadlag.measurable_eval t).aemeasurable) : Measure E) {a}ᶜ ≤ ε
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (Cadlag.measurable_eval t) isClosed_singleton.measurableSet.compl]
    simp [P, Cadlag.const]
  · intro η hη τ _
    have hevent (n : ℕ) (u : Time) :
        (P n : Measure (Cadlag.D T E))
          {x | η ≤ dist (x.1 (clipFiniteTime (τ n x) u)) (x.1 (τ n x))} = 0 := by
      simp [P, Cadlag.const, not_le.mpr hη]
    simp only [hevent, ENNReal.iSup_zero, limsup_const]
    exact tendsto_const_nhds

end

end LatticeProb.Cadlag.HalfLine
