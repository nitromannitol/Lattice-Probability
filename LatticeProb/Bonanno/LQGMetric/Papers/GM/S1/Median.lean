/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Median at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Defs
import LatticeProb.Bonanno.LQGMetric.Prob.Median
import Mathlib.Topology.MetricSpace.Sequences
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif

/-!
# GM §1.4: medians of the left–right crossing (GM.S1.16a, S1.17, S1.17a, S1.17b)

Blueprint `blueprint/M1.md` §3 rows 18, 19, 21; decision DEC-A D-A2 (i), (ii).
GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Theorems 1.1, 1.2, 1.8, l. 582–593 ("Recall that 𝔞_ε is the median … Hence for any
subsequential limiting metric the median D_h-distance between the left and right boundaries of the
unit square is 1", l. 588–589); 𝔞_ε is defined at l. 223.

* `abs_crossFn_sub_le` : `|crossFn f − crossFn g| ≤ sup_{L×R} |f − g|` (L × R ⊆ B̄₂(0)²),
  hence `tendstoInMeasure_crossFn` (local uniform convergence in probability ⇒ convergence in
  probability of the crossings; DEC-A D-A2 (i), first bullet);
* `gm_S1_17` (GM.S1.17): limits of medians are medians (via `IsMedian.of_tendstoInMeasure`,
  Portmanteau, `LQGMetric.Prob.Median`);
* `gm_S1_17a` (GM.S1.17a): if the limit crossing is a.s. positive, a subsequence of the medians
  converges to a positive limit (quantiles of the approximants eventually lie near the medians
  of the limit, `eventually_mem_Ioo_of_tendsto`; Bolzano–Weierstrass,
  `tendsto_subseq_of_frequently_bounded`);
* `crossFn_lfppDist` : `crossFn ∘ lfppDist = lfppCross` when `h*_ε` is continuous, and the bridge
  `isMedian_aEps_of` (GM.S1.16a from the field-layer inputs: law of `h` = `normGFFLaw`, a.s.
  continuity of `h*_ε`, measurability of `lfppCross`; `lowerMedian_eq_lowerMedianLaw`);
* `gm_S1_17b_of_S1_16a` (GM.S1.17b from GM.S1.16a): GM-normalized limits have median crossing 1
  (`𝔞_ε > 0` eventually, otherwise the limit would vanish; then GM.S1.17 with medians `1`).

Sources: GM l. 586–590 and DEC-A D-A2 (the argument written out there); Portmanteau
(Billingsley, *Convergence of Probability Measures*, Thm 2.1, via `LQGMetric.Prob.Median`).
The elementary estimates (Lipschitz bound of the crossing, positivity of `𝔞_ε` eventually) are
own elementary proofs filling GM's "hence".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM


lemma zero_mem_leftSide : (0 : ℂ) ∈ leftSide := by simp [leftSide]

lemma one_mem_rightSide : (1 : ℂ) ∈ rightSide := by simp [rightSide]

lemma crossSet_nonempty : (leftSide ×ˢ rightSide).Nonempty :=
  ⟨(0, 1), zero_mem_leftSide, one_mem_rightSide⟩

lemma norm_le_two_of_mem_leftSide {z : ℂ} (hz : z ∈ leftSide) : ‖z‖ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [h1, abs_zero, abs_of_nonneg h2] at this
  linarith

lemma norm_le_two_of_mem_rightSide {z : ℂ} (hz : z ∈ rightSide) : ‖z‖ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [h1, abs_one, abs_of_nonneg h2] at this
  linarith

/-- `L × R ⊆ B̄₂(0) × B̄₂(0)` -/
lemma crossSet_subset_closedBall :
    leftSide ×ˢ rightSide ⊆ Metric.closedBall (0 : ℂ) 2 ×ˢ Metric.closedBall (0 : ℂ) 2 :=
  fun _ hp => ⟨mem_closedBall_zero_iff.2 (norm_le_two_of_mem_leftSide hp.1),
    mem_closedBall_zero_iff.2 (norm_le_two_of_mem_rightSide hp.2)⟩

lemma bddBelow_crossSet_of_nonneg {d : ℂ × ℂ → ℝ} (hd : ∀ p, 0 ≤ d p) :
    BddBelow (d '' (leftSide ×ˢ rightSide)) :=
  ⟨0, by rintro _ ⟨p, -, rfl⟩; exact hd p⟩

lemma crossFn_le {d : ℂ × ℂ → ℝ} (hd : BddBelow (d '' (leftSide ×ˢ rightSide)))
    {p : ℂ × ℂ} (hp : p ∈ leftSide ×ˢ rightSide) : crossFn d ≤ d p :=
  csInf_le hd (mem_image_of_mem d hp)

lemma le_crossFn {d : ℂ × ℂ → ℝ} {c : ℝ} (hc : ∀ p ∈ leftSide ×ˢ rightSide, c ≤ d p) :
    c ≤ crossFn d :=
  le_csInf (crossSet_nonempty.image d) (by rintro _ ⟨p, hp, rfl⟩; exact hc p hp)

lemma crossFn_nonneg {d : ℂ × ℂ → ℝ} (hd : ∀ p, 0 ≤ d p) : 0 ≤ crossFn d :=
  le_crossFn fun p _ => hd p

/-- `crossFn f - c ≤ crossFn g` when `f ≤ g + c` on `L × R` -/
lemma crossFn_sub_le {f g : ℂ × ℂ → ℝ} (hf : BddBelow (f '' (leftSide ×ˢ rightSide)))
    {c : ℝ} (hc : ∀ p ∈ leftSide ×ˢ rightSide, f p - g p ≤ c) : crossFn f - c ≤ crossFn g :=
  le_crossFn fun p hp => by linarith [crossFn_le hf hp, hc p hp]

/-- GM.S1.17 (first part): `|crossFn f − crossFn g| ≤ sup_{L × R} |f − g|`. -/
theorem abs_crossFn_sub_le {f g : ℂ × ℂ → ℝ} (hf : BddBelow (f '' (leftSide ×ˢ rightSide)))
    (hg : BddBelow (g '' (leftSide ×ˢ rightSide))) {c : ℝ}
    (hc : ∀ p ∈ leftSide ×ˢ rightSide, |f p - g p| ≤ c) : |crossFn f - crossFn g| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · have := crossFn_sub_le hf (c := c) fun p hp => (le_abs_self _).trans (hc p hp)
    linarith
  · have := crossFn_sub_le hg (c := c) fun p hp => by
      have := hc p hp; rw [abs_sub_comm] at this; exact (le_abs_self _).trans this
    linarith

/-- Local uniform convergence in probability implies convergence in probability of the
left–right crossings (`L × R ⊆ B̄₂ × B̄₂`). -/
theorem tendstoInMeasure_crossFn {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {l : Filter ι} {X : ι → Ω → ℂ × ℂ → ℝ} {Y : Ω → ℂ × ℂ → ℝ}
    (hX : ∀ i ω, BddBelow ((X i ω) '' (leftSide ×ˢ rightSide)))
    (hY : ∀ ω, BddBelow ((Y ω) '' (leftSide ×ˢ rightSide))) (h : TendstoInProbLU P X l Y) :
    TendstoInMeasure P (fun i ω => crossFn (X i ω)) l (fun ω => crossFn (Y ω)) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h 2 two_pos δ hδ)
    (fun _ => bot_le) (fun i => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set s := ⨆ p ∈ Metric.closedBall (0 : ℂ) 2 ×ˢ Metric.closedBall (0 : ℂ) 2,
    edist (X i ω p) (Y ω p) with hs
  have hsr : s.toReal < δ := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hst : s ≠ ⊤ := ne_top_of_lt hlt
  have key : |crossFn (X i ω) - crossFn (Y ω)| ≤ s.toReal := by
    refine abs_crossFn_sub_le (hX i ω) (hY ω) fun p hp => ?_
    have h1 : edist (X i ω p) (Y ω p) ≤ s :=
      le_iSup₂ (f := fun p _ => edist (X i ω p) (Y ω p)) p (crossSet_subset_closedBall hp)
    rw [edist_dist, ENNReal.ofReal_le_iff_le_toReal hst] at h1
    rwa [← Real.dist_eq]
  rw [Real.dist_eq] at hω
  linarith

/-- GM.S1.17 -/
theorem gm_S1_17 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℂ × ℂ → ℝ) (Y : Ω → ℂ × ℂ → ℝ) (m : ℕ → ℝ) (m₀ : ℝ),
    (∀ n ω p, 0 ≤ X n ω p) → (∀ ω p, 0 ≤ Y ω p) →
    (∀ n, AEMeasurable (fun ω => crossFn (X n ω)) P) → AEMeasurable (fun ω => crossFn (Y ω)) P →
    TendstoInProbLU P X atTop Y → (∀ n, IsMedian (P.map fun ω => crossFn (X n ω)) (m n)) →
    Tendsto m atTop (𝓝 m₀) → IsMedian (P.map fun ω => crossFn (Y ω)) m₀ := by
  intro Ω _ P _ X Y m m₀ hX0 hY0 hXm _ hT hmed hm
  exact IsMedian.of_tendstoInMeasure
    (tendstoInMeasure_crossFn (fun n ω => bddBelow_crossSet_of_nonneg (hX0 n ω))
      (fun ω => bddBelow_crossSet_of_nonneg (hY0 ω)) hT) hXm hm (Eventually.of_forall hmed)

/-- GM.S1.17a -/
theorem gm_S1_17a : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℂ × ℂ → ℝ) (Y : Ω → ℂ × ℂ → ℝ) (m : ℕ → ℝ),
    (∀ n ω p, 0 ≤ X n ω p) → (∀ ω p, 0 ≤ Y ω p) →
    (∀ n, AEMeasurable (fun ω => crossFn (X n ω)) P) →
    AEMeasurable (fun ω => crossFn (Y ω)) P →
    TendstoInProbLU P X atTop Y → (∀ n, IsMedian (P.map fun ω => crossFn (X n ω)) (m n)) →
    (∀ᵐ ω ∂P, 0 < crossFn (Y ω)) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ m₀ : ℝ, 0 < m₀ ∧ Tendsto (m ∘ ψ) atTop (𝓝 m₀) := by
  intro Ω _ P _ X Y m hX0 hY0 hXm hYm hT hmed hpos
  have hTM := tendstoInMeasure_crossFn (fun n ω => bddBelow_crossSet_of_nonneg (hX0 n ω))
    (fun ω => bddBelow_crossSet_of_nonneg (hY0 ω)) hT
  have hD := hTM.tendstoInDistribution_of_aemeasurable hXm hYm
  set μY := P.map fun ω => crossFn (Y ω) with hμY
  have : IsProbabilityMeasure μY := (Measure.isProbabilityMeasure_map_iff hYm).2 ‹_›
  -- the lower median of the limit is positive
  have hl : 0 < lowerMedianLaw μY := by
    by_contra hle
    have h1 : (2 : ℝ≥0∞)⁻¹ ≤ μY (Iic 0) :=
      (le_measure_Iic_iff_lowerQuantile_le inv_two_pos' inv_two_lt_one').2 (not_lt.1 hle)
    have h2 : μY (Iic 0) = 0 := by
      rw [hμY, Measure.map_apply_of_aemeasurable hYm measurableSet_Iic]
      exact measure_mono_null (fun ω hω => not_lt.2 (mem_Iic.1 hω))
        (ae_iff.1 hpos)
    rw [h2] at h1
    exact absurd h1 (not_le.2 inv_two_pos')
  set l := lowerMedianLaw μY
  have hev := eventually_mem_Ioo_of_tendsto inv_two_pos' inv_two_lt_one' hD.tendsto
    (Eventually.of_forall hmed) (half_pos hl)
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc (l - l / 2) (upperMedianLaw μY + l / 2))
    (hev.mono fun n hn => Ioo_subset_Icc_self hn).frequently
  rw [closure_Icc] at ha
  exact ⟨ψ, hψ, a, by linarith [ha.1], hlim⟩

/-! ### The LFPP crossing as `crossFn ∘ lfppDist` -/

/-- the straight segment `t ↦ z + t (w - z)` -/
def segPath (z w : ℂ) : ℝ → ℂ := fun t => z + (t : ℂ) * (w - z)

lemma hasDerivAt_segPath (z w : ℂ) (t : ℝ) : HasDerivAt (segPath z w) (w - z) t := by
  have := (((hasDerivAt_id t).ofReal_comp).mul_const (w - z)).const_add z
  simp only [id, Complex.ofReal_one, one_mul] at this
  exact this

lemma isPiecewiseC1Path_segPath (z w : ℂ) : IsPiecewiseC1Path (segPath z w) z w where
  source := by simp [segPath]
  target := by simp [segPath]
  continuousOn := by unfold segPath; fun_prop
  piecewise := by
    refine ⟨1, ![0, 1], ?_, rfl, rfl, fun i => ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · have : ContDiff ℝ 1 (segPath z w) := by
        unfold segPath
        exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
      exact this.contDiffOn

/-- `D^ε_h(z,w) < ∞` when `h*_ε` is continuous (the straight segment). -/
theorem lfppDistE_ne_top {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g)) (z w : ℂ) :
    lfppDistE ξ ε g z w ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (iInf_le _ ⟨segPath z w, isPiecewiseC1Path_segPath z w⟩)
  have hd : ∀ t, deriv (segPath z w) t = w - z := fun t => (hasDerivAt_segPath z w t).deriv
  simp only [lfppLen, hd]
  have hcont : Continuous fun t : ℝ =>
      (Real.exp (ξ * heatMollify ε g (segPath z w t)) * ‖w - z‖).toNNReal := by
    have : Continuous (segPath z w) := by unfold segPath; fun_prop
    fun_prop
  exact (setLIntegral_lt_top_of_isCompact (by simp) isCompact_Icc hcont).ne

/-- `crossFn ∘ lfppDist = lfppCross` when `h*_ε` is continuous. -/
theorem crossFn_lfppDist {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g)) :
    crossFn (lfppDist ξ ε g) = lfppCross ξ ε g := by
  set E := lfppDistE ξ ε g
  have hA : (⨅ z ∈ leftSide, ⨅ w ∈ rightSide, E z w) =
      sInf ((fun p : ℂ × ℂ => E p.1 p.2) '' (leftSide ×ˢ rightSide)) := by
    rw [sInf_image]
    refine le_antisymm (le_iInf₂ fun p hp => iInf₂_le_of_le p.1 hp.1 (iInf₂_le p.2 hp.2))
      (le_iInf₂ fun z hz => le_iInf₂ fun w hw => iInf₂_le (z, w) ⟨hz, hw⟩)
  rw [lfppCross, hA, ENNReal.toReal_sInf _ (by
    rintro _ ⟨p, -, rfl⟩; exact lfppDistE_ne_top hc p.1 p.2), image_image]
  rfl

/-- **Bridge for GM.S1.16a** (`𝔞_ε` is a median of the law of `crossFn (D^ε_h)`), given the
field-layer inputs: the law of `h` is `normGFFLaw`, `h*_ε` is a.s. continuous, and `lfppCross` is
measurable for `normGFFLaw`. -/
theorem isMedian_aEps_of {ξ ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hm : Measurable h)
    (hlaw : normGFFLaw = P.map h) (hcont : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω)))
    (hmeas : AEMeasurable (lfppCross ξ ε) normGFFLaw) :
    AEMeasurable (fun ω => crossFn (lfppDist ξ ε (h ω))) P ∧
      IsMedian (P.map fun ω => crossFn (lfppDist ξ ε (h ω))) (aEps ξ ε) := by
  rw [hlaw] at hmeas
  have hae : (fun ω => lfppCross ξ ε (h ω)) =ᵐ[P] fun ω => crossFn (lfppDist ξ ε (h ω)) := by
    filter_upwards [hcont] with ω hω using (crossFn_lfppDist hω).symm
  have hcm : AEMeasurable (fun ω => lfppCross ξ ε (h ω)) P := hmeas.comp_measurable hm
  have hX : AEMeasurable (fun ω => crossFn (lfppDist ξ ε (h ω))) P := hcm.congr hae
  refine ⟨hX, ?_⟩
  have hmap : P.map (fun ω => crossFn (lfppDist ξ ε (h ω))) =
      (P.map h).map (lfppCross ξ ε) := by
    rw [AEMeasurable.map_map_of_aemeasurable hmeas hm.aemeasurable]
    exact (Measure.map_congr hae).symm
  have : IsProbabilityMeasure (P.map fun ω => crossFn (lfppDist ξ ε (h ω))) :=
    (Measure.isProbabilityMeasure_map_iff hX).2 ‹_›
  rw [aEps, lowerMedian, hlaw, lowerMedian_eq_lowerMedianLaw hmeas, ← hmap]
  exact isMedian_lowerMedianLaw

/-- **GM.S1.16a from the measurability of the LFPP crossing** (F.MEAS): the only input not yet
available is `AEMeasurable (lfppCross ξ ε) normGFFLaw`. -/
theorem gm_S1_16a_of_measurable
    (hmeas : ∀ ξ ε : ℝ, 0 < ε → AEMeasurable (lfppCross ξ ε) normGFFLaw) :
    ∀ {ξ ε : ℝ}, 0 < ε → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      AEMeasurable (fun ω => crossFn (lfppDist ξ ε (h ω))) P ∧
      IsMedian (P.map fun ω => crossFn (lfppDist ξ ε (h ω))) (aEps ξ ε) := by
  intro ξ ε hε Ω _ P _ h hh
  exact isMedian_aEps_of hh.1.measurable (normGFFLaw_eq hh)
    ((hh.1.ae_tendstoLocallyUniformly_heatMollify ε hε.ne').mono fun _ hω => hω.2)
    (hmeas ξ ε hε)

/-! ### GM.S1.17b -/

lemma crossFn_smul {c : ℝ} (hc : 0 ≤ c) (d : ℂ × ℂ → ℝ) : crossFn (c • d) = c * crossFn d := by
  rw [crossFn, crossFn, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hc]
  congr 1
  ext x
  simp [Set.mem_smul_set]

lemma cm_nonneg (D : ContMetric) (p : ℂ × ℂ) : 0 ≤ D.1 p := by
  have h1 := D.2.triangle p.1 p.2 p.1
  rw [D.2.self_eq_zero, D.2.symm p.2 p.1] at h1
  linarith

lemma cm_pos_of_ne (D : ContMetric) {x y : ℂ} (hxy : x ≠ y) : 0 < D.1 (x, y) :=
  lt_of_le_of_ne (cm_nonneg D (x, y)) fun h => hxy (D.2.eq_of_eq_zero x y h.symm)

lemma isGFFPlusBddCont_of_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) : IsGFFPlusBddCont h P := by
  refine ⟨hh.1.measurable, fun _ => 0, measurable_const, fun _ => ⟨0, by simp⟩, ?_⟩
  simpa [ofCont_zero_eq] using hh.1

lemma tendstoInProbLU_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℂ × ℂ → ℝ} {Y : Ω → ℂ × ℂ → ℝ} (h : TendstoInProbLU P X atTop Y) (N : ℕ) :
    TendstoInProbLU P (fun n => X (n + N)) atTop Y :=
  fun R hR δ hδ => (h R hR δ hδ).comp (tendsto_add_atTop_nat N)

/-- GM.S1.17b from GM.S1.16a. -/
theorem gm_S1_17b_of_S1_16a
    (hA : ∀ {ξ ε : ℝ}, 0 < ε → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      AEMeasurable (fun ω => crossFn (lfppDist ξ ε (h ω))) P ∧
      IsMedian (P.map fun ω => crossFn (lfppDist ξ ε (h ω))) (aEps ξ ε)) :
    ∀ {γ : ℝ} (D : DistC → ContMetric), Measurable D →
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) →
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        TendstoInProbLU P
          (fun n ω => (aEps (xiGamma γ) (ε n))⁻¹ • lfppDist (xiGamma γ) (ε n) (h ω))
          atTop (fun ω => (D (h ω)).1)) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P →
      IsMedian (P.map fun ω => crossFn (D (h ω)).1) 1 := by
  intro γ D _ ε hε hconv Ω _ P _ h hh
  set ξ := xiGamma γ
  set a : ℕ → ℝ := fun n => aEps ξ (ε n) with ha_def
  set X : ℕ → Ω → ℂ × ℂ → ℝ := fun n ω => (a n)⁻¹ • lfppDist ξ (ε n) (h ω) with hX_def
  set Y : Ω → ℂ × ℂ → ℝ := fun ω => (D (h ω)).1
  have hT : TendstoInProbLU P X atTop Y := hconv P h (isGFFPlusBddCont_of_normalized hh)
  have hL0 : ∀ n ω p, 0 ≤ lfppDist ξ (ε n) (h ω) p := fun _ _ _ => ENNReal.toReal_nonneg
  have hA' := fun n => hA (ξ := ξ) (hε n) P h hh
  -- `𝔞_ε ≥ 0`
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    by_contra hneg
    have h1 := (isMedian_map_iff (hA' n).1).1 (hA' n).2 |>.1
    have : {ω | crossFn (lfppDist ξ (ε n) (h ω)) ≤ a n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.1 hneg) (crossFn_nonneg (hL0 n ω))
    rw [this, measure_empty] at h1
    exact absurd h1 (not_le.2 inv_two_pos')
  -- `𝔞_ε > 0` eventually (else the limit vanishes on `B̄₂²`)
  have hev : ∀ᶠ n in atTop, 0 < a n := by
    by_contra hfr
    rw [not_eventually] at hfr
    have hfr0 : ∃ᶠ n in atTop, a n = 0 :=
      hfr.mono fun n hn => le_antisymm (not_lt.1 hn) (ha0 n)
    have hpos : ∀ ω, 0 < Y ω (0, 1) := fun ω => cm_pos_of_ne (D (h ω)) zero_ne_one
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < P {ω | 1 / ((k : ℝ) + 1) ≤ Y ω (0, 1)} := by
      by_contra hall
      push Not at hall
      have hU : (⋃ k : ℕ, {ω | 1 / ((k : ℝ) + 1) ≤ Y ω (0, 1)}) = univ := by
        refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (hpos ω)
        exact ⟨k, hk.le⟩
      have := measure_iUnion_null fun k => nonpos_iff_eq_zero.1 (hall k)
      rw [hU, measure_univ] at this
      exact one_ne_zero this
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    have hlim := hT 2 two_pos δ hδ
    set c := P {ω | 1 / ((k : ℝ) + 1) ≤ Y ω (0, 1)}
    have hmem : (0, 1) ∈ Metric.closedBall (0 : ℂ) 2 ×ˢ Metric.closedBall (0 : ℂ) 2 :=
      crossSet_subset_closedBall ⟨zero_mem_leftSide, one_mem_rightSide⟩
    have hge : ∃ᶠ n in atTop, c ≤ P {ω | ENNReal.ofReal δ ≤
        ⨆ p ∈ Metric.closedBall (0 : ℂ) 2 ×ˢ Metric.closedBall (0 : ℂ) 2,
          edist (X n ω p) (Y ω p)} := by
      refine hfr0.mono fun n hn => measure_mono fun ω hω => ?_
      simp only [Set.mem_ofPred_eq] at hω ⊢
      refine le_trans ?_ (le_iSup₂ (f := fun p _ => edist (X n ω p) (Y ω p)) (0, 1) hmem)
      simp only [X, hn, inv_zero, zero_smul, Pi.zero_apply]
      rw [edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (hpos ω)]
      exact ENNReal.ofReal_le_ofReal hω
    have hev2 := hlim.eventually (gt_mem_nhds hk)
    obtain ⟨n, h1, h2⟩ := (hge.and_eventually hev2).exists
    exact absurd h1 (not_le.2 h2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- apply GM.S1.17 to the shifted sequence, with medians `1`
  have hcX : ∀ n ω, crossFn (X n ω) = (a n)⁻¹ * crossFn (lfppDist ξ (ε n) (h ω)) :=
    fun n ω => crossFn_smul (inv_nonneg.2 (ha0 n)) _
  have hXm : ∀ n, AEMeasurable (fun ω => crossFn (X n ω)) P := fun n => by
    simp only [hcX]
    exact (hA' n).1.const_mul _
  have hX0 : ∀ n ω p, 0 ≤ X n ω p := fun n ω p =>
    mul_nonneg (inv_nonneg.2 (ha0 n)) (hL0 n ω p)
  have hY0 : ∀ ω p, 0 ≤ Y ω p := fun ω p => cm_nonneg (D (h ω)) p
  have hTM := tendstoInMeasure_crossFn (fun n ω => bddBelow_crossSet_of_nonneg (hX0 n ω))
    (fun ω => bddBelow_crossSet_of_nonneg (hY0 ω)) hT
  have hYm : AEMeasurable (fun ω => crossFn (Y ω)) P := hTM.aemeasurable hXm
  have hmed : ∀ n, IsMedian (P.map fun ω => crossFn (X (n + N) ω)) 1 := by
    intro n
    have hpos := hN (n + N) (Nat.le_add_left N n)
    have hmono : Monotone fun x : ℝ => (a (n + N))⁻¹ * x :=
      fun x y hxy => mul_le_mul_of_nonneg_left hxy (inv_nonneg.2 hpos.le)
    have := IsMedian.map_monotone hmono (measurable_const_mul _) (hA' (n + N)).2
    rw [inv_mul_cancel₀ hpos.ne', AEMeasurable.map_map_of_aemeasurable
      (measurable_const_mul _).aemeasurable (hA' (n + N)).1] at this
    simpa only [hcX, Function.comp_def] using this
  exact gm_S1_17 P (fun n => X (n + N)) Y (fun _ => 1) 1 (fun n => hX0 (n + N)) hY0
    (fun n => hXm (n + N)) hYm (tendstoInProbLU_shift hT N) hmed tendsto_const_nhds

/-- GM.S1.17b, given only the measurability of the LFPP crossing (F.MEAS). -/
theorem gm_S1_17b_of_measurable
    (hmeas : ∀ ξ ε : ℝ, 0 < ε → AEMeasurable (lfppCross ξ ε) normGFFLaw) :
    ∀ {γ : ℝ} (D : DistC → ContMetric), Measurable D →
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) →
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        TendstoInProbLU P
          (fun n ω => (aEps (xiGamma γ) (ε n))⁻¹ • lfppDist (xiGamma γ) (ε n) (h ω))
          atTop (fun ω => (D (h ω)).1)) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P →
      IsMedian (P.map fun ω => crossFn (D (h ω)).1) 1 :=
  gm_S1_17b_of_S1_16a (gm_S1_16a_of_measurable hmeas)

end GM
end LQGMetric
