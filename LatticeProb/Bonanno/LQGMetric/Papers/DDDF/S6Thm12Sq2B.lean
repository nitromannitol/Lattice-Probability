/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq2B at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq2A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8 with DDDF Theorem 1 (2) on the square (task P2-DDDF6f)

Copy of `Papers/DFGPS/P29SqB.lean` with `Blueprint.DDDFThm1_2` replaced by `DDDF.DDDFThm1_2Sq` (DDDF Theorem 1 (2)
for `D = (−1,2)²` only; DFGPS T:877–881 applies Theorem 1 (2) only to that domain, and `zb_step'`
reads only its tightness there). Same names in the namespace `LQGMetric.DFGPS.Q12`; proofs
verbatim. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS.Q12

open Blueprint LFPP HeatSq WhiteNoise DDDF

/-- **DFGPS Lemma 2.8, GFF case, `S = [0,1]²`.** -/
theorem lem2_8Gff_unitSq' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → DistC) (hg : IsWholePlaneGFF g P) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map fun ω => lfppSqC (xiGamma γ) ε (g ω) closedUnitSquare} ∧
      ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
        (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ)),
        (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
          (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (g ω) closedUnitSquare) →
        Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsPosOffDiag d := by
  obtain ⟨lam, C, εb, Y, hC, hεb, hlam0, hb, hYc, hT, hpos, hcmp⟩ :=
    unitSq_setup' h11 h12 h29 hLM hγ hγ2 P g hg
  set ξ := xiGamma γ
  have : ConnectedSpace closedUnitSquare := isConnected_iff_connectedSpace.1
    (convex_closedUnitSquare.isConnected ⟨0, by simp [closedUnitSquare]⟩)
  have hgc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous (heatMollify ε (g ω)) := fun ε hε =>
    (hg.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne').mono fun ω h => h.2
  set A : ℝ → Ω → C(closedUnitSquare × closedUnitSquare, ℝ) := fun ε ω =>
    sqMetricC ξ (lam ε) (fun x => Y (ε ^ 2) x ω)
  set B : ℝ → Ω → C(closedUnitSquare × closedUnitSquare, ℝ) := fun ε ω =>
    lfppSqC ξ ε (g ω) closedUnitSquare
  have hsq : ∀ ε : ℝ, 0 < ε → Real.sqrt (ε ^ 2) = ε := fun ε hε => Real.sqrt_sq hε.le
  have hδ : ∀ ε ∈ Ioo (0 : ℝ) 1, ε ^ 2 ∈ Ioo (0 : ℝ) 1 := fun ε hε =>
    ⟨by have := hε.1; positivity, by nlinarith [hε.1, hε.2]⟩
  have hAlaw : ∀ ε ∈ Ioo (0 : ℝ) 1, P.map (A ε) = P.map fun ω =>
      sqMetricC ξ (lam (Real.sqrt (ε ^ 2))) (fun x => Y (ε ^ 2) x ω) := fun ε hε => by
    simp only [A, hsq ε hε.1]
  have hAm : ∀ ε ∈ Ioo (0 : ℝ) 1, AEMeasurable (A ε) P := fun ε hε =>
    ((measurable_sqFun ξ _).comp (measurable_pathC (hYc _ (hδ ε hε)).1
      (hYc _ (hδ ε hε)).2)).aemeasurable
  have hBm : ∀ ε ∈ Ioo (0 : ℝ) 1, AEMeasurable (B ε) P := fun ε hε =>
    aemeasurable_lfppSqC_unitSq hg.measurable (hgc ε hε)
  -- the good events
  have hgood : ∀ ζ > 0, ∃ M : ℝ, ∃ e > 0, e ≤ εb ∧ e < 1 ∧ ∀ ε, 0 < ε → ε < e →
      ∃ E : Set Ω, P Eᶜ ≤ ENNReal.ofReal ζ ∧ ∀ ω ∈ E, ∀ p,
        B ε ω p ≤ Real.exp (|ξ| * M) * C * A ε ω p ∧
          A ε ω p ≤ Real.exp (|ξ| * M) * C * B ε ω p := by
    intro ζ hζ
    obtain ⟨M, ε₁, hε₁, hP⟩ := hcmp ζ hζ
    refine ⟨M, min (min ε₁ εb) (1 / 2), by positivity, (min_le_left _ _).trans
      (min_le_right _ _), lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun ε hε hεe => ?_⟩
    have h1 : ε < ε₁ := lt_of_lt_of_le hεe ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : ε < εb := lt_of_lt_of_le hεe ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : ε < 1 := lt_of_lt_of_le hεe ((min_le_right _ _).trans (by norm_num))
    set bad := {ω | ∃ x ∈ closedUnitSquare, M < |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|}
    set N := {ω | ¬ Continuous (heatMollify ε (g ω))}
    have hN : P N = 0 := measure_eq_zero_iff_ae_notMem.2
      ((hgc ε ⟨hε, h3⟩).mono fun ω hω h => h hω)
    refine ⟨(bad ∪ N)ᶜ, ?_, fun ω hω p => ?_⟩
    · rw [compl_compl]
      calc P (bad ∪ N) ≤ P bad + P N := measure_union_le _ _
        _ ≤ ENNReal.ofReal ζ := by rw [hN, add_zero]; exact hP ε hε h1
    · simp only [mem_compl_iff, mem_union, not_or] at hω
      have hd : ∀ x ∈ closedUnitSquare, |heatMollify ε (g ω) x - Y (ε ^ 2) x ω| ≤ M :=
        fun x hx => not_lt.1 fun h => hω.1 ⟨x, hx, h⟩
      obtain ⟨hl, hlo, hup⟩ := hb ε hε h2
      exact unitSq_dom (not_not.1 hω.2) ((hYc _ (hδ ε ⟨hε, h3⟩)).1 ω) hC hl hlo hup hd p
  refine ⟨?_, fun εn ν μ hν hε0 hμ => ?_⟩
  · -- tightness
    refine isTightMeasureSet_of_le_mul_ev' (Ioo (0 : ℝ) 1) A B
      (hT.subset (by rintro _ ⟨ε, hε, rfl⟩; exact ⟨ε ^ 2, hδ ε hε, hAlaw ε hε⟩)) hAm hBm
      (fun ε hε => Eventually.of_forall fun ω x => by
        simp only [A]
        rw [sqMetricC_apply ((hYc _ (hδ ε hε)).1 ω), lfppDOn_self convex_closedUnitSquare x.2,
          ENNReal.toReal_zero, mul_zero])
      (fun ε hε => Eventually.of_forall fun ω p => by
        simp only [A]
        rw [sqMetricC_apply ((hYc _ (hδ ε hε)).1 ω)]
        exact mul_nonneg (inv_nonneg.2 (hlam0 ε hε.1 hε.2.le)) ENNReal.toReal_nonneg)
      (fun ε hε => (hgc ε hε).mono fun ω hω => lfppSqC_unitSq_mem_pmetSet hω) ?_
    intro η hη
    set ζ := (min η 1).toReal
    have hmin : min η 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hζ : 0 < ζ := ENNReal.toReal_pos (lt_min hη one_pos).ne' hmin
    have hζη : ENNReal.ofReal ζ ≤ η := by
      rw [ENNReal.ofReal_toReal hmin]; exact min_le_left _ _
    obtain ⟨M, e, he, -, he1, hE⟩ := hgood ζ hζ
    refine ⟨Real.exp (|ξ| * M) * C, by positivity, Ioo 0 e,
      fun ε hε => ⟨hε.1, hε.2.trans he1⟩, ?_, fun ε hε => ?_⟩
    · have hf := lem2_8_tight_far' (γ := γ) (a := 0) (s := 1) one_pos hg he
      rw [← closedUnitSquare_eq] at hf
      refine hf.subset ?_
      rintro _ ⟨ε, ⟨hε, hεJ⟩, rfl⟩
      exact ⟨ε, ⟨not_lt.1 fun h => hεJ ⟨hε.1, h⟩, hε.2⟩, rfl⟩
    · obtain ⟨E, hPE, hdom⟩ := hE ε hε.1 hε.2
      exact ⟨E, hPE.trans hζη, Eventually.of_forall fun ω hω p => (hdom ω hω p).1⟩
  · -- positivity of the limits
    set α : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ) := fun n =>
      ⟨P.map (A (εn n)), (Measure.isProbabilityMeasure_map_iff (hAm _ (hν n).1)).2
        inferInstance⟩
    have hαT : IsTightMeasureSet {((m : ProbabilityMeasure _) : Measure _) | m ∈ range α} :=
      hT.subset (by
        rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨εn n ^ 2, hδ _ (hν n).1, hAlaw _ (hν n).1⟩)
    refine ae_posOffDiag_of_dominated hμ (isCompact_closure_of_isTightMeasureSet hαT)
      (fun ψ lam' hψ hlim => ?_) ?_
    · refine hpos (fun n => εn (ψ n) ^ 2) (α ∘ ψ) lam'
        (fun n => ⟨hδ _ (hν _).1, hAlaw _ (hν _).1⟩) ?_ hlim
      have := ((hε0.comp hψ.tendsto_atTop).pow 2)
      simpa using this
    · intro δ hδ0 ζ hζ
      obtain ⟨M, e, he, -, -, hE⟩ := hgood ζ hζ
      refine ⟨Real.exp (|ξ| * M) * C, by positivity, fun η hη => ?_⟩
      filter_upwards [hε0.eventually (gt_mem_nhds he)] with n hn
      obtain ⟨E, hPE, hdom⟩ := hE (εn n) (hν n).1.1 hn
      rw [(hν n).2]
      exact (map_smallSet_le_of_le_on (hBm _ (hν n).1) (hAm _ (hν n).1) (by positivity)
        (fun ω hω p => (hdom ω hω p).2) δ η).trans (add_le_add le_rfl hPE)

/-- **DFGPS Lemma 2.8, whole-plane GFF case, every closed square** (T:876–896). -/
theorem lem2_8Gff_gen' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) (h699 : DDDFEq6_99) : Lem2_8Gff := by
  intro γ hγ hγ2 a s hs Ω _ P _ g hg
  have hgt : IsWholePlaneGFF (fun ω => affineComp s a (g ω)) P := hg.affineComp hs a
  obtain ⟨hTU, hPU⟩ := lem2_8Gff_unitSq' h11 h12 h29 hLM hγ hγ2 P _ hgt
  obtain ⟨C, hC, ε₀, hε₀, hR⟩ := aEpsDF_ratio_bdd' h11 h12 h29 hLM h699 hγ hγ2 P g hg hs
  have hδf : ∀ ε : ℝ, 0 < ε → min (ε / s) (1 / 2) ∈ Ioo (0 : ℝ) 1 := fun ε hε =>
    ⟨lt_min (div_pos hε hs) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  set e₁ := min (min (s / 2) ε₀) 1 with he₁_def
  have he₁ : 0 < e₁ := lt_min (lt_min (by positivity) hε₀) one_pos
  have hJ : ∀ ε, 0 < ε → ε < e₁ → min (ε / s) (1 / 2) = ε / s ∧ ε < ε₀ ∧ ε < 1 := by
    intro ε hε hεe
    have h1 : ε < s / 2 := hεe.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    refine ⟨min_eq_left ?_, hεe.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
      hεe.trans_le (min_le_right _ _)⟩
    rw [div_le_iff₀ hs]; linarith
  have hgc : ∀ ε : ℝ, ε ≠ 0 → ∀ᵐ ω ∂P, Continuous (heatMollify ε (g ω)) := fun ε hε =>
    (hg.ae_tendstoLocallyUniformly_heatMollify ε hε).mono fun ω h => h.2
  have hgtc : ∀ ε : ℝ, ε ≠ 0 → ∀ᵐ ω ∂P, Continuous (heatMollify ε (affineComp s a (g ω))) :=
    fun ε hε => (hgt.ae_tendstoLocallyUniformly_heatMollify ε hε).mono fun ω h => h.2
  have hXm : ∀ δ : ℝ, δ ≠ 0 → AEMeasurable
      (fun ω => lfppSqC (xiGamma γ) δ (affineComp s a (g ω)) closedUnitSquare) P :=
    fun δ hδ => aemeasurable_lfppSqC_unitSq hgt.measurable (hgtc δ hδ)
  have hBm : ∀ ε : ℝ, ε ≠ 0 → AEMeasurable
      (fun ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)) P :=
    fun ε hε => aemeasurable_lfppSqC hg.measurable (hgc ε hε) hs
  have hPm : ∀ ε : ℝ, ε ≠ 0 → AEMeasurable
      (fun ω => pullC (sqHomeo a hs) (lfppSqC (xiGamma γ) ε (g ω) (closedSq a s))) P :=
    fun ε hε => (continuous_pullC _).measurable.comp_aemeasurable (hBm ε hε)
  -- the key identity (Lemma 2.6 on squares)
  have hkey : ∀ ε, 0 < ε → ε < e₁ → ∀ᵐ ω ∂P, ∀ p,
      pullC (sqHomeo a hs) (lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)) p =
        s * (aEpsDF (xiGamma γ) (ε / s) / aEpsDF (xiGamma γ) ε) *
          lfppSqC (xiGamma γ) (ε / s) (affineComp s a (g ω)) closedUnitSquare p ∧
      0 ≤ lfppSqC (xiGamma γ) (ε / s) (affineComp s a (g ω)) closedUnitSquare p := by
    intro ε hε hεe
    obtain ⟨-, hlt, -⟩ := hJ ε hε hεe
    obtain ⟨hA0, hAs0, -, -⟩ := hR ε hε hlt
    filter_upwards [lem2_6_sq hg (xiGamma γ) hε hs a, hgc ε hε.ne',
      hgtc (ε / s) (div_pos hε hs).ne'] with ω h26 hc1 hc2 p
    have hX := lfppSqC_apply_unitSq (ξ := xiGamma γ) hc2 p
    have hB : pullC (sqHomeo a hs) (lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)) p =
        (aEpsDF (xiGamma γ) ε)⁻¹ * (lfppDOn (xiGamma γ) (heatMollify ε (g ω)) (closedSq a s)
          (a + (s : ℂ) * p.1) (a + (s : ℂ) * p.2)).toReal := by
      rw [pullC_apply]; exact lfppSqC_apply_of_continuous hc1 hs _
    have hD : (lfppDOn (xiGamma γ) (heatMollify (ε / s) (affineComp s a (g ω)))
        closedUnitSquare p.1 p.2).toReal = s⁻¹ * (lfppDOn (xiGamma γ) (heatMollify ε (g ω))
          (closedSq a s) (a + (s : ℂ) * p.1) (a + (s : ℂ) * p.2)).toReal := by
      rw [h26 p.1 p.2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hs.le)]
    refine ⟨?_, ?_⟩
    · rw [hB, hX, hD]
      field_simp
    · rw [hX]
      exact mul_nonneg (inv_nonneg.2 (aEpsDF_nonneg_sq _ _)) ENNReal.toReal_nonneg
  have : ConnectedSpace closedUnitSquare := isConnected_iff_connectedSpace.1
    (convex_closedUnitSquare.isConnected ⟨0, by simp [closedUnitSquare]⟩)
  refine ⟨?_, fun εn ν μ hν hε0 hμ => ?_⟩
  · -- tightness
    refine tight_of_pullC (sqHomeo a hs) (Ioo (0 : ℝ) 1)
      (fun ε ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)) (fun ε hε => hBm ε hε.1.ne') ?_
    refine isTightMeasureSet_of_le_mul_ev' (Ioo (0 : ℝ) 1)
      (fun ε ω => lfppSqC (xiGamma γ) (min (ε / s) (1 / 2)) (affineComp s a (g ω))
        closedUnitSquare)
      (fun ε ω => pullC (sqHomeo a hs) (lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)))
      (hTU.subset ?_) (fun ε hε => hXm _ (hδf ε hε.1).1.ne') (fun ε hε => hPm ε hε.1.ne')
      (fun ε hε => (hgtc _ (hδf ε hε.1).1.ne').mono fun ω hω x =>
        (lfppSqC_unitSq_mem_pmetSet hω).1 x)
      (fun ε hε => (hgtc _ (hδf ε hε.1).1.ne').mono fun ω hω p => by
        show 0 ≤ lfppSqC (xiGamma γ) (min (ε / s) (1 / 2)) (affineComp s a (g ω))
          closedUnitSquare p
        rw [lfppSqC_apply_unitSq hω]
        exact mul_nonneg (inv_nonneg.2 (aEpsDF_nonneg_sq _ _)) ENNReal.toReal_nonneg)
      (fun ε hε => (hgc ε hε.1.ne').mono fun ω hω =>
        pullC_mem_pmetSet _ (lfppSqC_mem_pmetSet_sq hω hs)) ?_
    · rintro _ ⟨ε, hε, rfl⟩
      exact ⟨min (ε / s) (1 / 2), hδf ε hε.1, rfl⟩
    intro η hη
    refine ⟨s * C, by positivity, Ioo 0 e₁,
      fun ε hε => ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩, ?_, fun ε hε => ⟨univ, by simp, ?_⟩⟩
    · have hf := (lem2_8_tight_far' (γ := γ) (a := a) hs hg he₁).map (continuous_pullC
        (sqHomeo a hs))
      refine hf.subset ?_
      rintro _ ⟨ε, ⟨hε, hεJ⟩, rfl⟩
      refine ⟨_, ⟨ε, ⟨not_lt.1 fun h => hεJ ⟨hε.1, h⟩, hε.2⟩, rfl⟩, ?_⟩
      exact (map_pullC (sqHomeo a hs) (hBm ε hε.1.ne')).symm
    · obtain ⟨hδeq, hlt, -⟩ := hJ ε hε.1 hε.2
      have hRC := (hR ε hε.1 hlt).2.2.2
      refine (hkey ε hε.1 hε.2).mono fun ω hω _ p => ?_
      obtain ⟨h1, h2⟩ := hω p
      show _ ≤ s * C * lfppSqC (xiGamma γ) (min (ε / s) (1 / 2)) (affineComp s a (g ω))
        closedUnitSquare p
      rw [h1, hδeq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRC hs.le) h2
  · -- positivity of the subsequential limits
    refine pos_of_pullC (sqHomeo a hs)
      (fun n ω => lfppSqC (xiGamma γ) (εn n) (g ω) (closedSq a s))
      (fun n => hBm _ (hν n).1.1.ne') ν μ (fun n => (hν n).2) hμ ?_
    intro ν' μ' hν' hlim'
    set α : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ) := fun n =>
      ⟨P.map fun ω => lfppSqC (xiGamma γ) (min (εn n / s) (1 / 2)) (affineComp s a (g ω))
        closedUnitSquare, (Measure.isProbabilityMeasure_map_iff
          (hXm _ (hδf _ (hν n).1.1).1.ne')).2 inferInstance⟩ with hα
    have hαT : IsTightMeasureSet {((m : ProbabilityMeasure _) : Measure _) | m ∈ range α} :=
      hTU.subset (by
        rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨min (εn n / s) (1 / 2), hδf _ (hν n).1.1, rfl⟩)
    refine ae_posOffDiag_of_dominated hlim' (isCompact_closure_of_isTightMeasureSet hαT)
      (fun ψ lam hψ hlimψ => ?_) ?_
    · refine hPU (fun n => min (εn (ψ n) / s) (1 / 2)) (α ∘ ψ) lam
        (fun n => ⟨hδf _ (hν _).1.1, rfl⟩) ?_ hlimψ
      have h1 : Tendsto (fun n => εn (ψ n) / s) atTop (𝓝 0) := by
        simpa using (hε0.comp hψ.tendsto_atTop).div_const s
      have h2 := h1.min (tendsto_const_nhds (x := (1 / 2 : ℝ)))
      rwa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h2
    · intro δ hδ ζ hζ
      refine ⟨C / s, by positivity, fun η hη => ?_⟩
      filter_upwards [hε0.eventually (gt_mem_nhds he₁)] with n hn
      have hεn := (hν n).1.1
      obtain ⟨hδeq, hlt, -⟩ := hJ _ hεn hn
      have hRl := (hR _ hεn hlt).2.2.1
      have hCR : 1 ≤ C * (aEpsDF (xiGamma γ) (εn n / s) / aEpsDF (xiGamma γ) (εn n)) := by
        have := mul_le_mul_of_nonneg_left hRl hC.le
        rwa [mul_inv_cancel₀ hC.ne'] at this
      obtain ⟨E, hE, hEp⟩ := (hkey _ hεn hn).exists_mem
      have hPE : P Eᶜ = 0 := mem_ae_iff.1 hE
      rw [hν' n]
      show (P.map _) (smallSet δ η) ≤ (P.map fun ω => lfppSqC (xiGamma γ)
        (min (εn n / s) (1 / 2)) (affineComp s a (g ω)) closedUnitSquare)
          (smallSet δ (C / s * η)) + ENNReal.ofReal ζ
      refine (map_smallSet_le_of_le_on (hPm _ hεn.ne') (hXm _ (hδf _ hεn).1.ne')
        (by positivity : (0 : ℝ) < C / s) (E := E) (fun ω hω p => ?_) δ η).trans ?_
      · obtain ⟨h1, h2⟩ := hEp ω hω p
        rw [hδeq, h1]
        calc lfppSqC (xiGamma γ) (εn n / s) (affineComp s a (g ω)) closedUnitSquare p
            ≤ (C * (aEpsDF (xiGamma γ) (εn n / s) / aEpsDF (xiGamma γ) (εn n))) *
              lfppSqC (xiGamma γ) (εn n / s) (affineComp s a (g ω)) closedUnitSquare p :=
              le_mul_of_one_le_left h2 hCR
          _ = C / s * (s * (aEpsDF (xiGamma γ) (εn n / s) / aEpsDF (xiGamma γ) (εn n)) *
              lfppSqC (xiGamma γ) (εn n / s) (affineComp s a (g ω)) closedUnitSquare p) := by
              field_simp
      · rw [hPE]
        exact add_le_add le_rfl bot_le

/-- **DFGPS Lemma 2.8** (`lem-lfpp-tight-square`, T:872–898), from the Blueprint inputs
DDDF Thm 1.1, 1.2, Prop 29, (6.99) and LM Lemma 2.1. -/
theorem lem2_8_proved' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) (h699 : DDDFEq6_99) : Lem2_8 :=
  lem2_8_of_gff (lem2_8Gff_gen' h11 h12 h29 hLM h699)

end LQGMetric.DFGPS.Q12
