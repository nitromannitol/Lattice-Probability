/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Assembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.NoGap
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.WeakStrong
import LatticeProb.Bonanno.LQGMetric.Field.ExistGM
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence
import LatticeProb.Bonanno.LQGMetric.Statement.Thm11
import LatticeProb.Bonanno.LQGMetric.Statement.Thm12

/-!
# GM §1.4: proof of Theorems 1.1 and 1.2 from Theorem 1.9 (rows 17, 20, 23–25 of M1)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Theorems 1.1, 1.2, 1.8 assuming Theorem 1.9, l. 582–593:

* `gm_S1_15` (l. 583–586): any two strong metrics agree up to a deterministic constant
  (GM (1.15) for both, then GM Theorem 1.9 = `Blueprint.GMWeakUniqueness`).
* `gm_S1_16_of_measurable` (l. 588, with DEC-A D-A2 (i)): DFGPS Theorem 1.2 is stated with
  DFGPS's normalization `aEpsDF` (l. 285 of DFGPS); since `𝔞_ε/𝔞^{DF}_ε` is a median of the
  crossing distance of `(𝔞^{DF}_ε)⁻¹ D^ε_h`, along a further subsequence it converges to some
  `κ₀ > 0` (GM.S1.17a), and the subsequential limit for GM's `𝔞_ε` is `κ₀⁻¹ D`, again a weak metric
  (GM.S1.7).
* `gm_S1_19` (l. 589–591): two strong metrics whose crossing distance has median 1 are equal
  (GM.S1.15 gives `D = C D'`; the median of `D'_h(L,R)` is unique by GM.S1.18′, so `C = 1`).
* `theorem12_of_measurable`, `theorem11_of_theorem12` (l. 588–593): every subsequential limit is
  the same strong metric `D*` (normalized by median 1, GM.S1.17b), and the sub-subsequence
  principle GM.S1.20 gives convergence along `ε → 0⁺`.

The one field-layer input not yet imported is the measurability of the LFPP crossing
(`hmeas`, F.MEAS, task P2-LFPP); `LQGMetric/Assembly/M1.lean` plugs it in.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM

/-- the crossing distance of `[0,1]²` of a continuous metric is positive -/
lemma crossFn_pos_contMetric (D : ContMetric) : 0 < crossFn D.1 := by
  have hK : IsCompact (leftSide ×ˢ rightSide) := isCompact_leftSide.prod isCompact_rightSide
  obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, hpe⟩ :=
    (hK.image D.1.continuous).sInf_mem (crossSet_nonempty.image _)
  have huv : u ≠ v := fun e => by
    have h1 : u.re = 0 := hu.1
    have h2 : v.re = 1 := hv.1
    rw [e] at h1
    linarith
  show 0 < sInf _
  rw [← hpe]
  exact cm_pos_of_ne D huv

/-- DFGPS's `𝔞_ε` is nonnegative (the crossing distance is) -/
lemma aEpsDF_nonneg (ξ ε : ℝ) : 0 ≤ Blueprint.aEpsDF ξ ε := by
  refine Real.sInf_nonneg fun m hm => ?_
  by_contra hneg
  have he : {x | Blueprint.lfppCrossIn ξ ε x ≤ m} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx =>
      hneg (le_trans ENNReal.toReal_nonneg (show Blueprint.lfppCrossIn ξ ε x ≤ m from hx))
  have hm' : (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {x | Blueprint.lfppCrossIn ξ ε x ≤ m} := hm
  rw [he, measure_empty] at hm'
  exact absurd hm' (not_le.2 inv_two_pos')

lemma isGFFPlusCont_of_bdd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) : IsGFFPlusCont h P := by
  obtain ⟨hm, f, hfm, -, hg⟩ := hh
  exact ⟨hm, f, hfm, hg⟩

/-- `TendstoInProbLU` under eventual equality of the sequence and equality of the limit -/
lemma tendstoInProbLU_congr' {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' : ι → Ω → ℂ × ℂ → ℝ} {l : Filter ι} {Y : Ω → ℂ × ℂ → ℝ}
    (hX : TendstoInProbLU P X l Y) (hXX : ∀ᶠ i in l, X i = X' i) :
    TendstoInProbLU P X' l Y := by
  intro R hR δ hδ
  refine (hX R hR δ hδ).congr' ?_
  filter_upwards [hXX] with i hi
  rw [hi]

/-- **GM.S1.15** (GM l. 583–586): two strong γ-LQG metrics agree up to a deterministic
constant: GM (1.15) makes both weak metrics with `𝔠_r = r^{ξQ}`; then GM Theorem 1.9. -/
theorem gm_S1_15 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (h19 : Blueprint.GMWeakUniqueness)
    {D D' : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) (hD' : IsStrongLQGMetric γ D') :
    ∃ C : ℝ, 0 < C ∧ EqSmulAS D D' C := by
  obtain ⟨C, hC, H⟩ := h19 γ hγ hγ2 D D' _ (gm_eq1_15 hγ hD) (gm_eq1_15 hγ hD')
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh
  exact H P h hh

/-- **GM.S1.19** (GM l. 589–591): two strong metrics whose left–right crossing distance of
`[0,1]²` has median `1` (for the normalized GFF) are a.s. equal. -/
theorem gm_S1_19 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (h19 : Blueprint.GMWeakUniqueness)
    {D D' : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) (hD' : IsStrongLQGMetric γ D')
    (hm : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → IsMedian (P.map fun ω => crossFn (D (h ω)).1) 1)
    (hm' : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P →
      IsMedian (P.map fun ω => crossFn (D' (h ω)).1) 1) :
    EqSmulAS D D' 1 := by
  obtain ⟨C, hC, H⟩ := gm_S1_15 hγ hγ2 h19 hD hD'
  obtain ⟨Ω, _, P, _, h, hh⟩ := existsNormalizedGFF
  have hZm' : Measurable fun ω => crossFn (D' (h ω)).1 :=
    measurable_crossFn_contMetric.comp (hD'.measurable.comp hh.1.measurable)
  set μ := P.map fun ω => crossFn (D' (h ω)).1 with hμ
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hZm'.aemeasurable).2 ‹_›
  have hU : lowerMedianLaw μ = upperMedianLaw μ :=
    lowerMedianLaw_eq_upperMedianLaw_of_noGap (gm_S1_18 hγ (gm_eq1_15 hγ hD') P h hh)
  have hmap : P.map (fun ω => crossFn (D (h ω)).1) = μ.map (fun x => C * x) := by
    rw [hμ, Measure.map_map (measurable_const_mul C) hZm']
    refine Measure.map_congr ?_
    filter_upwards [H P h (isGFFPlusCont_of_normalized hh)] with ω hω
    have e : (⇑(D (h ω)).1) = C • ⇑(D' (h ω)).1 := funext fun p => hω p.1 p.2
    simp only [Function.comp_apply]
    rw [e, crossFn_smul hC.le]
  have hC1 : C = 1 := eq_one_of_isMedian_map_mul hU (hm' P h hh) hC (hmap ▸ hm P h hh)
  subst hC1
  intro Ω' _ P' _ h' hh'
  exact H P' h' hh'

/-- **GM.S1.16′** (GM l. 588; DEC-A D-A2 (i)), given the measurability of the LFPP crossing:
DFGPS Theorem 1.2 with GM's normalization `𝔞_ε`. -/
theorem gm_S1_16_of_measurable
    (hmeas : ∀ ξ ε : ℝ, 0 < ε → AEMeasurable (lfppCross ξ ε) normGFFLaw)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (h12 : Blueprint.DFGPSExistence)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          TendstoInProbLU P
            (fun n ω => (aEps (xiGamma γ) (ε (φ n)))⁻¹ • lfppDist (xiGamma γ) (ε (φ n)) (h ω))
            atTop (fun ω => (D (h ω)).1) := by
  obtain ⟨D, c, hD, φ, hφ, hconv⟩ := h12 γ hγ hγ2 ε hε hε0
  set ξ := xiGamma γ with hξ
  set b : ℕ → ℝ := fun n => Blueprint.aEpsDF ξ (ε (φ n)) with hb
  set κ : ℕ → ℝ := fun n => (b n)⁻¹ * aEps ξ (ε (φ n)) with hκdef
  have hb0 : ∀ n, 0 ≤ b n := fun n => aEpsDF_nonneg _ _
  -- the medians `κ_n`, computed for one normalized GFF
  obtain ⟨Ω, _, P, _, h, hh⟩ := existsNormalizedGFF
  set X : ℕ → Ω → ℂ × ℂ → ℝ := fun n ω => (b n)⁻¹ • lfppDist ξ (ε (φ n)) (h ω) with hXdef
  have hT : TendstoInProbLU P X atTop (fun ω => (D (h ω)).1) :=
    hconv P h (isGFFPlusBddCont_of_normalized hh)
  have hA := fun n => gm_S1_16a_of_measurable hmeas (ξ := ξ) (hε (φ n)) P h hh
  have hcX : ∀ n ω, crossFn (X n ω) = (b n)⁻¹ * crossFn (lfppDist ξ (ε (φ n)) (h ω)) :=
    fun n ω => crossFn_smul (inv_nonneg.2 (hb0 n)) _
  have hX0 : ∀ n ω p, 0 ≤ X n ω p := fun n ω p =>
    mul_nonneg (inv_nonneg.2 (hb0 n)) ENNReal.toReal_nonneg
  have hXm : ∀ n, AEMeasurable (fun ω => crossFn (X n ω)) P := fun n => by
    simp only [hcX]
    exact (hA n).1.const_mul _
  have hmed : ∀ n, IsMedian (P.map fun ω => crossFn (X n ω)) (κ n) := by
    intro n
    have hmono : Monotone fun x : ℝ => (b n)⁻¹ * x :=
      fun x y hxy => mul_le_mul_of_nonneg_left hxy (inv_nonneg.2 (hb0 n))
    have := IsMedian.map_monotone hmono (measurable_const_mul _) (hA n).2
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_const_mul _).aemeasurable
      (hA n).1] at this
    simpa only [hcX, Function.comp_def] using this
  have hYm : Measurable fun ω => crossFn (D (h ω)).1 :=
    measurable_crossFn_contMetric.comp (hD.measurable.comp hh.1.measurable)
  obtain ⟨ψ, hψ, κ₀, hκ₀, hκ⟩ := gm_S1_17a P X (fun ω => (D (h ω)).1) κ hX0
    (fun ω p => cm_nonneg _ p) hXm hYm.aemeasurable hT hmed
    (Eventually.of_forall fun ω => crossFn_pos_contMetric _)
  have hpos : ∀ᶠ n in atTop, 0 < κ (ψ n) := hκ.eventually (lt_mem_nhds hκ₀)
  -- the limit for GM's normalization is `κ₀⁻¹ D`
  refine ⟨smulMetric κ₀⁻¹ (inv_pos.2 hκ₀) D, fun r => κ₀⁻¹ * c r, gm_s1_7 hD _, φ ∘ ψ,
    hφ.comp hψ, ?_⟩
  intro Ω' _ P' _ h' hh'
  have hT' := hconv P' h' hh'
  have hTψ : TendstoInProbLU P'
      (fun n ω => (b (ψ n))⁻¹ • lfppDist ξ (ε (φ (ψ n))) (h' ω)) atTop
      (fun ω => (D (h' ω)).1) :=
    fun R hR δ hδ => (hT' R hR δ hδ).comp hψ.tendsto_atTop
  have hS := gm_tip_smul_of_aemeasurable P' _ atTop _ (fun n => (κ (ψ n))⁻¹) κ₀⁻¹
    (fun ω => (D (h' ω)).1.continuous)
    (fun p => ((continuous_eval_const p).measurable.comp
      (measurable_subtype_coe.comp (hD.measurable.comp hh'.1))).aemeasurable)
    hTψ ((hκ.inv₀ hκ₀.ne'))
  refine tendstoInProbLU_congr' hS ?_
  filter_upwards [hpos] with n hn
  funext ω
  have hbn : b (ψ n) ≠ 0 := by
    intro h0
    simp only [hκdef, h0, inv_zero, zero_mul, lt_irrefl] at hn
  have han : aEps ξ (ε (φ (ψ n))) ≠ 0 := by
    intro h0
    simp only [hκdef, h0, mul_zero, lt_irrefl] at hn
  simp only [Function.comp_apply, hκdef, smul_smul]
  congr 1
  field_simp

/-- **GM Theorem 1.2** (GM l. 582–593), given GM Theorem 1.9, DFGPS Theorems 1.2 and 1.5, and
the measurability of the LFPP crossing. -/
theorem theorem12_of_measurable
    (hmeas : ∀ ξ ε : ℝ, 0 < ε → AEMeasurable (lfppCross ξ ε) normGFFLaw)
    (h19 : Blueprint.GMWeakUniqueness) (h12 : Blueprint.DFGPSExistence)
    (h15 : Blueprint.DFGPSScaling) : Theorem12 := by
  intro γ hγ hγ2
  have hS16 := gm_S1_16_of_measurable hmeas hγ hγ2 h12
  have hS17b := gm_S1_17b_of_measurable hmeas (γ := γ)
  -- `D*`: the limit along `ε_n = 1/(n+1)` (GM l. 588–590)
  obtain ⟨D, c, hD, φ, hφ, hconv⟩ := hS16 (fun n => 1 / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hDs := gm_l1_10 hγ hγ2 h19 h15 hD
  refine ⟨⟨D, hDs, ?_⟩, fun D₁ D₂ h1 h2 => ?_⟩
  · intro Ω _ P _ h hh
    refine gm_s1_20 P _ _ fun ε hε hε0 => ?_
    obtain ⟨D', c', hD', φ', hφ', hconv'⟩ := hS16 ε hε hε0
    have hD's := gm_l1_10 hγ hγ2 h19 h15 hD'
    have heq : EqSmulAS D' D 1 := gm_S1_19 hγ hγ2 h19 hD's hDs
      (hS17b D' hD'.measurable (fun n => ε (φ' n)) (fun n => hε _) hconv')
      (hS17b D hD.measurable (fun n => 1 / ((φ n : ℝ) + 1)) (fun n => by positivity) hconv)
    refine ⟨φ', hφ', gm_tip_congr P _ atTop _ _ (hconv' P h hh) ?_⟩
    filter_upwards [heq P h (isGFFPlusCont_of_bdd hh)] with ω hω
    funext p
    rw [hω p.1 p.2, one_mul]
  · obtain ⟨C, hC, H⟩ := gm_S1_15 hγ hγ2 h19 h1 h2
    refine ⟨C, hC, ?_⟩
    intro Ω _ P _ h hh
    exact H P h hh

/-- **GM Theorem 1.1** from Theorem 1.2 (GM l. 593): the limit is `D*_h`, a measurable function
of `h`. -/
theorem theorem11_of_theorem12 (H : Theorem12) : Theorem11 := by
  intro γ hγ hγ2 Ω _ P _ h hh
  obtain ⟨⟨D, hD, hconv⟩, -⟩ := H γ hγ hγ2
  exact ⟨fun ω => (D (h ω)).1, Eventually.of_forall fun ω => (D (h ω)).2.toIsMetricFn,
    ⟨fun g => (D g).1, measurable_subtype_coe.comp hD.measurable, ae_of_all _ fun _ => rfl⟩,
    hconv P h hh⟩

end GM
end LQGMetric
