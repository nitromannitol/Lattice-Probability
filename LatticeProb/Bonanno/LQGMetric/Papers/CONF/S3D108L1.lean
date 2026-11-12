/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K5
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.ZBCM

/-!
# Cameron–Martin for the zero-boundary GFF extended by `0` (`CONFZBShiftAC`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), C:667–669 and
C:1239–1241: "adding a smooth compactly supported function to `h` affects its law in an absolutely
continuous way". The open node `CONFZBShiftAC U φ` (S3D108K5) is proved here for the shifts it is
true for: `φ = F` a test function with `supp F ⊆ U`, `U` bounded (`confZBShiftAC_of_test`).

The node is false for general `φ ∈ C(ℂ, ℝ)` (e.g. `φ ≠ 0` off `cl U`: `X` vanishes there, `X + tφ`
does not), and for unbounded `U` the covariance `zeroGFFTestCov U (φ 1_U) (ψ 1_U)` of
`IsZBExtField` need not be the `H⁻¹(U)` pairing (admissibility of `φ 1_U` is proved only for
bounded `U`, `admissible_bddOn`). The consumer `confProp2_8_diam_CM` takes `CONFZBShiftAC U (φ i)`
for its bumps `φ i = 1` on `V i`; with `V i ⋐ U` these can be chosen as `testCont F`, `supp F ⊆ U`.

* `zeroGFFTestCov_indicator_cmTest`: **Green's identity** `⟨φ 1_U, ρ_F⟩_{H⁻¹(U)} = ∫ φ F`
  (`ρ_F = −ΔF/(2π)`), from `zbRiesz_cmTestOn` (`zbRiesz U ρ_F = ∇F`) and the Riesz pairing
  `pair_rieszVec`;
* `map_shift_eq_map_tilt`: the law of `X + tF` is the law of `X` under the Cameron–Martin tilt
  `exp(t⟨X, ρ_F⟩ − t²(F, F)_∇/2) · P` (QZ's abstract `map_tiltMeasure_path`, as in
  `Field/CameronMartin.lean` and `Papers/MQ/ZBCM.lean`);
* **`confZBShiftAC_of_test`**: `CONFZBShiftAC U (testCont F)`.

Source: Cameron–Martin theorem (Bogachev, *Gaussian Measures*, Thm 2.4.5; Berestycki–Powell
arXiv:2404.16642, Prop. `lem:CMGFF`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric.CONF

open QuantumZipper QuantumZipper.K3 QuantumZipper.CameronMartin MarkovZB MarkovHarm

section Green

variable {U : Opens ℂ}

/-- `∫ f d(ρ⁺dz) − ∫ f d(ρ⁻dz) = ∫ f ρ` for bounded measurable `ρ` and `f ∈ C_c^∞` -/
lemma integral_mul_bddOn_eq (ρ : BddOn U) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ∫ x, f x ∂(testMeasPos ρ.1) - ∫ x, f x ∂(testMeasNeg ρ.1) = ∫ x, f x * ρ.1 x := by
  obtain ⟨hm, ⟨C, hC⟩, -⟩ := ρ.2
  have hfi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  rw [integral_testMeasPos_K3 hm, integral_testMeasNeg_K3 hm, ← integral_sub]
  · congr 1; funext x; rw [← sub_mul, max_sub_max_neg_K3, mul_comm]
  · refine hfi.bdd_mul (c := |C|) (hm.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_max_le_max_abs_abs.trans (max_le (hC x) (by rw [abs_zero]; exact (abs_nonneg _).trans (hC x)))).trans (le_abs_self C)
  · refine hfi.bdd_mul (c := |C|) (hm.neg.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_max_le_max_abs_abs.trans (max_le (by rw [abs_neg]; exact hC x) (by rw [abs_zero]; exact (abs_nonneg _).trans (hC x)))).trans
      (le_abs_self C)

lemma zbAdmissible_of_bounded (hU : Bornology.IsBounded (U : Set ℂ)) : ZBAdmissible U :=
  fun φ => admissible_bddOn hU φ.toBddOn

/-- **Green's identity on `U`**: `⟨φ 1_U, ρ_F⟩_{H⁻¹(U)} = ∫ φ F` for `F ∈ C_c^∞(U)`,
`ρ_F = −ΔF/(2π)` -/
theorem zeroGFFTestCov_indicator_cmTest (hU : Bornology.IsBounded (U : Set ℂ))
    (hne : (U : Set ℂ).Nonempty) (φ : TestC) (F : zsSub U) :
    zeroGFFTestCov U ((U : Set ℂ).indicator φ) (cmTestOn F) = ∫ x, φ x * F.1 x := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  have hadm := zbAdmissible_of_bounded hU
  have hpos := exists_pos_energy_zeroSpace_m7d U.isOpen hne
  obtain ⟨h1, h2⟩ : IsAdmissibleDual U (zeroSpace U) (testMeasPos ((U : Set ℂ).indicator φ)) ∧
      IsAdmissibleDual U (zeroSpace U) (testMeasNeg ((U : Set ℂ).indicator φ)) :=
    admissible_bddOn hU (extZeroTest U φ)
  obtain ⟨h3, h4⟩ := hadm (cmTestOn F)
  have hR : ⟪rieszVec U (zeroSpace U) (testMeasPos ((U : Set ℂ).indicator φ)) -
      rieszVec U (zeroSpace U) (testMeasNeg ((U : Set ℂ).indicator φ)), zbRiesz U (cmTestOn F)⟫ =
      ∫ x, φ x * F.1 x := by
    rw [MQ.zbRiesz_cmTestOn_mq hadm F, inner_sub_left, pair_rieszVec hV h1 hpos F.1 F.2,
      pair_rieszVec hV h2 hpos F.1 F.2]
    have := integral_mul_bddOn_eq (extZeroTest U φ) F.2
    refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    change F.1 x * (U : Set ℂ).indicator φ x = φ x * F.1 x
    by_cases hx : x ∈ (U : Set ℂ)
    · rw [indicator_of_mem hx, mul_comm]
    · have : F.1 x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (F.2.2.2 h)
      rw [this, zero_mul, mul_zero]
  rw [← hR]
  unfold zeroGFFTestCov zbRiesz
  rw [dualCov_eq_inner_rieszVec hV h1 h3, dualCov_eq_inner_rieszVec hV h1 h4,
    dualCov_eq_inner_rieszVec hV h2 h3, dualCov_eq_inner_rieszVec hV h2 h4]
  simp only [inner_sub_left, inner_sub_right]
  ring

end Green

section Shift

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Opens ℂ} {X : Ω → DistC}

/-- the pairings `(j, ω) ↦ ⟨X ω, j⟩`, `j ∈ 𝓓(ℂ)` -/
def zbProc (X : Ω → DistC) : TestC → Ω → ℝ := fun j ω => X ω j

lemma pair_addFun_testCont (g : DistC) (F : TestC) (t : ℝ) (j : TestC) :
    addFun g (t • testCont F) j = g j + t * ∫ x, j x * F x := by
  simp only [addFun, ofCont]
  rw [ContinuousLinearMap.add_apply,
    Distribution.ofFun_apply ((t • testCont F).continuous.locallyIntegrable.locallyIntegrableOn _),
    ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change j x * (t * F x) = t * (j x * F x)
  ring

/-- two finite measures on `𝒟'(ℂ)` with the same law of pairings agree -/
lemma measure_distC_ext {μ ν : Measure DistC}
    (h : μ.map (fun (g : DistC) (j : TestC) => g j) = ν.map (fun (g : DistC) (j : TestC) => g j)) :
    μ = ν := by
  have hev : Measurable fun (g : DistC) (j : TestC) => g j := fun _ hs => ⟨_, hs, rfl⟩
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [← Measure.map_apply hev hB, ← Measure.map_apply hev hB, h]

/-- **Cameron–Martin, law form**: the law of `X + tF` is the law of `X` under the tilt
`exp(Xσ − K(σ,σ)/2) · P`, `σ = t δ_{ρ_F}` -/
theorem map_shift_eq_map_tilt (hU : Bornology.IsBounded (U : Set ℂ)) (hne : (U : Set ℂ).Nonempty)
    (hX : IsZBExtField U X P) (F : TestC) (hF : tsupport (F : ℂ → ℝ) ⊆ U) (t : ℝ) :
    P.map (fun ω => addFun (X ω) (t • testCont F)) =
      (tiltMeasure (zbProc X) P (Finsupp.single (cmTest F) t)).map X := by
  have hFz : (F : ℂ → ℝ) ∈ zsSub U := ⟨F.contDiff, F.hasCompactSupport, hF⟩
  set F' : zsSub U := ⟨F, hFz⟩
  have hev : Measurable fun (g : DistC) (j : TestC) => g j := fun _ hs => ⟨_, hs, rfl⟩
  have hmeas : ∀ j, Measurable (zbProc X j) := fun j => (measurable_evalDist j).comp hX.measurable
  have hS : Measurable fun g : DistC => addFun g (t • testCont F) :=
    measurable_addFun.comp (measurable_id.prodMk measurable_const)
  have key := map_tiltMeasure_path hX.gaussian hmeas hX.centered (Finsupp.single (cmTest F) t)
  have hcs : ∀ j : TestC, covShift (zbProc X) P (Finsupp.single (cmTest F) t) j =
      t * ∫ x, j x * F x := fun j => by
    by_cases ht : t = 0
    · simp [ht, covShift]
    simp only [covShift, covK, Finsupp.support_single _ ht, Finset.sum_singleton,
      Finsupp.single_eq_same]
    congr 1
    rw [show (zbProc X j) = fun ω => X ω j from rfl,
      show zbProc X (cmTest F) = fun ω => X ω (cmTest F) from rfl, hX.covariance_eq]
    have e : (U : Set ℂ).indicator (cmTest F : ℂ → ℝ) = cmTestOn F' := by
      funext x
      by_cases hx : x ∈ (U : Set ℂ)
      · rw [indicator_of_mem hx]; rfl
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport fun h =>
          hx ((cmTestOn F').tsupport_subset h)).symm
    rw [e, zeroGFFTestCov_indicator_cmTest hU hne j F']
  refine measure_distC_ext ?_
  rw [Measure.map_map hev hX.measurable, Measure.map_map (f := fun ω => addFun (X ω) (t • testCont F))
    hev (hS.comp hX.measurable)]
  change P.map (fun ω j => addFun (X ω) (t • testCont F) j) =
    (tiltMeasure (zbProc X) P _).map (fun ω j => zbProc X j ω)
  refine Eq.trans ?_ key.symm
  congr 1
  funext ω j
  rw [pair_addFun_testCont, show covShift (fun φ ω => X ω φ) P (Finsupp.single (cmTest F) t) j =
    covShift (zbProc X) P (Finsupp.single (cmTest F) t) j from rfl, hcs]

/-- **`CONFZBShiftAC` for test-function shifts supported in a bounded `U`** -/
theorem confZBShiftAC_of_test (hU : Bornology.IsBounded (U : Set ℂ)) (F : TestC)
    (hF : tsupport (F : ℂ → ℝ) ⊆ U) : CONFZBShiftAC U (testCont F) := by
  intro Ω _ P _ X hX t
  rcases (U : Set ℂ).eq_empty_or_nonempty with he | hne
  · have h0 : t • testCont F = 0 := by
      ext x
      have : F x = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa [he] using hF h
      simp [testCont, this]
    simp only [h0, GM.addFun_zero_eq, Measure.map_id']
    exact Measure.AbsolutelyContinuous.rfl
  have hS : Measurable fun g : DistC => addFun g (t • testCont F) :=
    measurable_addFun.comp (measurable_id.prodMk measurable_const)
  have hmeas : ∀ j, Measurable (zbProc X j) := fun j => (measurable_evalDist j).comp hX.measurable
  rw [Measure.map_map hS hX.measurable]
  change P.map X ≪ P.map (fun ω => addFun (X ω) (t • testCont F))
  rw [map_shift_eq_map_tilt hU hne hX F hF t]
  refine Measure.AbsolutelyContinuous.map ?_ hX.measurable
  exact withDensity_absolutelyContinuous'
    (measurable_tiltDensity hX.gaussian hmeas _).real_toNNReal.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
      exact Real.exp_pos _)

end Shift

section Prop28

open Blueprint

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

end Prop28

end LQGMetric.CONF
