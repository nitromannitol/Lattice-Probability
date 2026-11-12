/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.FieldAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Statement.Thm12
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Field-layer helpers for GM §1.4 (GM.S1.16a, GM.S1.18′)

* `isWholePlaneGFF_id_map`, `normGFFLaw_eq`: `normGFFLaw` is the law of every normalized
  whole-plane GFF (law uniqueness `CircleAvg.map_eq_of_isNormalizedWPGFF`, tasks P2-FINV,
  P2-FCIRC);
* `measure_addFun_preimage_eq_zero` (DEC-A node `GFF.CM-wp`, null-set form): for `φ ∈ 𝓓(ℂ)` with
  zero average over `∂𝔻` and `h` a normalized whole-plane GFF, `P[h ∈ A] = 0 ⇒ P[h + φ ∈ A] = 0`.
  Proof: both `h` and `h + φ` are normalized, hence `sigma0`-measurable functions of their
  mean-zero pairings (`GFFLaw` recentering), whose laws are mutually absolutely continuous by the
  whole-plane Cameron–Martin theorem `lawPair0_addFun_ac` (Bogachev, *Gaussian Measures*,
  Thm 2.4.5; Berestycki–Powell, arXiv:2404.16642, Prop. `lem:CMGFF`);
* `exists_noGap_test`: the test function `f = φ − (φ_1(0)/ψ_1(0)) ψ` of DEC-A D-A2 (iii)
  (`φ ≡ 1` near `L`, `ψ ≥ 0` a bump at `−1`), with `f ≥ 1` within distance `1/4` of the left side
  `L` and zero average over `∂𝔻`;
* `xiGamma_pos`: `ξ > 0` for `γ > 0`.

Sources: DEC-A D-A2 (iii) (`decisions/DEC-A.md`); the test-function construction and the
positivity of a circle average are own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM
open GFFInv

/-- the law of a whole-plane GFF, as a field on `𝒟'(ℂ)` -/
theorem isWholePlaneGFF_id_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsWholePlaneGFF id (P.map h) where
  measurable := measurable_id
  gaussian := ⟨fun I => by
    have hm : Measurable fun g : DistC => I.restrict fun φ : TestC0 => g φ.1 :=
      measurable_pi_iff.2 fun _ => GFFInv.measurable_pair _
    refine ⟨hm.aemeasurable, ?_⟩
    have e := Measure.map_map hm hh.measurable (μ := P)
    change IsGaussian ((P.map h).map fun g : DistC => I.restrict fun φ : TestC0 => g φ.1)
    rw [e]
    exact (hh.gaussian.hasGaussianLaw I).isGaussian_map⟩
  centered := fun φ => by
    have e := integral_map (μ := P) hh.measurable.aemeasurable
      (f := fun g : DistC => g φ.1) (GFFInv.measurable_pair _).aestronglyMeasurable
    change ∫ g, g φ.1 ∂(P.map h) = 0
    rw [e]
    exact hh.centered φ
  covariance_eq := fun φ ψ => by
    have e := covariance_map (μ := P) (X := fun g : DistC => g φ.1) (Y := fun g : DistC => g ψ.1)
      (GFFInv.measurable_pair _).aestronglyMeasurable
      (GFFInv.measurable_pair _).aestronglyMeasurable hh.measurable.aemeasurable
    change cov[fun g : DistC => g φ.1, fun g : DistC => g ψ.1; P.map h] = _
    rw [e]
    exact hh.covariance_eq φ ψ

/-- `normGFFLaw` is the law of any normalized whole-plane GFF (FINV + FCIRC law uniqueness,
`CircleAvg.map_eq_of_isNormalizedWPGFF`). -/
theorem normGFFLaw_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) : normGFFLaw = P.map h := by
  have hex : ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧ IsNormalizedWPGFF id μ :=
    ⟨P.map h, (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 ‹_›,
      isWholePlaneGFF_id_map hh.1, (ae_map_iff hh.1.measurable.aemeasurable
        (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hh.2⟩
  rw [normGFFLaw, dite_eq_left_of_eq_true (eq_true hex)]
  have := CircleAvg.map_eq_of_isNormalizedWPGFF hex.choose_spec.2 hh
  rwa [Measure.map_id] at this

lemma ofCont_zero_eq : ofCont 0 = 0 := by
  ext φ
  simp [ofCont]

lemma addFun_zero_eq (g : DistC) : addFun g 0 = g := by
  simp [addFun, ofCont_zero_eq]

lemma isGFFPlusCont_of_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) : IsGFFPlusCont h P :=
  ⟨hh.1.measurable, fun _ => 0, measurable_const, by simpa [ofCont_zero_eq] using hh.1⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(h + φ)_1(0) = h_1(0) + (classical circle average of φ)` a.s. -/
lemma ae_circleAvg_addFun {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (f : C(ℂ, ℝ)) :
    ∀ᵐ ω ∂P, ∀ c, circleAvg (addConst (addFun (h ω) f) c) 1 0 =
      circleAvg (h ω) 1 0 + c + Real.circleAverage f 0 1 := by
  filter_upwards [CircleAvg.ae_tendsto_mollAvg hh 0 one_pos] with ω ⟨a, ha⟩ c
  have ha' : Tendsto (fun n => CircleAvg.mollAvg
      (addConst (addFun (h ω) f) c - ofCont f) n 0 1) atTop (𝓝 (a + c)) := by
    have e : addConst (addFun (h ω) f) c - ofCont f = addConst (h ω) c := by
      simp only [addConst, addFun]; abel
    rw [e]
    simp_rw [CircleAvg.mollAvg_addConst]
    exact ha.add_const c
  rw [(CircleAvg.circleAvg_eq_sub_ofCont_add ha').2, CircleAvg.circleAvg_eq_of_tendsto ha',
    CircleAvg.circleAvg_eq_of_tendsto ha]

lemma addConst_zero_eq (g : DistC) : addConst g 0 = g := GFFLaw.addConst_zero' g

/-- A `sigma0`-measurable map fixing every field with `N g = 0` at which `N` is equivariant
(`N` = any measurable normalization; the construction of `GFFLaw.map_eq_of_normalized_ae`). -/
lemma exists_sigma0_fix {N : DistC → ℝ} (hNm : Measurable N) :
    ∃ F : DistC → DistC, Measurable[GFFLaw.sigma0] F ∧
      ∀ g, (∀ c, N (addConst g c) = N g + c) → N g = 0 → F g = g := by
  have hρ : ∫ x, (bumpTest 0 0 : TestC) x = 1 := GFFLaw.integral_bumpTest 0 0
  have hm : Measurable (GFFLaw.equivNorm (bumpTest 0 0) N) :=
    (measurable_pair _).add (hNm.comp ((GFFLaw.measurable_recenter_sigma0 hρ).mono
      (by rw [GFFLaw.sigma0, ← measurable_iff_comap_le]
          exact measurable_pi_iff.2 fun φ => measurable_pair φ.1) le_rfl))
  have hK : Measurable fun g => addConst g (-(GFFLaw.equivNorm (bumpTest 0 0) N g)) :=
    measurable_distC_iff.2 fun ψ => by
      simp only [addConst_apply]
      exact (measurable_pair ψ).add (hm.neg.const_mul _)
  refine ⟨(fun g => addConst g (-(GFFLaw.equivNorm (bumpTest 0 0) N g))) ∘
    GFFLaw.recenter (bumpTest 0 0), hK.comp (GFFLaw.measurable_recenter_sigma0 hρ),
    fun g h1 h2 => ?_⟩
  have hg : GFFLaw.equivNorm (bumpTest 0 0) N g = 0 := (GFFLaw.equivNorm_eq h1).trans h2
  simp only [Function.comp_apply, GFFLaw.recenter, GFFLaw.equivNorm_addConst hρ,
    GFFLaw.addConst_addConst, hg]
  rw [show -g (bumpTest 0 0) + -(0 + -g (bumpTest 0 0)) = 0 by ring, GFFLaw.addConst_zero']

/-- Transfer of null events through `sigma0`-measurable reconstructions. -/
lemma measure_preimage_eq_zero_of_sigma0 {F : DistC → DistC} (hF : Measurable[GFFLaw.sigma0] F)
    {X Y : Ω → DistC} (hX : Measurable fun ω => pair0 (X ω))
    (hY : Measurable fun ω => pair0 (Y ω))
    (hac : P.map (fun ω => pair0 (Y ω)) ≪ P.map (fun ω => pair0 (X ω)))
    (hfX : ∀ᵐ ω ∂P, F (X ω) = X ω) (hfY : ∀ᵐ ω ∂P, F (Y ω) = Y ω)
    {A : Set DistC} (hA : MeasurableSet A) (h0 : P (X ⁻¹' A) = 0) : P (Y ⁻¹' A) = 0 := by
  obtain ⟨T, hT, hTS⟩ := hF hA
  have e : ∀ Z : Ω → DistC, (fun ω => F (Z ω)) ⁻¹' A = (fun ω => pair0 (Z ω)) ⁻¹' T := by
    intro Z
    ext ω
    have := congrArg (fun S : Set DistC => Z ω ∈ S) hTS
    simp only [mem_preimage] at this ⊢
    exact (Iff.of_eq this).symm
  have hXT : P ((fun ω => pair0 (X ω)) ⁻¹' T) = 0 := by
    rw [← e X, ← h0]
    exact measure_congr (hfX.mono fun ω hω => by simp only [mem_preimage, hω])
  have hYT := hac (by rw [Measure.map_apply hX hT]; exact hXT)
  rw [Measure.map_apply hY hT, ← e Y] at hYT
  rw [← hYT]
  exact measure_congr (hfY.mono fun ω hω => by simp only [mem_preimage, hω])

/-- **Cameron–Martin on `𝒟'(ℂ)` for the normalized whole-plane GFF** (DEC-A node `GFF.CM-wp`,
null-set form): for a test function `φ` with zero classical average over `∂𝔻`, a null event for
`h` is null for `h + φ`. Proof: the field is a `sigma0`-measurable function of its mean-zero
pairings at both `h` and `h + φ` (both are normalized; `GFFLaw` recentering), and the laws of the
mean-zero pairings are mutually absolutely continuous (`lawPair0_addFun_ac`). -/
theorem measure_addFun_preimage_eq_zero {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {φ : TestC} (hφ : Real.circleAverage (testCont φ) 0 1 = 0) {A : Set DistC}
    (hA : MeasurableSet A) (h0 : P (h ⁻¹' A) = 0) :
    P ((fun ω => addFun (h ω) (testCont φ)) ⁻¹' A) = 0 := by
  obtain ⟨F, hF, hfix⟩ := exists_sigma0_fix (measurable_circleAvg_left 1 0)
  have hfh : ∀ᵐ ω ∂P, F (h ω) = h ω := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh.1, hh.2] with ω h1 h2
    exact hfix _ h1 h2
  have hfh' : ∀ᵐ ω ∂P, F (addFun (h ω) (testCont φ)) = addFun (h ω) (testCont φ) := by
    filter_upwards [ae_circleAvg_addFun hh.1 (testCont φ), hh.2] with ω h1 h2
    have h0' := h1 0
    rw [addConst_zero_eq, h2, hφ] at h0'
    refine hfix _ (fun c => ?_) (by rw [h0']; ring)
    rw [h1 c, h2, hφ, h0']; ring
  exact measure_preimage_eq_zero_of_sigma0 hF (measurable_pair0_comp hh.1)
    (measurable_pair0_addFun hh.1 φ) (lawPair0_addFun_ac hh.1 φ) hfh hfh' hA h0

/-! ### The test function of DEC-A D-A2 (iii) -/

/-- positivity of the circle average over `∂𝔻` of a continuous `g ≥ 0` with `g(-1) > 0` -/
lemma circleAverage_pos_of {g : ℂ → ℝ} (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x)
    (hπ : 0 < g (-1)) : 0 < Real.circleAverage g 0 1 := by
  rw [Real.circleAverage_def, smul_eq_mul]
  refine mul_pos (by positivity) ?_
  set G : ℝ → ℝ := fun θ => g (circleMap 0 1 θ)
  have hG : Continuous G := hg.comp (continuous_circleMap 0 1)
  have hGπ : 0 < G Real.pi := by simpa [G, circleMap, Complex.exp_pi_mul_I] using hπ
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun θ => h0 _)
    (hG.intervalIntegrable _ _)]
  refine ⟨by positivity, ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hG) Real.pi hGπ
  set δ := min ε 1
  have hδ : 0 < δ := lt_min hε one_pos
  have hpi := Real.pi_gt_three
  have hsub : Ioo (Real.pi - δ) (Real.pi + δ) ⊆ Function.support G ∩ Ioc 0 (2 * Real.pi) := by
    intro θ hθ
    have hd : dist θ Real.pi < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, min_le_left ε 1]
    refine ⟨(hball hd).ne', ?_, ?_⟩
    · linarith [hθ.1, min_le_right ε 1]
    · linarith [hθ.2, min_le_right ε 1]
  exact ((Measure.measure_Ioo_pos volume).2 (by linarith)).trans_le (measure_mono hsub)

/-- the bump `≡ 1` on `B̄(i/2, 1)` -/
def bumpNearL : ContDiffBump (Complex.I / 2) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the bump at `-1`, supported in `B(-1, 1/4)` -/
def bumpAtNeg : ContDiffBump (-1 : ℂ) := ⟨8⁻¹, 4⁻¹, by norm_num, by norm_num⟩

lemma exists_near_leftSide {x : ℂ} (hx : Metric.infDist x leftSide ≤ 4⁻¹) :
    ∃ u ∈ leftSide, dist x u < 2⁻¹ :=
  (Metric.infDist_lt_iff ⟨0, by simp [leftSide]⟩).1 (by linarith)

lemma bumpNearL_eq_one {x : ℂ} (hx : Metric.infDist x leftSide ≤ 4⁻¹) : bumpNearL x = 1 := by
  obtain ⟨u, hu, hd⟩ := exists_near_leftSide hx
  refine bumpNearL.one_of_mem_closedBall (Metric.mem_closedBall.2 ?_)
  have hu' : dist u (Complex.I / 2) ≤ 2⁻¹ := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    obtain ⟨h1, h2, h3⟩ := hu
    simp only [Complex.sub_re, Complex.sub_im, h1, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.I_re, Complex.I_im, zero_div, sub_zero, abs_zero, zero_add]
    rw [abs_le]; constructor <;> linarith
  show dist x (Complex.I / 2) ≤ 1
  linarith [dist_triangle x u (Complex.I / 2)]

lemma bumpAtNeg_eq_zero {x : ℂ} (hx : Metric.infDist x leftSide ≤ 4⁻¹) : bumpAtNeg x = 0 := by
  obtain ⟨u, hu, hd⟩ := exists_near_leftSide hx
  refine bumpAtNeg.zero_of_le_dist ?_
  have hu' : 1 ≤ dist u (-1) := by
    rw [Complex.dist_eq]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp [hu.1]
  show 4⁻¹ ≤ dist x (-1)
  linarith [dist_triangle u x (-1), dist_comm x u]

/-- **The test function** `f = φ − (φ_1(0)/ψ_1(0)) ψ` of DEC-A D-A2 (iii) (with the
`1/4`-neighbourhood of `L` in place of the annulus): `f ≥ 1` within distance `1/4` of `L`,
and `f` has zero average over `∂𝔻`. -/
theorem exists_noGap_test : ∃ f₀ : TestC,
    (∀ x, Metric.infDist x leftSide ≤ 4⁻¹ → 1 ≤ f₀ x) ∧
      Real.circleAverage (testCont f₀) 0 1 = 0 := by
  set aL := Real.circleAverage (fun x => bumpNearL x) 0 1
  set aM := Real.circleAverage (fun x => bumpAtNeg x) 0 1
  have haM : 0 < aM := circleAverage_pos_of bumpAtNeg.continuous (fun x => bumpAtNeg.nonneg)
    (by rw [bumpAtNeg.one_of_mem_closedBall (Metric.mem_closedBall_self bumpAtNeg.rIn_pos.le)]; exact one_pos)
  set k := aL / aM
  let F : ℂ → ℝ := fun x => bumpNearL x - k * bumpAtNeg x
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    bumpNearL.contDiff.sub (contDiff_const.mul bumpAtNeg.contDiff)
  have hFs : HasCompactSupport F :=
    bumpNearL.hasCompactSupport.sub (bumpAtNeg.hasCompactSupport.mul_left)
  refine ⟨⟨F, hF, hFs, subset_univ _⟩, fun x hx => ?_, ?_⟩
  · show 1 ≤ bumpNearL x - k * bumpAtNeg x
    rw [bumpNearL_eq_one hx, bumpAtNeg_eq_zero hx]; simp
  · show Real.circleAverage (fun x => bumpNearL x - k * bumpAtNeg x) 0 1 = 0
    have hi1 : CircleIntegrable (fun x => bumpNearL x) 0 1 :=
      bumpNearL.continuous.continuousOn.circleIntegrable zero_le_one
    have hi2 : CircleIntegrable (fun x => k * bumpAtNeg x) 0 1 :=
      (continuous_const.mul bumpAtNeg.continuous).continuousOn.circleIntegrable zero_le_one
    rw [Real.circleAverage_fun_sub hi1 hi2]
    simp_rw [← smul_eq_mul (a := k)]
    rw [Real.circleAverage_fun_smul, smul_eq_mul]
    show aL - aL / aM * aM = 0
    rw [div_mul_cancel₀ _ haM.ne', sub_self]

lemma chiDZZ_pos (γ : ℝ) : 0 < chiDZZ γ := by
  unfold chiDZZ
  split_ifs with h
  · exact h.choose_spec.1
  · norm_num

lemma xiGamma_pos {γ : ℝ} (hγ : 0 < γ) : 0 < xiGamma γ :=
  div_pos hγ (div_pos two_pos (chiDZZ_pos γ))

end GM
end LQGMetric
