/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P16Indep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Cross
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseIndep
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiBlock

/-!
# DDDF (4.44): `P(L_{3,3}(ψ) ≤ l) ≤ P(L_{1,3}(ψ) ≤ l)²` (for DDDF Proposition 16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 836–841, proof of Prop 16 = `Prop:LowerTail`, display
`decaysquare`): "if `L^{(n)}_{3,3}(ψ)` is less than `l`, then both `[0,1] × [0,3]` and
`[2,3] × [0,3]` have a left-right crossing of length `≤ l` and the restrictions of the field to
these two rectangles are independent (if `r₀` [...] is small enough)". Here:
* `PsiSmall Q`: DDDF's "`r₀` small enough", in the form `σ_t ≤ 1/4` for `t ∈ (0,1]` (then the
  kernels of `ψ_{0,n}` at points of the two rectangles see the white noise on the disjoint
  half-planes `Re y < 3/2`, `Re y ≥ 3/2`; `psiKernel_eq_zero_of_far` is DDDF's finite range,
  l. 358);
* `rectLen_13_le_33`, `crossLenIn_shift_le_33`: a crossing of `[0,3]²` contains crossings of
  `[0,1] × [0,3]` and `[2,3] × [0,3]` (`RectCross.exists_sub_crossing`, last visit before the
  first hit);
* `indepFun_psiMN_clamp`: independence (white noise on disjoint sets, then modifications);
* `prob_33_le_sq`: (4.44), the second factor identified by translation invariance
  (`map_psiMN_add`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- DDDF's "`r₀` small enough" (l. 822, 838): `σ_t ≤ 1/4` for `t ∈ (0, 1]`. -/
def PsiSmall (Q : PsiParams) : Prop := ∀ t : ℝ, 0 < t → t ≤ 1 → Q.sigma t ≤ 1 / 4

lemma supportedIn_psiKernelL2_of_far (Q : PsiParams) (hQ : PsiSmall Q) {a b : ℝ} (ha : 0 < a)
    (hb0 : 0 ≤ b) (hb : b ≤ 1) (x : ℂ) {A : Set (ℝ × ℂ)} (hA : MeasurableSet A)
    (hfar : ∀ p : ℝ × ℂ, p ∉ A → 1 / 2 ≤ ‖x - p.2‖) :
    SupportedIn A (Q.psiKernelL2 a b x) := by
  unfold SupportedIn
  rw [ae_restrict_iff' hA.compl]
  filter_upwards [Q.coeFn_psiKernelL2 a b ha x] with p hp hpA
  rw [hp]
  by_cases ht : p.1 ∈ Icc (a ^ 2) (b ^ 2)
  · have ht0 : 0 < p.1 := lt_of_lt_of_le (by positivity) ht.1
    have hb2 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb
    have hs := hQ p.1 ht0 (ht.2.trans hb2)
    exact Q.psiKernel_eq_zero_of_far a b x ht0 (by linarith [hfar p hpA])
  · simp [PsiParams.psiKernel, phiKernel, indicator, Set.mem_prod, ht]

/-- the projection of `ℂ` onto `[0,1] × [0,3]` -/
def clampR (x : ℂ) : ℂ :=
  ((projIcc (0 : ℝ) 1 zero_le_one x.re : ℝ) : ℂ) +
    ((projIcc (0 : ℝ) 3 (by norm_num) x.im : ℝ) : ℂ) * Complex.I

lemma continuous_clampR : Continuous clampR :=
  (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
    (continuous_projIcc.comp Complex.continuous_re))).add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp
      (continuous_projIcc.comp Complex.continuous_im))).mul continuous_const)

lemma clampR_re (x : ℂ) : (clampR x).re = (projIcc (0 : ℝ) 1 zero_le_one x.re : ℝ) := by
  simp [clampR]

lemma mem_rectAB_toSet {a b : ℝ} {z : ℂ} :
    z ∈ (rectAB a b).toSet ↔ z.re ∈ Icc 0 a ∧ z.im ∈ Icc 0 b := by
  simp [rectAB, MarkedRect.toSet, Complex.mem_reProdIm]

lemma mem_rectAB_side₁ {a b : ℝ} {z : ℂ} :
    z ∈ (rectAB a b).side₁ ↔ z.re = 0 ∧ z.im ∈ Icc 0 b := by
  simp [rectAB, MarkedRect.side₁, Complex.mem_reProdIm]

lemma mem_rectAB_side₂ {a b : ℝ} {z : ℂ} :
    z ∈ (rectAB a b).side₂ ↔ z.re = a ∧ z.im ∈ Icc 0 b := by
  simp [rectAB, MarkedRect.side₂, Complex.mem_reProdIm]

lemma clampR_of_mem {x : ℂ} (hx : x ∈ (rectAB 1 3).toSet) : clampR x = x := by
  rw [mem_rectAB_toSet] at hx
  apply Complex.ext <;> simp [clampR, projIcc_of_mem _ hx.1, projIcc_of_mem _ hx.2]

/-- **Independence of `ψ_{0,n}` on `[0,1] × [0,3]` and on `[2,3] × [0,3]`** (DDDF l. 838–839). -/
theorem indepFun_psiMN_clamp (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q)
    (n : ℕ) :
    IndepFun (fun ω x => psiMN Q W P 0 n (clampR x) ω)
      (fun ω x => psiMN Q W P 0 n (clampR x + 2) ω) P := by
  have := hW.isProbabilityMeasure
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set a : ℝ := (2 : ℝ)⁻¹ ^ n
  set b : ℝ := (2 : ℝ)⁻¹ ^ 0
  have ha : 0 < a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hb : b ≤ 1 := by simp [b]
  set A₁ : Set (ℝ × ℂ) := {p | p.2.re < 3 / 2}
  set A₂ : Set (ℝ × ℂ) := {p | 3 / 2 ≤ p.2.re}
  have hm : Measurable fun p : ℝ × ℂ => p.2.re := Complex.measurable_re.comp measurable_snd
  have hA₁ : MeasurableSet A₁ := measurableSet_lt hm measurable_const
  have hA₂ : MeasurableSet A₂ := measurableSet_le measurable_const hm
  let A : Bool → Set (ℝ × ℂ) := fun i => if i then A₁ else A₂
  have hA : Pairwise fun i j => Disjoint (A i) (A j) := by
    rintro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact Set.disjoint_left.2 fun p (h1 : 3 / 2 ≤ p.2.re) (h2 : p.2.re < 3 / 2) => by linarith
    · exact Set.disjoint_left.2 fun p (h1 : p.2.re < 3 / 2) (h2 : 3 / 2 ≤ p.2.re) => by linarith
    · exact absurd rfl hij
  have hre : ∀ x : ℂ, (clampR x).re ∈ Icc (0 : ℝ) 1 := fun x => by
    rw [clampR_re]; exact (projIcc (0 : ℝ) 1 zero_le_one x.re).2
  have hs₁ : ∀ x : ℂ, SupportedIn (A true) (Q.psiKernelL2 a b (clampR x)) := fun x =>
    supportedIn_psiKernelL2_of_far Q hQ ha hb0 hb _ hA₁ fun p hp => by
      have hp' : 3 / 2 ≤ p.2.re := not_lt.1 hp
      have h1 := Complex.abs_re_le_norm (clampR x - p.2)
      rw [Complex.sub_re] at h1
      have := hre x
      rw [abs_le] at h1
      linarith [h1.1, this.2]
  have hs₂ : ∀ x : ℂ, SupportedIn (A false) (Q.psiKernelL2 a b (clampR x + 2)) := fun x =>
    supportedIn_psiKernelL2_of_far Q hQ ha hb0 hb _ hA₂ fun p hp => by
      have hp' : p.2.re < 3 / 2 := not_le.1 hp
      have h1 := Complex.abs_re_le_norm (clampR x + 2 - p.2)
      simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat] at h1
      have := hre x
      rw [abs_le] at h1
      linarith [h1.2, this.1]
  have hI := (hW.iIndepFun_of_pairwise_disjoint hA).indepFun (show true ≠ false by decide)
  let Φ₁ : ({f // SupportedIn (A true) f} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨Q.psiKernelL2 a b (clampR x), hs₁ x⟩
  let Φ₂ : ({f // SupportedIn (A false) f} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨Q.psiKernelL2 a b (clampR x + 2), hs₂ x⟩
  have hΦ₁ : Measurable Φ₁ := measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  have hΦ₂ : Measurable Φ₂ := measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  have h3 := hI.comp hΦ₁ hΦ₂
  exact indepFun_modification
    (X := fun x ω => Real.sqrt Real.pi * W (Q.psiKernelL2 a b (clampR x)) ω)
    (Z := fun x ω => Real.sqrt Real.pi * W (Q.psiKernelL2 a b (clampR x + 2)) ω)
    (fun x => (hW.measurable _).const_mul _) (fun x => hψ.meas _)
    (fun x => (hW.measurable _).const_mul _) (fun x => hψ.meas _)
    (fun x => hψ.ae_eq _) (fun x => hψ.ae_eq _) h3

/-- a crossing of `[0,3]²` contains a crossing of `[z₀, z₀ + 1] × [0,3]` -/
theorem sub_crossing_33 {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ + 1 ≤ 3) {P : ℝ → ℂ}
    (hP : AdmPath (rectAB 3 3).toSet (rectAB 3 3).side₁ (rectAB 3 3).side₂ P) :
    ∃ z w, IsPiecewiseC1Path P z w ∧ ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, s ≤ t ∧
      (P s).re = z₀ ∧ (P t).re = z₀ + 1 ∧
      ∀ u ∈ Icc s t, (P u).re ∈ Icc z₀ (z₀ + 1) ∧ (P u).im ∈ Icc 0 3 := by
  obtain ⟨z, hz, w, hw, hPc, hPK⟩ := hP
  rw [mem_rectAB_side₁] at hz
  rw [mem_rectAB_side₂] at hw
  obtain ⟨s, t, h0s, hst, ht1, hfs, hft, hI⟩ := RectCross.exists_sub_crossing
    (f := fun u => (P u).re) zero_le_one
    (Complex.continuous_re.comp_continuousOn hPc.continuousOn) (by linarith : z₀ ≤ z₀ + 1)
    (show (P 0).re ≤ z₀ by rw [hPc.source, hz.1]; exact hz0)
    (show z₀ + 1 ≤ (P 1).re by rw [hPc.target, hw.1]; exact hz1)
  refine ⟨z, w, hPc, s, ⟨h0s, hst.trans ht1⟩, t, ⟨h0s.trans hst, ht1⟩, hst, hfs, hft,
    fun u hu => ⟨hI u hu, ?_⟩⟩
  exact (mem_rectAB_toSet.1 (hPK u ⟨h0s.trans hu.1, hu.2.trans ht1⟩)).2

/-- `L_{1,3} ≤ L_{3,3}` (a crossing of `[0,3]²` crosses `[0,1] × [0,3]`) -/
theorem rectLen_13_le_33 (f : ℂ → ℝ) : rectLen ξ f (rectAB 1 3) ≤ rectLen ξ f (rectAB 3 3) := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, w, hPc, s, hs, t, ht, hst, h1, h2, h3⟩ :=
    sub_crossing_33 (z₀ := 0) le_rfl (by norm_num) hP
  refine crossLenIn_le_of_sub hPc hs ht (fun u hu => ?_) ?_ ?_
  · rw [uIcc_of_le hst] at hu
    have := h3 u hu
    rw [mem_rectAB_toSet]
    exact ⟨by simpa using this.1, this.2⟩
  · rw [mem_rectAB_side₁]; exact ⟨h1, (h3 s ⟨le_rfl, hst⟩).2⟩
  · rw [mem_rectAB_side₂]; exact ⟨by simpa using h2, (h3 t ⟨hst, le_rfl⟩).2⟩

/-- the crossing length of `[2,3] × [0,3]`, written on `[0,1] × [0,3]` with the shifted field,
is at most `L_{3,3}` -/
theorem crossLenIn_shift_le_33 (f : ℂ → ℝ) :
    crossLenIn ξ (fun x => f (x + 2)) (rectAB 1 3).toSet (rectAB 1 3).side₁ (rectAB 1 3).side₂ ≤
      rectLen ξ f (rectAB 3 3) := by
  rw [← crossLenIn_image_add]
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, w, hPc, s, hs, t, ht, hst, h1, h2, h3⟩ :=
    sub_crossing_33 (z₀ := 2) (by norm_num) (by norm_num) hP
  refine crossLenIn_le_of_sub hPc hs ht (fun u hu => ?_) ?_ ?_
  · rw [uIcc_of_le hst] at hu
    have := h3 u hu
    refine ⟨P u - 2, ?_, by simp⟩
    rw [mem_rectAB_toSet]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith [this.1.1, this.1.2, this.2.1, this.2.2]
  · have := h3 s ⟨le_rfl, hst⟩
    refine ⟨P s - 2, ?_, by simp⟩
    rw [mem_rectAB_side₁]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith [this.2.1, this.2.2]
  · have := h3 t ⟨hst, le_rfl⟩
    refine ⟨P t - 2, ?_, by simp⟩
    rw [mem_rectAB_side₂]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith [this.2.1, this.2.2]

/-- **DDDF (4.44)** (`decaysquare`, l. 840): `P(L_{3,3}(ψ) ≤ m) ≤ P(L_{1,3}(ψ) ≤ m)²`. -/
theorem prob_33_le_sq (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q) (n : ℕ)
    (m : ℝ) :
    P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 3 3) ω ≤ m} ≤
      P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤ m} ^ 2 := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set Y := psiMN Q W P 0 n
  set K := (rectAB 1 3).toSet
  set A := (rectAB 1 3).side₁
  set B := (rectAB 1 3).side₂
  have hK : IsCompact K := MarkedRect.isCompact_toSet _
  set S : Set ℝ≥0∞ := {v | v.toReal ≤ m}
  have hS : MeasurableSet S := measurableSet_le ENNReal.measurable_toReal measurable_const
  obtain ⟨T, hT, hTiff⟩ := exists_set_crossLenIn (ξ := ξ) hK A B hS
  set X₁ : Ω → ℂ → ℝ := fun ω x => Y (clampR x) ω
  set X₂ : Ω → ℂ → ℝ := fun ω x => Y (clampR x + 2) ω
  have hX₁c : ∀ ω, Continuous (X₁ ω) := fun ω => (hψ.cont ω).comp continuous_clampR
  have hX₂c : ∀ ω, Continuous (X₂ ω) := fun ω =>
    (hψ.cont ω).comp (continuous_clampR.add continuous_const)
  set E₁ := {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m}
  set E₂ := {ω | crossLenIn ξ (fun x => Y (x + 2) ω) K A B ∈ S}
  have hE₁ : E₁ = X₁ ⁻¹' T := by
    ext ω
    have e : crossLenIn ξ (fun x => Y x ω) K A B = crossLenIn ξ (X₁ ω) K A B :=
      crossLenIn_congr' fun x hx => by simp only [X₁, clampR_of_mem hx]
    show (crossLenIn ξ (fun x => Y x ω) K A B).toReal ≤ m ↔ X₁ ω ∈ T
    rw [e]; exact hTiff _ (hX₁c ω)
  have hE₂ : E₂ = X₂ ⁻¹' T := by
    ext ω
    have e : crossLenIn ξ (fun x => Y (x + 2) ω) K A B = crossLenIn ξ (X₂ ω) K A B :=
      crossLenIn_congr' fun x hx => by simp only [X₂, clampR_of_mem hx]
    show crossLenIn ξ (fun x => Y (x + 2) ω) K A B ∈ S ↔ X₂ ω ∈ T
    rw [e]; exact hTiff _ (hX₂c ω)
  have hsub : {ω | lenObs ξ Y (rectAB 3 3) ω ≤ m} ⊆ E₁ ∩ E₂ := by
    intro ω hω
    have hne := rectLen_ne_top (ξ := ξ) (rectAB 3 3) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hψ.cont ω)
    refine ⟨(ENNReal.toReal_mono hne (rectLen_13_le_33 _)).trans hω,
      (ENNReal.toReal_mono hne (crossLenIn_shift_le_33 _)).trans hω⟩
  have hprod : P (E₁ ∩ E₂) = P E₁ * P E₂ := by
    rw [hE₁, hE₂]
    exact (indepFun_psiMN_clamp hW Q hQ n).measure_inter_preimage_eq_mul T T hT hT
  have hlaw : P E₂ = P E₁ :=
    measure_crossLenIn_eq hK (Y := fun x ω => Y (x + 2) ω) (Y₂ := Y)
      (fun ω => (hψ.cont ω).comp (continuous_id.add continuous_const)) (fun x => hψ.meas _)
      hψ.cont hψ.meas (map_psiMN_add hW Q n 2) hS
  calc _ ≤ P (E₁ ∩ E₂) := measure_mono hsub
    _ = P E₁ ^ 2 := by rw [hprod, hlaw, sq]

end DDDF
end LQGMetric
