/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.MarkovNorm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryField
import LatticeProb.Bonanno.LQGMetric.Complex.HarmonicComp
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Markov property of the whole-plane GFF at the normalization `h_r(z) = 0` (DF-B3)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, T:878, proof of Lemma 2.8) uses "the
Markov property of the whole-plane GFF" on the square `(-1,2)²`, which meets `∂𝔻`; this needs the
Markov property for a normalization `h_r(z) = 0` with `∂B_r(z)` disjoint from the domain.
`Blueprint.LMLem2_1` (LM Lemma 2.1, l. 425–429; GMSh Lemma 2.2) is stated for `h_1(0) = 0`.

We derive the general case by scaling and translation (FINV): `g := h(r · + z)` is a whole-plane
GFF with `g_1(0) = h_r(z) = 0` (`CircleAvg.ae_circleAvg_affineComp`), so `LMLem2_1` applies to `g`
on `V' = {y | r y + z ∈ V}` (disjoint from `∂𝔻` iff `V` is disjoint from `∂B_r(z)`); the
decomposition `g = 𝔥' + h̊'` is pulled back by `k ↦ k((· − z)/r)`. Transport facts reused:
`GM.affineComp_comp`, `GM.restrictTo_apply_eq_scale`, `GM.fieldSigma_le_affineComp`,
`IsZeroBoundaryGFF.affine` (Sheffield §2.2 conformal invariance), `harmonicOnNhd_comp_holo`.
The scaling reduction is the standard one ("by scale and translation invariance"); the
σ-algebra and thickening bookkeeping is own elementary work.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.DFGPS

open Blueprint GFFInv

variable {r : ℝ} {z : ℂ}

/-! ### Elementary geometry of `y ↦ a y + b` -/

/-- thickenings are transported by a similarity `T y = a y + b`, `a > 0` -/
lemma mem_thickening_aff {a : ℝ} (ha : 0 < a) (b : ℂ) {K K' : Set ℂ}
    (hK : ∀ y, y ∈ K' ↔ a • y + b ∈ K) {ε : ℝ} (y : ℂ) :
    y ∈ thickening ε K' ↔ a • y + b ∈ thickening (a * ε) K := by
  have hd : ∀ x w : ℂ, dist (a • x + b) (a • w + b) = a * dist x w := fun x w => by
    rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos ha]
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.1 hy
    refine mem_thickening_iff.2 ⟨a • x + b, (hK x).1 hx, ?_⟩
    rw [hd]; exact mul_lt_mul_of_pos_left hxy ha
  · intro hy
    obtain ⟨w, hw, hwy⟩ := mem_thickening_iff.1 hy
    have hw' : a • (a⁻¹ • (w - b)) + b = w := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, sub_add_cancel]
    refine mem_thickening_iff.2 ⟨a⁻¹ • (w - b), (hK _).2 (hw'.symm ▸ hw), ?_⟩
    rw [← hw', hd] at hwy
    exact lt_of_mul_lt_mul_left hwy ha.le

lemma affineComp_one_zero' (g : DistC) : affineComp 1 0 g = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull 1 0 φ = φ := TestFunction.ext fun x => by
    rw [testAffinePull_apply _ _ one_ne_zero]; simp
  rw [GFFInv.affineComp_apply, e]; simp

/-- the inverse affine pullback `k ↦ k((· − z)/r)` -/
def affInvC (r : ℝ) (z : ℂ) : DistC → DistC := affineComp r⁻¹ (-(r⁻¹ • z))

lemma affInvC_affineComp (hr : r ≠ 0) (g : DistC) : affInvC r z (affineComp r z g) = g := by
  rw [affInvC, GM.affineComp_comp (inv_ne_zero hr) hr]
  have e1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have e2 : (r : ℂ) * -(r⁻¹ • z) + z = 0 := by
    have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    rw [Complex.real_smul]; push_cast; field_simp; ring
  rw [e1, e2, affineComp_one_zero']

lemma affineComp_affInvC (hr : r ≠ 0) (g : DistC) : affineComp r z (affInvC r z g) = g := by
  rw [affInvC, GM.affineComp_comp hr (inv_ne_zero hr)]
  have e1 : r⁻¹ * r = 1 := inv_mul_cancel₀ hr
  have e2 : ((r⁻¹ : ℝ) : ℂ) * z + -(r⁻¹ • z) = 0 := by
    rw [Complex.real_smul]; ring
  rw [e1, e2, affineComp_one_zero']

/-- the domain `V' = {y | r y + z ∈ V}` -/
abbrev preOpens (r : ℝ) (z : ℂ) (V : Opens ℂ) : Opens ℂ := affOpens r⁻¹ (-(r⁻¹ • z)) V

lemma mem_preOpens (hr : r ≠ 0) (V : Opens ℂ) (y : ℂ) :
    y ∈ preOpens r z V ↔ r • y + z ∈ V := by
  show affMap r⁻¹ (-(r⁻¹ • z)) y ∈ (V : Set ℂ) ↔ _
  rw [GM.affMap_inv_apply hr]; rfl

/-! ### σ-algebras -/

variable {Ω : Type} [MeasurableSpace Ω]

lemma fieldSigmaClosed_le_affineComp (hr : 0 < r) (V : Opens ℂ) (h : Ω → DistC) :
    fieldSigmaClosed h (V : Set ℂ)ᶜ ≤
      fieldSigmaClosed (fun ω => affineComp r z (h ω)) (preOpens r z V : Set ℂ)ᶜ := by
  refine le_iInf₂ fun ε hε => ?_
  refine (iInf₂_le (r * ε) (mul_pos hr hε)).trans ?_
  refine GM.fieldSigma_le_affineComp hr (fun y => ?_) h
  exact mem_thickening_aff hr z (fun x => by
    rw [mem_compl_iff, mem_compl_iff, SetLike.mem_coe, mem_preOpens hr.ne']; rfl) y

lemma fieldSigmaClosed_affineComp_le (hr : 0 < r) (V : Opens ℂ) (h : Ω → DistC) :
    fieldSigmaClosed (fun ω => affineComp r z (h ω)) (preOpens r z V : Set ℂ)ᶜ ≤
      fieldSigmaClosed h (V : Set ℂ)ᶜ := by
  refine le_iInf₂ fun ε hε => ?_
  refine (iInf₂_le (r⁻¹ * ε) (mul_pos (inv_pos.2 hr) hε)).trans ?_
  have e : h = fun ω => affineComp r⁻¹ (-(r⁻¹ • z)) (affineComp r z (h ω)) := by
    funext ω; exact (affInvC_affineComp hr.ne' (h ω)).symm
  conv_rhs => rw [e]
  refine GM.fieldSigma_le_affineComp (inv_pos.2 hr) (fun y => ?_) _
  refine mem_thickening_aff (inv_pos.2 hr) _ (fun x => ?_) y
  rw [mem_compl_iff, mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe, mem_preOpens hr.ne']
  have : r • (r⁻¹ • x + -(r⁻¹ • z)) + z = x := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, smul_neg, smul_smul,
      mul_inv_cancel₀ hr.ne', one_smul, neg_add_cancel_right]
  rw [this]

/-- `h − h_r(z)` is a whole-plane GFF normalized so that its `r`-circle average at `z` vanishes -/
theorem isNormalizedAt_recenter {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hr : 0 < r) (z : ℂ) :
    IsWholePlaneGFF (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) P ∧
      ∀ᵐ ω ∂P, circleAvg (addConst (h ω) (-circleAvg (h ω) r z)) r z = 0 := by
  refine ⟨hh.addConst ((measurable_circleAvg_left r z).comp hh.measurable).neg, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst hh z hr] with ω hω
  rw [hω]; ring

/-! ### The Markov property at `h_r(z) = 0` -/

lemma disjoint_preOpens (hr : 0 < r) {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere z r)) :
    Disjoint (preOpens r z V : Set ℂ) (sphere (0 : ℂ) 1) := by
  refine Set.disjoint_left.2 fun y hy hy1 => Set.disjoint_left.1 hV
    ((mem_preOpens hr.ne' V y).1 hy) ?_
  rw [mem_sphere_zero_iff_norm] at hy1
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_right, norm_smul, hy1, mul_one,
    Real.norm_eq_abs, abs_of_pos hr]

/-- `(h((· − z)/r))|_V` is the affine image of `h|_{V'}` (`V' = preOpens r z V`) -/
lemma restrictTo_affInvC (hr : 0 < r) (V : Opens ℂ) (k : DistC) :
    restrictTo V (affInvC r z k) =
      distAffine r⁻¹ (-(r⁻¹ • z)) (inv_ne_zero hr.ne') (restrictTo (preOpens r z V) k) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [distAffine_apply]
  show affineComp r⁻¹ (-(r⁻¹ • z)) k (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V)
      (Ω₂ := ⊤) φ) = _
  rw [GFFInv.affineComp_apply]
  congr 1
  show k _ = k _
  congr 1
  ext x
  rw [testAffinePull_apply _ _ (inv_ne_zero hr.ne')]
  simp only [TestFunction.monoCLM_apply, le_refl, le_top, and_self, ite_true]
  erw [TestFunction.monoCLM_apply]
  simp only [le_refl, le_top, and_self, ite_true]
  show φ _ = φ (affMap r⁻¹ (-(r⁻¹ • z)) x)
  congr 1
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [affMap, inv_inv, Complex.real_smul, sub_eq_add_neg, div_eq_mul_inv]
  push_cast
  field_simp

/-- **Markov property of the whole-plane GFF at the normalization `h_r(z) = 0`** (DFGPS T:878;
LM Lemma 2.1 transported by `y ↦ r y + z`): for a whole-plane GFF `h` with `h_r(z) = 0` a.s. and
an open `V` disjoint from `∂B_r(z)`, `h = 𝔥 + h̊` with `𝔥` harmonic on `V` and determined by
`h|_{ℂ∖V}`, `h̊` independent of `𝔥`, a zero-boundary GFF on `V` vanishing off `cl V`, and `h̊`
independent of `h|_{ℂ∖V}`. -/
theorem markov_normAt (hLM : LMLem2_1) (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (hr : 0 < r) (z : ℂ)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) r z = 0) (V : Opens ℂ)
    (hV : Disjoint (V : Set ℂ) (sphere z r)) :
    ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh =ᵐ[P] G) ∧
      IndepFun hh hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P := by
  set g : Ω → DistC := fun ω => affineComp r z (h ω) with hg_def
  have hgN : IsNormalizedWPGFF g P := by
    refine ⟨hh.affineComp hr z, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_affineComp hh hr z, hn] with ω h1 h2
    rw [h1, h2]
  set V' := preOpens r z V
  have hUV : ∀ y : ℂ, y ∈ V' ↔ r • y + z ∈ V := mem_preOpens hr.ne' V
  obtain ⟨hh', hz', hsum, hharm, ⟨G', hG'm, hG'⟩, hind, hzb, hvan, hindep⟩ :=
    hLM P g hgN V' (disjoint_preOpens hr hV)
  have hmA : Measurable (affInvC r z) := measurable_affineComp _ _
  have hrec : ∀ ω, h ω = affInvC r z (g ω) := fun ω => (affInvC_affineComp hr.ne' (h ω)).symm
  refine ⟨fun ω => affInvC r z (hh' ω), fun ω => affInvC r z (hz' ω), fun ω => ?_, ?_,
    ⟨fun ω => affInvC r z (G' ω), ?_, ?_⟩, hind.comp hmA hmA, ?_, fun ω => ?_, ?_⟩
  · rw [hrec, hsum, affInvC, GM.affineComp_add]
  · filter_upwards [hharm] with ω hω
    obtain ⟨g', hg'h, hg'p⟩ := hω
    refine ⟨g' ∘ affMap r z, ?_, fun φ => ?_⟩
    · have he : affMap r z = fun x : ℂ => ((r : ℂ)⁻¹) * (x + -z) := by
        funext x; simp only [affMap, Complex.real_smul]; push_cast; ring
      refine harmonicOnNhd_comp_holo V'.isOpen V.isOpen hg'h ?_ fun x hx => ?_
      · rw [he]; fun_prop
      · show affMap r z x ∈ (V' : Set ℂ)
        rw [SetLike.mem_coe, hUV]
        have : r • affMap r z x + z = x := by
          rw [affMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, neg_add_cancel_right]
        rw [this]; exact hx
    · rw [GM.restrictTo_apply_eq_scale hr hUV, affineComp_affInvC hr.ne', hg'p]
      conv_rhs => rw [GFFInv.integral_eq_smul_add _ hr z]
      congr 2
      funext v
      rw [GM.testScalePush_apply]
      have : affMap r z (r • v + z) = v := by
        rw [affMap, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      simp only [Function.comp_apply, this]
  · exact hmA.comp (hG'm.mono (fieldSigmaClosed_affineComp_le hr V h) le_rfl)
  · filter_upwards [hG'] with ω hω
    simp only [hω]
  · have := hzb.affine (r := r⁻¹) (z := -(r⁻¹ • z)) (inv_ne_zero hr.ne')
    convert this using 2 with ω
    exact restrictTo_affInvC hr V (hz' ω)
  · refine DFunLike.ext _ _ fun φ => ?_
    have hUV2 : ∀ y : ℂ, y ∈ toOpens (closure (V' : Set ℂ))ᶜ isClosed_closure.isOpen_compl ↔
        r • y + z ∈ toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl := by
      intro y
      let T : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight z)
      have hT : (V' : Set ℂ) = T ⁻¹' (V : Set ℂ) := by ext y; exact hUV y
      show y ∈ (closure (V' : Set ℂ))ᶜ ↔ T y ∈ (closure (V : Set ℂ))ᶜ
      rw [hT, ← T.preimage_closure]; rfl
    rw [GM.restrictTo_apply_eq_scale hr hUV2, affineComp_affInvC hr.ne', hvan ω]
    simp
  · refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep ?_) ?_
    · rw [show (fun ω => affInvC r z (hz' ω)) = affInvC r z ∘ hz' from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hmA.comap_le
    · exact fieldSigmaClosed_le_affineComp hr V h

end LQGMetric.DFGPS
