/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L4_Trans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Centre
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.WeakStrong

/-!
# LM S4.0: ξ-additivity is preserved under translation (task P2-LM42)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 4.1, l. 813–815: "by the ξ-additivity of `(D, D̃)` and
the fact that the locality condition is preserved under translating and scaling space, it follows
that `e^{−ξh_r(z)} D(r·+z, r·+z)` and `e^{−ξh_r(z)} D̃(r·+z, r·+z)` are jointly local metrics for
the field `h(r·+z) − h_r(z)`", which "has the same law as `h`".

We only need translations (`r = 1`): LM Lemma 3.1 allows arbitrary radii `r_k`, so the scaling is
absorbed in the radii (as in `GM.gm_L3_8`). Main results:

* `isJointlyLocalFam_transl`: joint locality for `g` gives joint locality for `g(· + z)` with the
  translated families `I(· + z, · + z; W + z)` (the σ-algebras are equal: `fieldSigma_transl`,
  `fieldSigmaClosed_transl`, `famSigma_transFam`).
* `lm_S4_0`: for `h` normalized and `(D₁, D₂)` ξ-additive for `h`, the field
  `transField h z = h(· + z) − h_1(z)` is a normalized whole-plane GFF and
  `transMetric ξ h z D_j = e^{−ξh_1(z)} D_j(· + z, · + z)` are ξ-additive for it.

Own routine argument (LM give none); σ-algebra transport and null-set changes reuse
`GM.fieldSigma_le_affineComp`, `GM.Bilip.isJointlyLocalFam_congr`, `DFGPS.L217.condIndepEv_congr_cond`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

section Transl

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- the translated family `I(· + z, · + z; W + z)` -/
def transFam (z : ℂ) (I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞) : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω W u v => I ω ((fun x => x - z) ⁻¹' W) (u + z) (v + z)

omit mΩ in
lemma affineComp_neg_comp (z : ℂ) (g : DistC) : affineComp 1 (-z) (affineComp 1 z g) = g := by
  rw [GM.affineComp_comp one_ne_zero one_ne_zero]
  simp only [mul_one, Complex.ofReal_one, one_mul, neg_add_cancel]
  exact GM.affineComp_one_zero g

/-- `σ(g(· + z)|_V) = σ(g|_{V + z})` -/
lemma fieldSigma_transl (z : ℂ) (g : Ω → DistC) {V U : TopologicalSpace.Opens ℂ}
    (hUV : ∀ y, y ∈ V ↔ y + z ∈ U) :
    fieldSigma (fun ω => affineComp 1 z (g ω)) V = fieldSigma g U := by
  refine le_antisymm ?_ (GM.fieldSigma_le_affineComp (r := 1) (z := z) (V := V) (U := U) one_pos
    (fun y => by rw [one_smul]; exact hUV y) g)
  have h1 := GM.fieldSigma_le_affineComp (r := 1) (z := -z) (V := U) (U := V) one_pos
    (fun y => by rw [one_smul, hUV, neg_add_cancel_right]) (fun ω => affineComp 1 z (g ω))
  simpa only [affineComp_neg_comp] using h1

lemma fieldSigmaClosed_transl (z : ℂ) (g : Ω → DistC) {S T : Set ℂ}
    (hST : ∀ y, y ∈ S ↔ y + z ∈ T) :
    fieldSigmaClosed (fun ω => affineComp 1 z (g ω)) S = fieldSigmaClosed g T := by
  unfold fieldSigmaClosed
  refine iInf_congr fun ε => iInf_congr fun _ => fieldSigma_transl z g fun y => ?_
  show y ∈ thickening ε S ↔ y + z ∈ thickening ε T
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨x, hx, hd⟩
    exact ⟨x + z, (hST x).1 hx, by rwa [dist_add_right]⟩
  · rintro ⟨x, hx, hd⟩
    refine ⟨x - z, (hST _).2 (by rwa [sub_add_cancel]), ?_⟩
    rw [← dist_add_right _ _ z, sub_add_cancel]
    exact hd

omit mΩ in
lemma famSigma_transFam (z : ℂ) (I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞) (W : Set ℂ) :
    famSigma (transFam z I) W = famSigma I ((fun x => x - z) ⁻¹' W) := by
  unfold famSigma transFam
  set X : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω => I ω ((fun x => x - z) ⁻¹' W) with hX
  let Φ : (ℂ → ℂ → ℝ≥0∞) → (ℂ → ℂ → ℝ≥0∞) := fun F u v => F (u + z) (v + z)
  let Ψ : (ℂ → ℂ → ℝ≥0∞) → (ℂ → ℂ → ℝ≥0∞) := fun F u v => F (u - z) (v - z)
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    (measurable_pi_apply (v + z)).comp (measurable_pi_apply (u + z))
  have hΨ : Measurable Ψ := measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    (measurable_pi_apply (v - z)).comp (measurable_pi_apply (u - z))
  have e1 : (fun ω u v => I ω ((fun x => x - z) ⁻¹' W) (u + z) (v + z)) = Φ ∘ X := rfl
  have e2 : X = Ψ ∘ (Φ ∘ X) := by
    funext ω u v
    simp only [Function.comp, Φ, Ψ, sub_add_cancel]
  rw [e1]
  refine le_antisymm ?_ ?_
  · rw [← MeasurableSpace.comap_comp]; exact MeasurableSpace.comap_mono hΦ.comap_le
  · conv_lhs => rw [e2]
    rw [← MeasurableSpace.comap_comp]; exact MeasurableSpace.comap_mono hΨ.comap_le

/-- **joint locality is preserved under translation** (LM l. 814) -/
theorem isJointlyLocalFam_transl (z : ℂ) {g : Ω → DistC} {I₁ I₂ : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞}
    (hI : IsJointlyLocalFam P g I₁ I₂) :
    IsJointlyLocalFam P (fun ω => affineComp 1 z (g ω)) (transFam z I₁) (transFam z I₂) := by
  intro V
  let U : TopologicalSpace.Opens ℂ :=
    ⟨(fun x => x - z) ⁻¹' V, V.isOpen.preimage (continuous_sub_right z)⟩
  have hUV : ∀ y, y ∈ V ↔ y + z ∈ U := fun y => by
    show _ ↔ y + z - z ∈ (V : Set ℂ)
    rw [add_sub_cancel_right]; rfl
  have e1 := fieldSigma_transl z g hUV
  have e2 : fieldSigmaClosed (fun ω => affineComp 1 z (g ω)) (V : Set ℂ)ᶜ =
      fieldSigmaClosed g (U : Set ℂ)ᶜ := fieldSigmaClosed_transl z g fun y => not_congr (hUV y)
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-z)
  have he : (e : ℂ → ℂ) = fun x => x - z := funext fun x => by simp [e, sub_eq_add_neg]
  have e3 : (fun x => x - z) ⁻¹' (closure (V : Set ℂ))ᶜ = (closure (U : Set ℂ))ᶜ := by
    rw [preimage_compl, ← he, e.preimage_closure]; rfl
  have H := hI U
  rw [e1, e2, famSigma_transFam, famSigma_transFam, famSigma_transFam, famSigma_transFam, e3]
  exact H

/-- joint locality is unchanged when the field is changed on a null event -/
theorem isJointlyLocalFam_congr_field [IsProbabilityMeasure P] {g g' : Ω → DistC}
    {I₁ I₂ : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞} (hI : IsJointlyLocalFam P g I₁ I₂) (hg : Measurable g)
    (hg' : Measurable g') (hgg : ∀ᵐ ω ∂P, g ω = g' ω)
    (h₁ : ∀ W : Set ℂ, IsOpen W → famSigma I₁ W ≤ aeClosure P mΩ)
    (h₂ : ∀ W : Set ℂ, IsOpen W → famSigma I₂ W ≤ aeClosure P mΩ) :
    IsJointlyLocalFam P g' I₁ I₂ := by
  intro V
  have hOV : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have H' := CondIndepEv.of_le_aeClosure (hI V) (le_aeClosure _)
    (sup_le (sup_le ((DFGPS.L217.fieldSigmaClosed_le_aeClosure_of_ae_eq
        (hgg.mono fun ω hω => hω.symm) _).trans (aeClosure_mono (le_sup_left.trans le_sup_left)))
      ((le_sup_right.trans le_sup_left).trans (le_aeClosure _))) (le_sup_right.trans
        (le_aeClosure _)))
  refine DFGPS.L217.condIndepEv_congr_cond (fieldSigma_le hg V) (fieldSigma_le hg' V) ?_ ?_
    (sup_le (h₁ V V.isOpen) (h₂ V V.isOpen))
    (sup_le (sup_le ((fieldSigmaClosed_le hg' _).trans (le_aeClosure _)) (h₁ _ hOV)) (h₂ _ hOV))
    H'
  · exact DFGPS.L219.comap_le_aeClosure_of_ae_eq (comap_measurable _)
      (hgg.mono fun ω hω => by simp only [hω])
  · exact DFGPS.L219.comap_le_aeClosure_of_ae_eq (comap_measurable _)
      (hgg.mono fun ω hω => by simp only [hω])

/-! ### The translated field and metrics -/

/-- `h(· + z) − h_1(z)` -/
def transField (h : Ω → DistC) (z : ℂ) : Ω → DistC :=
  fun ω => addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)

/-- `e^{−ξh_1(z)} D(· + z, · + z)` -/
def transMetric (ξ : ℝ) (h : Ω → DistC) (z : ℂ) (D : Ω → ContMetric) : Ω → ContMetric :=
  fun ω => ((D ω).affine 1 one_ne_zero z).smulPos (Real.exp (-ξ * circleAvg (h ω) 1 z))
    (Real.exp_pos _)

omit mΩ in
lemma transField_eq (h : Ω → DistC) (z : ℂ) :
    transField h z = fun ω => affineComp 1 z (addConst (h ω) (-circleAvg (h ω) 1 z)) :=
  funext fun ω => (GM.affineComp_addConst one_pos z _ _).symm

omit mΩ in
lemma internal_transMetric (ξ : ℝ) (h : Ω → DistC) (z : ℂ) (D : Ω → ContMetric) (ω : Ω)
    (W : Set ℂ) (u v : ℂ) :
    (transMetric ξ h z D ω).internal W u v = ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) 1 z))
      * (D ω).internal ((fun x => x - z) ⁻¹' W) (u + z) (v + z) := by
  rw [transMetric, ContMetric.internal_smulPos]
  congr 1
  have := DFGPS.internal_transl_smul (D := D ω) (D' := (D ω).affine 1 one_ne_zero z) one_pos z
    (fun u v => by
      show (D ω).1 (affinePt 1 z u, affinePt 1 z v) = _
      simp [affinePt_apply]) ((fun x => x - z) ⁻¹' W) (u + z) (v + z)
  rw [ENNReal.ofReal_one, one_mul, add_sub_cancel_right, add_sub_cancel_right,
    image_preimage_eq _ (fun y => ⟨y + z, add_sub_cancel_right y z⟩)] at this
  exact this

omit mΩ in
lemma internalFam_transMetric (ξ : ℝ) (h : Ω → DistC) (z : ℂ) (D : Ω → ContMetric) :
    internalFam (transMetric ξ h z D) = transFam z (fun ω V u v =>
      ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) 1 z)) * (D ω).internal V u v) :=
  funext fun ω => funext fun W => funext fun u => funext fun v =>
    internal_transMetric ξ h z D ω W u v

theorem ContMetric.isLength_affine_one {D : ContMetric} (hD : D.IsLength) (z : ℂ) :
    (D.affine 1 one_ne_zero z).IsLength := by
  let f : D.Space → (D.affine 1 one_ne_zero z).Space := fun x : ℂ => x - z
  have hf : ∀ a c, edist (f a) (f c) = 1 * edist a c := fun a c => by
    rw [one_mul, edist_dist, edist_dist]
    congr 1
    show D.1 (affinePt 1 z ((show ℂ from a) - z), affinePt 1 z ((show ℂ from c) - z)) = D.1 (a, c)
    simp only [affinePt_apply, Complex.ofReal_one, one_mul]
    exact congrArg D.1 (Prod.ext (sub_add_cancel (show ℂ from a) z) (sub_add_cancel (show ℂ from c) z))
  have hfc : Continuous f :=
    (show LipschitzWith 1 f from fun a c => by rw [hf, one_mul]; simp).continuous
  intro x y ε hε
  let x' : D.Space := (show ℂ from x) + z
  let y' : D.Space := (show ℂ from y) + z
  have hx : f x' = x := add_sub_cancel_right (show ℂ from x) z
  have hy : f y' = y := add_sub_cancel_right (show ℂ from y) z
  obtain ⟨γ, hγ⟩ := hD x' y' ε hε
  rw [← hx, ← hy]
  refine ⟨γ.map hfc, ?_⟩
  rw [MetricGeometry.pathLength_map_of_edist_eq hf hfc γ, one_mul, hf, one_mul]
  exact hγ

lemma measurable_transMetric {D : Ω → ContMetric} (hD : Measurable D) (ξ : ℝ) {h : Ω → DistC}
    (hh : Measurable h) (z : ℂ) : Measurable (transMetric ξ h z D) := by
  have ha : Measurable fun ω => (D ω).affine 1 one_ne_zero z :=
    ((ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp hD)).subtype_mk
  exact DFGPS.L217.measurable_smulPos_rand ha
    (((measurable_circleAvg_left 1 z).comp hh).const_mul (-ξ))

/-- scaled internal families of a measurable a.s.-length random metric are measurable up to null
events -/
lemma famSigma_scaled_le [IsProbabilityMeasure P] {D : Ω → ContMetric} (hD : Measurable D)
    (hl : ∀ᵐ ω ∂P, (D ω).IsLength) (ξ : ℝ) {x : Ω → ℝ} (hx : Measurable x) (W : Set ℂ)
    (hW : IsOpen W) :
    famSigma (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * x ω)) * (D ω).internal V u v) W ≤
      aeClosure P mΩ := by
  obtain ⟨F, hF, hFe⟩ := measurable_internal hW
  refine famSigma_le_aeClosure_of_measurable (DFGPS.L219.measurable_scaleF hD hF ξ hx) ?_
  filter_upwards [hl] with ω hω
  funext u v
  rw [hFe _ hω u v]

/-- **LM S4.0** (l. 813–815), translation case: `h(· + z) − h_1(z)` is a normalized whole-plane
GFF, and `e^{−ξh_1(z)} D_j(· + z, · + z)` are jointly local and ξ-additive for it. -/
theorem lm_S4_0 [IsProbabilityMeasure P] {ξ : ℝ} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hxi : IsXiAdditive2 ξ P h D₁ D₂) (z : ℂ) :
    IsNormalizedWPGFF (transField h z) P ∧
      IsXiAdditive2 ξ P (transField h z) (transMetric ξ h z D₁) (transMetric ξ h z D₂) := by
  obtain ⟨⟨hm₁, hm₂, hlen, hJL⟩, hadd⟩ := hxi
  have hz := hh.1.affineComp one_pos z
  have hc1 : Measurable fun ω => circleAvg (h ω) 1 z :=
    (measurable_circleAvg_left 1 z).comp hh.1.measurable
  have hT : IsWholePlaneGFF (transField h z) P := hz.addConst hc1.neg
  have hT1 : ∀ᵐ ω ∂P, circleAvg (transField h z ω) 1 0 = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    simp only [transField]
    rw [hω, GM.Tight.circleAvg_affineComp_one]; ring
  have hM₁ := measurable_transMetric hm₁ ξ hh.1.measurable z
  have hM₂ := measurable_transMetric hm₂ ξ hh.1.measurable z
  have hlen' : ∀ᵐ ω ∂P, (transMetric ξ h z D₁ ω).IsLength ∧ (transMetric ξ h z D₂ ω).IsLength := by
    filter_upwards [hlen] with ω ⟨h1, h2⟩
    exact ⟨ContMetric.isLength_smulPos _ (ContMetric.isLength_affine_one h1 z),
      ContMetric.isLength_smulPos _ (ContMetric.isLength_affine_one h2 z)⟩
  refine ⟨⟨hT, hT1⟩, ⟨hM₁, hM₂, hlen', ?_⟩, fun w ρ hρ => ?_⟩
  · rw [transField_eq, internalFam_transMetric, internalFam_transMetric]
    exact isJointlyLocalFam_transl z (hadd z 1 one_pos)
  -- the scale `(w, ρ)`: from ξ-additivity of `h` at `(w + z, ρ)`
  have H := isJointlyLocalFam_transl z (hadd (w + z) ρ hρ)
  have hA := CircleAvg.ae_circleAvg_addConst hz w hρ
  have key : ∀ᵐ ω ∂P, circleAvg (transField h z ω) ρ w =
      circleAvg (h ω) ρ (w + z) - circleAvg (h ω) 1 z := by
    filter_upwards [hA] with ω hω
    simp only [transField]
    rw [hω, GM.circleAvg_affineComp_one_at]; ring
  have hfam : ∀ D : Ω → ContMetric, ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V →
      (fun u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (transField h z ω) ρ w)) *
        (transMetric ξ h z D ω).internal V u v) =
      transFam z (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) ρ (w + z))) *
        (D ω).internal V u v) ω V := fun D => by
    filter_upwards [key] with ω hω V _
    funext u v
    simp only [transFam]
    rw [internal_transMetric, hω, DFGPS.L219.ofReal_exp_mul_ofReal_exp]
    congr 3; ring
  have H2 := isJointlyLocalFam_congr H (hfam D₁) (hfam D₂)
  have hTm : Measurable (transField h z) := hT.measurable
  have hcw : Measurable fun ω => circleAvg (transField h z ω) ρ w :=
    (measurable_circleAvg_left ρ w).comp hTm
  refine isJointlyLocalFam_congr_field H2 ?_ ((hT.addConst hcw.neg).measurable) ?_
    (fun W hW => famSigma_scaled_le hM₁ (hlen'.mono fun ω hω => hω.1) ξ hcw W hW)
    (fun W hW => famSigma_scaled_le hM₂ (hlen'.mono fun ω hω => hω.2) ξ hcw W hW)
  · exact (measurable_affineComp 1 z).comp (hh.1.addConst
      ((measurable_circleAvg_left ρ (w + z)).comp hh.1.measurable).neg).measurable
  · filter_upwards [key] with ω hω
    show _ = addConst (transField h z ω) (-circleAvg (transField h z ω) ρ w)
    rw [hω]
    simp only [transField]
    rw [GM.affineComp_addConst one_pos, GFFLaw.addConst_addConst]
    congr 1; ring

end Transl

end LQGMetric.LM
