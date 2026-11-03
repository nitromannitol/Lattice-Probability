/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Dilate at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.StrongWeak
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# GM.S1.8: `D^{(b)}_h := D_{h(·/b)}(b·, b·)` is a weak γ-LQG metric with the same `𝔠_r`

Source: Gwynne–Miller, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 1.10, l. 490–505 (claim and Axiom V) and the commented-out axiom checks
l. 537–580 (Axioms I–IV′).

* Field layer: `affineComp_ofCont` (`(f)(r·+z)` of a continuous function, change of variables),
  `affineComp_addFun`, `affineComp_comp` (composition of affine pullbacks),
  `isGFFPlusCont_affineComp` (GM l. 211: `h(r·+z)` is again a GFF plus a continuous function).
* Metric layer: `ContMetric.isLength_rescale`, `ContMetric.internal_rescale`
  (`D(b·,b·)(·,·;U) = D(b·, b·; bU)`, GM l. 546), `restrictTo_affineComp_inv`
  (`h(·/b)|_{bU}` is a measurable function of `h|_U`, GM l. 547).
* `gm_s1_8` (GM.S1.8). Axiom V follows blueprint BP-M1-4: `(h(·/b))_{br}(0) = h_r(0)` a.s.
  (`CircleAvg.ae_circleAvg_affineComp` twice), so the normalized field of `D^{(b)}` at scale `r`
  is `(𝔠_{br}/𝔠_r)` times that of `D` at the GFF `h(·/b)` and scale `br` (own simplification of
  GM l. 497–505: the factor `e^{−ξ(h_r(0) − h_{br}(0))}` is not needed). The ratio `𝔠_{br}/𝔠_r`
  lies in a compact subset of `(0,∞)` by (1.12); the closure of the laws is handled by the
  continuity of `(a, μ) ↦ law of a·X` (mathlib `ProbabilityMeasure.continuous_prod`,
  `continuous_diracProba`, `continuous_map`) and Prokhorov's theorem
  (`isCompact_closure_of_isTightMeasureSet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace GM

/-! ### Affine pullbacks of fields -/

lemma affineComp_ofCont {r : ℝ} (hr : 0 < r) (z : ℂ) (f : C(ℂ, ℝ)) :
    affineComp r z (ofCont f) = ofCont (f.comp (affinePt r z)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [GFFInv.affineComp_apply, ofCont_apply, ofCont_apply]
  have h1 : (∫ x, testAffinePull r z φ x * f x) =
      ∫ x, (fun u => φ u * f (affinePt r z u)) ((x - z) / r) := by
    congr 1
    funext x
    simp only [testAffinePull_apply r z hr.ne', affinePt_apply]
    rw [mul_div_cancel₀ _ hr', sub_add_cancel]
  rw [h1, GFFInv.integral_comp_aff (fun u => φ u * f (affinePt r z u)) hr z, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rfl

lemma affineComp_add (r : ℝ) (z : ℂ) (g k : DistC) :
    affineComp r z (g + k) = affineComp r z g + affineComp r z k := by
  refine DFunLike.ext _ _ fun φ => ?_
  simp only [GFFInv.affineComp_apply, ContinuousLinearMap.add_apply, mul_add]

lemma affineComp_sub (r : ℝ) (z : ℂ) (g k : DistC) :
    affineComp r z (g - k) = affineComp r z g - affineComp r z k := by
  refine DFunLike.ext _ _ fun φ => ?_
  simp only [GFFInv.affineComp_apply, ContinuousLinearMap.sub_apply, mul_sub]

lemma affineComp_addFun {r : ℝ} (hr : 0 < r) (z : ℂ) (g : DistC) (f : C(ℂ, ℝ)) :
    affineComp r z (addFun g f) = addFun (affineComp r z g) (f.comp (affinePt r z)) := by
  rw [addFun, addFun, affineComp_add, affineComp_ofCont hr]

/-- `h(r₂ · + z₂)(r₁ · + z₁) = h(r₂ r₁ · + r₂ z₁ + z₂)` -/
theorem affineComp_comp {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (z₁ z₂ : ℂ) (h : DistC) :
    affineComp r₁ z₁ (affineComp r₂ z₂ h) = affineComp (r₂ * r₁) ((r₂ : ℂ) * z₁ + z₂) h := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull r₂ z₂ (testAffinePull r₁ z₁ φ) =
      testAffinePull (r₂ * r₁) ((r₂ : ℂ) * z₁ + z₂) φ :=
    TestFunction.ext fun x => by
      rw [testAffinePull_apply _ _ h₂, testAffinePull_apply _ _ h₁,
        testAffinePull_apply _ _ (mul_ne_zero h₂ h₁)]
      congr 1
      have : (r₁ : ℂ) ≠ 0 := by exact_mod_cast h₁
      have : (r₂ : ℂ) ≠ 0 := by exact_mod_cast h₂
      push_cast
      field_simp
      ring
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply, e, mul_pow]
  ring

/-- `h(r·+z)` of a GFF plus a continuous function is again one (GM l. 211). -/
theorem isGFFPlusCont_affineComp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusCont h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsGFFPlusCont (fun ω => affineComp r z (h ω)) P := by
  obtain ⟨hm, f, hf, hg⟩ := hh
  refine ⟨(measurable_affineComp r z).comp hm, fun ω => (f ω).comp (affinePt r z),
    (ContinuousMap.continuous_precomp _).measurable.comp hf, ?_⟩
  have e : (fun ω => affineComp r z (h ω) - ofCont ((f ω).comp (affinePt r z))) =
      fun ω => affineComp r z (h ω - ofCont (f ω)) := by
    funext ω; rw [affineComp_sub, affineComp_ofCont hr]
  rw [e]; exact hg.affineComp hr z

/-! ### `D(b·, b·)`: length, internal metrics -/

theorem _root_.LQGMetric.ContMetric.rescale_eq_affine (b : ℝ) (hb : 0 < b) (D : ContMetric) :
    D.rescale b hb = D.affine b hb.ne' 0 :=
  Subtype.ext (ContinuousMap.ext fun p => by
    show D.1 ((b : ℂ) * p.1, (b : ℂ) * p.2) = D.1 (affinePt b 0 p.1, affinePt b 0 p.2)
    simp only [affinePt_apply, add_zero])

theorem _root_.LQGMetric.ContMetric.isLength_rescale {b : ℝ} (hb : 0 < b) {D : ContMetric}
    (hD : D.IsLength) : (D.rescale b hb).IsLength := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  let f : D.Space → (D.rescale b hb).Space := fun z : ℂ => z / (b : ℂ)
  have hf : ∀ a c, edist (f a) (f c) = 1 * edist a c := fun a c => by
    rw [one_mul, edist_dist, edist_dist]
    congr 1
    show D.1 ((b : ℂ) * ((show ℂ from a) / b), (b : ℂ) * ((show ℂ from c) / b)) = D.1 (a, c)
    rw [mul_div_cancel₀ _ hb', mul_div_cancel₀ _ hb']
  have hfc : Continuous f :=
    (show LipschitzWith 1 f from fun a c => by rw [hf, one_mul]; simp).continuous
  intro x y ε hε
  let x' : D.Space := (b : ℂ) * (show ℂ from x)
  let y' : D.Space := (b : ℂ) * (show ℂ from y)
  have hx : f x' = x := mul_div_cancel_left₀ (show ℂ from x) hb'
  have hy : f y' = y := mul_div_cancel_left₀ (show ℂ from y) hb'
  obtain ⟨γ, hγ⟩ := hD x' y' ε hε
  rw [← hx, ← hy]
  refine ⟨γ.map hfc, ?_⟩
  rw [MetricGeometry.pathLength_map_of_edist_eq hf hfc γ, one_mul, hf, one_mul]
  exact hγ

/-- the open set `bU` (as the preimage of `U` under `x ↦ x/b`) -/
def dilOpens (b : ℝ) (U : Opens ℂ) : Opens ℂ :=
  ⟨affMap b 0 ⁻¹' U, U.isOpen.preimage (by unfold affMap; fun_prop)⟩

lemma affMap_inv_comp {b : ℝ} (hb : b ≠ 0) (x : ℂ) : affMap b 0 (affMap b⁻¹ 0 x) = x := by
  simp [affMap, hb]

lemma image_mul_eq_dilOpens {b : ℝ} (hb : b ≠ 0) (U : Opens ℂ) :
    (fun x : ℂ => (b : ℂ) * x) '' (U : Set ℂ) = (dilOpens b U : Set ℂ) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  ext y
  simp only [mem_image, dilOpens, Opens.coe_mk, mem_preimage, affMap, neg_zero, add_zero,
    Complex.real_smul, Complex.ofReal_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ hb', one_mul]
  · intro hy
    exact ⟨(b : ℂ)⁻¹ * y, hy, by rw [← mul_assoc, mul_inv_cancel₀ hb', one_mul]⟩

/-- `D(b·, b·)(z, w; U) = D(bz, bw; bU)` (GM l. 546) -/
theorem _root_.LQGMetric.ContMetric.internal_rescale {b : ℝ} (hb : 0 < b) (D : ContMetric)
    (U : Opens ℂ) (z w : ℂ) :
    (D.rescale b hb).internal U z w = D.internal (dilOpens b U) ((b : ℂ) * z) ((b : ℂ) * w) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  let e : (D.rescale b hb).Space ≃ D.Space := (Equiv.mulLeft₀ (b : ℂ) hb' : ℂ ≃ ℂ)
  have h := MetricGeometry.internalEDist_image_of_edist_eq e one_ne_zero ENNReal.one_ne_top
    (fun a c => by rw [one_mul, edist_dist, edist_dist]; rfl) ((D.rescale b hb).pt '' U) z w
  rw [one_mul] at h
  unfold ContMetric.internal
  rw [← image_mul_eq_dilOpens hb.ne' U]
  convert h.symm using 2
  all_goals first | rfl | (rw [image_image, image_image]; rfl)

/-! ### Restriction of `h(·/b)` to `bU` -/

/-- `φ ↦ φ(b ·)` from `𝓓(bU)` to `𝓓(U)` (function part) -/
def dilPullFun (b : ℝ) (hb : b ≠ 0) (U : Opens ℂ) (φ : TestOn (dilOpens b U)) : TestOn U :=
  ⟨φ ∘ affMap b⁻¹ 0, contDiff_comp_affMap _ _ φ.contDiff,
    hasCompactSupport_comp_affMap _ _ (inv_ne_zero hb) φ.hasCompactSupport,
    (tsupport_comp_subset_preimage _ (by unfold affMap; fun_prop)).trans fun x hx => by
      have := φ.tsupport_subset hx
      simpa only [dilOpens, Opens.coe_mk, mem_preimage, affMap_inv_comp hb] using this⟩

/-- `φ ↦ φ(b ·)` as a continuous linear map `𝓓(bU) → 𝓓(U)` -/
def dilPull (b : ℝ) (hb : b ≠ 0) (U : Opens ℂ) : TestOn (dilOpens b U) →L[ℝ] TestOn U :=
  TestFunction.mkCLM ℝ (dilPullFun b hb U) (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
    have hsub : (affK b⁻¹ 0 K : Set ℂ) ⊆ U := by
      rintro x ⟨y, hy, rfl⟩
      have := hK hy
      simp only [dilOpens, Opens.coe_mk, mem_preimage, affMap] at this
      simpa [Complex.real_smul] using this
    have : (dilPullFun b hb U ∘ TestFunction.ofSupportedIn hK) =
        TestFunction.ofSupportedInCLM ℝ hsub ∘ pullK b⁻¹ 0 (inv_ne_zero hb) K := by
      funext φ; ext x; rfl
    rw [this]
    exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp
      (continuous_pullK _ _ (inv_ne_zero hb) K))

/-- `k ↦ k(·/b)` from `𝒟'(U)` to `𝒟'(bU)` -/
def dilDist (b : ℝ) (hb : b ≠ 0) (U : Opens ℂ) (k : DistOn U) : DistOn (dilOpens b U) :=
  ((b⁻¹) ^ 2)⁻¹ • k.comp (dilPull b hb U)

theorem measurable_dilDist {b : ℝ} (hb : b ≠ 0) (U : Opens ℂ) : Measurable (dilDist b hb U) :=
  measurable_distOn_iff.2 fun φ => (measurable_distOn_apply (dilPull b hb U φ)).const_mul _

/-- `h(·/b)|_{bU}` is `h|_U` pulled back (GM l. 547) -/
theorem restrictTo_affineComp_inv {b : ℝ} (hb : b ≠ 0) (U : Opens ℂ) (g : DistC) :
    restrictTo (dilOpens b U) (affineComp b⁻¹ 0 g) = dilDist b hb U (restrictTo U g) := by
  refine DFunLike.ext _ _ fun φ => ?_
  have key : testAffinePull b⁻¹ 0 (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := dilOpens b U) (Ω₂ := ⊤) φ) =
      TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) (dilPull b hb U φ) := by
    ext x
    rw [testAffinePull_apply _ _ (inv_ne_zero hb), TestFunction.monoCLM_apply,
      TestFunction.monoCLM_apply]
    simp only [le_refl, le_top, and_self, ite_true]
    show φ _ = φ (affMap b⁻¹ 0 x)
    congr 1
    simp [affMap, div_eq_mul_inv, Complex.real_smul, mul_comm]
  show affineComp b⁻¹ 0 g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := dilOpens b U) (Ω₂ := ⊤) φ) = ((b⁻¹) ^ 2)⁻¹ * g (TestFunction.monoCLM ℝ (n₁ := ⊤)
      (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) (dilPull b hb U φ))
  rw [GFFInv.affineComp_apply, key]

/-! ### Axiom V under a bounded deterministic rescaling -/

lemma isContinuousMetric_smul {d : C(ℂ × ℂ, ℝ)} (hd : IsContinuousMetric d) {a : ℝ}
    (ha : 0 < a) : IsContinuousMetric (a • d) :=
  (ContMetric.smulPos a ha ⟨d, hd⟩).2

/-- the law of `a X` for `X ∼ ν` -/
def smulLaw (p : ℝ × ProbabilityMeasure C(ℂ × ℂ, ℝ)) : ProbabilityMeasure C(ℂ × ℂ, ℝ) :=
  ((diracProba p.1).prod p.2).map (fun q : ℝ × C(ℂ × ℂ, ℝ) => q.1 • q.2)

lemma continuous_smulLaw : Continuous smulLaw :=
  (ProbabilityMeasure.continuous_map continuous_smul).comp
    (ProbabilityMeasure.continuous_prod.comp (continuous_diracProba.prodMap continuous_id))

lemma toMeasure_smulLaw (a : ℝ) (ν : ProbabilityMeasure C(ℂ × ℂ, ℝ)) :
    ((smulLaw (a, ν) : ProbabilityMeasure C(ℂ × ℂ, ℝ)) : Measure C(ℂ × ℂ, ℝ)) =
      (ν : Measure C(ℂ × ℂ, ℝ)).map (fun d => a • d) := by
  show ((Measure.dirac a).prod (ν : Measure C(ℂ × ℂ, ℝ))).map _ = _
  rw [Measure.dirac_prod, Measure.map_map continuous_smul.measurable
    measurable_prodMk_left]
  rfl

/-- Axiom V transfers to `X_r = a_r Y_{βr}` when `a_r` stays in a compact subset of `(0,∞)`
(tightness: images of compacts under `(a, d) ↦ a d`; limit laws: continuity of `smulLaw` and
Prokhorov's theorem). -/
theorem tight_smul_family {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y X : ℝ → Ω → C(ℂ × ℂ, ℝ)} {a : ℝ → ℝ} {m M β : ℝ} (hm : 0 < m)
    (ha : ∀ r, 0 < r → a r ∈ Icc m M) (hβ : 0 < β) (hY : ∀ s, 0 < s → AEMeasurable (Y s) P)
    (hXY : ∀ r, 0 < r → X r =ᵐ[P] fun ω => a r • Y (β * r) ω)
    (hT : IsTightMeasureSet {μ | ∃ s : ℝ, 0 < s ∧ μ = P.map (Y s)})
    (hC : ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ), μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
      ∃ s : ℝ, 0 < s ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (Y s)} →
        ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d) :
    IsTightMeasureSet {μ | ∃ r : ℝ, 0 < r ∧ μ = P.map (X r)} ∧
    ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ), μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
      ∃ r : ℝ, 0 < r ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)} →
        ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d := by
  have hmapX : ∀ r, 0 < r → P.map (X r) = (P.map (Y (β * r))).map (fun d => a r • d) :=
    fun r hr => by
      rw [Measure.map_congr (hXY r hr), AEMeasurable.map_map_of_aemeasurable
        (continuous_const_smul _).measurable.aemeasurable (hY _ (mul_pos hβ hr))]
      rfl
  refine ⟨?_, fun μ hμ => ?_⟩
  · rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hT ⊢
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := hT ε hε
    have hK' := ((isCompact_Icc (a := m) (b := M)).prod hK).image
      (continuous_smul (M := ℝ) (X := C(ℂ × ℂ, ℝ)))
    refine ⟨_, hK', ?_⟩
    rintro μ ⟨r, hr, rfl⟩
    rw [hmapX r hr, Measure.map_apply (continuous_const_smul _).measurable
      hK'.isClosed.measurableSet.compl]
    refine (measure_mono ?_).trans (hKε _ ⟨β * r, mul_pos hβ hr, rfl⟩)
    intro d hd hdK
    exact hd ⟨(a r, d), ⟨ha r hr, hdK⟩, rfl⟩
  · let T := {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
      ∃ s : ℝ, 0 < s ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (Y s)}
    have hTt : IsTightMeasureSet {((ν : ProbabilityMeasure C(ℂ × ℂ, ℝ)) : Measure C(ℂ × ℂ, ℝ)) |
        ν ∈ T} :=
      hT.subset (by rintro _ ⟨ν, ⟨s, hs, hν⟩, rfl⟩; exact ⟨s, hs, hν⟩)
    have hK : IsCompact (smulLaw '' (Icc m M ×ˢ closure T)) :=
      ((isCompact_Icc (a := m) (b := M)).prod
        (isCompact_closure_of_isTightMeasureSet hTt)).image continuous_smulLaw
    have hsub : {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
        (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)} ⊆ smulLaw '' (Icc m M ×ˢ closure T) := by
      rintro ν ⟨r, hr, hν⟩
      refine ⟨(a r, (⟨P.map (Y (β * r)), inferInstance⟩ : ProbabilityMeasure C(ℂ × ℂ, ℝ))), ⟨ha r hr, subset_closure
        ⟨β * r, mul_pos hβ hr, rfl⟩⟩, ?_⟩
      apply ProbabilityMeasure.toMeasure_injective
      refine (toMeasure_smulLaw _ _).trans ?_
      rw [hν, hmapX r hr]
      rfl
    obtain ⟨⟨a₀, ν⟩, ⟨ha₀, hν⟩, rfl⟩ := closure_minimal hsub hK.isClosed hμ
    rw [toMeasure_smulLaw, ae_map_iff (continuous_const_smul a₀).measurable.aemeasurable
      measurableSet_isContinuousMetric]
    filter_upwards [hC ν hν] with d hd using isContinuousMetric_smul hd (hm.trans_le ha₀.1)

/-- `𝔠_{br}/𝔠_r` stays in a compact subset of `(0,∞)` (GM (1.12), l. 446–447). -/
lemma exists_ratio_bounds {c : ℝ → ℝ} (hpos : ∀ r, 0 < r → 0 < c r) {Λ : ℝ} (hΛ : 1 < Λ)
    (hrat : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    {b : ℝ} (hb : 0 < b) : ∃ m M : ℝ, 0 < m ∧ ∀ r, 0 < r → c (b * r) / c r ∈ Icc m M := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans hΛ
  rcases lt_trichotomy b 1 with h1 | rfl | h1
  · exact ⟨Λ⁻¹ * b ^ Λ, Λ * b ^ (-Λ), mul_pos (inv_pos.2 hΛ0) (Real.rpow_pos_of_pos hb _),
      fun r hr => hrat b ⟨hb, h1⟩ r hr⟩
  · exact ⟨1, 1, one_pos, fun r hr => by simp [div_self (hpos r hr).ne']⟩
  · have hb' : 0 < b⁻¹ := inv_pos.2 hb
    have hp : 0 < Λ⁻¹ * b⁻¹ ^ Λ := mul_pos (inv_pos.2 hΛ0) (Real.rpow_pos_of_pos hb' _)
    have hq : 0 < Λ * b⁻¹ ^ (-Λ) := mul_pos hΛ0 (Real.rpow_pos_of_pos hb' _)
    refine ⟨(Λ * b⁻¹ ^ (-Λ))⁻¹, (Λ⁻¹ * b⁻¹ ^ Λ)⁻¹, inv_pos.2 hq, fun r hr => ?_⟩
    obtain ⟨l, u⟩ := hrat b⁻¹ ⟨hb', inv_lt_one_of_one_lt₀ h1⟩ (b * r) (mul_pos hb hr)
    rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul] at l u
    rw [← inv_div]
    exact ⟨inv_anti₀ (hp.trans_le l) u, inv_anti₀ hp l⟩

/-! ### GM.S1.8 -/

theorem measurable_dilateMetric {D : DistC → ContMetric} (hD : Measurable D) {b : ℝ}
    (hb : 0 < b) : Measurable (dilateMetric b hb D) :=
  ((ContinuousMap.continuous_precomp (scaleArgs b)).measurable.comp
    (measurable_subtype_coe.comp (hD.comp (measurable_affineComp _ _)))).subtype_mk

/-- **GM.S1.8** (GM l. 490–505, 537–580): `D^{(b)}` is a weak γ-LQG metric with the same
scaling constants `𝔠_r` as `D`. -/
theorem gm_s1_8 {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {b : ℝ} (hb : 0 < b) : IsWeakLQGMetric γ (dilateMetric b hb D) c where
  measurable := measurable_dilateMetric hD.measurable hb
  length P _ h hh := by
    filter_upwards [hD.length P _ (isGFFPlusCont_affineComp hh (inv_pos.2 hb) 0)] with ω hω
      using ContMetric.isLength_rescale hb hω
  locality P _ h hh U := by
    obtain ⟨F, hFm, hF⟩ :=
      hD.locality P _ (isGFFPlusCont_affineComp hh (inv_pos.2 hb) 0) (dilOpens b U)
    refine ⟨fun k z w => F (dilDist b hb.ne' U k) ((b : ℂ) * z) ((b : ℂ) * w), ?_, ?_⟩
    · exact measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w =>
        (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
          (hFm.comp (measurable_dilDist hb.ne' U)))
    · filter_upwards [hF] with ω hω z hz w hw
      have hmem : ∀ x ∈ U, (b : ℂ) * x ∈ dilOpens b U := fun x hx => by
        rw [← SetLike.mem_coe, ← image_mul_eq_dilOpens hb.ne' U]
        exact ⟨x, hx, rfl⟩
      rw [dilateMetric, ContMetric.internal_rescale, hω _ (hmem z hz) _ (hmem w hw),
        restrictTo_affineComp_inv hb.ne']
  weyl P _ h hh := by
    filter_upwards [hD.weyl P _ (isGFFPlusCont_affineComp hh (inv_pos.2 hb) 0)] with ω hω f u v
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have e1 : (f.comp (affinePt b⁻¹ 0)).comp (affinePt b 0) = f := by
      ext x
      simp [affinePt_apply, hb']
    have e2 := weylScale_affine (ξ := xiGamma γ) (f := f.comp (affinePt b⁻¹ 0)) hb.ne' 0
      (D (affineComp b⁻¹ 0 (h ω))) u v
    rw [e1, hω] at e2
    rw [dilateMetric, dilateMetric, ContMetric.rescale_eq_affine, e2,
      affineComp_addFun (inv_pos.2 hb), ContMetric.rescale_apply]
    simp only [affinePt_apply, add_zero]
  translation P _ h hh z := by
    filter_upwards [hD.translation P _ (isGFFPlusCont_affineComp hh (inv_pos.2 hb) 0)
      ((b : ℂ) * z)] with ω hω u v
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have e : affineComp b⁻¹ 0 (affineComp 1 z (h ω)) =
        affineComp 1 ((b : ℂ) * z) (affineComp b⁻¹ 0 (h ω)) := by
      rw [affineComp_comp (inv_ne_zero hb.ne') one_ne_zero,
        affineComp_comp one_ne_zero (inv_ne_zero hb.ne')]
      congr 1
      · ring
      · push_cast; field_simp; ring
    simp only [dilateMetric, ContMetric.rescale_apply]
    rw [e, hω, mul_add, mul_add]
  tightness := by
    obtain ⟨hpos, ⟨Λ, hΛ, hrat⟩, hT⟩ := hD.tightness
    obtain ⟨m, M, hm, hmM⟩ := exists_ratio_bounds hpos hΛ hrat hb
    refine ⟨hpos, ⟨Λ, hΛ, hrat⟩, ?_⟩
    intro Ω _ P _ h hh X
    have hg := hh.affineComp (inv_pos.2 hb) 0
    have key := hT P _ hg
    dsimp only at key
    refine tight_smul_family (Y := fun s ω => ((c s)⁻¹ * Real.exp (-xiGamma γ *
      circleAvg (affineComp b⁻¹ 0 (h ω)) s 0)) • (D (affineComp b⁻¹ 0 (h ω))).1.comp
        (scaleArgs s)) (a := fun r => c (b * r) / c r) hm hmM hb ?_ ?_ key.1 key.2
    · intro s _
      exact (((((measurable_circleAvg_left s 0).comp hg.measurable).const_mul
        (-xiGamma γ)).exp.const_mul _).smul ((ContinuousMap.continuous_precomp _).measurable.comp
          (measurable_subtype_coe.comp (hD.measurable.comp hg.measurable)))).aemeasurable
    · intro r hr
      filter_upwards [CircleAvg.ae_circleAvg_affineComp hg (mul_pos hb hr) 0,
        CircleAvg.ae_circleAvg_affineComp hh hr 0] with ω h1 h2
      have e : affineComp (b * r) 0 (affineComp b⁻¹ 0 (h ω)) = affineComp r 0 (h ω) := by
        rw [affineComp_comp (mul_pos hb hr).ne' (inv_ne_zero hb.ne')]
        congr 1
        · field_simp
        · simp
      rw [e, h2] at h1
      have hc := (hpos (b * r) (mul_pos hb hr)).ne'
      have hc' := (hpos r hr).ne'
      ext p
      simp only [X, ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul, scaleArgs,
        ContinuousMap.coe_mk, dilateMetric, ContMetric.rescale_apply]
      rw [h1]
      push_cast
      rw [show (b : ℂ) * r * p.1 = b * (r * p.1) by ring,
        show (b : ℂ) * r * p.2 = b * (r * p.2) by ring]
      field_simp

end GM
end LQGMetric
