import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-!
# Uniform translation modulo `p` and joint independence

If `U` is uniform on `[0,p)` and independent of the data `I`, and `a` is a measurable real function of
the data, then `V = (U + a(I)) mod p` is uniform on `[0,p)` and independent of `I`, hence of every
measurable function `G(I)`. The representative of `U + a(I)` in `[0,p)` is `toIcoMod hp 0 (U + a(I))`.

## Main results

* `LatticeProb.measurable_toIcoMod_zero`: the representative map `x ↦ x mod p` into `[0,p)` is measurable.
* `LatticeProb.map_toIcoMod_add_uniformIco`: the uniform law on `[0,p)` is invariant under
  `x ↦ (x + c) mod p`. The proof uses that `toIcoMod⁻¹' S` is `p ℤ`-periodic, so its measure in every
  fundamental window `Ioc c (c + p)` is the same (`IsAddFundamentalDomain.measure_set_eq`).
* `LatticeProb.map_prod_toIcoMod_add_uniformIco`: the product law `uniformIco p ⊗ μ` is invariant under
  `(u, ι) ↦ ((u + a ι) mod p, ι)` (Tonelli, `Measure.prod_apply_symm`).
* `LatticeProb.indepFun_toIcoMod_add_uniformIco`: `V` is uniform on `[0,p)` and the pair `(V, I)` has the
  product law.
* `LatticeProb.indepFun_toIcoMod_add_uniformIco_comp`: `V` is independent of `G ∘ I` for every measurable `G`.
-/
open MeasureTheory Set

namespace LatticeProb

/-- The uniform law on `[0,p)`: Lebesgue measure conditioned on `Set.Ico 0 p`. -/
noncomputable def uniformIco (p : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Ico 0 p)

lemma isProbabilityMeasure_uniformIco {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (uniformIco p) := by
  unfold uniformIco
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Ico, sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top

/-- The representative `x ↦ x mod p` in `[0,p)` is measurable. -/
lemma measurable_toIcoMod_zero {p : ℝ} (hp : 0 < p) : Measurable (toIcoMod hp (0 : ℝ)) := by
  have hfl : Measurable (fun b : ℝ => ⌊(b - 0) / p⌋) :=
    Int.measurable_floor.comp ((measurable_id.sub_const 0).div_const p)
  have hfun : toIcoMod hp (0 : ℝ) = fun b => b - (fun k : ℤ => k • p) ⌊(b - 0) / p⌋ := by
    funext b
    rw [← self_sub_toIcoDiv_zsmul hp 0 b, toIcoDiv_eq_floor]
  rw [hfun]
  exact measurable_id.sub ((Measurable.of_discrete (f := fun k : ℤ => k • p)).comp hfl)

/-- The map `(u, ι) ↦ ((u + a ι) mod p, ι)` is measurable. -/
lemma measurable_toIcoMod_shift {E : Type*} [MeasurableSpace E] {p : ℝ} (hp : 0 < p)
    {a : E → ℝ} (ha : Measurable a) :
    Measurable (fun q : ℝ × E => (toIcoMod hp 0 (q.1 + a q.2), q.2)) :=
  ((measurable_toIcoMod_zero hp).comp (measurable_fst.add (ha.comp measurable_snd))).prodMk
    measurable_snd

lemma volume_inter_Ico_eq_Ioc (A : Set ℝ) (a b : ℝ) :
    volume (A ∩ Ico a b) = volume (A ∩ Ioc a b) :=
  measure_congr (ae_eq_set_inter (ae_eq_refl A) Ico_ae_eq_Ioc)

/-- Translation by `c` moves the window `[0,p)` to `[c, c + p)`. -/
lemma volume_Ico_inter_add_preimage {p : ℝ} (P : Set ℝ) (c : ℝ) :
    volume (Ico 0 p ∩ (fun x => x + c) ⁻¹' P) = volume (P ∩ Ico c (c + p)) := by
  have h : Ico 0 p ∩ (fun x => x + c) ⁻¹' P = (fun x => x + c) ⁻¹' (P ∩ Ico c (c + p)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, hP⟩
      exact ⟨hP, by linarith, by linarith⟩
    · rintro ⟨hP, h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, hP⟩
  rw [h, measure_preimage_add_right]

/-- Periodic-window invariance: the `p ℤ`-periodic set `toIcoMod⁻¹' S` has the same measure in
every fundamental window `Ioc c (c + p)`, in particular in `Ioc 0 p`. -/
lemma volume_toIcoMod_preimage_inter_Ioc {p : ℝ} {S : Set ℝ} (hp : 0 < p) (hS : MeasurableSet S)
    (c : ℝ) :
    volume (toIcoMod hp 0 ⁻¹' S ∩ Ioc c (c + p)) = volume (toIcoMod hp 0 ⁻¹' S ∩ Ioc 0 p) := by
  have hA : MeasurableSet (toIcoMod hp (0 : ℝ) ⁻¹' S) := measurable_toIcoMod_zero hp hS
  have hinv : ∀ g : AddSubgroup.zmultiples p,
      (fun x : ℝ => g +ᵥ x) ⁻¹' (toIcoMod hp 0 ⁻¹' S) = toIcoMod hp 0 ⁻¹' S := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
    ext x
    show toIcoMod hp 0 (k • p + x) ∈ S ↔ toIcoMod hp 0 x ∈ S
    rw [show k • p + x = x + k • p from add_comm _ _, toIcoMod_add_zsmul]
  have h := IsAddFundamentalDomain.measure_set_eq (isAddFundamentalDomain_Ioc hp c)
    (isAddFundamentalDomain_Ioc hp 0) hA hinv
  simpa only [zero_add] using h

/-- On `[0,p)` the representative map is the identity, so `toIcoMod⁻¹' S` and `S` agree there. -/
lemma toIcoMod_preimage_inter_Ico {p : ℝ} (hp : 0 < p) (S : Set ℝ) :
    toIcoMod hp 0 ⁻¹' S ∩ Ico 0 p = Ico 0 p ∩ S := by
  ext x
  have hx : x ∈ Ico (0 : ℝ) p → toIcoMod hp (0 : ℝ) x = x := fun h =>
    (toIcoMod_eq_self hp).mpr (by rwa [zero_add])
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by simpa [hx h2] using h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [hx h1] using h2, h1⟩

/-- Uniform translation on `[0,p)`: for measurable `S`, the mass of `S` is unchanged by the
representative map of a translate, `volume (Ico 0 p ∩ (x ↦ (x + c) mod p)⁻¹' S)`. -/
lemma volume_Ico_inter_map {p : ℝ} (hp : 0 < p) {S : Set ℝ} (hS : MeasurableSet S) (c : ℝ) :
    volume (Ico 0 p ∩ (fun x => toIcoMod hp 0 (x + c)) ⁻¹' S) = volume (Ico 0 p ∩ S) := by
  have h1 : (fun x => toIcoMod hp 0 (x + c)) ⁻¹' S =
      (fun x => x + c) ⁻¹' (toIcoMod hp 0 ⁻¹' S) := rfl
  rw [h1, volume_Ico_inter_add_preimage, volume_inter_Ico_eq_Ioc,
    volume_toIcoMod_preimage_inter_Ioc hp hS c, ← volume_inter_Ico_eq_Ioc,
    toIcoMod_preimage_inter_Ico hp S]

/-- The uniform law on `[0,p)` is invariant under `x ↦ (x + c) mod p` for every `c`. -/
theorem map_toIcoMod_add_uniformIco {p : ℝ} (hp : 0 < p) (c : ℝ) :
    (uniformIco p).map (fun x => toIcoMod hp 0 (x + c)) = uniformIco p := by
  have hf : Measurable (fun x : ℝ => toIcoMod hp (0 : ℝ) (x + c)) :=
    (measurable_toIcoMod_zero hp).comp (measurable_id.add_const c)
  ext S hS
  rw [Measure.map_apply hf hS]
  unfold uniformIco
  rw [ProbabilityTheory.cond_apply measurableSet_Ico,
    ProbabilityTheory.cond_apply measurableSet_Ico, volume_Ico_inter_map hp hS c]

/-- Tonelli step: the product law `uniformIco p ⊗ μ` is invariant under
`(u, ι) ↦ ((u + a ι) mod p, ι)`. -/
theorem map_prod_toIcoMod_add_uniformIco {p : ℝ} {E : Type*} [MeasurableSpace E] (hp : 0 < p)
    {μI : Measure E} [SFinite μI] {a : E → ℝ} (ha : Measurable a) :
    ((uniformIco p).prod μI).map (fun q : ℝ × E => (toIcoMod hp 0 (q.1 + a q.2), q.2)) =
      (uniformIco p).prod μI := by
  have := isProbabilityMeasure_uniformIco hp
  ext S hS
  rw [Measure.map_apply (measurable_toIcoMod_shift hp ha) hS,
    Measure.prod_apply_symm (measurable_toIcoMod_shift hp ha hS), Measure.prod_apply_symm hS]
  refine lintegral_congr fun ι => ?_
  have hSι : MeasurableSet ((fun x : ℝ => (x, ι)) ⁻¹' S) := measurable_prodMk_right hS
  have hf : Measurable (fun u : ℝ => toIcoMod hp 0 (u + a ι)) :=
    (measurable_toIcoMod_zero hp).comp (measurable_id.add_const (a ι))
  have hpre : (fun u : ℝ => (u, ι)) ⁻¹'
      ((fun q : ℝ × E => (toIcoMod hp 0 (q.1 + a q.2), q.2)) ⁻¹' S) =
      (fun u : ℝ => toIcoMod hp 0 (u + a ι)) ⁻¹' ((fun x : ℝ => (x, ι)) ⁻¹' S) := rfl
  rw [hpre, ← Measure.map_apply hf hSι, map_toIcoMod_add_uniformIco hp (a ι)]

/-- Joint independence. If `U ∼ uniformIco p` and `U ⊥ I`, and `a` is measurable, then
`V = (U + a(I)) mod p` is uniform on `[0,p)` and `V ⊥ I` (as random elements: the law of `(V, I)`
is the product `uniformIco p ⊗ P.map I`). -/
theorem indepFun_toIcoMod_add_uniformIco {p : ℝ} {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] (hp : 0 < p) {U : Ω → ℝ}
    {I : Ω → E} (hU : Measurable U) (hI : Measurable I) (hUlaw : P.map U = uniformIco p)
    (hind : ProbabilityTheory.IndepFun U I P) {a : E → ℝ} (ha : Measurable a) :
    P.map (fun ω => toIcoMod hp 0 (U ω + a (I ω))) = uniformIco p ∧
      ProbabilityTheory.IndepFun (fun ω => toIcoMod hp 0 (U ω + a (I ω))) I P := by
  have := isProbabilityMeasure_uniformIco hp
  have hV : Measurable (fun ω => toIcoMod hp 0 (U ω + a (I ω))) :=
    (measurable_toIcoMod_zero hp).comp (hU.add (ha.comp hI))
  have hUI : P.map (fun ω => (U ω, I ω)) = (uniformIco p).prod (P.map I) := by
    rw [← hUlaw]
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hI.aemeasurable).mp hind
  have hVI : P.map (fun ω => (toIcoMod hp 0 (U ω + a (I ω)), I ω)) =
      (uniformIco p).prod (P.map I) := by
    have hcomp : (fun ω => (toIcoMod hp 0 (U ω + a (I ω)), I ω)) =
        (fun q : ℝ × E => (toIcoMod hp 0 (q.1 + a q.2), q.2)) ∘ (fun ω => (U ω, I ω)) := rfl
    rw [hcomp, ← Measure.map_map (measurable_toIcoMod_shift hp ha) (hU.prodMk hI), hUI]
    exact map_prod_toIcoMod_add_uniformIco hp ha
  have hVlaw : P.map (fun ω => toIcoMod hp 0 (U ω + a (I ω))) = uniformIco p := by
    have h := congrArg (Measure.map Prod.fst) hVI
    rw [Measure.map_map measurable_fst (hV.prodMk hI), Measure.map_fst_prod,
      Measure.map_apply hI MeasurableSet.univ, preimage_univ, measure_univ, one_smul] at h
    exact h
  refine ⟨hVlaw, ?_⟩
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hI.aemeasurable, hVlaw]
  exact hVI

/-- Every measurable function of the data: `V ⊥ G(I)` for every measurable `G`. -/
theorem indepFun_toIcoMod_add_uniformIco_comp {p : ℝ} {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P] (hp : 0 < p)
    {U : Ω → ℝ} {I : Ω → E} (hU : Measurable U) (hI : Measurable I)
    (hUlaw : P.map U = uniformIco p) (hind : ProbabilityTheory.IndepFun U I P) {a : E → ℝ} (ha : Measurable a)
    {G : E → F} (hG : Measurable G) :
    ProbabilityTheory.IndepFun (fun ω => toIcoMod hp 0 (U ω + a (I ω))) (fun ω => G (I ω)) P :=
  (indepFun_toIcoMod_add_uniformIco hp hU hI hUlaw hind ha).2.comp measurable_id hG

end LatticeProb
