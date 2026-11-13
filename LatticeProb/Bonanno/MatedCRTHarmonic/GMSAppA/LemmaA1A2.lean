/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA1A2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.FarCircle
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108L2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2D

/-!
# [18] Lemmas A.1 and A.2: conditioning on the average over an enclosing circle

[18] = Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv 1807.07511v3.

**Lemma A.1** : "Let `h` be a whole-plane GFF normalized so that `h_1(0) = 0`. Also fix `ρ ∈ (0,1)` and
let `R ≥ (1 − ρ)^{-1}` and `w ∈ ℂ` be such that `|w| ≤ ρR`, so that `𝔻 ⊂ B_R(w)`. For `a ∈ ℝ`, the conditional law of
`h|_𝔻` given `{h_R(w) = a}` is absolutely continuous with respect to the unconditional law of `h|_𝔻`. Furthermore,
for each `p₀ > 0` there are constants `R_* ≥ (1−ρ)^{-1}` and `c > 0` depending only on `p₀` and `ρ` such that for each
`p ∈ [−p₀, ∞)` and `R ≥ R_*`, the Radon–Nikodym derivative `M_a` satisfies
`E[M_a^p] ≲ exp(c|p| a² |w|² / (R⁴ (log R)²))`."

**Lemma A.2** : "Let `h` be a whole-plane GFF normalized so that its circle average over `∂𝔻` is 0. Also
let `ρ ∈ (0,1]` and `δ ∈ (0, 1−ρ)`. For `a ∈ ℝ` and `z ∈ B_ρ(0)`, the conditional law of `h|_{B_δ(z)}` given
`{h_δ(z) = a}` is absolutely continuous with respect to the law of a whole-plane GFF in `B_δ(z)` normalized so that its
circle average over `∂B_δ(z)` is `a`. Furthermore … `E[M_a^p] ≲ exp(c|p| δ² a² |z|² / (log δ^{-1})²)`."

## What is proved here: both lemmas hold with `M_a ≡ 1`

The circle average over a circle `∂B_r(w)` that encloses `B̄_ρ(z)` is **independent** of `(h − h_ρ(z))|_{B_ρ(z)}`
(`GMSAppA.indepFun_circleAvg_restrict_nested`; Newton's theorem: `∫ log|x − y| dσ_{w,r}(x) = log r` for every `y` with
`|y − w| ≤ r`). Hence in Lemma A.1 the conditional law of `h|_𝔻` given `h_R(w) = a` *is* the unconditional law, and in
Lemma A.2 the conditional law of `h|_{B_δ(z)}` given `h_δ(z) = a` *is* the law of `(h − h_δ(z) + a)|_{B_δ(z)}`, a
whole-plane GFF normalized to have circle average `a` over `∂B_δ(z)`. The Radon–Nikodym derivatives are identically
`1`, so (A.1) and (A.5) hold with `E[M_a^p] = 1` for every `p` and `a`, and the size conditions `R ≥ R_*`, `δ ≤ δ_*`
are unnecessary: only `B̄_1(0) ⊆ B̄_R(w)`, resp. `B̄_δ(z) ⊆ B̄_1(0)`, is used.

**Erratum of [18] (proof of Lemma A.1).** The step "by the mean value property of harmonic functions,
`𝔥_R(w) = 𝔥(1/w̃)`" is incorrect: the inversion `z ↦ 1/z` maps the uniform measure on `∂B_R(w)` to the harmonic
measure of the image disk seen from `0` (the reflection of `1/w` in the image circle), not to the uniform measure
around the centre `w̃`; so `𝔥_R(w) = 𝔥(∞) = 0`, and the variance `log((1−|w̃|²)^{-1})` of (A.4) is `0`. The lemma's
statement survives (with `M_a ≡ 1`). Independently, the paper's exponent `c|p|` in (A.1) does not follow from its own
formula (A.4), whose exponent is `p(p−1) a² v₁ / (2 log R̃ (log R̃ + (p−1) v₁))` and grows like `p²` for large `p`;
this is moot since `M_a ≡ 1`.

## Main declarations
* `GMSAppA.closedBall_subset_of_lemmaA1` — the paper's hypotheses give `B̄_1(0) ⊆ B̄_R(w)`.
* `GMSAppA.lemmaA1_indepFun`, `GMSAppA.lemmaA1_map_eq_compProd` — Lemma A.1 (conditional law = unconditional law).
* `GMSAppA.closedBall_subset_of_lemmaA2` — the paper's hypotheses give `B̄_δ(z) ⊆ B̄_1(0)`.
* `GMSAppA.lemmaA2_indepFun`, `GMSAppA.lemmaA2_condExp` — Lemma A.2 (conditional law = law of the GFF re-normalized
  at `∂B_δ(z)` to have average `a`), and `GMSAppA.lemmaA2_isWholePlaneGFF` (that field is a whole-plane GFF with
  circle average `a` over `∂B_δ(z)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMSAppA

/-! ### Adding a constant on an open set -/

/-- `T + c` for a distribution `T` on `U` and a constant `c`. -/
def addConstOn (U : Opens ℂ) (T : DistOn U) (c : ℝ) : DistOn U :=
  T + restrictTo U (addConst 0 c)

lemma addConstOn_apply (U : Opens ℂ) (T : DistOn U) (c : ℝ) (φ : TestOn U) :
    addConstOn U T c φ = T φ + (∫ x, φ x) * c := by
  show T φ + restrictTo U (addConst 0 c) φ = _
  rw [DG.L22T.restrictTo_addConst]
  have : restrictTo U 0 φ = 0 := rfl
  rw [this, zero_add]

lemma restrictTo_addConst_eq_addConstOn (U : Opens ℂ) (g : DistC) (c : ℝ) :
    restrictTo U (addConst g c) = addConstOn U (restrictTo U g) c := by
  ext φ
  rw [addConstOn_apply, DG.L22T.restrictTo_addConst]

lemma measurable_addConstOn (U : Opens ℂ) :
    Measurable fun p : ℝ × DistOn U => addConstOn U p.2 p.1 := by
  refine measurable_distOn_iff.2 fun φ => ?_
  simp only [addConstOn_apply]
  exact ((measurable_distOn_apply φ).comp measurable_snd).add (measurable_fst.const_mul _)

/-! ### Lemma A.1 -/

/-- The hypotheses of [18] Lemma A.1 (`ρ ∈ (0,1)`, `R ≥ (1−ρ)^{-1}`, `|w| ≤ ρR`) give `B̄_1(0) ⊆ B̄_R(w)`. -/
lemma closedBall_subset_of_lemmaA1 {ρ R : ℝ} {w : ℂ} (hρ1 : ρ < 1) (hR : (1 - ρ)⁻¹ ≤ R)
    (hw : ‖w‖ ≤ ρ * R) : closedBall (0 : ℂ) 1 ⊆ closedBall w R := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [mem_closedBall, dist_eq_norm]
  have h1 : 1 ≤ (1 - ρ) * R := by
    have := mul_le_mul_of_nonneg_left hR (by linarith : 0 ≤ 1 - ρ)
    rwa [mul_inv_cancel₀ (by linarith)] at this
  calc ‖x - w‖ ≤ ‖x‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 1 + ρ * R := add_le_add hx hw
    _ ≤ R := by nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **[18] Lemma A.1, independence form.** For a whole-plane GFF normalized by `h_1(0) = 0` and a circle `∂B_R(w)`
enclosing `B̄_1(0)`, the circle average `h_R(w)` is independent of `h|_𝔻`. -/
theorem lemmaA1_indepFun (hh : IsNormalizedWPGFF h P) {R : ℝ} {w : ℂ} (hR : 0 < R)
    (hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R) :
    IndepFun (fun ω => circleAvg (h ω) R w) (fun ω => restrictTo (ballO 0 1) (h ω)) P := by
  have H := indepFun_circleAvg_restrict_nested hh.1 one_pos hR hnest (ballO 0 1)
    ball_subset_closedBall
  have hf : (fun ω => circleAvg (h ω) 1 0 - circleAvg (h ω) R w) =ᵐ[P]
      fun ω => -circleAvg (h ω) R w := by
    filter_upwards [hh.2] with ω hω
    rw [hω, zero_sub]
  have hg : (fun ω => restrictTo (ballO 0 1) (addConst (h ω) (-circleAvg (h ω) 1 0))) =ᵐ[P]
      fun ω => restrictTo (ballO 0 1) (h ω) := by
    filter_upwards [hh.2] with ω hω
    rw [hω, neg_zero, GFFLaw.addConst_zero']
  have H2 := (H.congr hf hg).comp (φ := fun x : ℝ => -x) (ψ := id) measurable_neg measurable_id
  convert H2 using 1
  · funext ω
    simp
  · rfl

/-- **[18] Lemma A.1, conditional-law form.** The joint law of `(h_R(w), h|_𝔻)` is the law of `h_R(w)` composed with
The constant kernel `a ↦ law(h|_𝔻)`: the conditional law of `h|_𝔻` given `h_R(w) = a` is the unconditional law, with
Radon–Nikodym derivative `M_a ≡ 1` (so `E[M_a^p] = 1` for all `p`, `a`). -/
theorem lemmaA1_map_eq_compProd (hh : IsNormalizedWPGFF h P) {R : ℝ} {w : ℂ} (hR : 0 < R)
    (hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R) :
    P.map (fun ω => (circleAvg (h ω) R w, restrictTo (ballO 0 1) (h ω))) =
      (P.map fun ω => circleAvg (h ω) R w) ⊗ₘ
        Kernel.const ℝ (P.map fun ω => restrictTo (ballO 0 1) (h ω)) := by
  have := hh.1.gaussian.isProbabilityMeasure
  rw [Measure.compProd_const]
  exact (lemmaA1_indepFun hh hR hnest).map_prod_eq_prod_map_map
    ((measurable_circleAvg_left R w).comp hh.1.measurable).aemeasurable
    ((measurable_restrictTo _).comp hh.1.measurable).aemeasurable

/-! ### Lemma A.2 -/
/-- The hypotheses of [18] Lemma A.2 (`δ ∈ (0, 1−ρ)`, `z ∈ B_ρ(0)`) give `B̄_δ(z) ⊆ B̄_1(0)`. -/
lemma closedBall_subset_of_lemmaA2 {ρ δ : ℝ} {z : ℂ} (hδ : δ < 1 - ρ) (hz : ‖z‖ < ρ) :
    closedBall z δ ⊆ closedBall (0 : ℂ) 1 := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 1 := by linarith

/-- **[18] Lemma A.2, independence form.** For a whole-plane GFF normalized by `h_1(0) = 0` and `B̄_δ(z) ⊆ B̄_1(0)`,
The circle average `h_δ(z)` is independent of `(h − h_δ(z))|_{B_δ(z)}`. -/
theorem lemmaA2_indepFun (hh : IsNormalizedWPGFF h P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1) :
    IndepFun (fun ω => circleAvg (h ω) δ z)
      (fun ω => restrictTo (ballO z δ) (addConst (h ω) (-circleAvg (h ω) δ z))) P := by
  have H := indepFun_circleAvg_restrict_nested hh.1 hδ one_pos hnest (ballO z δ)
    ball_subset_closedBall
  have hf : (fun ω => circleAvg (h ω) δ z - circleAvg (h ω) 1 0) =ᵐ[P]
      fun ω => circleAvg (h ω) δ z := by
    filter_upwards [hh.2] with ω hω
    rw [hω, sub_zero]
  exact H.congr hf (ae_of_all _ fun _ => rfl)

/-- The field `h − h_δ(z) + a` of [18] Lemma A.2 is a whole-plane GFF whose circle average over `∂B_δ(z)` is `a`. -/
theorem lemmaA2_isWholePlaneGFF (hh : IsWholePlaneGFF h P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ) (a : ℝ) :
    IsWholePlaneGFF (fun ω => addConst (h ω) (-circleAvg (h ω) δ z + a)) P ∧
      ∀ᵐ ω ∂P, circleAvg (addConst (h ω) (-circleAvg (h ω) δ z + a)) δ z = a := by
  refine ⟨hh.addConst (((measurable_circleAvg_left δ z).comp hh.measurable).neg.add_const a), ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst hh z hδ] with ω hω
  rw [hω]
  ring

/-- **[18] Lemma A.2, conditional-law form.** For a whole-plane GFF normalized by `h_1(0) = 0`, `B̄_δ(z) ⊆ B̄_1(0)` and
every bounded measurable functional `F` of a distribution on `B_δ(z)`,
`E[F(h|_{B_δ(z)}) | h_δ(z)] = Φ(h_δ(z))` with `Φ(a) = E[F((h − h_δ(z) + a)|_{B_δ(z)})]`: the conditional law of
`h|_{B_δ(z)}` given `h_δ(z) = a` is the law of the whole-plane GFF `h − h_δ(z) + a`, normalized to have circle average
`a` over `∂B_δ(z)` (`lemmaA2_isWholePlaneGFF`), with Radon–Nikodym derivative `M_a ≡ 1`. -/
theorem lemmaA2_condExp (hh : IsNormalizedWPGFF h P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1) {F : DistOn (ballO z δ) → ℝ} (hF : Measurable F)
    {C : ℝ} (hFb : ∀ T, |F T| ≤ C) :
    P[(fun ω => F (restrictTo (ballO z δ) (h ω))) |
        MeasurableSpace.comap (fun ω => circleAvg (h ω) δ z) inferInstance] =ᵐ[P]
      fun ω => ∫ ω', F (restrictTo (ballO z δ)
        (addConst (h ω') (-circleAvg (h ω') δ z + circleAvg (h ω) δ z))) ∂P := by
  have := hh.1.gaussian.isProbabilityMeasure
  set S : Ω → ℝ := fun ω => circleAvg (h ω) δ z
  set R : Ω → DistOn (ballO z δ) := fun ω => restrictTo (ballO z δ) (addConst (h ω) (-S ω))
  have hSm : Measurable S := (measurable_circleAvg_left δ z).comp hh.1.measurable
  have hRm : Measurable R :=
    (measurable_restrictTo (ballO z δ)).comp (hh.1.addConst hSm.neg).measurable
  set G : ℝ × DistOn (ballO z δ) → ℝ := fun p => F (addConstOn (ballO z δ) p.2 p.1)
  have hGm : Measurable G := hF.comp (measurable_addConstOn (ballO z δ))
  have hdec : ∀ ω, restrictTo (ballO z δ) (h ω) = addConstOn (ballO z δ) (R ω) (S ω) := by
    intro ω
    rw [← restrictTo_addConst_eq_addConstOn, GFFLaw.addConst_addConst, neg_add_cancel,
      GFFLaw.addConst_zero']
  have hind : Indep (MeasurableSpace.comap S inferInstance)
      (MeasurableSpace.comap R inferInstance) P := by
    have := lemmaA2_indepFun hh hδ hnest
    exact this
  have key := CONF.condExp_comp_indep (𝓖 := MeasurableSpace.comap S inferInstance)
    hSm.comap_le (comap_measurable S) hRm hind hGm (C := C) (fun p => hFb _)
  have e1 : (fun ω => F (restrictTo (ballO z δ) (h ω))) = fun ω => G (S ω, R ω) := by
    funext ω
    rw [hdec]
  rw [e1]
  refine key.trans (ae_of_all _ fun ω => ?_)
  simp only
  rw [integral_map (f := fun r => G (S ω, r)) hRm.aemeasurable
    (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  congr 1
  funext ω'
  simp only [G, R]
  rw [← restrictTo_addConst_eq_addConstOn, GFFLaw.addConst_addConst]

end MatedCRTHarmonic.GMSAppA
