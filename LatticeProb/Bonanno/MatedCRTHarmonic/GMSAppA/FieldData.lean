/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.FieldData at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.DiskMarkov
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.IndepCancel

/-!
# The data `(E, C, Z)` of the Markov decomposition on `𝔻` and their independence

For a whole-plane GFF `h` normalized so that its circle average over a circle `∂B_R(w)` enclosing `𝔻̄` vanishes, and its
Markov decomposition `h = G + h̊` on `𝔻` (`DiskMarkov`):

* `C = h_1(0)`, `E = (G − h_1(0))|_𝔻` (the harmonic part minus its value `𝔥(0) = h_1(0)` at the centre, as a
  distribution on `𝔻`), `Z = h̊|_𝔻` (a zero-boundary GFF on `𝔻`);
* `h|_𝔻 = E + Z + C` a.s.;
* `Z` is independent of `σ(h|_{ℂ∖𝔻})`, which contains `σ(E, C)`; `E` is independent of `C`; hence `C` is independent
  of `(E, Z)`.

These are the independence statements used implicitly in the proof of [18] Lemma A.5
(: "`h − h_1(0)` and `h̃ − h̃_1(0)` are i.i.d."). The
independence of `E` and `C` combines Newton's theorem (`indepFun_circleAvg_restrict_nested`: `(h − h_1(0))|_𝔻` is
independent of `h_1(0) − h_R(w) = h_1(0)`) with the cancellation of the independent Gaussian summand `Z`
(`indepFun_of_add_of_isGaussianProcess`).

* `GMSAppA.indepFun_fst_prodMk_of` — `C ⊥ (E, Z)` from `E ⊥ C` and `Z ⊥ (E, C)`.
* `GMSAppA.DiskMarkov.{cAvg, Ed, Zd}` and their properties.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint LQGMetric.CircleAvg
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-! ### An independence lemma -/

/-- If `E` is independent of `C` and `Z` is independent of `(E, C)`, then `C` is independent of `(E, Z)`. -/
theorem indepFun_fst_prodMk_of {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → α} {C : Ω → β} {Z : Ω → γ} (hE : Measurable E) (hC : Measurable C) (hZ : Measurable Z)
    (hEC : IndepFun E C P) (hZEC : IndepFun Z (fun ω => (E ω, C ω)) P) :
    IndepFun C (fun ω => (E ω, Z ω)) P := by
  have hZE : IndepFun Z E P := hZEC.comp measurable_id measurable_fst
  rw [indepFun_iff_map_prod_eq_prod_map_map hC.aemeasurable (hE.prodMk hZ).aemeasurable]
  have hCm : IsProbabilityMeasure (P.map C) := (Measure.isProbabilityMeasure_map_iff hC.aemeasurable).2 ‹_›
  have hEZm : IsProbabilityMeasure (P.map fun ω => (E ω, Z ω)) :=
    (Measure.isProbabilityMeasure_map_iff (hE.prodMk hZ).aemeasurable).2 ‹_›
  symm
  let hD : (P.map fun ω => (E ω, Z ω)).FiniteSpanningSetsIn
      (Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set γ | MeasurableSet t}) :=
    { set := fun _ => univ
      set_mem := fun _ => ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩
      finite := fun _ => measure_lt_top _ _
      spanning := iUnion_const univ }
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set γ | MeasurableSet t})
    MeasurableSpace.generateFrom_measurableSet generateFrom_prod
    MeasurableSpace.isPiSystem_measurableSet isPiSystem_prod
    (P.map C).toFiniteSpanningSetsIn hD ?_
  intro s hs t ht
  obtain ⟨A, hA, B, hB, rfl⟩ := ht
  have hmeas : MeasurableSet (s ×ˢ (A ×ˢ B)) := hs.prod (hA.prod hB)
  rw [Measure.map_apply (hC.prodMk (hE.prodMk hZ)) hmeas,
    Measure.map_apply hC hs, Measure.map_apply (hE.prodMk hZ) (hA.prod hB)]
  have e1 : (fun ω => (C ω, E ω, Z ω)) ⁻¹' (s ×ˢ (A ×ˢ B)) =
      Z ⁻¹' B ∩ (fun ω => (E ω, C ω)) ⁻¹' (A ×ˢ s) := by
    ext ω; simp [and_comm, and_assoc, and_left_comm]
  have e2 : (fun ω => (E ω, Z ω)) ⁻¹' (A ×ˢ B) = E ⁻¹' A ∩ Z ⁻¹' B := by ext ω; simp
  have e3 : (fun ω => (E ω, C ω)) ⁻¹' (A ×ˢ s) = E ⁻¹' A ∩ C ⁻¹' s := by ext ω; simp
  rw [e1, (indepFun_iff_measure_inter_preimage_eq_mul.1 hZEC) B (A ×ˢ s) hB (hA.prod hs), e3,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 hEC) A s hA hs, e2,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 hZE.symm) A B hA hB]
  ring

/-! ### The data of the decomposition -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

namespace DiskMarkov

/-- `C = h_1(0)` -/
def cAvg (h : Ω → DistC) (ω : Ω) : ℝ := circleAvg (h ω) 1 0

/-- `E = (G − h_1(0))|_𝔻` -/
def Ed (M : DiskMarkov P h) (ω : Ω) : DistOn (ballO 0 1) :=
  restrictTo (ballO 0 1) (addConst (M.G ω) (-cAvg h ω))

/-- `Z = h̊|_𝔻` -/
def Zd (M : DiskMarkov P h) (ω : Ω) : DistOn (ballO 0 1) := restrictTo (ballO 0 1) (M.hz ω)

lemma measurable_cAvg_ext (h : Ω → DistC) : Measurable[extSigma h] (cAvg h) :=
  measurable_circleAvg_one h

lemma measurable_Ed_ext (M : DiskMarkov P h) : Measurable[extSigma h] M.Ed :=
  (measurable_restrictTo _).comp
    (GFFInv.measurable_distC_iff.2 fun φ => by
      simp only [GFFInv.addConst_apply]
      exact ((measurable_distOn_apply φ).comp M.G_meas).add
        ((measurable_cAvg_ext h).neg.const_mul _))

lemma measurable_Zd (M : DiskMarkov P h) : Measurable M.Zd := M.zb.measurable

lemma comap_Zd_le (M : DiskMarkov P h) :
    MeasurableSpace.comap M.Zd inferInstance ≤ MeasurableSpace.comap M.hz inferInstance := by
  rw [show M.Zd = restrictTo (ballO 0 1) ∘ M.hz from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_restrictTo _).comap_le

/-- `Z` is independent of `σ(h|_{ℂ∖𝔻})` -/
lemma indep_ext_Zd (M : DiskMarkov P h) :
    Indep (extSigma h) (MeasurableSpace.comap M.Zd inferInstance) P :=
  (indep_of_indep_of_le_left M.indep M.comap_Zd_le).symm

/-- `h|_𝔻 = E + Z + C` a.s. -/
lemma restrictTo_eq (M : DiskMarkov P h) :
    ∀ᵐ ω ∂P, restrictTo (ballO 0 1) (h ω) = addConstOn (ballO 0 1) (M.Ed ω + M.Zd ω) (cAvg h ω) := by
  filter_upwards [M.dec] with ω hω
  ext φ
  rw [addConstOn_apply, hω]
  simp only [Ed, Zd, add_apply, LQGMetric.DG.L22T.restrictTo_addConst]
  have e : restrictTo (ballO 0 1) (M.G ω + M.hz ω) φ =
      restrictTo (ballO 0 1) (M.G ω) φ + restrictTo (ballO 0 1) (M.hz ω) φ := rfl
  rw [e]
  ring

/-- `(h − h_1(0))|_𝔻 = E + Z` a.s. -/
lemma restrictTo_sub_eq (M : DiskMarkov P h) :
    ∀ᵐ ω ∂P, restrictTo (ballO 0 1) (addConst (h ω) (-cAvg h ω)) = M.Ed ω + M.Zd ω := by
  filter_upwards [M.dec] with ω hω
  ext φ
  simp only [Ed, Zd, add_apply, LQGMetric.DG.L22T.restrictTo_addConst, hω]
  have e : restrictTo (ballO 0 1) (M.G ω + M.hz ω) φ =
      restrictTo (ballO 0 1) (M.G ω) φ + restrictTo (ballO 0 1) (M.hz ω) φ := rfl
  rw [e]
  ring

/-- the pairing map `𝒟'(𝔻) → (𝓓(𝔻) → ℝ)` -/
def pairMap (T : DistOn (ballO 0 1)) : TestOn (ballO 0 1) → ℝ := fun φ => T φ

lemma measurable_pairMap : Measurable pairMap :=
  measurable_pi_iff.2 fun φ => measurable_distOn_apply φ

lemma comap_pairMap {β : Type*} (f : β → DistOn (ballO 0 1)) :
    MeasurableSpace.comap (pairMap ∘ f) MeasurableSpace.pi =
      MeasurableSpace.comap f inferInstance := by
  rw [← MeasurableSpace.comap_comp]; rfl

/-- **`E` is independent of `C = h_1(0)`** (normalization on a circle `∂B_R(w)` enclosing `𝔻̄`). -/
theorem indepFun_Ed_cAvg [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P)
    {R : ℝ} {w : ℂ} (hR : 0 < R) (hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) R w = 0) : IndepFun M.Ed (cAvg h) P := by
  have hm : extSigma h ≤ ‹MeasurableSpace Ω› := extSigma_le hh.measurable
  have hEm : Measurable M.Ed := M.measurable_Ed_ext.mono hm le_rfl
  have hCm : Measurable (cAvg h) := (measurable_cAvg_ext h).mono hm le_rfl
  set Xp : Ω → TestOn (ballO 0 1) → ℝ := pairMap ∘ M.Ed
  set Yp : Ω → TestOn (ballO 0 1) → ℝ := pairMap ∘ M.Zd
  have hXp : Measurable Xp := measurable_pairMap.comp hEm
  have hYp : Measurable Yp := measurable_pairMap.comp M.measurable_Zd
  -- (i) `X + Y = (h − h_1(0))|_𝔻` is independent of `C`
  have H := indepFun_circleAvg_restrict_nested hh one_pos hR hnest (ballO 0 1) ball_subset_closedBall
  have H' := H.symm.comp measurable_pairMap measurable_id
  have hsum : IndepFun (Xp + Yp) (cAvg h) P := by
    refine H'.congr ?_ ?_
    · filter_upwards [M.restrictTo_sub_eq] with ω hω
      show pairMap (restrictTo (ballO 0 1) (addConst (h ω) (-circleAvg (h ω) 1 0))) = _
      rw [show circleAvg (h ω) 1 0 = cAvg h ω from rfl, hω]
      rfl
    · filter_upwards [hn] with ω hω
      simp only [Function.comp_apply, id, hω, sub_zero]
      rfl
  -- (ii) `Y` is independent of `(X, C)`
  have hYXC : IndepFun Yp (fun ω => (Xp ω, cAvg h ω)) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left M.indep_ext_Zd.symm ?_) ?_
    · rw [show Yp = pairMap ∘ M.Zd from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono measurable_pairMap.comap_le
    · exact ((measurable_pairMap.comp M.measurable_Ed_ext).prodMk (measurable_cAvg_ext h)).comap_le
  -- (iii) `Y` is a Gaussian process
  have hYG : IsGaussianProcess (fun φ ω => Yp ω φ) P := M.zb.process.gaussian
  have hX := indepFun_of_add_of_isGaussianProcess hXp hYp hCm hsum hYXC hYG
  rw [IndepFun_iff_Indep] at hX ⊢
  rwa [show MeasurableSpace.comap Xp MeasurableSpace.pi = MeasurableSpace.comap M.Ed inferInstance
    from comap_pairMap M.Ed] at hX

/-- **`C` is independent of `(E, Z)`** and **`E` of `Z`**. -/
theorem indepFun_cAvg_EdZd [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P)
    {R : ℝ} {w : ℂ} (hR : 0 < R) (hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) R w = 0) :
    IndepFun (cAvg h) (fun ω => (M.Ed ω, M.Zd ω)) P ∧ IndepFun M.Ed M.Zd P := by
  have hm : extSigma h ≤ ‹MeasurableSpace Ω› := extSigma_le hh.measurable
  have hEm : Measurable M.Ed := M.measurable_Ed_ext.mono hm le_rfl
  have hCm : Measurable (cAvg h) := (measurable_cAvg_ext h).mono hm le_rfl
  have hZEC : IndepFun M.Zd (fun ω => (M.Ed ω, cAvg h ω)) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right M.indep_ext_Zd.symm
      (M.measurable_Ed_ext.prodMk (measurable_cAvg_ext h)).comap_le
  refine ⟨indepFun_fst_prodMk_of hEm hCm M.measurable_Zd
    (M.indepFun_Ed_cAvg hh hR hnest hn) hZEC, ?_⟩
  exact (hZEC.comp measurable_id measurable_fst).symm

end DiskMarkov

end MatedCRTHarmonic.GMSAppA
