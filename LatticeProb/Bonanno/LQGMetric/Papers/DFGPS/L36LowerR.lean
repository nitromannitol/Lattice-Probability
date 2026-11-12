/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36LowerR at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Scale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS Lemma 3.6 (arXiv:1905.00380, T:1628–1650), lower half: w.p. → 1 as `δ → 0`, uniformly in
`𝕣 > 0`, `D̃^{δ𝕣}_h(∂_L(𝕣𝕊), ∂_R(𝕣𝕊); 𝕣𝕊) ≥ δ^{−ξQ+ζ} e^{ξ h_𝕣(0)}`.
The reduction to `𝕣 = 1` follows T:1640–1644 (`L36Scale`): `h' = h(𝕣·) − h_𝕣(0)` has the law of `h`
(`CircleAvg.map_affine_sub_circleAvg`) and the event for `(h, 𝕣)` is, up to a null set, the event
for `(h', 1)`; the latter is a measurable set of fields (the graph LFPP is a countable infimum), so
its probability is that for `(h, 1)`, bounded by `lem3_6_lower_one`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint

/-- admissible graph paths form a countable family -/
instance countable_adm (ε : ℝ) (U A B : Set ℂ) :
    Countable {L : List ℂ // IsGraphPath ε U L ∧ (∃ x ∈ L.head?, x ∈ A) ∧
      ∃ y ∈ L.getLast?, y ∈ B} := by
  have hG : (gridPts ε).Countable := by
    have : gridPts ε = range fun ab : ℤ × ℤ => (⟨ab.1 * ε, ab.2 * ε⟩ : ℂ) := by
      ext w; simp [gridPts, eq_comm]
    rw [this]; exact countable_range _
  haveI := hG.to_subtype
  let f : {L : List ℂ // IsGraphPath ε U L ∧ (∃ x ∈ L.head?, x ∈ A) ∧
      ∃ y ∈ L.getLast?, y ∈ B} → List (gridPts ε) :=
    fun L => L.1.attach.map fun x => ⟨x.1, (L.2.1.2.1 x.1 x.2).2⟩
  refine Function.Injective.countable (f := f) fun L L' hLL' => Subtype.ext ?_
  have key : ∀ L : {L : List ℂ // IsGraphPath ε U L ∧ (∃ x ∈ L.head?, x ∈ A) ∧
      ∃ y ∈ L.getLast?, y ∈ B}, (f L).map Subtype.val = L.1 := fun L => by
    simp [f, List.map_attach_eq_pmap]
  rw [← key L, ← key L', hLL']

lemma measurable_listSum {α : Type*} [MeasurableSpace α] (F : α → ℂ → ℝ)
    (hF : ∀ x, Measurable fun a => F a x) (l : List ℂ) :
    Measurable fun a => (l.map (F a)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF x).add ih

lemma measurable_graphLFPP_circ (ξ ε : ℝ) (A B U : Set ℂ) :
    Measurable fun g : DistC => graphLFPP ξ ε (fun x => circleAvg g ε x) A B U := by
  unfold graphLFPP
  refine Measurable.iInf fun L => ?_
  exact measurable_listSum (fun g x => Real.exp (ξ * circleAvg g ε x))
    (fun x => ((measurable_circleAvg_left ε x).const_mul ξ).exp) L.1

/-- **Scale reduction** (T:1640–1644). For a measurable `S ⊆ ℝ²` invariant under
`(x, y) ↦ (x, y)/t` (`t > 0`), the probability that `(e^{ξ h_𝕣(0)}, D̃^{δ𝕣}_h(…; 𝕣𝕊)) ∈ S` is at most
the probability that `(e^{ξ h_1(0)}, D̃^δ_h(…; 𝕊)) ∈ S`. -/
theorem prob_scale_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) (ξ : ℝ) {δ : ℝ} (hδ0 : 0 < δ) {𝕣 : ℝ}
    (h𝕣 : 0 < 𝕣) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hSinv : ∀ t : ℝ, 0 < t → ∀ x y : ℝ, (t * x, t * y) ∈ S → (x, y) ∈ S) :
    P {ω | (Real.exp (ξ * circleAvg (h ω) 𝕣 0),
        graphLFPP ξ (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
          (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣)) ∈ S} ≤
      P {ω | (Real.exp (ξ * circleAvg (h ω) 1 0),
        graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1) (rS 1)) ∈ S} := by
  set E : Set DistC := {g | (Real.exp (ξ * circleAvg g 1 0),
    graphLFPP ξ δ (fun x => circleAvg g δ x) (leftVerts δ 1) (rightVerts δ 1) (rS 1)) ∈ S}
    with hEdef
  have hE : MeasurableSet E :=
    (((measurable_circleAvg_left 1 0).const_mul ξ).exp.prodMk
      (measurable_graphLFPP_circ ξ δ _ _ _)) hS
  set c : Ω → ℝ := fun ω => circleAvg (h ω) 𝕣 0 with hc
  set g : Ω → DistC := fun ω => affineComp 𝕣 0 (h ω) with hgdef
  set h' : Ω → DistC := fun ω => addConst (g ω) (-c ω) with hh'def
  have hg : IsWholePlaneGFF g P := hh.1.affineComp h𝕣 0
  have hcm : Measurable c := (measurable_circleAvg_left 𝕣 0).comp hh.1.measurable
  have hh'm : Measurable h' := (hg.addConst hcm.neg).measurable
  have hmap : P.map h' = P.map h := CircleAvg.map_affine_sub_circleAvg hh h𝕣 0
  have h2 : P (h' ⁻¹' E) = P (h ⁻¹' E) := by
    rw [← Measure.map_apply hh'm hE, hmap, Measure.map_apply hh.1.measurable hE]
  -- the null set
  set u : ℤ × ℤ → ℂ := fun ab => ⟨ab.1 * δ, ab.2 * δ⟩
  set N := {ω | ¬ (circleAvg (h' ω) 1 0 = 0 ∧ ∀ ab : ℤ × ℤ,
    circleAvg (h' ω) δ (u ab) = circleAvg (h ω) (δ * 𝕣) ((𝕣 : ℂ) * u ab) - c ω)} with hN
  have hN0 : P N = 0 := by
    have hA : ∀ᵐ ω ∂P, circleAvg (h' ω) 1 0 = 0 := by
      filter_upwards [CircleAvg.ae_circleAvg_addConst hg 0 one_pos,
        CircleAvg.ae_circleAvg_affineComp hh.1 h𝕣 0] with ω h1 h2
      simp only [hh'def, hgdef] at h1 h2 ⊢
      rw [h1, h2]; ring
    have hB : ∀ᵐ ω ∂P, ∀ ab : ℤ × ℤ,
        circleAvg (h' ω) δ (u ab) = circleAvg (h ω) (δ * 𝕣) ((𝕣 : ℂ) * u ab) - c ω := by
      refine ae_all_iff.2 fun ab => ?_
      filter_upwards [CircleAvg.ae_circleAvg_addConst hg (u ab) hδ0,
        CircleAvg.ae_circleAvg_affineComp hg hδ0 (u ab),
        CircleAvg.ae_circleAvg_affineComp hh.1 (mul_pos h𝕣 hδ0) ((𝕣 : ℂ) * u ab + 0)]
        with ω e1 e2 e3
      simp only [hh'def, hgdef] at e1 e2 e3 ⊢
      rw [e1 (-c ω), ← e2, GM.affineComp_comp hδ0.ne' h𝕣.ne', e3, add_zero, mul_comm 𝕣 δ]
      ring
    have := hA.and hB
    rwa [ae_iff] at this
  have hsub : {ω | (Real.exp (ξ * circleAvg (h ω) 𝕣 0),
      graphLFPP ξ (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
        (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣)) ∈ S} ⊆ h' ⁻¹' E ∪ N := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or, mem_preimage] at hcon
    obtain ⟨hEω, hNω⟩ := hcon
    simp only [hN, mem_setOf_eq, not_not] at hNω
    apply hEω
    simp only [hEdef, mem_setOf_eq, hNω.1, mul_zero, Real.exp_zero]
    simp only [mem_setOf_eq] at hω
    rw [graphLFPP_scale h𝕣] at hω
    have hcongr : graphLFPP ξ δ (fun x => circleAvg (h ω) (δ * 𝕣) ((𝕣 : ℂ) * x))
        (leftVerts δ 1) (rightVerts δ 1) (rS 1) =
        graphLFPP ξ δ (fun x => circleAvg (h' ω) δ x + c ω)
          (leftVerts δ 1) (rightVerts δ 1) (rS 1) :=
      graphLFPP_congr fun x _ ⟨p, q, hx⟩ => by
        have := hNω.2 (p, q)
        simp only [u] at this
        rw [hx, this]; ring
    rw [hcongr, graphLFPP_add_const] at hω
    refine hSinv (Real.exp (ξ * c ω)) (Real.exp_pos _) _ _ ?_
    rw [mul_one]; exact hω
  calc P _ ≤ P (h' ⁻¹' E ∪ N) := measure_mono hsub
    _ ≤ P (h' ⁻¹' E) + P N := measure_union_le _ _
    _ = P (h ⁻¹' E) := by rw [hN0, add_zero, h2]
    _ = _ := rfl

/-- **DFGPS Lemma 3.6, lower bound** (all `𝕣 > 0` with one `δ₀`). -/
theorem lem3_6_lower (hKU : DGThm1_5KU) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) {ζ : ℝ} (hζ : 0 < ζ) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P {ω | ¬ δ ^ (-xiGamma γ * Q γ + ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 𝕣 0) ≤
        graphLFPP (xiGamma γ) (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
          (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣)} ≤ ENNReal.ofReal η := by
  obtain ⟨δ₀, hδ₀, H1⟩ := lem3_6_lower_one hKU hγ0 hγ2 P h hh hζ hη
  refine ⟨δ₀, hδ₀, fun δ hδ 𝕣 h𝕣 => ?_⟩
  set a := -xiGamma γ * Q γ + ζ
  have hS : MeasurableSet {p : ℝ × ℝ | ¬ δ ^ a * p.1 ≤ p.2} :=
    (measurableSet_le (measurable_const.mul measurable_fst) measurable_snd).compl
  refine (prob_scale_le P h hh (xiGamma γ) hδ.1 h𝕣 _ hS fun t ht x y hxy => ?_).trans (H1 δ hδ)
  simp only [mem_setOf_eq] at hxy ⊢
  intro hle; apply hxy
  calc δ ^ a * (t * x) = t * (δ ^ a * x) := by ring
    _ ≤ t * y := mul_le_mul_of_nonneg_left hle ht.le

/-- **DFGPS Lemma 3.6, upper bound, reduction to `𝕣 = 1`.** -/
theorem lem3_6_upper_of_one {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) {ζ η δ₀ : ℝ}
    (H1 : ∀ δ ∈ Ioo (0 : ℝ) δ₀, P {ω | ¬ graphLFPP (xiGamma γ) δ (fun x => circleAvg (h ω) δ x)
        (leftVerts δ 1) (rightVerts δ 1) (rS 1) ≤
          δ ^ (-xiGamma γ * Q γ - ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 1 0)} ≤
        ENNReal.ofReal η) :
    ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P {ω | ¬ graphLFPP (xiGamma γ) (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
          (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣) ≤
        δ ^ (-xiGamma γ * Q γ - ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 𝕣 0)} ≤
        ENNReal.ofReal η := by
  intro δ hδ 𝕣 h𝕣
  set b := -xiGamma γ * Q γ - ζ
  have hS : MeasurableSet {p : ℝ × ℝ | ¬ p.2 ≤ δ ^ b * p.1} :=
    (measurableSet_le measurable_snd (measurable_const.mul measurable_fst)).compl
  refine (prob_scale_le P h hh (xiGamma γ) hδ.1 h𝕣 _ hS fun t ht x y hxy => ?_).trans (H1 δ hδ)
  simp only [mem_setOf_eq] at hxy ⊢
  intro hle; apply hxy
  calc t * y ≤ t * (δ ^ b * x) := mul_le_mul_of_nonneg_left hle ht.le
    _ = δ ^ b * (t * x) := by ring

end LQGMetric.DFGPS.L36
