/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural




 





set_option autoImplicit false
noncomputable section

open Set unitInterval
open LQGMetric.MetricGeometry
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics

 
theorem curveLength_comp_le_of_edist_le
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (f : X → Y) (hf : ∀ x y, edist (f x) (f y) ≤ edist x y)
    (P : ℝ → X) (a b : ℝ) :
    curveLength (f ∘ P) a b ≤ curveLength P a b := by
  unfold curveLength eVariationOn
  refine iSup_le fun q => ?_
  refine (Finset.sum_le_sum fun i _ => hf _ _).trans ?_
  exact le_iSup_of_le q le_rfl


 

theorem lipschitzOnWith_internalSpace
    {X : Type*} [EMetricSpace X] (Y : Set X)
    (P : ℝ → Y) {a b : ℝ} {C : ℝ≥0}
    (hP : LipschitzOnWith C (fun t => (P t : X)) (Icc a b)) :
    LipschitzOnWith C (fun t => InternalSpace.mk (P t)) (Icc a b) := by
  intro s hs t ht
  rcases le_total s t with hst | hts
  · have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hbound : curveLength (fun u => (P u : X)) s t ≤ C * edist s t := by
      have h := (hP.mono hsub).comp_eVariationOn_le
        (g := id) (s := Icc s t) (fun u hu => hu)
      have hed : edist s t = ENNReal.ofReal (t - s) := by
        rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      rw [hed]
      simpa only [Function.comp_id, curveLength, eVariationOn_id_Icc] using h
    have hcont : ContinuousOn (fun u => (P u : X)) (Icc s t) :=
      (hP.mono hsub).continuousOn
    change internalEDist Y (P s : X) (P t : X) ≤ C * edist s t
    exact (internalEDist_le_curveLength hst hcont
      (fun u hu => (P u).property)).trans hbound
  · rw [edist_comm (InternalSpace.mk (P s)) (InternalSpace.mk (P t)),
      edist_comm s t]
    have hsub : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1 hs.2
    have hbound : curveLength (fun u => (P u : X)) t s ≤ C * edist t s := by
      have h := (hP.mono hsub).comp_eVariationOn_le
        (g := id) (s := Icc t s) (fun u hu => hu)
      have hed : edist t s = ENNReal.ofReal (s - t) := by
        rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      rw [hed]
      simpa only [Function.comp_id, curveLength, eVariationOn_id_Icc] using h
    have hcont : ContinuousOn (fun u => (P u : X)) (Icc t s) :=
      (hP.mono hsub).continuousOn
    change internalEDist Y (P t : X) (P s : X) ≤ C * edist t s
    exact (internalEDist_le_curveLength hts hcont
      (fun u hu => (P u).property)).trans hbound


 
theorem curveLength_eq_internalSpace
    {X : Type*} [EMetricSpace X] (Y : Set X)
    (P : ℝ → Y) (a b : ℝ)
    (hP : ContinuousOn (fun t => (P t : X)) (Icc a b)) :
    curveLength (fun t => (P t : X)) a b =
      curveLength (fun t => InternalSpace.mk (P t)) a b := by
  rw [curveLength_eq_iSup_internalEDist hP (fun t ht => (P t).property)]
  rfl


 
def intoInternal {X : Type*} [EMetricSpace X]
    {Z Y : Set X} (hZY : Z ⊆ Y) (z : Z) : InternalSpace Y :=
  InternalSpace.mk ⟨z.1, hZY z.2⟩

 

theorem internalEDist_le_internalOfInternal
    {X : Type*} [EMetricSpace X] {Z Y : Set X} (hZY : Z ⊆ Y) (x y : Z) :
    internalEDist Z (x : X) (y : X) ≤
      internalEDist (Set.range (intoInternal hZY))
        (intoInternal hZY x) (intoInternal hZY y) := by
  have hVal : LipschitzWith 1 (InternalSpace.val : InternalSpace Y → X) := by
    intro u v
    simpa only [ENNReal.coe_one, one_mul] using InternalSpace.edist_val_le u v
  refine le_iInf fun γ => ?_
  let δ : Path (x : X) (y : X) := γ.1.map hVal.continuous
  have hδ : ∀ t, δ t ∈ Z := by
    intro t
    obtain ⟨z, hz⟩ := γ.2 t
    have hz' : (γ.1 t).val = (z : X) := congrArg InternalSpace.val hz.symm
    change (γ.1 t).val ∈ Z
    rw [hz']
    exact z.2
  have hlen : pathLength δ ≤ pathLength γ.1 := by
    unfold δ pathLength
    exact curveLength_comp_le_of_edist_le InternalSpace.val
      (fun u v => InternalSpace.edist_val_le u v) γ.1.extend 0 1
  exact (internalEDist_le_pathLength δ hδ).trans hlen


 

theorem internalOfInternal_le_internalEDist
    {X : Type*} [EMetricSpace X] {Z Y : Set X} (hZY : Z ⊆ Y) (x y : Z) :
    internalEDist (Set.range (intoInternal hZY))
        (intoInternal hZY x) (intoInternal hZY y) ≤
      internalEDist Z (x : X) (y : X) := by
  refine le_iInf fun γ => ?_
  by_cases hL : pathLength γ.1 = ∞
  · simp only [hL, le_top]
  obtain ⟨γ', hγ'len, hγ'range, hγ'lip⟩ := exists_lipschitz_path γ.1 hL
  have hγ'Z : ∀ t : I, γ' t ∈ Z := by
    intro t
    obtain ⟨s, hs⟩ := hγ'range (mem_range_self t)
    exact hs ▸ γ.2 s
  have hPZ : ∀ t : ℝ, γ'.extend t ∈ Z := by
    intro t
    obtain ⟨s, hs⟩ := γ'.extend_range.subset (mem_range_self t)
    exact hs ▸ hγ'Z s
  let P : ℝ → Y := fun t => ⟨γ'.extend t, hZY (hPZ t)⟩
  have hPlip : LipschitzOnWith (pathLength γ.1).toNNReal
      (fun t => (P t : X)) (Icc 0 1) := by
    intro s hs t ht
    change edist (γ'.extend s) (γ'.extend t) ≤
      ↑(pathLength γ.1).toNNReal * edist s t
    rw [γ'.extend_apply hs, γ'.extend_apply ht]
    simpa only [edist_dist, Subtype.dist_eq] using
      hγ'lip ⟨s, hs⟩ ⟨t, ht⟩
  have hIlip := lipschitzOnWith_internalSpace Y P hPlip
  obtain ⟨δ, hδlen, hδrange⟩ :=
    exists_path_of_curve zero_le_one hIlip.continuousOn
  have hP0 : P 0 = (⟨(x : X), hZY x.2⟩ : Y) := by
    apply Subtype.ext
    exact γ'.extend_zero
  have hP1 : P 1 = (⟨(y : X), hZY y.2⟩ : Y) := by
    apply Subtype.ext
    exact γ'.extend_one
  let δ' : Path (intoInternal hZY x) (intoInternal hZY y) :=
    δ.cast (congrArg InternalSpace.mk hP0).symm
      (congrArg InternalSpace.mk hP1).symm
  have hδ' : ∀ t, δ' t ∈ Set.range (intoInternal hZY) := by
    intro t
    obtain ⟨s, hs, heq⟩ := hδrange (mem_range_self t)
    exact ⟨⟨(P s : X), hPZ s⟩, heq⟩
  have hδ'len : pathLength δ' = pathLength γ.1 := by
    calc pathLength δ' = curveLength (fun t => InternalSpace.mk (P t)) 0 1 := hδlen
      _ = curveLength (fun t => (P t : X)) 0 1 :=
        (curveLength_eq_internalSpace Y P 0 1 hPlip.continuousOn).symm
      _ = pathLength γ' := rfl
      _ = pathLength γ.1 := hγ'len
  exact (internalEDist_le_pathLength δ' hδ').trans_eq hδ'len


 

theorem internalEDist_internalSpace
    {X : Type*} [EMetricSpace X] {Z Y : Set X} (hZY : Z ⊆ Y) (x y : Z) :
    internalEDist (Set.range (intoInternal hZY))
        (intoInternal hZY x) (intoInternal hZY y) =
      internalEDist Z (x : X) (y : X) := by
  exact le_antisymm
    (internalOfInternal_le_internalEDist hZY x y)
    (internalEDist_le_internalOfInternal hZY x y)


 


def internalOfInternal (D : LSCMetric) {K U : Set ℂ} (hKU : K ⊆ U)
    (p : K × K) : ℝ≥0∞ :=
  let hZY : D.pt '' K ⊆ D.pt '' U := Set.image_mono hKU
  internalEDist (Set.range (intoInternal hZY))
    (intoInternal hZY ⟨D.pt p.1, ⟨p.1, p.1.2, rfl⟩⟩)
    (intoInternal hZY ⟨D.pt p.2, ⟨p.2, p.2.2, rfl⟩⟩)

 

theorem internal_eq_internalOfInternal
    (D : LSCMetric) {K U : Set ℂ} (hKU : K ⊆ U) (p : K × K) :
    D.internal K p = internalOfInternal D hKU p := by
  rw [LSCMetric.internal_eq_internalEDist]
  exact (internalEDist_internalSpace (Set.image_mono hKU)
    (⟨D.pt p.1, ⟨p.1, p.1.2, rfl⟩⟩ : D.pt '' K)
    (⟨D.pt p.2, ⟨p.2, p.2.2, rfl⟩⟩ : D.pt '' K)).symm



 

theorem internal_eq_of_internal_eq (D₁ D₂ : LSCMetric)
    {K U : Set ℂ} (hKU : K ⊆ U)
    (hEq : D₁.internal U = D₂.internal U) :
    D₁.internal K = D₂.internal K := by
  funext p
  rw [internal_eq_internalOfInternal D₁ hKU p,
    internal_eq_internalOfInternal D₂ hKU p]
  let m₁ : EMetricSpace (InternalSpace (D₁.pt '' U)) :=
    @InternalSpace.instEMetricSpace D₁.Space (LSCMetric.instEMetricSpace D₁) (D₁.pt '' U)
  let m₂ : EMetricSpace (InternalSpace (D₂.pt '' U)) :=
    @InternalSpace.instEMetricSpace D₂.Space (LSCMetric.instEMetricSpace D₂) (D₂.pt '' U)
  have hm : m₁ = m₂ := by
    apply EMetricSpace.ext
    ext x y
    have hx : (x.val : ℂ) ∈ U := by
      obtain ⟨z, hz, hzEq⟩ := x.val_mem
      change z = (x.val : ℂ) at hzEq
      exact hzEq ▸ hz
    have hy : (y.val : ℂ) ∈ U := by
      obtain ⟨z, hz, hzEq⟩ := y.val_mem
      change z = (y.val : ℂ) at hzEq
      exact hzEq ▸ hz
    let pxy : U × U := (⟨(x.val : ℂ), hx⟩, ⟨(y.val : ℂ), hy⟩)
    have h₁ := D₁.internal_eq_internalEDist U pxy
    have h₂ := D₂.internal_eq_internalEDist U pxy
    have hh : internalEDist (D₁.pt '' U) x.val y.val =
        internalEDist (D₂.pt '' U) x.val y.val := by
      calc
        _ = D₁.internal U pxy := h₁.symm
        _ = D₂.internal U pxy := congrFun hEq pxy
        _ = _ := h₂
    change internalEDist (D₁.pt '' U) x.val y.val =
      internalEDist (D₂.pt '' U) x.val y.val
    exact hh
  let f : PseudoEMetricSpace (InternalSpace (D₁.pt '' U)) → ℝ≥0∞ := fun m => by
    exact @internalEDist _ m (Set.range (intoInternal (Set.image_mono hKU)))
      (intoInternal (Set.image_mono hKU)
        (⟨D₁.pt p.1, ⟨p.1, p.1.2, rfl⟩⟩ : D₁.pt '' K))
      (intoInternal (Set.image_mono hKU)
        (⟨D₁.pt p.2, ⟨p.2, p.2.2, rfl⟩⟩ : D₁.pt '' K))
  change f m₁.toPseudoEMetricSpace = f m₂.toPseudoEMetricSpace
  exact congrArg f (congrArg
    (fun m : EMetricSpace (InternalSpace (D₁.pt '' U)) => m.toPseudoEMetricSpace) hm)


 

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics
