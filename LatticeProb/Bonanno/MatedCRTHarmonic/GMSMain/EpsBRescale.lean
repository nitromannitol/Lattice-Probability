/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBRescale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Time changes `t ↦ c t` of the mated-CRT data

The mated-CRT map of mesh `ε` of a Brownian pair `w` is the mated-CRT map of mesh `ε / c` of the time-changed pair
`t ↦ w (c t)` (`c > 0`): the side condition (1.1) of [18], the edge predicate `MatedCRT.IsEdge`, local finiteness,
adjacency, the strict side condition `RouteM.SideStrict` and the Peanosphere bundle `RouteM.Peanosphere` only see the
infima of the coordinates over the intervals `[ε(x−1), εx]`, and the cells `η([ε(x−1), εx])` are unchanged when the
curve is time-changed as well. uses this to present the mesh-`θₖ` map (any real `θₖ` in the dyadic band
of `2⁻ᵏ`) with the nominal dyadic mesh `2⁻ᵏ` demanded by `CellFamily.PeanosphereG0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-- The time change `t ↦ w (c t)` of a Brownian pair path. -/
def rescalePath (c : ℝ) (w : MatedCRT.Path2) : MatedCRT.Path2 :=
  w.comp ⟨fun t => c * t, continuous_const.mul continuous_id⟩

@[simp] theorem rescalePath_apply (c : ℝ) (w : MatedCRT.Path2) (t : ℝ) : rescalePath c w t = w (c * t) := rfl

/-- The time change `t ↦ η (c t)` of a curve. -/
def rescaleCurve (c : ℝ) (η : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  η.comp ⟨fun t => c * t, continuous_const.mul continuous_id⟩

@[simp] theorem rescaleCurve_apply (c : ℝ) (η : C(ℝ, ℂ)) (t : ℝ) : rescaleCurve c η t = η (c * t) := rfl

theorem image_rescale_Icc {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) (a b : ℝ) :
    (fun t => f (c * t)) '' Icc a b = f '' Icc (c * a) (c * b) := by
  rw [show (fun t => f (c * t)) = f ∘ (fun t => c * t) from rfl, Set.image_comp, image_mul_left_Icc' hc]

/-- The cells of the time-changed curve at mesh `ε` are the cells of the curve at mesh `c ε`. -/
theorem rescaleCurve_cell {c : ℝ} (hc : 0 < c) (η : C(ℝ, ℂ)) (ε : ℝ) (x : ℤ) :
    rescaleCurve c η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) = η '' Icc (c * ε * ((x : ℝ) - 1)) (c * ε * x) := by
  have h := image_rescale_Icc hc (η : ℝ → ℂ) (ε * ((x : ℝ) - 1)) (ε * x)
  simp only [mul_assoc] at h ⊢
  exact h

theorem intervalInf_rescale {c : ℝ} (hc : 0 < c) (X : ℝ → ℝ) (a b : ℝ) :
    MatedCRT.intervalInf (fun t => X (c * t)) a b = MatedCRT.intervalInf X (c * a) (c * b) := by
  unfold MatedCRT.intervalInf
  rw [show (fun t => X (c * t)) = X ∘ (fun t => c * t) from rfl, Set.image_comp, image_mul_left_Icc' hc]

theorem sideCond_rescale {c : ℝ} (hc : 0 < c) (ε : ℝ) (X : ℝ → ℝ) (x y : ℤ) :
    MatedCRT.SideCond ε (fun t => X (c * t)) x y ↔ MatedCRT.SideCond (c * ε) X x y := by
  unfold MatedCRT.SideCond
  simp only [intervalInf_rescale hc, mul_assoc]

/-- **Edges are time-change invariant**: `IsEdge ε (w ∘ c) = IsEdge (c ε) w`. -/
theorem isEdge_rescale {c : ℝ} (hc : 0 < c) (ε : ℝ) (w : MatedCRT.Path2) :
    MatedCRT.IsEdge ε (rescalePath c w) = MatedCRT.IsEdge (c * ε) w := by
  funext e
  unfold MatedCRT.IsEdge
  have h := sideCond_rescale hc ε (fun t => if e.2.2 then (w t).2 else (w t).1) e.1 e.2.1
  simp only [rescalePath_apply]
  rw [h]

theorem isLocallyFinite_iff_of_isEdge_eq {ε ε' : ℝ} {w w' : MatedCRT.Path2}
    (h : MatedCRT.IsEdge ε w = MatedCRT.IsEdge ε' w') :
    MatedCRT.IsLocallyFinite ε w ↔ MatedCRT.IsLocallyFinite ε' w' := by
  unfold MatedCRT.IsLocallyFinite MatedCRT.Edge
  rw [h]

theorem adj_iff_of_isEdge_eq {ε ε' : ℝ} {w w' : MatedCRT.Path2}
    (h : MatedCRT.IsEdge ε w = MatedCRT.IsEdge ε' w') (hlf : MatedCRT.IsLocallyFinite ε w)
    (hlf' : MatedCRT.IsLocallyFinite ε' w') (x y : ℤ) :
    (MatedCRT.graph ε w hlf).adj.Adj x y ↔ (MatedCRT.graph ε' w' hlf').adj.Adj x y := by
  simp only [LFMultigraph.adj, SimpleGraph.fromRel_adj, MatedCRT.graph, Subtype.exists, exists_prop]
  rw [h]

theorem isLocallyFinite_rescale {c : ℝ} (hc : 0 < c) {ε : ℝ} {w : MatedCRT.Path2}
    (h : MatedCRT.IsLocallyFinite (c * ε) w) : MatedCRT.IsLocallyFinite ε (rescalePath c w) :=
  (isLocallyFinite_iff_of_isEdge_eq (isEdge_rescale hc ε w)).mpr h

theorem sideStrict_rescale {c : ℝ} (hc : 0 < c) {ε : ℝ} {w : MatedCRT.Path2}
    (h : RouteM.SideStrict (c * ε) w) : RouteM.SideStrict ε (rescalePath c w) := by
  intro b x y hxy hside
  have hside' := (sideCond_rescale hc ε (fun t => if b then (w t).2 else (w t).1) x y).mp hside
  have key := h b x y hxy hside'
  have e : ∀ a a' : ℝ, MatedCRT.intervalInf (fun t => if b then (rescalePath c w t).2 else (rescalePath c w t).1)
      a a' = MatedCRT.intervalInf (fun t => if b then (w t).2 else (w t).1) (c * a) (c * a') :=
    fun a a' => intervalInf_rescale hc (fun t => if b then (w t).2 else (w t).1) a a'
  rw [e, e, e]
  simpa only [mul_assoc] using key

theorem directRel_rescale {c : ℝ} (hc : 0 < c) (X : ℝ → ℝ) (s t : ℝ) :
    RouteM.directRel (fun u => X (c * u)) s t ↔ RouteM.directRel X (c * s) (c * t) := by
  unfold RouteM.directRel
  constructor
  · rintro ⟨hst, heq, hlt⟩
    refine ⟨mul_lt_mul_of_pos_left hst hc, heq, fun v hv => ?_⟩
    have hv' : v / c ∈ Ioo s t := by
      constructor
      · rw [lt_div_iff₀ hc, mul_comm]; exact hv.1
      · rw [div_lt_iff₀ hc, mul_comm]; exact hv.2
    have := hlt (v / c) hv'
    simpa only [mul_div_cancel₀ v hc.ne'] using this
  · rintro ⟨hst, heq, hlt⟩
    refine ⟨lt_of_mul_lt_mul_left hst hc.le, heq, fun u hu => ?_⟩
    exact hlt (c * u) ⟨mul_lt_mul_of_pos_left hu.1 hc, mul_lt_mul_of_pos_left hu.2 hc⟩

/-- **The Peanosphere bundle is time-change invariant.** -/
theorem peanosphere_rescale {c : ℝ} (hc : 0 < c) {w : MatedCRT.Path2} {η : ℝ → ℂ}
    (hP : RouteM.Peanosphere w η) : RouteM.Peanosphere (rescalePath c w) (fun t => η (c * t)) := by
  have hcont : Continuous fun t : ℝ => c * t := continuous_const.mul continuous_id
  let R : ℝ → ℝ → Prop := fun a b =>
    RouteM.directRel (fun u => (w u).1) a b ∨ RouteM.directRel (fun u => (w u).2) a b
  let R' : ℝ → ℝ → Prop := fun a b =>
    RouteM.directRel (fun u => (rescalePath c w u).1) a b ∨
      RouteM.directRel (fun u => (rescalePath c w u).2) a b
  have hRR' : ∀ a b, R' a b ↔ R (c * a) (c * b) := by
    intro a b
    simp only [R, R', rescalePath_apply]
    rw [directRel_rescale hc (fun u => (w u).1), directRel_rescale hc (fun u => (w u).2)]
  refine
    { cont := hP.cont.comp hcont
      surj := ?_
      transient := ?_
      merge := ?_
      onlyMerge := ?_
      liminf_L := ?_
      liminf_R := ?_
      locMinDistinct := ?_ }
  · intro z
    obtain ⟨t, ht⟩ := hP.surj z
    exact ⟨t / c, by simp only [mul_div_cancel₀ t hc.ne', ht]⟩
  · exact hP.transient.comp (Homeomorph.mulLeft₀ c hc.ne').isClosedEmbedding.tendsto_cocompact
  · intro s t hst
    exact hP.merge (c * s) (c * t) ((hRR' s t).mp hst)
  · intro s t hst
    have hE := hP.onlyMerge (c * s) (c * t) hst
    have key : ∀ a b, Relation.EqvGen R a b → Relation.EqvGen R' (a / c) (b / c) := by
      intro a b hab
      induction hab with
      | rel a b h =>
        refine Relation.EqvGen.rel _ _ ((hRR' _ _).mpr ?_)
        rwa [mul_div_cancel₀ a hc.ne', mul_div_cancel₀ b hc.ne']
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    have := key _ _ hE
    rwa [mul_div_cancel_left₀ s hc.ne', mul_div_cancel_left₀ t hc.ne'] at this
  · intro M T
    obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := hP.liminf_L M (c * T)
    refine ⟨⟨t₁ / c, ?_, ?_⟩, ⟨t₂ / c, ?_, ?_⟩⟩
    · rw [ge_iff_le, le_div_iff₀ hc, mul_comm]; exact ht₁
    · simp only [rescalePath_apply, mul_div_cancel₀ t₁ hc.ne']; exact h₁
    · rw [div_le_iff₀ hc, neg_mul, mul_comm]; exact ht₂
    · simp only [rescalePath_apply, mul_div_cancel₀ t₂ hc.ne']; exact h₂
  · intro M T
    obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := hP.liminf_R M (c * T)
    refine ⟨⟨t₁ / c, ?_, ?_⟩, ⟨t₂ / c, ?_, ?_⟩⟩
    · rw [ge_iff_le, le_div_iff₀ hc, mul_comm]; exact ht₁
    · simp only [rescalePath_apply, mul_div_cancel₀ t₁ hc.ne']; exact h₁
    · rw [div_le_iff₀ hc, neg_mul, mul_comm]; exact ht₂
    · simp only [rescalePath_apply, mul_div_cancel₀ t₂ hc.ne']; exact h₂
  · intro i a b hab ha hb
    have hcoord : ∀ t, MatedCRT.lrCoord i t (rescalePath c w) = MatedCRT.lrCoord i (c * t) w := by
      intro t
      simp only [MatedCRT.lrCoord, rescalePath_apply]
    have hinv : Continuous fun t : ℝ => t / c := continuous_id.div_const c
    have hloc : ∀ a, IsLocalMin (MatedCRT.lrCoord i · (rescalePath c w)) a →
        IsLocalMin (MatedCRT.lrCoord i · w) (c * a) := by
      intro a ha
      have ha' : IsLocalMin (MatedCRT.lrCoord i · (rescalePath c w)) ((fun t => t / c) (c * a)) := by
        simpa only [mul_div_cancel_left₀ a hc.ne'] using ha
      have hcomp := IsLocalMin.comp_continuous (g := fun t => t / c) (b := c * a) ha' hinv.continuousAt
      have hfun : ((MatedCRT.lrCoord i · (rescalePath c w)) ∘ fun t => t / c) =
          (MatedCRT.lrCoord i · w) := by
        funext t
        simp only [Function.comp_apply, hcoord, mul_div_cancel₀ t hc.ne']
      rwa [hfun] at hcomp
    have hne : c * a ≠ c * b := fun h => hab (mul_left_cancel₀ hc.ne' h)
    rw [hcoord, hcoord]
    exact hP.locMinDistinct i (c * a) (c * b) hne (hloc a ha) (hloc b hb)

end MatedCRTHarmonic.GMSMain.EpsB
