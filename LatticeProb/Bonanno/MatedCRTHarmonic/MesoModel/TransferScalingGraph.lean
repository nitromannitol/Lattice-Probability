/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.TransferScaling at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u v

namespace MatedCRTHarmonic.MesoModel

/-- The two edge subtypes have the same labelled triples, by edge-criterion invariance. -/
theorem edgeTypeEq_unitRescalePath {ε : ℝ} (hε : 0 < ε) (ω : MatedCRT.Path2) :
    MatedCRT.Edge ε ω = MatedCRT.Edge 1 (unitRescalePath ε ω) := by
  unfold MatedCRT.Edge
  exact congrArg (fun P : (ℤ × ℤ × Bool) → Prop => {e // P e})
    (edgePredicateEq_unitRescalePath hε ω)

/-- The explicit equivalence of edge labels between the mesh-`ε` graph and the unit graph of the
rescaled path. It fixes both integer endpoints and the left/right edge tag. -/
def edgeEquiv_unitRescalePath {ε : ℝ} (hε : 0 < ε) (ω : MatedCRT.Path2) :
    MatedCRT.Edge ε ω ≃ MatedCRT.Edge 1 (unitRescalePath ε ω) where
  toFun e := ⟨e.1, (isEdge_unitRescalePath hε ω e.1).mp e.2⟩
  invFun e := ⟨e.1, (isEdge_unitRescalePath hε ω e.1).mpr e.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Local finiteness is preserved by the labelled edge equivalence. -/
theorem isLocallyFinite_unitRescalePath_iff {ε : ℝ} (hε : 0 < ε)
    (ω : MatedCRT.Path2) :
    MatedCRT.IsLocallyFinite ε ω ↔
      MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω) := by
  unfold MatedCRT.IsLocallyFinite
  let f := edgeEquiv_unitRescalePath hε ω
  constructor
  · intro h x
    have hsource := h x
    change {e : MatedCRT.Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x}.Finite at hsource
    have himage : f '' {e : MatedCRT.Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x} =
        {e : MatedCRT.Edge 1 (unitRescalePath ε ω) | e.1.1 = x ∨ e.1.2.1 = x} := by
      ext e
      constructor
      · rintro ⟨e', he', rfl⟩
        exact he'
      · intro he
        refine ⟨f.symm e, ?_, f.apply_symm_apply e⟩
        exact he
    rw [← himage]
    exact hsource.image f
  · intro h x
    have htarget := h x
    change {e : MatedCRT.Edge 1 (unitRescalePath ε ω) | e.1.1 = x ∨ e.1.2.1 = x}.Finite at htarget
    have himage : f.symm '' {e : MatedCRT.Edge 1 (unitRescalePath ε ω) | e.1.1 = x ∨ e.1.2.1 = x} =
        {e : MatedCRT.Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x} := by
      ext e
      constructor
      · rintro ⟨e', he', rfl⟩
        exact he'
      · intro he
        refine ⟨f e, ?_, f.symm_apply_apply e⟩
        exact he
    rw [← himage]
    exact htarget.image f.symm

/-- After transport along the edge-subtype equality, the two locally finite graph structures are
equal. The vertex labels and every labelled edge are fixed. -/
private theorem castSubtypeVal {α : Type*} {P Q : α → Prop} (h : P = Q)
    (e : {x // P x}) :
    (cast (congrArg (fun R : α → Prop => {x // R x}) h) e).1 = e.1 := by
  cases h
  rfl

private theorem castGraphSrc {V E F : Type u} (h : E = F)
    (G : LFMultigraph V E) :
    (cast (congrArg (LFMultigraph V) h) G).src =
      fun e => G.src (cast h.symm e) := by
  cases h
  rfl

private theorem castGraphTgt {V E F : Type u} (h : E = F)
    (G : LFMultigraph V E) :
    (cast (congrArg (LFMultigraph V) h) G).tgt =
      fun e => G.tgt (cast h.symm e) := by
  cases h
  rfl

private theorem lfMultigraph_ext_src_tgt {V E : Type*}
    {G H : LFMultigraph V E} (hs : G.src = H.src) (ht : G.tgt = H.tgt) : G = H := by
  cases G with
  | mk srcG tgtG finG incG =>
    cases H with
    | mk srcH tgtH finH incH =>
      simp_all

/-- After transport along the edge-subtype equality, the two locally finite graph structures are
equal. The vertex labels and every labelled edge are fixed. -/
theorem graphCast_eq_unitRescalePath {ε : ℝ} (hε : 0 < ε)
    (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω)
    (h' : MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω)) :
    cast (congrArg (LFMultigraph ℤ) (edgeTypeEq_unitRescalePath hε ω))
      (MatedCRT.graph ε ω h) = MatedCRT.graph 1 (unitRescalePath ε ω) h' := by
  let hpred := edgePredicateEq_unitRescalePath hε ω
  let hedge := edgeTypeEq_unitRescalePath hε ω
  let hgraph := congrArg (LFMultigraph ℤ) hedge
  change cast hgraph (MatedCRT.graph ε ω h) =
    MatedCRT.graph 1 (unitRescalePath ε ω) h'
  have hsrc : (cast hgraph (MatedCRT.graph ε ω h)).src =
      (MatedCRT.graph 1 (unitRescalePath ε ω) h').src := by
    rw [castGraphSrc hedge (MatedCRT.graph ε ω h)]
    funext e
    change (cast hedge.symm e).1.1 = e.1.1
    exact congrArg (fun a : ℤ × ℤ × Bool => a.1)
      (castSubtypeVal hpred.symm e)
  have htgt : (cast hgraph (MatedCRT.graph ε ω h)).tgt =
      (MatedCRT.graph 1 (unitRescalePath ε ω) h').tgt := by
    rw [castGraphTgt hedge (MatedCRT.graph ε ω h)]
    funext e
    change (cast hedge.symm e).1.2.1 = e.1.2.1
    exact congrArg (fun a : ℤ × ℤ × Bool => a.2.1)
      (castSubtypeVal hpred.symm e)
  exact lfMultigraph_ext_src_tgt hsrc htgt

end MatedCRTHarmonic.MesoModel
