/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.Prop210Degree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg

/-!
# Edge multiplicity in the mated-CRT graph

Each pair of distinct mesh vertices carries at most one edge of each
Brownian side. This is the multigraph counting part of [18] (4.7).
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.GMS4F

open MatedCRTHarmonic

theorem matedCRT_dart_target_side_inj
    {ε : ℝ} {ω : MatedCRT.Path2} (h : MatedCRT.IsLocallyFinite ε ω)
    (x : ℤ) :
    Set.InjOn (fun d : (MatedCRT.graph ε ω h).Dart =>
      ((MatedCRT.graph ε ω h).dtgt d, d.1.1.2.2))
      ((MatedCRT.graph ε ω h).outDarts x : Set _) := by
  intro d hd e he hpair
  have hds : (MatedCRT.graph ε ω h).dsrc d = x := by
    have hm : ((MatedCRT.graph ε ω h).src d.1 = x ∨
      (MatedCRT.graph ε ω h).tgt d.1 = x) ∧
      (MatedCRT.graph ε ω h).dsrc d = x := by
      simpa [LFMultigraph.outDarts] using hd
    exact hm.2
  have hes : (MatedCRT.graph ε ω h).dsrc e = x := by
    have hm : ((MatedCRT.graph ε ω h).src e.1 = x ∨
      (MatedCRT.graph ε ω h).tgt e.1 = x) ∧
      (MatedCRT.graph ε ω h).dsrc e = x := by
      simpa [LFMultigraph.outDarts] using he
    exact hm.2
  have htgt := congrArg Prod.fst hpair
  have hside := congrArg Prod.snd hpair
  rcases d with ⟨⟨⟨a, b, c⟩, habc⟩, rev⟩
  rcases e with ⟨⟨⟨a', b', c'⟩, ha'b'c'⟩, rev'⟩
  have hab : a < b := habc.1
  have ha'b' : a' < b' := ha'b'c'.1
  change (if rev then b else a) = x at hds
  change (if rev' then b' else a') = x at hes
  change (if rev then a else b) = (if rev' then a' else b') at htgt
  change c = c' at hside
  cases rev <;> cases rev' <;> simp at hds hes htgt
  · have ha : a = a' := by omega
    have hb : b = b' := by omega
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext ha (Prod.ext hb hside)
    · rfl
  · omega
  · omega
  · have ha : a = a' := by omega
    have hb : b = b' := by omega
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext ha (Prod.ext hb hside)
    · rfl

/-- The degree is at most twice the number of distinct neighbours. This
retains the actual graph's edge multiplicities, including its `Bool` side. -/
theorem matedCRT_degree_le_two_neighborCount
    {ε : ℝ} {ω : MatedCRT.Path2} (h : MatedCRT.IsLocallyFinite ε ω)
    (x : ℤ) :
    (MatedCRT.graph ε ω h).deg x ≤
      2 * (((MatedCRT.graph ε ω h).outDarts x).image
        (MatedCRT.graph ε ω h).dtgt).card := by
  classical
  let G := MatedCRT.graph ε ω h
  let S := G.outDarts x
  let N := S.image G.dtgt
  have hmaps : Set.MapsTo
      (fun d : G.Dart => (G.dtgt d, d.1.1.2.2))
      (S : Set G.Dart) (↑(N.product (Finset.univ : Finset Bool))) := by
    intro d hd
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem G.dtgt hd,
      Finset.mem_univ _⟩
  have hinj : Set.InjOn
      (fun d : G.Dart => (G.dtgt d, d.1.1.2.2)) (S : Set G.Dart) :=
    matedCRT_dart_target_side_inj h x
  have hcard := Finset.card_le_card_of_injOn
    (fun d : G.Dart => (G.dtgt d, d.1.1.2.2)) hmaps hinj
  simpa [G, S, N, LFMultigraph.deg, Finset.card_product, mul_comm] using hcard

end MatedCRTHarmonic.GMS4F

