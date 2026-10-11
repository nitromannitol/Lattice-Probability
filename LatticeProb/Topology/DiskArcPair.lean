/-
# Injective arcs in disjoint finite disk chains

Finite loop pruning extracts injective polygonal paths while preserving the
original endpoints and trace inclusion. Applying it to two disjoint chains
preserves disjointness, disk containment and strict nonendpoint interior.
-/
import LatticeProb.Topology.PolygonalArc

open Set LatticeProb.Topology

namespace LatticeProb.Topology.DiskArcPair

/-- A finite coordinate chain with distinct endpoints contains an injective polygonal arc. -/
theorem coordinate_chain_consumer {vs : List (ℝ × ℝ)} (hv : vs ≠ [])
    (hne : vs.head hv ≠ vs.getLast hv) :
    ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [],
      us.head hu = vs.head hv ∧ us.getLast hu = vs.getLast hv ∧
      ∃ p : Path (vs.head hv) (vs.getLast hv), Function.Injective p ∧
        range p = polygonalChain us ∧ range p ⊆ polygonalChain vs := by
  obtain ⟨us, hu, _, hhead, hlast, hsub, hinj, hrange⟩ :=
    exists_injective_polygonal_arc vs hv hne
  let p := (polygonalChainPath us hu).cast hhead.symm hlast.symm
  have hprange : range p = polygonalChain us := hrange
  exact ⟨us, hu, hhead, hlast, p, hinj, hprange, hprange ▸ hsub⟩

/-- **Disjoint injective disk arcs.** Disjoint finite disk chains contain disjoint injective polygonal arcs with the same endpoints. -/
theorem disjoint_disk_chain_pair_consumer {vs ws : List (ℝ × ℝ)}
    (hv : vs ≠ []) (hw : ws ≠ [])
    (hvne : vs.head hv ≠ vs.getLast hv) (hwne : ws.head hw ≠ ws.getLast hw)
    (hdisj : Disjoint (polygonalChain vs) (polygonalChain ws))
    (hvD : polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hwD : polygonalChain ws ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hvI : polygonalChain vs \ {vs.head hv, vs.getLast hv} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1})
    (hwI : polygonalChain ws \ {ws.head hw, ws.getLast hw} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1}) :
    ∃ us zs : List (ℝ × ℝ), ∃ hu : us ≠ [], ∃ hz : zs ≠ [],
      us.head hu = vs.head hv ∧ us.getLast hu = vs.getLast hv ∧
      zs.head hz = ws.head hw ∧ zs.getLast hz = ws.getLast hw ∧
      ∃ p : Path (vs.head hv) (vs.getLast hv), ∃ q : Path (ws.head hw) (ws.getLast hw),
        Function.Injective p ∧ Function.Injective q ∧
        range p = polygonalChain us ∧ range q = polygonalChain zs ∧
        Disjoint (range p) (range q) ∧
        range p ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
        range q ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
        range p \ {vs.head hv, vs.getLast hv} ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
        range q \ {ws.head hw, ws.getLast hw} ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
  obtain ⟨us, hu, uh, ul, p, hp, hpu, hpv⟩ := coordinate_chain_consumer hv hvne
  obtain ⟨zs, hz, zh, zl, q, hq, hqz, hqw⟩ := coordinate_chain_consumer hw hwne
  exact ⟨us, zs, hu, hz, uh, ul, zh, zl, p, q, hp, hq, hpu, hqz,
    hdisj.mono hpv hqw, hpv.trans hvD, hqw.trans hwD,
    fun _ h => hvI ⟨hpv h.1, h.2⟩, fun _ h => hwI ⟨hqw h.1, h.2⟩⟩

end LatticeProb.Topology.DiskArcPair
