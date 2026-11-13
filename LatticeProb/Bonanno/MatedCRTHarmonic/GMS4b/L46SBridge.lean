/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SBridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SVisit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SGraphBall
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected

/-!
# A point contact gives a bounded graph path

Route M proves that all cells containing one point induce a connected graph.
DMS's finite visit bound bounds that induced graph's vertices, and a shortest
path uses fewer edges than vertices. Closed mesh intervals produce a factor
two at grid endpoints.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace MatedCRTHarmonic.GMS4b

/-- Two cells containing the same point admit a path of length `<2k` whose
every vertex cell also contains that point. This support condition lets
coverage confine the entire path to a deterministic finite index interval. -/
theorem contact_cells_short_path {ω : MatedCRT.Path2}
    {η : ℝ → ℂ} (P : RouteM.Peanosphere ω η) {ε : ℝ} (hε : 0 < ε)
    (h : MatedCRT.IsLocallyFinite ε ω) {k : ℕ}
    (hvisit : ∀ z : ℂ, (η ⁻¹' {z}).encard ≤ k)
    {z : ℂ} {m n : ℤ} (hzm : z ∈ cellOf ε η m)
    (hzn : z ∈ cellOf ε η n) :
    ∃ p : ((MatedCRT.graph ε ω h).adj).Walk m n,
      p.length < 2 * k ∧ ∀ v ∈ p.support, z ∈ cellOf ε η v := by
  let G : SimpleGraph ℤ := (MatedCRT.graph ε ω h).adj
  let S : Set ℤ := {x | z ∈ cellOf ε η x}
  have hSbound : S.encard ≤ 2 * k :=
    cells_through_point_encard_le_two_mul hε (hvisit z)
  have hSfinite : S.Finite := Set.finite_of_encard_le_coe hSbound
  letI : Fintype S := hSfinite.fintype
  have hm : m ∈ S := hzm
  have hn : n ∈ S := hzn
  have hconn : (G.induce S).Connected := RouteM.thmB_induce_connected P hε h z
  obtain ⟨w⟩ := hconn ⟨m, hm⟩ ⟨n, hn⟩
  let p : (G.induce S).Walk ⟨m, hm⟩ ⟨n, hn⟩ := w.toPath
  have hlen : p.length < Fintype.card S := w.toPath.isPath.length_lt
  let f : (G.induce S) →g G :=
    { toFun := Subtype.val
      map_rel' := fun hxy => hxy }
  have hmap : (p.map f).length = p.length := by simp [p]
  have hcard : (Fintype.card S : ℕ∞) ≤ 2 * k := by
    rw [Set.coe_fintypeCard]
    exact hSbound
  have hpath : ((p.map f).length : ℕ∞) < 2 * k := by
    calc
      ((p.map f).length : ℕ∞) = p.length := by exact_mod_cast hmap
      _ < Fintype.card S := by exact_mod_cast hlen
      _ ≤ 2 * k := hcard
  refine ⟨p.map f, by exact_mod_cast hpath, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact u.property

/-- The contact path stays inside the finite mesh interval furnished by
covered-ball confinement. -/
theorem contact_cells_short_path_in_interval {ω : MatedCRT.Path2}
    {η : ℝ → ℂ} (P : RouteM.Peanosphere ω η) {ε : ℝ} (hε : 0 < ε)
    (h : MatedCRT.IsLocallyFinite ε ω) {k : ℕ}
    (hvisit : ∀ z : ℂ, (η ⁻¹' {z}).encard ≤ k)
    {M R : ℝ} (hconf : η ⁻¹' Metric.ball (0 : ℂ) R ⊆ Icc (-M) M)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R)
    {m n : ℤ} (hzm : z ∈ cellOf ε η m) (hzn : z ∈ cellOf ε η n) :
    ∃ p : ((MatedCRT.graph ε ω h).adj).Walk m n,
      p.length < 2 * k ∧ ∀ v ∈ p.support,
        v ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
  obtain ⟨p, hp, hsupp⟩ := contact_cells_short_path P hε h hvisit hzm hzn
  exact ⟨p, hp, fun v hv =>
    cell_index_mem_interval_of_preimage_ball_bound hε hconf hz (hsupp v hv)⟩

end MatedCRTHarmonic.GMS4b
