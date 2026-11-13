/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCompactLimits at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCompactSpace
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactCoreAlgebra
import Mathlib.Topology.ClusterPt

/-!
# Coordinate limits in the compact resolvent space

The compactification is generated jointly by vertex indicators and bounded
resolvent-core features.  This file records the corresponding product-topology
limit criterion and uses compactness to turn compatible coordinate limits into
a unique limit point.  In particular, no separation claim is made for the
resolvent coordinates without the indicator coordinates.
-/

set_option autoImplicit false

open Filter Set Topology

namespace ReflectedGMS.CompactVertexSpace

variable {V I A : Type*} (feature : I → V → ℝ) (bound : I → ℝ)
  (hbound : ∀ i x, |feature i x| ≤ bound i)

@[simp] theorem indicatorCoordinate_vertex [DecidableEq V] (x y : V) :
    indicatorCoordinate feature bound hbound y (vertex feature bound hbound x) =
      if x = y then 1 else 0 := by
  simp [indicatorCoordinate, vertex, evaluation]

/-- The two coordinate families defining the compact evaluation closure jointly
separate its points. -/
theorem ext_of_indicator_coordinate_eq {z w : Space feature bound hbound}
    (hI : ∀ x, indicatorCoordinate feature bound hbound x z =
      indicatorCoordinate feature bound hbound x w)
    (hF : ∀ i, coordinate feature bound hbound i z =
      coordinate feature bound hbound i w) : z = w := by
  apply Subtype.ext
  apply Prod.ext
  · funext x
    apply Subtype.ext
    exact hI x
  · funext i
    apply Subtype.ext
    exact hF i

/-- Convergence in the compact evaluation closure is exactly convergence of
all indicator and feature coordinates. -/
theorem tendsto_iff_indicator_coordinate
    (u : A → Space feature bound hbound) (l : Filter A)
    (z : Space feature bound hbound) :
    Tendsto u l (nhds z) ↔
      (∀ x, Tendsto (fun a ↦ indicatorCoordinate feature bound hbound x (u a)) l
        (nhds (indicatorCoordinate feature bound hbound x z))) ∧
      ∀ i, Tendsto (fun a ↦ coordinate feature bound hbound i (u a)) l
        (nhds (coordinate feature bound hbound i z)) := by
  rw [tendsto_subtype_rng, Prod.tendsto_iff]
  constructor
  · rintro ⟨hI, hF⟩
    constructor
    · intro x
      exact tendsto_subtype_rng.mp (tendsto_pi_nhds.mp hI x)
    · intro i
      exact tendsto_subtype_rng.mp (tendsto_pi_nhds.mp hF i)
  · rintro ⟨hI, hF⟩
    constructor
    · apply tendsto_pi_nhds.mpr
      intro x
      exact tendsto_subtype_rng.mpr (hI x)
    · apply tendsto_pi_nhds.mpr
      intro i
      exact tendsto_subtype_rng.mpr (hF i)

private theorem coordinate_eq_of_mapClusterPt
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {u : A → X} {l : Filter A} {z : X} {c : X → ℝ} {r : ℝ}
    (hz : MapClusterPt z l u) (hc : ContinuousAt c z)
    (hr : Tendsto (fun a ↦ c (u a)) l (nhds r)) : c z = r := by
  apply eq_of_nhds_neBot
  have hcluster : MapClusterPt (c z) l (c ∘ u) := hz.continuousAt_comp hc
  have hle : map (c ∘ u) l ≤ nhds r := by
    change map (fun a ↦ c (u a)) l ≤ nhds r
    exact hr
  exact hcluster.clusterPt.mono hle

/-- On a nontrivial filter, limits of every defining coordinate determine a
unique point of the compact evaluation closure, and the original map converges
to that point. -/
theorem existsUnique_tendsto_of_coordinate_limits
    (u : A → Space feature bound hbound) (l : Filter A) [NeBot l]
    (indicatorLimit : V → ℝ) (featureLimit : I → ℝ)
    (hI : ∀ x, Tendsto (fun a ↦ indicatorCoordinate feature bound hbound x (u a)) l
      (nhds (indicatorLimit x)))
    (hF : ∀ i, Tendsto (fun a ↦ coordinate feature bound hbound i (u a)) l
      (nhds (featureLimit i))) :
    ∃! z : Space feature bound hbound,
      Tendsto u l (nhds z) ∧
      (∀ x, indicatorCoordinate feature bound hbound x z = indicatorLimit x) ∧
      ∀ i, coordinate feature bound hbound i z = featureLimit i := by
  haveI : NeBot (map u l) := map_neBot
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (map u l)
  have hzmap : MapClusterPt z l u := hz
  have hzI : ∀ x, indicatorCoordinate feature bound hbound x z = indicatorLimit x :=
    fun x ↦ coordinate_eq_of_mapClusterPt hzmap
      (indicatorCoordinate feature bound hbound x).continuous.continuousAt (hI x)
  have hzF : ∀ i, coordinate feature bound hbound i z = featureLimit i :=
    fun i ↦ coordinate_eq_of_mapClusterPt hzmap
      (coordinate feature bound hbound i).continuous.continuousAt (hF i)
  refine ⟨z, ⟨(tendsto_iff_indicator_coordinate feature bound hbound u l z).mpr
    ⟨fun x ↦ hzI x ▸ hI x, fun i ↦ hzF i ▸ hF i⟩, hzI, hzF⟩, ?_⟩
  intro w hw
  exact ext_of_indicator_coordinate_eq feature bound hbound
    (fun x ↦ (hw.2.1 x).trans (hzI x).symm)
    (fun i ↦ (hw.2.2 i).trans (hzF i).symm)

end ReflectedGMS.CompactVertexSpace

namespace ReflectedGMS.ResolventCompactSpace

open FullNetworkForm

variable {V A : Type*} [DecidableEq V]

/-- The indicator coordinate in the resolvent compactification. -/
noncomputable abbrev indicatorCoordinate
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (x : V) : C(Space G m hm, ℝ) :=
  CompactVertexSpace.indicatorCoordinate (feature G m) bound (feature_abs_le G m hm) x

@[simp] theorem indicatorCoordinate_vertex
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (x y : V) :
    indicatorCoordinate G m hm y (vertex G m hm x) = if x = y then 1 else 0 :=
  CompactVertexSpace.indicatorCoordinate_vertex
    (feature G m) bound (feature_abs_le G m hm) x y

/-- Abstract compact-limit adapter for the resolvent compactification.  Its
hypotheses are precisely limits of both coordinate families used to define the
space. -/
theorem existsUnique_tendsto_of_definingCoordinate_limits
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (u : A → Space G m hm) (l : Filter A) [NeBot l]
    (indicatorLimit : V → ℝ) (resolventLimit : Index V → ℝ)
    (hI : ∀ x, Tendsto (fun a ↦ indicatorCoordinate G m hm x (u a)) l
      (nhds (indicatorLimit x)))
    (hR : ∀ q, Tendsto (fun a ↦ coordinate G m hm q (u a)) l
      (nhds (resolventLimit q))) :
    ∃! z : Space G m hm,
      Tendsto u l (nhds z) ∧
      (∀ x, indicatorCoordinate G m hm x z = indicatorLimit x) ∧
      ∀ q, coordinate G m hm q z = resolventLimit q :=
  CompactVertexSpace.existsUnique_tendsto_of_coordinate_limits
    (feature G m) bound (feature_abs_le G m hm) u l indicatorLimit resolventLimit hI hR

/-- Vertex-valued form of the compact-limit adapter.  The hypotheses are stated
directly in terms of the indicator evaluations and finite rational combinations
of discount-one vertex occupation potentials. -/
theorem existsUnique_tendsto_vertex_of_definingCoordinate_limits
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (path : A → V) (l : Filter A) [NeBot l]
    (indicatorLimit : V → ℝ) (resolventLimit : Index V → ℝ)
    (hI : ∀ y, Tendsto (fun a ↦ if path a = y then (1 : ℝ) else 0) l
      (nhds (indicatorLimit y)))
    (hR : ∀ q, Tendsto (fun a ↦ q.sum fun y c ↦
      (c : ℝ) * vertexOccupationPotential G m 1 (path a) y) l
      (nhds (resolventLimit q))) :
    ∃! z : Space G m hm,
      Tendsto (fun a ↦ vertex G m hm (path a)) l (nhds z) ∧
      (∀ y, indicatorCoordinate G m hm y z = indicatorLimit y) ∧
      ∀ q, coordinate G m hm q z = resolventLimit q := by
  apply existsUnique_tendsto_of_definingCoordinate_limits G m hm
    (fun a ↦ vertex G m hm (path a)) l indicatorLimit resolventLimit
  · intro y
    simpa only [indicatorCoordinate_vertex] using hI y
  · intro q
    simpa only [coordinate_vertex] using hR q

end ReflectedGMS.ResolventCompactSpace
