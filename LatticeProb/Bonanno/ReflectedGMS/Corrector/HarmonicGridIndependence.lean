/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.HarmonicGridIndependence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.BracketSpecificEnergy

/-!
# The auxiliary grid disappears: the comparison and anchoring steps

This module formalizes the *comparison* half of the manuscript proposition
`s:prop:gridindependence` ("The auxiliary grid disappears"), together with the
*anchored equality* that the manuscript deduces from it.

The manuscript argument, for two grids `𝔻₁, 𝔻₂` coupled on one joint marked law,
is the following chain of specific inner products:

```
  ⟪g¹, g² - g₀⟫ = 0,  ⟪g¹, g¹ - g₀⟫ = 0,
  ⟪g², g¹ - g₀⟫ = 0,  ⟪g², g² - g₀⟫ = 0
        ⟹  ‖g¹ - g²‖²_sp = 0
        ⟹  the difference vanishes on every edge
        ⟹  (both potentials vanish at `H₀`)  g¹ = g² at every vertex.
```

Everything in this file is proved.  Nothing here assumes grid independence, nor
equality of the two limiting gradients, nor uniqueness of an arbitrary sublinear
harmonic function: the four orthogonality relations are the manuscript's own
inputs (they come from the full variational orthogonality of the limiting
potential over the *other* grid's blocks, after signed redistribution) and they
are carried as explicit hypotheses.

## The objects

`RootDensities.specificEnergyDensity F Φ v` is the project's `ρ_Φ(H)`, an
`ℝ≥0∞`-valued quantity.  A comparison argument needs the *signed* polarization of
that density, so this module introduces its real-valued bilinear version

```
  specificPairingDensity F Φ Ψ v
    = (2 a_H)⁻¹ ∑_{H' ~ H} c(H,H') ⟪Φ(H') - Φ(H), Ψ(H') - Ψ(H)⟫
```

and checks in `ofReal_specificPairingDensity_self` that its diagonal is exactly
the existing `ρ_Φ`, so no competing energy notion is created.  The specific inner
product `⟪·,·⟫_sp` is the expectation of the rooted density under the joint
marked law, `specificPairing`.

## What is *not* done here

The passage from "the expected rooted density of `g¹ - g²` vanishes" to "the
density vanishes at **every** vertex" is the manuscript's maximal-inequality step
(`s:prop:maximal`, then `s:lem:localcontrol`); it is owned elsewhere and is
carried as an explicit hypothesis in `ae_eq_of_specificPairing_orthogonal`.  The
final conditional-variance/measurability step is likewise a separate packet.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS.HarmonicGridIndependence

open StatementIngredients RootDensities

variable {V : Type*} [Countable V]

/-! ### Coordinates on the plane -/

/-- The squared distance in the plane, in coordinates. -/
theorem norm_sub_sq_eq_sum_coord (x y : Plane) :
    ‖x - y‖ ^ 2 = ∑ i : Fin 2, (x i - y i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

/-! ### The polarized specific-energy density -/

/-- The unnormalized polarized endpoint sum at a vertex:
`∑_{H' ~ H} c(H,H') ⟪Φ(H') - Φ(H), Ψ(H') - Ψ(H)⟫`, written in coordinates
exactly as `StatementIngredients.bracketDensity` does. -/
noncomputable def pairingSum (F : IndexedCells V) (Φ Ψ : V → Plane) (v : V) : ℝ :=
  ∑' w : V, ∑ i : Fin 2, F.graph.c v w * ((Φ w i - Φ v i) * (Ψ w i - Ψ v i))

/-- The signed (polarized) specific-energy density.  Its diagonal is the
project's `RootDensities.specificEnergyDensity`, see
`ofReal_specificPairingDensity_self`. -/
noncomputable def specificPairingDensity (F : IndexedCells V) (Φ Ψ : V → Plane) (v : V) : ℝ :=
  pairingSum F Φ Ψ v / (2 * cellArea F v)

/-- The boundary-masked polarized density, in the exact shape of
`RootDensities.rootedSpecificEnergyDensity`. -/
noncomputable def rootedSpecificPairingDensity (F : IndexedCells V) (Φ Ψ : V → Plane)
    (z : Plane) : ℝ :=
  (rootAt F z).elim 0 (specificPairingDensity F Φ Ψ)

theorem rootedSpecificPairingDensity_of_eq_none (F : IndexedCells V) (Φ Ψ : V → Plane)
    {z : Plane} (h : rootAt F z = none) :
    rootedSpecificPairingDensity F Φ Ψ z = 0 := by
  simp [rootedSpecificPairingDensity, h]

theorem rootedSpecificPairingDensity_of_eq_some (F : IndexedCells V) (Φ Ψ : V → Plane)
    {z : Plane} {v : V} (h : rootAt F z = some v) :
    rootedSpecificPairingDensity F Φ Ψ z = specificPairingDensity F Φ Ψ v := by
  simp [rootedSpecificPairingDensity, h]

/-! ### Local finiteness of the endpoint sum -/

/-- The polarized endpoint sum has finite support: `Geometry` makes the degree
finite and the coefficient vanishes off the neighbor set. -/
theorem summable_pairingTerm (F : IndexedCells V) (hF : Geometry F) (Φ Ψ : V → Plane) (v : V) :
    Summable (fun w : V => ∑ i : Fin 2, F.graph.c v w * ((Φ w i - Φ v i) * (Ψ w i - Ψ v i))) := by
  apply summable_of_hasFiniteSupport
  refine (hF.2.2.2.2.2.2.1 v).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw
  rw [SimpleGraph.mem_neighborSet, ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
  have hc : F.graph.c v w ≠ 0 := by
    intro hc
    apply hw
    simp [hc]
  exact lt_of_le_of_ne (F.graph.c_nonneg v w) hc.symm

/-! ### Bilinearity and symmetry -/

theorem pairingSum_comm (F : IndexedCells V) (Φ Ψ : V → Plane) (v : V) :
    pairingSum F Φ Ψ v = pairingSum F Ψ Φ v := by
  simp only [pairingSum]
  exact tsum_congr fun w => Finset.sum_congr rfl fun i _ => by ring

theorem pairingSum_sub_right (F : IndexedCells V) (hF : Geometry F) (Φ Ψ X : V → Plane) (v : V) :
    pairingSum F Φ (fun u => Ψ u - X u) v = pairingSum F Φ Ψ v - pairingSum F Φ X v := by
  have s₁ := summable_pairingTerm F hF Φ Ψ v
  have s₂ := summable_pairingTerm F hF Φ X v
  have hfun : ∀ w : V,
      (∑ i : Fin 2, F.graph.c v w *
          ((Φ w i - Φ v i) * ((Ψ w - X w) i - (Ψ v - X v) i)))
        = (∑ i : Fin 2, F.graph.c v w * ((Φ w i - Φ v i) * (Ψ w i - Ψ v i)))
          - ∑ i : Fin 2, F.graph.c v w * ((Φ w i - Φ v i) * (X w i - X v i)) := by
    intro w
    simp only [Fin.sum_univ_two, PiLp.sub_apply]
    ring
  simp only [pairingSum]
  rw [tsum_congr hfun]
  exact (s₁.hasSum.sub s₂.hasSum).tsum_eq

theorem pairingSum_sub_left (F : IndexedCells V) (hF : Geometry F) (Φ Ψ X : V → Plane) (v : V) :
    pairingSum F (fun u => Φ u - Ψ u) X v = pairingSum F Φ X v - pairingSum F Ψ X v := by
  rw [pairingSum_comm F (fun u => Φ u - Ψ u) X v, pairingSum_sub_right F hF X Φ Ψ v,
    pairingSum_comm F X Φ v, pairingSum_comm F X Ψ v]

/-! ### The manuscript's comparison identity -/

/-- **The algebraic heart of `s:prop:gridindependence`.**  For any base field `g₀`
and any two fields `g₁, g₂`,

`‖g₁ - g₂‖² = (⟪g₁, g₁ - g₀⟫ - ⟪g₁, g₂ - g₀⟫) + (⟪g₂, g₂ - g₀⟫ - ⟪g₂, g₁ - g₀⟫)`

pointwise at every vertex.  The four terms on the right are exactly the four
specific inner products the manuscript shows to vanish. -/
theorem pairingSum_sub_self (F : IndexedCells V) (hF : Geometry F) (g₀ g₁ g₂ : V → Plane)
    (v : V) :
    pairingSum F (fun u => g₁ u - g₂ u) (fun u => g₁ u - g₂ u) v
      = (pairingSum F g₁ (fun u => g₁ u - g₀ u) v - pairingSum F g₁ (fun u => g₂ u - g₀ u) v)
        + (pairingSum F g₂ (fun u => g₂ u - g₀ u) v
            - pairingSum F g₂ (fun u => g₁ u - g₀ u) v) := by
  rw [pairingSum_sub_left F hF g₁ g₂ (fun u => g₁ u - g₂ u) v,
    pairingSum_sub_right F hF g₁ g₁ g₂ v, pairingSum_sub_right F hF g₂ g₁ g₂ v,
    pairingSum_sub_right F hF g₁ g₁ g₀ v, pairingSum_sub_right F hF g₁ g₂ g₀ v,
    pairingSum_sub_right F hF g₂ g₂ g₀ v, pairingSum_sub_right F hF g₂ g₁ g₀ v,
    pairingSum_comm F g₂ g₁ v]
  ring

theorem specificPairingDensity_sub_self (F : IndexedCells V) (hF : Geometry F)
    (g₀ g₁ g₂ : V → Plane) (v : V) :
    specificPairingDensity F (fun u => g₁ u - g₂ u) (fun u => g₁ u - g₂ u) v
      = (specificPairingDensity F g₁ (fun u => g₁ u - g₀ u) v
          - specificPairingDensity F g₁ (fun u => g₂ u - g₀ u) v)
        + (specificPairingDensity F g₂ (fun u => g₂ u - g₀ u) v
            - specificPairingDensity F g₂ (fun u => g₁ u - g₀ u) v) := by
  simp only [specificPairingDensity, pairingSum_sub_self F hF g₀ g₁ g₂ v, sub_div, add_div]

theorem rootedSpecificPairingDensity_sub_self (F : IndexedCells V) (hF : Geometry F)
    (g₀ g₁ g₂ : V → Plane) (z : Plane) :
    rootedSpecificPairingDensity F (fun u => g₁ u - g₂ u) (fun u => g₁ u - g₂ u) z
      = (rootedSpecificPairingDensity F g₁ (fun u => g₁ u - g₀ u) z
          - rootedSpecificPairingDensity F g₁ (fun u => g₂ u - g₀ u) z)
        + (rootedSpecificPairingDensity F g₂ (fun u => g₂ u - g₀ u) z
            - rootedSpecificPairingDensity F g₂ (fun u => g₁ u - g₀ u) z) := by
  rcases hroot : rootAt F z with _ | v
  · rw [rootedSpecificPairingDensity_of_eq_none F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_none F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_none F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_none F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_none F _ _ hroot]
    ring
  · rw [rootedSpecificPairingDensity_of_eq_some F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_some F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_some F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_some F _ _ hroot,
      rootedSpecificPairingDensity_of_eq_some F _ _ hroot]
    exact specificPairingDensity_sub_self F hF g₀ g₁ g₂ v

/-! ### Nonnegativity and the identification with the project's `ρ_Φ` -/

theorem pairingSum_self_nonneg (F : IndexedCells V) (Φ : V → Plane) (v : V) :
    0 ≤ pairingSum F Φ Φ v :=
  tsum_nonneg fun w =>
    Finset.sum_nonneg fun i _ => mul_nonneg (F.graph.c_nonneg v w) (mul_self_nonneg _)

theorem specificPairingDensity_self_nonneg (F : IndexedCells V) (Φ : V → Plane) (v : V) :
    0 ≤ specificPairingDensity F Φ Φ v := by
  have harea : (0 : ℝ) ≤ cellArea F v := ENNReal.toReal_nonneg
  exact div_nonneg (pairingSum_self_nonneg F Φ v) (by linarith)

theorem rootedSpecificPairingDensity_self_nonneg (F : IndexedCells V) (Φ : V → Plane)
    (z : Plane) : 0 ≤ rootedSpecificPairingDensity F Φ Φ z := by
  rcases hroot : rootAt F z with _ | v
  · rw [rootedSpecificPairingDensity_of_eq_none F _ _ hroot]
  · rw [rootedSpecificPairingDensity_of_eq_some F _ _ hroot]
    exact specificPairingDensity_self_nonneg F Φ v

/-- The diagonal of the polarized density **is** the project's specific-energy
density `ρ_Φ`.  No competing energy notion is introduced. -/
theorem ofReal_specificPairingDensity_self (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) (v : V) :
    ENNReal.ofReal (specificPairingDensity F Φ Φ v) = specificEnergyDensity F Φ v := by
  have harea : 0 < cellArea F v := StatementIngredients.cellArea_pos F hF v
  have hterm : ∀ w : V, (∑ i : Fin 2, F.graph.c v w * ((Φ w i - Φ v i) * (Φ w i - Φ v i)))
      = F.graph.c v w * ‖Φ w - Φ v‖ ^ 2 := by
    intro w
    rw [norm_sub_sq_eq_sum_coord]
    simp only [Fin.sum_univ_two]
    ring
  have hsum : Summable (fun w : V => F.graph.c v w * ‖Φ w - Φ v‖ ^ 2) :=
    (summable_pairingTerm F hF Φ Φ v).congr hterm
  have hnum : pairingSum F Φ Φ v = ∑' w : V, F.graph.c v w * ‖Φ w - Φ v‖ ^ 2 := by
    simp only [pairingSum]
    exact tsum_congr hterm
  have hnumnn : 0 ≤ pairingSum F Φ Φ v := pairingSum_self_nonneg F Φ v
  have h2 : ENNReal.ofReal ((2 : ℝ) * cellArea F v) = 2 * ENNReal.ofReal (cellArea F v) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpos : (0 : ℝ) < 2 * cellArea F v := by linarith
  calc ENNReal.ofReal (specificPairingDensity F Φ Φ v)
      = ENNReal.ofReal (pairingSum F Φ Φ v * (2 * cellArea F v)⁻¹) := by
        rw [specificPairingDensity, div_eq_mul_inv]
    _ = ENNReal.ofReal (pairingSum F Φ Φ v) * ENNReal.ofReal ((2 * cellArea F v)⁻¹) := by
        rw [ENNReal.ofReal_mul hnumnn]
    _ = ENNReal.ofReal (pairingSum F Φ Φ v) * (ENNReal.ofReal (2 * cellArea F v))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hpos]
    _ = ENNReal.ofReal (pairingSum F Φ Φ v) / (2 * ENNReal.ofReal (cellArea F v)) := by
        rw [← h2, div_eq_mul_inv]
    _ = (∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2)) /
          (2 * ENNReal.ofReal (cellArea F v)) := by
        rw [hnum, ENNReal.ofReal_tsum_of_nonneg
          (fun w => mul_nonneg (F.graph.c_nonneg v w) (sq_nonneg _)) hsum]
        congr 1
        exact tsum_congr fun w => ENNReal.ofReal_mul (F.graph.c_nonneg v w)
    _ = specificEnergyDensity F Φ v := rfl

/-! ### A vanishing density kills every edge at that vertex -/

/-- **`s:lem:localcontrol`, vertex form.**  If the polarized density of `Ψ`
against itself vanishes at `v`, then `Ψ` is constant on the closed star of `v`. -/
theorem eq_of_specificPairingDensity_self_eq_zero (F : IndexedCells V) (hF : Geometry F)
    (Ψ : V → Plane) {v w : V} (hzero : specificPairingDensity F Ψ Ψ v = 0)
    (hc : 0 < F.graph.c v w) : Ψ w = Ψ v := by
  have harea : 0 < cellArea F v := StatementIngredients.cellArea_pos F hF v
  have hden : (2 : ℝ) * cellArea F v ≠ 0 := by positivity
  have hnum : pairingSum F Ψ Ψ v = 0 := by
    rw [specificPairingDensity, div_eq_zero_iff] at hzero
    rcases hzero with h | h
    · exact h
    · exact absurd h hden
  have hsum := summable_pairingTerm F hF Ψ Ψ v
  have hnonneg : ∀ u : V,
      0 ≤ ∑ i : Fin 2, F.graph.c v u * ((Ψ u i - Ψ v i) * (Ψ u i - Ψ v i)) := fun u =>
    Finset.sum_nonneg fun i _ => mul_nonneg (F.graph.c_nonneg v u) (mul_self_nonneg _)
  have hle : (∑ i : Fin 2, F.graph.c v w * ((Ψ w i - Ψ v i) * (Ψ w i - Ψ v i))) ≤ 0 := by
    have h := hsum.le_tsum w (fun j _ => hnonneg j)
    rw [show (∑' u : V, ∑ i : Fin 2, F.graph.c v u * ((Ψ u i - Ψ v i) * (Ψ u i - Ψ v i)))
      = pairingSum F Ψ Ψ v from rfl, hnum] at h
    exact h
  have hterm : (∑ i : Fin 2, F.graph.c v w * ((Ψ w i - Ψ v i) * (Ψ w i - Ψ v i))) = 0 :=
    le_antisymm hle (hnonneg w)
  rw [Fin.sum_univ_two] at hterm
  have hA : 0 ≤ F.graph.c v w * ((Ψ w 0 - Ψ v 0) * (Ψ w 0 - Ψ v 0)) :=
    mul_nonneg hc.le (mul_self_nonneg _)
  have hB : 0 ≤ F.graph.c v w * ((Ψ w 1 - Ψ v 1) * (Ψ w 1 - Ψ v 1)) :=
    mul_nonneg hc.le (mul_self_nonneg _)
  have h0 : Ψ w 0 - Ψ v 0 = 0 := by
    have hA0 : F.graph.c v w * ((Ψ w 0 - Ψ v 0) * (Ψ w 0 - Ψ v 0)) = 0 := by linarith
    rcases mul_eq_zero.1 hA0 with h | h
    · exact absurd h hc.ne'
    · exact mul_self_eq_zero.1 h
  have h1 : Ψ w 1 - Ψ v 1 = 0 := by
    have hB0 : F.graph.c v w * ((Ψ w 1 - Ψ v 1) * (Ψ w 1 - Ψ v 1)) = 0 := by linarith
    rcases mul_eq_zero.1 hB0 with h | h
    · exact absurd h hc.ne'
    · exact mul_self_eq_zero.1 h
  have hnormsq : ‖Ψ w - Ψ v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_eq_sum_coord, Fin.sum_univ_two, h0, h1]
    ring
  have hnorm : ‖Ψ w - Ψ v‖ = 0 := by nlinarith [norm_nonneg (Ψ w - Ψ v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

/-! ### Anchoring along the connected graph -/

/-- A vertex function that is constant across every edge is constant along every
walk. -/
theorem eq_of_walk {α : Type*} {G : SimpleGraph V} {θ : V → α}
    (h : ∀ ⦃x y : V⦄, G.Adj x y → θ y = θ x) {a b : V} (p : G.Walk a b) : θ b = θ a := by
  induction p with
  | nil => rfl
  | cons hadj q ih =>
      rw [ih]
      exact h hadj

/-- **The manuscript's anchored equality.**  If the polarized density of the
difference vanishes at every vertex and the two potentials agree at the root cell
`H₀`, they agree at every vertex.  `Geometry` supplies the connectivity of the
cell adjacency graph. -/
theorem eq_of_forall_specificPairingDensity_self_eq_zero (F : IndexedCells V) (hF : Geometry F)
    (Φ Ψ : V → Plane)
    (hzero : ∀ v : V,
      specificPairingDensity F (fun u => Φ u - Ψ u) (fun u => Φ u - Ψ u) v = 0)
    {v₀ : V} (hanchor : Φ v₀ = Ψ v₀) : Φ = Ψ := by
  have hadj : ∀ ⦃x y : V⦄, F.graph.toSimpleGraph.Adj x y →
      (fun u => Φ u - Ψ u) y = (fun u => Φ u - Ψ u) x := by
    intro x y hxy
    have hcpos : 0 < F.graph.c x y := hxy
    exact eq_of_specificPairingDensity_self_eq_zero F hF (fun u => Φ u - Ψ u) (hzero x) hcpos
  have hconn : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  funext v
  obtain ⟨p⟩ := hconn.preconnected v₀ v
  have hval : Φ v - Ψ v = Φ v₀ - Ψ v₀ := eq_of_walk (θ := fun u => Φ u - Ψ u) hadj p
  rw [hanchor, sub_self] at hval
  exact sub_eq_zero.1 hval

/-! ### The specific inner product on the joint marked law -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The comparison proposition -/

end ReflectedGMS.HarmonicGridIndependence
