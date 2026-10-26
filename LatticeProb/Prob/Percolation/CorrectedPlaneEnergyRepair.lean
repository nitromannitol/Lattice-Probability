import LatticeProb.Network.SingleEdgeEnergyRepair
import LatticeProb.Prob.Percolation.NonBridgeComponentCarrier
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.Prob.Percolation.MeasurableRootedPlane

/-!
# Actual corrected-plane repair and comparison on a nonbridge deletion

A bounded dipole repairs harmonicity on the literal deleted graph. The position-fixing
carrier isomorphism transports the repaired plane, its full real-radius slope tail and
finite ordered energy to the new actual infinite component. Validity identifies every
other same-slope source plane up to an additive constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace LatticeProb.Percolation

open LatticeProb.Graph

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- A globally bounded difference preserves every real-radius uniform slope tail. -/
theorem componentSlopeAsymptotics_of_bounded_difference (C : OpenComponent ω)
    {q : Fin d → ℝ} {u w : C → ℝ} (hu : componentSlopeAsymptotics C q u)
    (B : ℝ) (hB : ∀ x, |w x - u x| ≤ B) : componentSlopeAsymptotics C q w := by
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hu (ε / 2) (by positivity)
  refine ⟨max R₀ (2 * (|B| + 1) / ε), hR₀.trans_le (le_max_left _ _), ?_⟩
  intro R hR x hx
  have hsmall := htail R ((le_max_left _ _).trans hR) x hx
  have hlarge : 2 * (|B| + 1) ≤ R * ε :=
    (div_le_iff₀ hε).mp ((le_max_right _ _).trans hR)
  calc
    |w x - componentSlope C q x| =
        |(w x - u x) + (u x - componentSlope C q x)| := by congr 1; ring
    _ ≤ |w x - u x| + |u x - componentSlope C q x| := abs_add_le _ _
    _ ≤ B + (ε / 2) * R := add_le_add (hB x) hsmall
    _ ≤ ε * R := by linarith [le_abs_self B]

variable (C : OpenComponent ω) (hOld : HasUniqueInfiniteOpenComponent ω)
  (hC : C.supp.Infinite) {a b : C} (hab : (componentGraph C).Adj a b)
  (hNew : HasUniqueInfiniteOpenComponent (componentEdgeFlip C hab))
  (hreach : ((openGraph (componentEdgeFlip C hab)).induce C.supp).Reachable a b)

/-- Pullback through the position-fixing deletion isomorphism preserves the whole
finite Laplacian, with its actual neighbor indexing. -/
theorem nonBridgeComponent_laplacian (w : C → ℝ) (x : C) :
    componentLaplacian (uniqueInfiniteComponent hNew)
      (fun y => w ((nonBridgeComponentEquiv C hOld hC hab hNew hreach).symm y))
      (nonBridgeComponentEquiv C hOld hC hab hNew hreach x) =
    laplacian ((componentGraph C).deleteEdges
      (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C))) w x := by
  classical
  let e := nonBridgeComponentIso C hOld hC hab hNew hreach
  change laplacian (componentGraph (uniqueInfiniteComponent hNew))
    (fun y => w (e.symm y)) (e x) = laplacian _ w x
  unfold laplacian
  symm
  apply Finset.sum_bij (fun y _ => e y)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mpr hy
  · intro y _ y' _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact e.map_rel_iff.mp (by simpa only [e.apply_symm_apply] using hy)
  · intro y _
    change w y - w x = w (e.symm (e y)) - w (e.symm (e x))
    rw [e.symm_apply_apply, e.symm_apply_apply]

/-- The constructed new source plane has bounded finite-energy difference from the
old plane transported through the fully characterized actual carrier equivalence. -/
theorem exists_correctedPlane_bounded_finite_energy_of_nonbridge
    {q : Fin d → ℝ} {u : C → ℝ} (hu : IsCorrectedPlane C q u) :
    let E := nonBridgeComponentEquiv C hOld hC hab hNew hreach
    ∃ v : uniqueInfiniteComponent hNew → ℝ, ∃ B K : ℝ,
      IsCorrectedPlane (uniqueInfiniteComponent hNew) q v ∧
      (∀ y, |v y - u (E.symm y)| ≤ B) ∧
      (∀ F : Finset (uniqueInfiniteComponent hNew × uniqueInfiniteComponent hNew),
        (∀ e ∈ F, (componentGraph (uniqueInfiniteComponent hNew)).Adj e.1 e.2) →
        ∑ e ∈ F, ((v e.1 - u (E.symm e.1)) -
          (v e.2 - u (E.symm e.2))) ^ 2 ≤ K) := by
  classical
  letI : Infinite C := hC.to_subtype
  let E := nonBridgeComponentEquiv C hOld hC hab hNew hreach
  let e := nonBridgeComponentIso C hOld hC hab hNew hreach
  have hreachD : ((componentGraph C).deleteEdges
      (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C))).Reachable a b := by
    rw [← singletonBondFlip_induce_eq_deleteEdges C hab]
    exact hreach
  obtain ⟨w, B, K, hw, hB, hK⟩ :=
    Network.exists_bounded_finite_energy_single_edge_repair (componentGraph C)
      C.connected_toSimpleGraph hab hreachD u (fun x => hu.1.1 x)
  let v : uniqueInfiniteComponent hNew → ℝ := fun y => w (E.symm y)
  refine ⟨v, B, K, ?_, fun y => hB (E.symm y), ?_⟩
  · apply (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mpr
    constructor
    · intro y
      have h := nonBridgeComponent_laplacian C hOld hC hab hNew hreach w (E.symm y)
      change componentLaplacian (uniqueInfiniteComponent hNew)
        (fun y => w (E.symm y)) (E (E.symm y)) = _ at h
      rw [E.apply_symm_apply, hw] at h
      exact h
    · have hs := componentSlopeAsymptotics_of_bounded_difference C hu.2 B hB
      intro ε hε
      obtain ⟨R₀, hR₀, ht⟩ := hs ε hε
      refine ⟨R₀, hR₀, ?_⟩
      intro R hR y hy
      have hy' : E.symm y ∈ componentEuclideanBall C 0 R := by
        rw [mem_componentEuclideanBall] at hy ⊢
        exact hy
      exact ht R hR (E.symm y) hy'
  · intro F hF
    let P : (uniqueInfiniteComponent hNew × uniqueInfiniteComponent hNew) → C × C :=
      fun z => (E.symm z.1, E.symm z.2)
    have hP : Function.Injective P := (E.symm.prodCongr E.symm).injective
    have hbound := hK (F.image P) (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact e.symm.map_rel_iff.mpr (hF t ht))
    rw [Finset.sum_image (fun x _ y _ h => hP h)] at hbound
    exact hbound

/-- Validity on the actual new configuration makes every two same-slope source planes
have constant difference, using normalization at an actual component vertex. -/
theorem correctedPlane_sub_eq_const_of_valid
    {η : Configuration d} (hvalid : η ∈ correctorValidEvent d)
    (hη : HasUniqueInfiniteOpenComponent η) (o : uniqueInfiniteComponent hη)
    {q : Fin d → ℝ} {v v' : uniqueInfiniteComponent hη → ℝ}
    (hv : IsCorrectedPlane (uniqueInfiniteComponent hη) q v)
    (hv' : IsCorrectedPlane (uniqueInfiniteComponent hη) q v') :
    ∀ y, v' y - v y = v' o - v o := by
  let N := uniqueInfiniteComponent hη
  have hn : IsCorrectedPlane N q (v - fun _ => v o) := by
    simpa only [sub_zero] using isCorrectedPlane_sub N hv (isCorrectedPlane_const N (v o))
  have hn' : IsCorrectedPlane N q (v' - fun _ => v' o) := by
    simpa only [sub_zero] using isCorrectedPlane_sub N hv' (isCorrectedPlane_const N (v' o))
  have heq := ((hvalid.2 hη).1 q o).unique
    ⟨hn, sub_self _⟩ ⟨hn', sub_self _⟩
  intro y
  have hy := congrFun heq y
  change v y - v o = v' y - v' o at hy
  linarith

/-- Every actual new same-slope source plane has produced bounded finite ordered energy
relative to the transported old plane. No energy or slope-preservation premise is used. -/
theorem correctedPlane_comparison_bounded_finite_energy_of_nonbridge
    (hvalid : componentEdgeFlip C hab ∈ correctorValidEvent d)
    {q : Fin d → ℝ} {u : C → ℝ} (hu : IsCorrectedPlane C q u)
    {v' : uniqueInfiniteComponent hNew → ℝ}
    (hv' : IsCorrectedPlane (uniqueInfiniteComponent hNew) q v') :
    let E := nonBridgeComponentEquiv C hOld hC hab hNew hreach
    ∃ B K : ℝ, (∀ y, |v' y - u (E.symm y)| ≤ B) ∧
      (∀ F : Finset (uniqueInfiniteComponent hNew × uniqueInfiniteComponent hNew),
        (∀ e ∈ F, (componentGraph (uniqueInfiniteComponent hNew)).Adj e.1 e.2) →
        ∑ e ∈ F, ((v' e.1 - u (E.symm e.1)) -
          (v' e.2 - u (E.symm e.2))) ^ 2 ≤ K) := by
  let E := nonBridgeComponentEquiv C hOld hC hab hNew hreach
  obtain ⟨v, B, K, hv, hB, hK⟩ :=
    exists_correctedPlane_bounded_finite_energy_of_nonbridge C hOld hC hab hNew hreach hu
  let c := v' (E a) - v (E a)
  have hc : ∀ y, v' y - v y = c :=
    correctedPlane_sub_eq_const_of_valid hvalid hNew (E a) hv hv'
  refine ⟨|c| + B, K, ?_, ?_⟩
  · intro y
    calc
      |v' y - u (E.symm y)| = |c + (v y - u (E.symm y))| := by
        congr 1
        linarith [hc y]
      _ ≤ |c| + |v y - u (E.symm y)| := abs_add_le _ _
      _ ≤ |c| + B := add_le_add (le_refl |c|) (hB y)
  · intro F hF
    have hd (x y : uniqueInfiniteComponent hNew) :
        (v' x - u (E.symm x)) - (v' y - u (E.symm y)) =
          (v x - u (E.symm x)) - (v y - u (E.symm y)) := by
      linarith [hc x, hc y]
    calc
      _ = ∑ e ∈ F, ((v e.1 - u (E.symm e.1)) -
          (v e.2 - u (E.symm e.2))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hd]
      _ ≤ K := hK F hF

end

end LatticeProb.Percolation
