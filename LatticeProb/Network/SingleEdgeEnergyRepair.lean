import LatticeProb.Network.FiniteEnergyVoltage
import LatticeProb.Network.EdgeDeletionRigidity

/-!
# Bounded finite-energy harmonic repair after a nonbridge deletion

The deleted graph is connected by the endpoint detour. A bounded unit dipole on that
actual graph cancels the removed-edge forcing, with bounded finite ordered energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- The removed edge produces exactly the signed old endpoint drop. -/
theorem laplacian_delete_singleton_of_harmonic {a b : V} (hab : G.Adj a b)
    (u : V → ℝ) (hu : ∀ x, laplacian G u x = 0) (x : V) :
    laplacian (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))) u x =
      (u a - u b) * ((if x = a then (1 : ℝ) else 0) -
        (if x = b then 1 else 0)) := by
  have h := netLaplacian_single_edge_difference G hab u x
  simp only [netLaplacian_unitCond, hu, zero_sub] at h
  split_ifs at h ⊢ <;> linarith

/-- A harmonic function admits an actual bounded finite-energy repair on the nonbridge
single-edge deletion. The repair is constructed as the old function plus its edge drop
times a bounded unit dipole on the deleted graph. -/
theorem exists_bounded_finite_energy_single_edge_repair [Infinite V]
    (hG : G.Connected) {a b : V} (hab : G.Adj a b)
    (hreach : (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b)
    (u : V → ℝ) (hu : ∀ x, laplacian G u x = 0) :
    ∃ w : V → ℝ, ∃ B K : ℝ,
      (∀ x, laplacian (G.deleteEdges
        (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))) w x = 0) ∧
      (∀ x, |w x - u x| ≤ B) ∧
      (∀ F : Finset (V × V),
        (∀ e ∈ F, (G.deleteEdges
          (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))).Adj e.1 e.2) →
        ∑ e ∈ F, ((w e.1 - u e.1) - (w e.2 - u e.2)) ^ 2 ≤ K) := by
  classical
  let D := G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))
  have hD : D.Connected := by
    simpa only [D, Finset.coe_singleton] using
      hG.connected_delete_edge_of_not_isBridge (x := a) (y := b) (by
        rw [SimpleGraph.isBridge_iff]
        exact not_not.mpr (by simpa only [Finset.coe_singleton] using hreach))

  obtain ⟨f, M, _, _, hf, hlap, K, henergy⟩ :=
    exists_finite_energy_voltage_of_connected hD hab.ne
  let g := u a - u b
  let w : V → ℝ := u + g • f
  have hdiff (x : V) : w x - u x = g * f x := by
    dsimp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨w, |g| * M, g ^ 2 * K, ?_, ?_, ?_⟩
  · intro x
    have hd := laplacian_delete_singleton_of_harmonic G hab u hu x
    have hf' : netLaplacian D (unitCond D) f x =
        (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
      rw [netLaplacian_unitCond]
      exact hlap x
    change laplacian D w x = 0
    rw [← netLaplacian_unitCond]
    change netLaplacian D (unitCond D) (u + g • f) x = 0
    rw [netLaplacian_add]
    change netLaplacian D (unitCond D) u x +
      netLaplacian D (unitCond D) (fun y => g * f y) x = 0
    rw [netLaplacian_smul, netLaplacian_unitCond, hd, hf']
    dsimp only [g]
    ring
  · intro x
    rw [hdiff, abs_mul, abs_of_nonneg (hf x).1]
    exact mul_le_mul_of_nonneg_left (hf x).2 (abs_nonneg g)
  · intro F hF
    simp_rw [hdiff]
    calc
      _ = g ^ 2 * ∑ e ∈ F, (f e.1 - f e.2) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ ≤ g ^ 2 * K := mul_le_mul_of_nonneg_left (henergy F hF) (sq_nonneg g)

end LatticeProb.Network
