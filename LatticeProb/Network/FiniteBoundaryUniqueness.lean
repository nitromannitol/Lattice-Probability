import LatticeProb.Network.Dirichlet

/-!
# Boundary uniqueness on finite connected networks

Two functions harmonic outside a nonempty boundary and equal there agree on all vertices.
This specializes the existing Dirichlet uniqueness theorem, whose proof applies the maximum
and minimum principles to their difference. Equal terminal values therefore force constancy.
-/

namespace LatticeProb.Network

variable {V : Type*} [Finite V] {G : SimpleGraph V} [G.LocallyFinite]

/-- On a finite connected network, boundary agreement and harmonicity away from a nonempty
boundary determine a function on every actual vertex. -/
theorem eq_of_harmonic_off_boundary (hG : G.Connected) {c : V → V → ℝ}
    (hc : IsCond G c) {B : Set V} (hB : B.Nonempty) {u v : V → ℝ}
    (hu : ∀ x, x ∉ B → netLaplacian G c u x = 0)
    (hv : ∀ x, x ∉ B → netLaplacian G c v x = 0)
    (hboundary : ∀ x ∈ B, u x = v x) : u = v := by
  classical
  letI := Fintype.ofFinite V
  let A := Finset.univ.filter fun x => x ∉ B
  have hmem (x : V) : x ∈ A ↔ x ∉ B := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
  have hout : ∃ x, x ∉ A := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, fun h => (hmem b).mp h hb⟩
  have haccess := boundaryAccessible_of_connected hG A hout
  apply dirichlet_unique hc A haccess (g := v)
  · constructor
    · exact fun x hx => hu x ((hmem x).mp hx)
    · intro x hx
      exact hboundary x (by simpa only [hmem, not_not] using hx)
  · constructor
    · exact fun x hx => hv x ((hmem x).mp hx)
    · exact fun _ _ => rfl

/-- Constant boundary values force a harmonic function to have that value everywhere on a
finite connected network. -/
theorem eq_const_of_harmonic_off_boundary (hG : G.Connected) {c : V → V → ℝ}
    (hc : IsCond G c) {B : Set V} (hB : B.Nonempty) {u : V → ℝ} {a : ℝ}
    (hu : ∀ x, x ∉ B → netLaplacian G c u x = 0)
    (hboundary : ∀ x ∈ B, u x = a) : u = fun _ => a := by
  exact eq_of_harmonic_off_boundary hG hc hB hu
    (fun x _ => netLaplacian_const c a x) hboundary

/-- If a function on a finite connected network is harmonic at every nonterminal vertex,
equal terminal values force it to equal the first terminal value everywhere. -/
theorem eq_const_of_harmonic_off_terminals (hG : G.Connected) {c : V → V → ℝ}
    (hc : IsCond G c) {s t : V} {u : V → ℝ}
    (hu : ∀ x, x ≠ s → x ≠ t → netLaplacian G c u x = 0)
    (hst : u s = u t) : u = fun _ => u s := by
  apply eq_const_of_harmonic_off_boundary hG hc
    (B := {s, t}) ⟨s, Set.mem_insert s {t}⟩
  · intro x hx
    have hxs : x ≠ s := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or])
    have hxt : x ≠ t := fun h => hx (by simp only [h, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true])
    exact hu x hxs hxt
  · intro x hx
    rcases hx with rfl | hx
    · rfl
    · rw [Set.mem_singleton_iff.mp hx]
      exact hst.symm

/-- Genuine nonconstancy on the actual finite connected graph forces unequal terminal
values when every other vertex is harmonic. -/
theorem terminal_ne_of_harmonic_off_terminals (hG : G.Connected) {c : V → V → ℝ}
    (hc : IsCond G c) {s t : V} {u : V → ℝ}
    (hu : ∀ x, x ≠ s → x ≠ t → netLaplacian G c u x = 0)
    (hnonconstant : ∃ x y, u x ≠ u y) : u s ≠ u t := by
  intro hst
  have heq := eq_const_of_harmonic_off_terminals hG hc hu hst
  obtain ⟨x, y, hxy⟩ := hnonconstant
  exact hxy ((congrFun heq x).trans (congrFun heq y).symm)

end LatticeProb.Network
