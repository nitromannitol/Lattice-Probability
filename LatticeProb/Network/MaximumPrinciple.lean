/-
The maximum principle for a network Laplacian.

If `f` is `c`-harmonic at every vertex of a finite set `C` outside a set `S`,
and `f ≤ M` off `C` and on `S`, then `f ≤ M` everywhere.  The proof is the
usual one: a vertex of `C` where `f` exceeds `M` and attains the maximum of `f`
over `C` is harmonic there, so every neighbour carries the same value and lies
again in `C`; walking to a vertex outside `C`, which a connected graph provides,
contradicts that.

In the application `S = {o}` is the source of the killed Green function and `M`
its value there, so a voltage vanishing on the boundary of `C` is bounded by its
value at the source, and two voltages with the same data agree.
-/
import LatticeProb.Network.Killed

open Finset

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The maximum principle. -/
theorem le_of_harmonicOn (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) (S : Set V) (f : V → ℝ) (M : ℝ) {q : V} (hq : q ∉ C)
    (hharm : ∀ x ∈ C, x ∉ S → netLaplacian G c f x = 0)
    (hout : ∀ x, x ∉ C → f x ≤ M) (hS : ∀ x ∈ S, f x ≤ M) :
    ∀ x, f x ≤ M := by
  classical
  intro x
  by_contra hcon
  rw [not_le] at hcon
  have hxC : x ∈ C := by
    by_contra h
    exact absurd (hout x h) (not_le.mpr hcon)
  obtain ⟨b, hbC, hbmax⟩ := Finset.exists_max_image C f ⟨x, hxC⟩
  have hMb : M < f b := lt_of_lt_of_le hcon (hbmax x hxC)
  have hle : ∀ y : V, f y ≤ f b := by
    intro y
    by_cases hy : y ∈ C
    · exact hbmax y hy
    · exact le_trans (hout y hy) hMb.le
  have hstep : ∀ y : V, y ∈ C → f y = f b → ∀ z : V, G.Adj y z → z ∈ C ∧ f z = f b := by
    intro y hyC hyb z hyz
    have hyS : y ∉ S := fun h => absurd (hS y h) (not_le.mpr (hyb ▸ hMb))
    have hzero := hharm y hyC hyS
    have hnonpos : ∀ w ∈ G.neighborFinset y, c y w * (f w - f y) ≤ 0 := by
      intro w _
      exact mul_nonpos_of_nonneg_of_nonpos (hc.nonneg y w) (by
        have := hle w
        rw [hyb]
        linarith)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hzero
    have hz := hall z ((SimpleGraph.mem_neighborFinset _ _ _).mpr hyz)
    have hfz : f z = f y := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (hc.pos hyz).ne'
      · linarith
    refine ⟨?_, by rw [hfz, hyb]⟩
    by_contra hzC
    have := hout z hzC
    rw [hfz, hyb] at this
    linarith
  have hwalk : ∀ {u v : V} (p : G.Walk u v), u ∈ C → f u = f b → v ∈ C ∧ f v = f b := by
    intro u v p
    induction p with
    | nil => intro h1 h2; exact ⟨h1, h2⟩
    | @cons a d e hadj p' ih =>
        intro h1 h2
        obtain ⟨hd, hfd⟩ := hstep a h1 h2 d hadj
        exact ih hd hfd
  obtain ⟨p⟩ := hG.preconnected b q
  exact hq (hwalk p hbC rfl).1

end LatticeProb.Network
