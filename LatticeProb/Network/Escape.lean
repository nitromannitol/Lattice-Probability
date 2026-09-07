/-
The equilibrium potential, and the escape rate as the reciprocal resistance.

The killed Green function normalized to one at the source solves the boundary
value problem that the probability of reaching the source before leaving `C`
solves: it vanishes off `C`, it is harmonic on `C` away from the source, and it
is one at the source.  That problem has exactly one solution, by the maximum
principle, so the normalized Green function IS that potential however it is
later constructed.

Its normal derivative at the source is the reciprocal of the degree times the
effective resistance, which is the escape rate: one minus the mean of the
potential over the neighbours of `o` is `1 / (deg(o) · R_eff)`.  That is the
identity `P_o(leave C before returning) = 1 / (deg(o) · R_eff)` in potential
form; identifying the potential with the hitting probability itself needs a
first-passage decomposition of the killed kernel, which is not proved here.
-/
import LatticeProb.Network.Series
import LatticeProb.Network.MaximumPrinciple

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### Linearity of the Laplacian -/

theorem laplacian_sub (f g : V → ℝ) (x : V) :
    laplacian G (fun v => f v - g v) x = laplacian G f x - laplacian G g x := by
  rw [laplacian, laplacian, laplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem laplacian_div (f : V → ℝ) (c : ℝ) (x : V) :
    laplacian G (fun v => f v / c) x = laplacian G f x / c := by
  rw [laplacian, laplacian, Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem laplacian_neg (f : V → ℝ) (x : V) :
    laplacian G (fun v => -f v) x = -laplacian G f x := by
  rw [laplacian, laplacian, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-! ### The effective resistance is positive -/

/-- The walk stands at the source at time zero, so the expected local time there
is at least one and the effective resistance is positive. -/
theorem effRes_pos (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C) (hq : q ∉ C) :
    0 < effRes G C o := by
  have hne : o ≠ q := fun h => hq (h ▸ ho)
  have hdeg : 0 < G.degree o := degree_pos_of_ne hG hne o
  rw [effRes, killedGreenReal_eq_tsum hG C hq]
  refine div_pos ?_ (by exact_mod_cast hdeg)
  have hsum := summable_killedHeat hG C hq o o
  have hterm : killedHeat G (C : Set V) 0 o o = 1 := by
    rw [killedHeat_zero, if_pos (by exact_mod_cast ho), if_pos rfl]
  refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ?_
  rw [← hterm]
  exact hsum.le_tsum 0 fun k _ => killedHeat_nonneg _ k o o

/-! ### The equilibrium potential -/

/-- The killed Green function normalized to one at the source. -/
noncomputable def equilibrium (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (o : V) :
    V → ℝ :=
  fun x => killedGreenReal G (C : Set V) o x / effRes G C o

theorem equilibrium_self (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C) (hq : q ∉ C) :
    equilibrium G C o o = 1 := by
  have hR : effRes G C o ≠ 0 := ne_of_gt (effRes_pos hG C ho hq)
  show killedGreenReal G (C : Set V) o o / effRes G C o = 1
  rw [show killedGreenReal G (C : Set V) o o = effRes G C o from rfl, div_self hR]

theorem equilibrium_eq_zero (hG : G.Connected) (C : Finset V) {o q : V} (_ho : o ∈ C)
    (hq : q ∉ C) {v : V} (hv : v ∉ C) : equilibrium G C o v = 0 := by
  show killedGreenReal G (C : Set V) o v / effRes G C o = 0
  rw [killedGreen_vanishes hG C hq (by exact_mod_cast hv), zero_div]

theorem laplacian_equilibrium (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) {v : V} (hv : v ∈ C) (hvo : v ≠ o) :
    laplacian G (equilibrium G C o) v = 0 := by
  have hrw : equilibrium G C o
      = fun w => killedGreenReal G (C : Set V) o w / effRes G C o := rfl
  rw [hrw, laplacian_div, harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hv) hvo,
    zero_div]

theorem laplacian_equilibrium_source (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) :
    laplacian G (equilibrium G C o) o = -1 / effRes G C o := by
  have hrw : equilibrium G C o
      = fun w => killedGreenReal G (C : Set V) o w / effRes G C o := rfl
  rw [hrw, laplacian_div, laplacian_killedGreenReal_source hG C ho hq]

/-! ### Uniqueness -/

/-- **The boundary value problem has one solution.**  A function that vanishes
off `C`, is harmonic on `C` away from the source and equals one at the source is
the equilibrium potential. -/
theorem equilibrium_unique (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (f : V → ℝ) (hf0 : ∀ x, x ∉ C → f x = 0) (hfo : f o = 1)
    (hharm : ∀ x ∈ C, x ≠ o → laplacian G f x = 0) :
    f = equilibrium G C o := by
  classical
  have hbound : ∀ (u : V → ℝ), (∀ x, x ∉ C → u x = 0) → u o = 0 →
      (∀ x ∈ C, x ≠ o → laplacian G u x = 0) → ∀ x, u x ≤ 0 := by
    intro u hu0 huo hharmu
    refine le_of_harmonicOn hG isCond_unitCond C {o} u 0 hq ?_ ?_ ?_
    · intro x hx hxS
      rw [netLaplacian_unitCond]
      exact hharmu x hx fun hEq => hxS (by simp [hEq])
    · intro x hx
      rw [hu0 x hx]
    · intro x hx
      have : x = o := hx
      rw [this, huo]
  set u : V → ℝ := fun v => f v - equilibrium G C o v with hu
  have hu0 : ∀ x, x ∉ C → u x = 0 := by
    intro x hx
    show f x - equilibrium G C o x = 0
    rw [hf0 x hx, equilibrium_eq_zero hG C ho hq hx, sub_zero]
  have huo : u o = 0 := by
    show f o - equilibrium G C o o = 0
    rw [hfo, equilibrium_self hG C ho hq, sub_self]
  have hharmu : ∀ x ∈ C, x ≠ o → laplacian G u x = 0 := by
    intro x hx hxo
    rw [hu, laplacian_sub, hharm x hx hxo, laplacian_equilibrium hG C ho hq hx hxo, sub_zero]
  have h1 := hbound u hu0 huo hharmu
  have h2 := hbound (fun v => -u v) (fun x hx => by rw [hu0 x hx, neg_zero])
    (by rw [huo, neg_zero])
    (fun x hx hxo => by rw [laplacian_neg, hharmu x hx hxo, neg_zero])
  funext x
  have hle1 : f x - equilibrium G C o x ≤ 0 := h1 x
  have hle2 : -(f x - equilibrium G C o x) ≤ 0 := h2 x
  linarith

/-! ### The escape rate -/

/-- **The escape rate is the reciprocal of the degree times the effective
resistance.**  One minus the mean of the equilibrium potential over the
neighbours of the source is the normal derivative there, and the boundary value
problem fixes it at `1 / (deg(o) · R_eff)`. -/
theorem escape_eq_inv (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C) (hq : q ∉ C) :
    1 - (∑ y ∈ G.neighborFinset o, equilibrium G C o y) / (G.degree o : ℝ)
      = 1 / ((G.degree o : ℝ) * effRes G C o) := by
  have hne : o ≠ q := fun h => hq (h ▸ ho)
  have hdeg : 0 < G.degree o := degree_pos_of_ne hG hne o
  have hdegR : (0 : ℝ) < (G.degree o : ℝ) := by exact_mod_cast hdeg
  have hR : 0 < effRes G C o := effRes_pos hG C ho hq
  have hlap := laplacian_equilibrium_source hG C ho hq
  rw [laplacian] at hlap
  have hself := equilibrium_self hG C ho hq
  have hsum : ∑ y ∈ G.neighborFinset o, (equilibrium G C o y - equilibrium G C o o)
      = (∑ y ∈ G.neighborFinset o, equilibrium G C o y) - (G.degree o : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hself, SimpleGraph.card_neighborFinset_eq_degree]
    simp
  rw [hsum] at hlap
  have h1 : ((∑ y ∈ G.neighborFinset o, equilibrium G C o y) - (G.degree o : ℝ))
      * effRes G C o = -1 := by
    rw [hlap]
    field_simp
  have hkey : ((G.degree o : ℝ) - ∑ y ∈ G.neighborFinset o, equilibrium G C o y)
      * effRes G C o = 1 := by
    have h2 : ((G.degree o : ℝ) - ∑ y ∈ G.neighborFinset o, equilibrium G C o y)
        * effRes G C o
        = -(((∑ y ∈ G.neighborFinset o, equilibrium G C o y) - (G.degree o : ℝ))
          * effRes G C o) := by ring
    rw [h2, h1]
    norm_num
  field_simp
  linarith [hkey]

end LatticeProb.Network
