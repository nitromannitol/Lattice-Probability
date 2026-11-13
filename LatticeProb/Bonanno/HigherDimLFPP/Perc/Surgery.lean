/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Surgery at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.ExtBoundary
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD

/-!
# The surgery lemma (HA5 D7(iii))

Let `O ⊆ ℤ^d` be the set of open sites, `D ∈ ℕ`, `R ∈ ℤ`, and `γ = (v₀, …, v_L)` an L-path with
`v₀ = u ∈ O` and `v_L = v ∈ O`. If every closed cluster `C` meeting `γ` has `ℓ^∞`-diameter `≤ D`,
lies in `[-R, R]^d` and has `u, v ∈ Ext R C`, then `u` and `v` are joined by an L-path of open sites
each within `ℓ^∞`-distance `D + 1` of `γ` (`surgeryLemma`). No hypothesis on `d` is needed.

Proof. HA5 proves this by induction on the length of `γ`, rerouting around the first closed cluster
met by `γ`. We run the same surgery as an extremal argument, which avoids the bookkeeping of the
induction. Let `A` be the set of sites joined to `u` by an L-path in the allowed set `S` (open
sites within distance `D + 1` of `γ`). Suppose `v ∉ A`. Let `k` be the last index with `v_k ∈ A`,
so `k < L`. Then `v_{k+1}` is closed (otherwise it would be in `A`); let `C` be its closed cluster,
and `j ≥ k + 1` the last index with `v_j ∈ C`, so `j < L`. Then `w := v_{j+1}` is open (a closed
L-neighbour of `C` would lie in `C`). Both `v_k` and `w` are in `Ext R C`: `v_k` is joined to
`u ∈ Ext R C` by an open path, and `w` to `v ∈ Ext R C` by `v_{j+1}, …, v_L`, which avoids `C`.
Both are `*`-adjacent to `C`, so by exterior-boundary connectivity (`extBoundaryConn`) they are
joined by an L-path in the exterior boundary of `C`. Its sites are open (a closed site
`*`-adjacent to `C` is in `C`, and `Ext R C ∩ C = ∅`) and within distance `1 + D` of
`v_{k+1} ∈ γ`, so they are in `S`; hence `w ∈ A`, contradicting the choice of `k`.
-/

set_option autoImplicit false

open Relation

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### Closed clusters -/

/-- The `*`-connected component of a closed site `c` among the closed sites. -/
def closedComp (O : Set (Zd d)) (c : Zd d) : Set (Zd d) :=
  {y | ReflTransGen (StepIn Oᶜ SAdj) c y}

lemma mem_closedComp_self (O : Set (Zd d)) (c : Zd d) : c ∈ closedComp O c :=
  ReflTransGen.refl

lemma reflTransGen_closedComp {O : Set (Zd d)} {c y : Zd d} (h : ReflTransGen (StepIn Oᶜ SAdj) c y) :
    ReflTransGen (StepIn (closedComp O c) SAdj) c y := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b e hcb hbe ih => exact ih.tail ⟨hcb, hcb.tail hbe, hbe.2.2⟩

/-- The component of a closed site is a closed cluster. -/
lemma isClosedCluster_closedComp {O : Set (Zd d)} {c : Zd d} (hc : c ∉ O) :
    IsClosedCluster O (closedComp O c) := by
  refine ⟨⟨c, mem_closedComp_self O c⟩, fun y hy => mem_of_reflTransGen_stepIn hy hc, ?_, ?_⟩
  · intro x hx y hy
    exact (reflTransGen_sAdj_symm (reflTransGen_closedComp hx)).trans (reflTransGen_closedComp hy)
  · intro x hx y hy hxy
    exact hx.tail ⟨mem_of_reflTransGen_stepIn hx hc, hy, hxy⟩

/-- A set contained in a box is finite. -/
lemma finite_of_withinInf {R : ℤ} {F : Set (Zd d)} (hF : ∀ x ∈ F, WithinInf R x 0) : F.Finite := by
  refine (Fintype.piFinset fun _ : Fin d => Finset.Icc (-R) R).finite_toSet.subset fun x hx => ?_
  simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ,
    Finset.coe_Icc, Set.mem_Icc, forall_const]
  intro i
  have := hF x hx i
  simp only [Pi.zero_apply, sub_zero, abs_le] at this
  exact this

/-! ### Lists as index functions -/

lemma getD_mem {γ : List (Zd d)} {i : ℕ} (hi : i < γ.length) : γ.getD i 0 ∈ γ := by
  rw [List.getD_eq_getElem γ 0 hi]
  exact List.getElem_mem hi

lemma getD_chain {R : Zd d → Zd d → Prop} {γ : List (Zd d)} (hγ : γ.IsChain R) {i : ℕ}
    (hi : i + 1 < γ.length) : R (γ.getD i 0) (γ.getD (i + 1) 0) := by
  rw [List.getD_eq_getElem γ 0 (by omega), List.getD_eq_getElem γ 0 hi]
  exact hγ.getElem i hi

lemma getD_zero_of_head? {γ : List (Zd d)} {u : Zd d} (h : γ.head? = some u) : γ.getD 0 0 = u := by
  cases γ with
  | nil => simp at h
  | cons a t => simpa using h

lemma getD_last_of_getLast? {γ : List (Zd d)} {v : Zd d} (h : γ.getLast? = some v) :
    γ.getD (γ.length - 1) 0 = v := by
  rw [List.getLast?_eq_getElem?] at h
  have hlen : γ.length - 1 < γ.length := by
    cases γ with
    | nil => simp at h
    | cons a t => simp
  rw [List.getElem?_eq_getElem hlen, Option.some.injEq] at h
  rw [List.getD_eq_getElem γ 0 hlen, h]

/-! ### The surgery lemma -/

/-- **D7(iii): the surgery lemma** (for every `d`). -/
theorem surgeryLemma (d : ℕ) : SurgeryLemma d := by
  intro O D R γ u v hchain hhead hlast hu hv hC
  classical
  set S : Set (Zd d) := {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x} with hSdef
  set A : Set (Zd d) := {y | ReflTransGen (StepIn S LAdj) u y} with hAdef
  have hlen : 0 < γ.length := by
    cases γ with
    | nil => simp at hhead
    | cons a t => simp
  set m := γ.length - 1 with hm
  set w : ℕ → Zd d := fun i => γ.getD i 0 with hwdef
  have hw0 : w 0 = u := getD_zero_of_head? hhead
  have hwm : w m = v := getD_last_of_getLast? hlast
  have hwmem : ∀ i, i ≤ m → w i ∈ γ := fun i hi => getD_mem (by omega)
  have hwadj : ∀ i, i < m → LAdj (w i) (w (i + 1)) := fun i hi => getD_chain hchain (by omega)
  have hD1 : (0 : ℤ) ≤ (D : ℤ) + 1 := by positivity
  have hwS : ∀ i, i ≤ m → w i ∈ O → w i ∈ S := fun i hi hO =>
    ⟨hO, w i, hwmem i hi, withinInf_refl hD1 _⟩
  have huS : u ∈ S := hw0 ▸ hwS 0 (Nat.zero_le _) (hw0 ▸ hu)
  have hAS : ∀ y ∈ A, y ∈ S := fun y hy => mem_of_reflTransGen_stepIn hy huS
  -- it suffices to show `w m ∈ A`
  suffices hP : w m ∈ A by rwa [hwm] at hP
  by_contra hPm
  -- the last index `k` with `w k ∈ A`
  set k := Nat.findGreatest (fun i => w i ∈ A) m with hkdef
  have hk : w k ∈ A := Nat.findGreatest_spec (P := fun i => w i ∈ A) (Nat.zero_le m)
    (by rw [hw0]; exact ReflTransGen.refl)
  have hkm : k < m := lt_of_le_of_ne (Nat.findGreatest_le m) fun h => hPm (h ▸ hk)
  have hgreat : ∀ i, k < i → i ≤ m → w i ∉ A := fun i h1 h2 =>
    Nat.findGreatest_is_greatest (P := fun i => w i ∈ A) h1 h2
  -- `w (k+1)` is closed
  have hcO : w (k + 1) ∉ O := by
    intro hO
    exact hgreat (k + 1) (by omega) (by omega)
      (hk.tail ⟨hAS _ hk, hwS (k + 1) (by omega) hO, hwadj k hkm⟩)
  -- its cluster
  set C := closedComp O (w (k + 1)) with hCdef
  have hCcl : IsClosedCluster O C := isClosedCluster_closedComp hcO
  obtain ⟨hdiam, hbox, huE, hvE⟩ :=
    hC C hCcl ⟨w (k + 1), hwmem (k + 1) (by omega), mem_closedComp_self O _⟩
  -- the last index `j` with `w j ∈ C`
  set j := Nat.findGreatest (fun i => w i ∈ C) m with hjdef
  have hcC : w (k + 1) ∈ C := mem_closedComp_self O _
  have hj : w j ∈ C := Nat.findGreatest_spec (P := fun i => w i ∈ C) (show k + 1 ≤ m by omega) hcC
  have hkj : k + 1 ≤ j := Nat.le_findGreatest (P := fun i => w i ∈ C) (show k + 1 ≤ m by omega) hcC
  have hvC : v ∉ C := fun h => hCcl.2.1 h hv
  have hjm : j < m := lt_of_le_of_ne (Nat.findGreatest_le m) fun h => hvC (hwm ▸ h ▸ hj)
  have hjgreat : ∀ i, j < i → i ≤ m → w i ∉ C := fun i h1 h2 =>
    Nat.findGreatest_is_greatest (P := fun i => w i ∈ C) h1 h2
  -- `w (j+1)` is open
  have heC : w (j + 1) ∉ C := hjgreat (j + 1) (by omega) (by omega)
  have heO : w (j + 1) ∈ O := by
    by_contra hO
    exact heC (hCcl.2.2.2 _ hj _ hO (hwadj j hjm).sAdj)
  -- `w (j+1) ∈ Ext R C`: follow `γ` to its end
  have hsuffix : ∀ t i, i + t = m → j + 1 ≤ i → w i ∈ Ext R C := by
    intro t
    induction t with
    | zero =>
      intro i hi _
      rw [show i = m by omega, hwm]
      exact hvE
    | succ t ih =>
      intro i hi hji
      exact mem_ext_of_lAdj (hjgreat i (by omega) (by omega))
        (hjgreat (i + 1) (by omega) (by omega)) (hwadj i (by omega)) (ih (i + 1) (by omega) (by omega))
  have heE : w (j + 1) ∈ Ext R C := hsuffix (m - (j + 1)) (j + 1) (by omega) le_rfl
  -- `w k ∈ Ext R C`: reverse the open path from `u`
  have hSC : S ⊆ Cᶜ := fun y hy hyC => hCcl.2.1 hyC hy.1
  have hkE : w k ∈ Ext R C :=
    (reflTransGen_stepIn_mono hSC (reflTransGen_lAdj_symm hk)).trans huE
  -- exterior-boundary connectivity of `C`
  have hCfin : C.Finite := finite_of_withinInf hbox
  have hBconn := extBoundaryConn d R C hCfin hCcl.1 hbox hCcl.2.2.1
  have hkB : w k ∈ {y | y ∈ Ext R C ∧ ∃ f ∈ C, SAdj y f} :=
    ⟨hkE, w (k + 1), hcC, (hwadj k hkm).sAdj⟩
  have heB : w (j + 1) ∈ {y | y ∈ Ext R C ∧ ∃ f ∈ C, SAdj y f} :=
    ⟨heE, w j, hj, (hwadj j hjm).symm.sAdj⟩
  have hBS : {y | y ∈ Ext R C ∧ ∃ f ∈ C, SAdj y f} ⊆ S := by
    intro y hy
    obtain ⟨hyE, f, hfC, hyf⟩ := hy
    refine ⟨?_, w (k + 1), hwmem (k + 1) (by omega), ?_⟩
    · by_contra hyO
      exact notMem_of_mem_extBdry hbox ⟨hyE, f, hfC, hyf⟩
        (hCcl.2.2.2 f hfC y hyO hyf.symm)
    · have h1 : WithinInf (1 + (D : ℤ)) y (w (k + 1)) := hyf.withinInf.trans (hdiam f hfC _ hcC)
      rwa [add_comm] at h1
  have heA : w (j + 1) ∈ A :=
    hk.trans (reflTransGen_stepIn_mono hBS (hBconn _ hkB _ heB))
  exact hgreat (j + 1) (by omega) (by omega) heA

end Perc

end HigherDimLFPP
