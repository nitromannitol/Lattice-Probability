/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412dArc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cLC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanLC
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutMain

/-!
# GM L4.14′, repaired proof (DEC-86 (1)): the two sides of a circle arc, and (†)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.14
(`lem-dc-set`, l. 2457–2520), as repaired in DEC-86 (decisions/DEC-86.md, item (1)).

* `dgB F`, `dgW F` — the union of the bounded resp. unbounded components of `ℂ ∖ F`. For an arc
  `α` of `∂B ∖ K`, `dgB (α ∪ K) = U(α)`, `dgW (α ∪ K) = W(α)` (`crosscut_circle`, GM l. 2479).
  `dgW (closedBall c r ∪ K) = N(B)`.
* `p412d_dagger` — DEC-86 (†) (replaces GM l. 2485 / 2490–2501): for `X ⊆ ℂ∖K` preconnected,
  `X ⊆ int B`, and a bounded component `V` of `ℂ ∖ (X ∪ K)`, there is an arc `α ⊆ cl N(B)` of
  `∂B ∖ K` with `V ⊆ U(α)` (and the inner collar of `α` in `U(α)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

/-- Union of the bounded components of `ℂ ∖ F`. -/
def dgB (F : Set ℂ) : Set ℂ := {x | x ∉ F ∧ IsBounded (connectedComponentIn Fᶜ x)}

/-- Union of the unbounded components of `ℂ ∖ F`. -/
def dgW (F : Set ℂ) : Set ℂ := {x | x ∉ F ∧ ¬ IsBounded (connectedComponentIn Fᶜ x)}

theorem p412d_dgB_dgW_disj (F : Set ℂ) : Disjoint (dgB F) (dgW F) :=
  disjoint_left.2 fun _ h1 h2 => h2.2 h1.2

theorem p412d_mem_dgB_or (F : Set ℂ) {x : ℂ} (hx : x ∉ F) : x ∈ dgB F ∨ x ∈ dgW F := by
  by_cases h : IsBounded (connectedComponentIn Fᶜ x)
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

theorem p412d_dgB_compl (F : Set ℂ) : dgB F ⊆ Fᶜ := fun _ h => h.1

theorem p412d_dgW_compl (F : Set ℂ) : dgW F ⊆ Fᶜ := fun _ h => h.1

/-- A preconnected subset of `ℂ ∖ F` meeting `dgB F` lies in it. -/
theorem p412d_sub_dgB {F S : Set ℂ} (hS : IsPreconnected S) (hSF : S ⊆ Fᶜ) {x : ℂ}
    (hx : x ∈ S) (hxB : x ∈ dgB F) : S ⊆ dgB F := fun s hs => by
  refine ⟨hSF hs, ?_⟩
  rw [connectedComponentIn_eq (hS.subset_connectedComponentIn hs hSF hx)]
  exact hxB.2

/-- A preconnected subset of `ℂ ∖ F` meeting `dgW F` lies in it. -/
theorem p412d_sub_dgW {F S : Set ℂ} (hS : IsPreconnected S) (hSF : S ⊆ Fᶜ) {x : ℂ}
    (hx : x ∈ S) (hxW : x ∈ dgW F) : S ⊆ dgW F := fun s hs => by
  refine ⟨hSF hs, ?_⟩
  rw [connectedComponentIn_eq (hS.subset_connectedComponentIn hs hSF hx)]
  exact hxW.2

/-- An unbounded preconnected subset of `ℂ ∖ F` lies in `dgW F`. -/
theorem p412d_sub_dgW_of_unbdd {F S : Set ℂ} (hS : IsPreconnected S) (hSF : S ⊆ Fᶜ)
    (hSu : ¬ IsBounded S) : S ⊆ dgW F := fun _ hs =>
  ⟨hSF hs, fun hb => hSu (hb.subset (hS.subset_connectedComponentIn hs hSF))⟩

theorem p412d_isOpen_dgB {F : Set ℂ} (hF : IsClosed F) : IsOpen (dgB F) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, ?_, hF.isOpen_compl.connectedComponentIn,
    mem_connectedComponentIn hx.1⟩
  exact p412d_sub_dgB isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (mem_connectedComponentIn hx.1) hx

theorem p412d_isOpen_dgW {F : Set ℂ} (hF : IsClosed F) : IsOpen (dgW F) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, ?_, hF.isOpen_compl.connectedComponentIn,
    mem_connectedComponentIn hx.1⟩
  exact p412d_sub_dgW isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (mem_connectedComponentIn hx.1) hx

/-- The closure of a component of `ℂ ∖ F` adds only points of `F`. -/
theorem p412d_closure_cc {F : Set ℂ} (hF : IsClosed F) (x : ℂ) :
    closure (connectedComponentIn Fᶜ x) ⊆ connectedComponentIn Fᶜ x ∪ F := by
  rw [closure_eq_self_union_frontier]
  exact union_subset_union_right _ (jl_frontier_cc_subset hF x)

/-- For bounded `F`, `dgW F` is the component of `ℂ ∖ F` of any far point. -/
theorem p412d_dgW_eq {F : Set ℂ} {R : ℝ} (hR : F ⊆ ball 0 R) {a : ℂ} (ha : R < ‖a‖) :
    dgW F = connectedComponentIn Fᶜ a := by
  have haF : a ∈ Fᶜ := QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR ha
  have hfar : {z : ℂ | R < ‖z‖} ⊆ connectedComponentIn Fᶜ a :=
    QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R) (jb_not_isBounded_lt_norm R)
      (disjoint_left.2 fun _ h1 h2 => QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR h1 h2)
      ha
  ext x
  constructor
  · rintro ⟨hxF, hxb⟩
    exact QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      isPreconnected_connectedComponentIn hxb
      (disjoint_left.2 fun _ h1 h2 => connectedComponentIn_subset _ _ h1 h2) ha
      (mem_connectedComponentIn hxF)
  · intro hx
    refine ⟨connectedComponentIn_subset _ _ hx, fun hb => ?_⟩
    rw [← connectedComponentIn_eq hx] at hb
    exact jb_not_isBounded_lt_norm R (hb.subset hfar)

/-- For bounded `F`, `dgW F` is preconnected and unbounded. -/
theorem p412d_dgW_props {F : Set ℂ} (hF : IsBounded F) :
    IsPreconnected (dgW F) ∧ ¬ IsBounded (dgW F) := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hF
  set a : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have ha : R < ‖a‖ := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (by linarith [le_abs_self R]) (le_abs_self _)
  rw [p412d_dgW_eq hR ha]
  refine ⟨isPreconnected_connectedComponentIn, fun hb => jb_not_isBounded_lt_norm R
    (hb.subset (QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R) (jb_not_isBounded_lt_norm R)
      (disjoint_left.2 fun _ h1 h2 => QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR h1 h2)
      ha))⟩

/-- **The two sides of an arc** (`crosscut_circle`, GM l. 2478–2479). -/
theorem p412d_arc {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKo : IsPreconnected Kᶜ)
    {c y₀ : ℂ} {r : ℝ} (hr : 0 < r) (hy₀ : y₀ ∈ sphere c r) (hy₀K : y₀ ∉ K) :
    ∃ u w : ℂ,
      dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K) =
        connectedComponentIn (connectedComponentIn (sphere c r \ K) y₀ ∪ K)ᶜ u ∧
      dgW (connectedComponentIn (sphere c r \ K) y₀ ∪ K) =
        connectedComponentIn (connectedComponentIn (sphere c r \ K) y₀ ∪ K)ᶜ w ∧
      connectedComponentIn (sphere c r \ K) y₀ ⊆
        closure (dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K)) ∧
      connectedComponentIn (sphere c r \ K) y₀ ⊆
        closure (dgW (connectedComponentIn (sphere c r \ K) y₀ ∪ K)) := by
  obtain ⟨u, w, hu, hw, hub, hwb, hdich, hYu, hYw⟩ := crosscut_circle hK hKc hKo hr hy₀ hy₀K rfl
  set F := connectedComponentIn (sphere c r \ K) y₀ ∪ K
  have hB : dgB F = connectedComponentIn Fᶜ u := by
    ext x
    constructor
    · rintro ⟨hxF, hxb⟩
      rcases hdich x hxF with h | h
      · exact h
      · rw [connectedComponentIn_eq h] at hwb; exact absurd hxb hwb
    · intro hx
      exact ⟨connectedComponentIn_subset _ _ hx, by rw [← connectedComponentIn_eq hx]; exact hub⟩
  have hW : dgW F = connectedComponentIn Fᶜ w := by
    ext x
    constructor
    · rintro ⟨hxF, hxb⟩
      rcases hdich x hxF with h | h
      · rw [connectedComponentIn_eq h] at hub; exact absurd hub hxb
      · exact h
    · intro hx
      exact ⟨connectedComponentIn_subset _ _ hx, by rw [← connectedComponentIn_eq hx]; exact hwb⟩
  exact ⟨u, w, hB, hW, hB ▸ hYu, hW ▸ hYw⟩

end LQGMetric.GM
