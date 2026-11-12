/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.Shortcut at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Paths crossing disconnecting sets: GM (3.16) and GM §4.6 (F.TOPO II)

* `exists_mem_of_disconnects`: a path `P : [a, b] → ℂ` from `E` to `F` meets every set
  disconnecting `E` from `F` (immediate from `Disconnects`, after reparametrizing `[a, b]` by
  `[0, 1]`).
* **GM (3.16)** (Gwynne–Miller, *Existence and uniqueness of the LQG metric*, arXiv:1905.00383,
  `uniqueness-final.tex` lines 1467–1477): `shortcut_le` and `shortcut_le_frac`. A geodesic
  crossing an annulus once before time `t_{j-1}` and once during `[s_j, t_j]` hits a
  disconnecting path `L` at times `u₁ ≤ t_{j-1}` and `u₂ ≥ s_j`; since it is a geodesic,
  `s_j - t_{j-1} ≤ u₂ - u₁ = D(P(u₁), P(u₂)) ≤ len(L)`. We follow GM's argument; the length of
  `L` enters only through `D(x, y) ≤ ℓ` for `x, y ∈ L` (use `edist_le_curveLength`).
* **GM §4.6** (`uniqueness-final.tex` lines 2232–2236): `disconnects_of_frontier_thickening`. A set
  covering the boundary `∂B_δ(K)` of the open `δ`-neighbourhood of `K` disconnects `K` from every
  point outside the closed `δ`-neighbourhood. (GM: "if `ε` is sufficiently small then the union of
  these Euclidean balls disconnects `∂𝓑^•_{t_k}` from `𝕨`"; own elementary argument: a connected
  path range meeting the interior and the exterior of a set meets its frontier.)
-/

namespace LQGMetric

open Set Metric

/-- The path `τ ↦ P(a + (b - a) τ)` on `[0, 1]`, for `P` continuous on `[a, b]`. -/
noncomputable def pathOfIcc (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) : Path (P a) (P b) where
  toFun τ := P (a + (b - a) * (τ : ℝ))
  continuous_toFun := by
    refine hP.comp_continuous (by fun_prop) fun τ => ?_
    have h0 := τ.2.1; have h1 := τ.2.2
    constructor <;> nlinarith
  source' := by simp
  target' := by simp

theorem range_pathOfIcc_subset (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) : range (pathOfIcc P hab hP) ⊆ P '' Icc a b := by
  rintro _ ⟨τ, rfl⟩
  have h0 := τ.2.1; have h1 := τ.2.2
  exact ⟨_, ⟨by nlinarith, by nlinarith⟩, rfl⟩

/-- A path from the interior of a set to the exterior of its closure meets its frontier. -/
theorem disconnects_frontier (S : Set ℂ) :
    Disconnects (frontier S) (interior S) (closure S)ᶜ := by
  intro x y γ hx hy
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : range γ ⊆ interior S ∪ (closure S)ᶜ := by
    rintro _ ⟨τ, rfl⟩
    by_cases h : γ τ ∈ closure S
    · left
      by_contra h'
      exact (eq_empty_iff_forall_notMem.1 hne) (γ τ) ⟨mem_range_self τ, ⟨h, h'⟩⟩
    · exact Or.inr h
  rcases (isConnected_range γ.continuous).isPreconnected.subset_or_subset isOpen_interior
      isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hsub with h | h
  · exact interior_subset_closure (h ⟨1, γ.target⟩) |> (show y ∉ closure S from hy)
  · exact h ⟨0, γ.source⟩ (interior_subset_closure hx)

end LQGMetric
