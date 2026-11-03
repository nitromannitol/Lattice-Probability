/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.Disconnect at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Topology.Path
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import LatticeProb.Bonanno.LQGMetric.Statement.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Disconnecting sets and the distance around an annulus (DFGPS Definition 3.7)

DFGPS (Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380), Definition 3.7 (`def-around-annulus`, tex lines 1655–1657):
"for a set `A ⊂ ℂ` with the topology of an annulus, the `D_h`-distance around `A` is the infimum
of the `D_h`-lengths of the paths in `A` which disconnect the inner and outer boundaries of `A`."

We formalize "`X` disconnects `E` from `F`" in the form the proofs use: every path in `ℂ` from
a point of `E` to a point of `F` meets `X` (`Disconnects`). The inner and outer boundaries are
passed explicitly (for `𝔸_{r,R}(z)`: `sphere z r` and `sphere z R`).

Basic facts used throughout DFGPS/GM:
* `Disconnects.symm`, `Disconnects.mono`;
* a circle `∂B_ρ(z)`, `r ≤ ρ ≤ R`, disconnects `closedBall z r` from `(ball z R)ᶜ`
  (`disconnects_sphere`; intermediate value theorem);
* a set disconnecting `∂B_r(z)` from `∂B_R(z)` disconnects `closedBall z r` from `(ball z R)ᶜ`
  (`Disconnects.closedBall_compl_ball`: every path from inside to outside has a sub-path from the
  inner to the outer circle, again by the intermediate value theorem).
These two are own elementary arguments (the papers use them without comment).
-/

namespace LQGMetric

open Set Metric

/-- `X` disconnects `E` from `F` (in `ℂ`): every path from a point of `E` to a point of `F`
meets `X`. -/
def Disconnects (X E F : Set ℂ) : Prop :=
  ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F → (range γ ∩ X).Nonempty

/-- **DFGPS Definition 3.7** (tex 1655–1657): the `D`-distance around a set `A` with inner and
outer boundaries `E`, `F`: the infimum of the `D`-lengths `len(P; D)` of the (Euclidean
continuous) paths `P : [a, b] → A` whose range disconnects `E` from `F`. -/
noncomputable def ContMetric.aroundDist (D : ContMetric) (A E F : Set ℂ) : ENNReal :=
  ⨅ (a : ℝ) (b : ℝ) (P : ℝ → ℂ) (_ : a ≤ b) (_ : ContinuousOn P (Icc a b))
    (_ : P '' Icc a b ⊆ A) (_ : Disconnects (P '' Icc a b) E F), D.len P a b

namespace Disconnects

theorem symm {X E F : Set ℂ} (h : Disconnects X E F) : Disconnects X F E := by
  intro x y γ hx hy
  obtain ⟨z, hz, hzX⟩ := h y x γ.symm hy hx
  exact ⟨z, by rwa [Path.symm_range] at hz, hzX⟩

theorem mono {X X' E E' F F' : Set ℂ} (h : Disconnects X E F) (hX : X ⊆ X') (hE : E' ⊆ E)
    (hF : F' ⊆ F) : Disconnects X' E' F' := by
  intro x y γ hx hy
  obtain ⟨z, hz, hzX⟩ := h x y γ (hE hx) (hF hy)
  exact ⟨z, hz, hX hzX⟩

/-- A set disconnecting the circles `∂B_r(z)` and `∂B_R(z)` (`r ≤ R`) disconnects the closed
inner disc from the complement of the open outer disc. -/
theorem closedBall_compl_ball {X : Set ℂ} {z : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (h : Disconnects X (sphere z r) (sphere z R)) :
    Disconnects X (closedBall z r) (ball z R)ᶜ := by
  intro x y γ hx hy
  set f : ℝ → ℝ := fun t => dist (γ.extend t) z with hf
  have hfc : Continuous f := γ.continuous_extend.dist continuous_const
  have hf0 : f 0 ≤ r := by simpa [hf] using hx
  have hf1 : R ≤ f 1 := by simpa [hf, not_lt] using hy
  -- first a time `t₁` at which `γ` is on the outer circle
  obtain ⟨t₁, ht₁, hft₁⟩ : ∃ t₁ ∈ Icc (0 : ℝ) 1, f t₁ = R :=
    intermediate_value_Icc zero_le_one hfc.continuousOn ⟨hf0.trans hrR, hf1⟩
  -- then an earlier time `t₀` at which `γ` is on the inner circle
  obtain ⟨t₀, ht₀, hft₀⟩ : ∃ t₀ ∈ Icc (0 : ℝ) t₁, f t₀ = r :=
    intermediate_value_Icc ht₁.1 hfc.continuousOn ⟨hf0, hft₁ ▸ hrR⟩
  obtain ⟨w, hw, hwX⟩ := h _ _ (γ.truncateOfLE ht₀.2) (mem_sphere.2 hft₀)
    (mem_sphere.2 hft₁)
  refine ⟨w, ?_, hwX⟩
  have : range (γ.truncateOfLE ht₀.2) ⊆ range γ := by
    intro u ⟨s, hs⟩
    exact γ.truncate_range ⟨s, by rw [← hs]; rfl⟩
  exact this hw

end Disconnects

end LQGMetric
