/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bL414 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanLC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cLC
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutMain
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut

/-!
# GM Lemma 4.14′ (`lem-dc-set`): statement, and the choice of `z_y` in L4.15 Step 3

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.14 (`lem-dc-set`,
l. 2097–2102), proof l. 2457–2520; L4.15 Step 3, choice (∗) of `z_y` (l. 2158–2167).

* `dcSetC K y ε = 𝒞^ε_y` (l. 2099–2100; DV-B11 reading: Euclidean closures, Jordan `∂K`).
* `GML4_14'` — GM Lemma 4.14 with GM's own `Y^ε_y` (l. 2516–2518): an arc
  `Y = connectedComponentIn (∂B̃ ∖ K) y₀` of the boundary of a closed ball `B̃` of radius
  `≤ 8ε` (with `B̃ ∩ K ≠ ∅`, as for every ball of GM's family `𝓑`, l. 2481).

  **Correction of the statement of handoff/P2-M2I.md item 2.** That draft (and GM's text,
  "compact connected set `Y^ε_y ⊂ ℂ∖𝒦`") asks for a *compact* `Y ⊆ ℂ ∖ K`. This is false:
  for `K = closedBall 0 1`, `ε < 1/16`, `y = 1`, the point `1 + ε/6` lies in `𝒞^ε_y`
  (take `X = {|z−1| = ε/3, |z| > 1}`), and `𝒞^ε_y` accumulates at `∂K` near `1`; but if `Y`
  is compact, connected, disjoint from `K` and of diameter `≤ 16ε < diam K`, every bounded
  component `U` of `ℂ∖(Y∪K)` is a bounded component of `ℂ∖Y` not containing `K`, so
  `closure U ⊆ U ∪ Y` is a compact set disjoint from `K`, and cannot contain `𝒞^ε_y`. GM's
  own `Y^ε_y` is an *open* arc of `∂B̃ ∖ K` (l. 2516), not compact; the formal statement uses
  exactly that arc.
* `p412b_zy` — L4.15 Step 3 (∗) (l. 2162–2165): from the conclusion of `GML4_14'`, a point
  `z_y ∈ ∂K` such that every path in `ℂ∖K` from `𝒞^ε_y` to the complement of
  `cl U` (`U` the bounded component of `ℂ∖(Y∪K)`) meets `cl B_{2r}(z_y)`, `2r ≤ 16ε`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

/-- `𝒞^ε_y` (GM Lemma 4.14, l. 2099–2100) -/
def dcSetC (K : Set ℂ) (y : ℂ) (ε : ℝ) : Set ℂ :=
  {x | x ∉ K ∧ ∃ X ⊆ Kᶜ, IsConnected X ∧ Metric.ediam X ≤ ENNReal.ofReal ε ∧
    ∃ v, v ∉ X ∪ K ∧ Bornology.IsBounded (connectedComponentIn (X ∪ K)ᶜ v) ∧
      x ∈ closure (connectedComponentIn (X ∪ K)ᶜ v) ∧
      y ∈ closure (connectedComponentIn (X ∪ K)ᶜ v)}

/-- A closed ball meeting `K` and containing a point outside `K` contains a point of `∂K`. -/
theorem p412b_frontier_mem_closedBall {K : Set ℂ} (hK : IsClosed K) {c y₀ : ℂ} {r : ℝ}
    (hKB : (closedBall c r ∩ K).Nonempty) (hy₀ : y₀ ∈ closedBall c r) (hy₀K : y₀ ∉ K) :
    ∃ z ∈ frontier K, z ∈ closedBall c r := by
  obtain ⟨k, hkB, hkK⟩ := hKB
  by_cases hki : k ∈ interior K
  · have hJ : JoinedIn (closedBall c r) k y₀ :=
      ((convex_closedBall c r).isPathConnected ⟨k, hkB⟩).joinedIn k hkB y₀ hy₀
    have hy₀c : y₀ ∈ (closure K)ᶜ := by rw [hK.closure_eq]; exact hy₀K
    obtain ⟨_, ⟨τ, rfl⟩, hτ⟩ := disconnects_frontier K k y₀ hJ.somePath hki hy₀c
    exact ⟨_, hτ, hJ.somePath_mem τ⟩
  · exact ⟨k, ⟨hK.closure_eq.symm ▸ hkK, hki⟩, hkB⟩

/-- GM l. 2240 ("`⋃_y 𝒞_y ⊆ 𝓑^•_{s_{k+1}}`"): a closed bounded `F ⊇ Y ∪ K` with connected
complement (`F = 𝓑^•_{s_{k+1}}`) contains the closure of every bounded component of
`ℂ ∖ (Y ∪ K)`. -/
theorem p412b_closure_cc_subset {K Y F : Set ℂ} {v : ℂ} (hYF : Y ∪ K ⊆ F) (hF : IsClosed F)
    (hFb : Bornology.IsBounded F) (hFc : IsConnected Fᶜ)
    (hU : Bornology.IsBounded (connectedComponentIn (Y ∪ K)ᶜ v)) :
    closure (connectedComponentIn (Y ∪ K)ᶜ v) ⊆ F := by
  intro p hp
  by_contra hpF
  obtain ⟨q, hqF, hqU⟩ := mem_closure_iff.1 hp _ hF.isOpen_compl hpF
  have hsub : Fᶜ ⊆ connectedComponentIn (Y ∪ K)ᶜ v := by
    rw [connectedComponentIn_eq hqU]
    exact hFc.isPreconnected.subset_connectedComponentIn hqF (compl_subset_compl.2 hYF)
  refine (Metric.isBounded_iff.not.2 ?_) ((hU.subset hsub).union hFb)
  rw [compl_union_self]
  rintro ⟨C, hC⟩
  have h1 := hC (mem_univ (0 : ℂ)) (mem_univ ((C + 1 : ℝ) : ℂ))
  rw [dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 : 0 ≤ C := le_trans dist_nonneg (hC (mem_univ (0 : ℂ)) (mem_univ 0))
  rw [abs_of_pos (by linarith)] at h1
  linarith

end LQGMetric.GM
