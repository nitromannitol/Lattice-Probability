/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412dL414 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412dDag
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412dUniq
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bL414

/-!
# GM Lemma 4.14′ (`GML4_14'`), proved (DEC-86 (1), D88)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.14 (`lem-dc-set`,
l. 2097–2102), proof l. 2457–2520, as repaired in DEC-86 (decisions/DEC-86.md, item (1)).

Proof (DEC-86): fix a radius `ρ ∈ [3ε/2, 2ε]` with `y ∉ ∂B(c, ρ)` for the finitely many centres
`c` of an `ε/4`-net of the `3ε`-neighbourhood of `K` (GM use the grid `(ε/4)ℤ²`, l. 2477; any
finite net works). For a witness `(X, V)` of `x ∈ 𝒞^ε_y`, `X` lies in some `int B(c, ρ)`
(a witness far from `K` is impossible: `p412d_far`), and (†) (`p412d_dagger`) gives an arc
`α_B ⊆ cl N(B)` with `V ⊆ U(α_B)`, unique by `p412d_unique` (Step 1). The bounded sides
`U(α_B)` form a finite family; closures of maximal arcs meet (`p412d_max_meet`, Step 2), so all
maximal arcs lie in `B(c₁, 6ε)`; (†) for the ball `B̃ = B(c₁, ρ̃)`, `ρ̃ ∈ {7ε, 8ε}`,
`y ∉ ∂B̃`, puts every maximal `U(α*)` in `U(β)` for one arc `β` of `∂B̃ ∖ K` (`p412d_unique`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

/-- `U(α)` is the component of `ℂ ∖ (α ∪ K)` of each of its points. -/
theorem p412d_dgB_eq_cc {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r) (hy₀ : y₀ ∈ sphere c r)
    (hy₀K : y₀ ∉ K) {x : ℂ} (hx : x ∈ dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K)) :
    dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K) =
      connectedComponentIn (connectedComponentIn (sphere c r \ K) y₀ ∪ K)ᶜ x := by
  obtain ⟨u, w, hBu, -⟩ := p412d_arc hK hKc hKo hr hy₀ hy₀K
  rw [hBu] at hx ⊢
  exact connectedComponentIn_eq hx

/-- A witness `X` of `𝒞_y` inside a disc `B` with `cl B ∩ K = ∅` is impossible: `U(∂B) = int B`. -/
theorem p412d_far {K X : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hXK : X ⊆ Kᶜ) {c v y : ℂ} {r : ℝ} (hr : 0 < r)
    (hXB : X ⊆ ball c r) (hBK : ∀ k ∈ K, r < dist k c) (hv : v ∉ X ∪ K)
    (hb : IsBounded (connectedComponentIn (X ∪ K)ᶜ v))
    (hyV : y ∈ closure (connectedComponentIn (X ∪ K)ᶜ v)) (hyK : y ∈ K) : False := by
  obtain ⟨y₀, hy₀, hy₀K, -, hVB, hcol⟩ := p412d_dagger hK hKc hKo hXK hr hXB hv hb
  set α := connectedComponentIn (sphere c r \ K) y₀
  have hSK : sphere c r ⊆ sphere c r \ K := fun z hz =>
    ⟨hz, fun h => by linarith [hBK z h, mem_sphere.1 hz]⟩
  have hSα : sphere c r ⊆ α :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c r).subset_connectedComponentIn
      hy₀ hSK
  obtain ⟨u, w, hBu, -, -, -⟩ := p412d_arc hK hKc hKo hr hy₀ hy₀K
  have hBpre : IsPreconnected (dgB (α ∪ K)) := hBu ▸ isPreconnected_connectedComponentIn
  have hy₀α : y₀ ∈ α := mem_connectedComponentIn ⟨hy₀, hy₀K⟩
  have hz₁ : colMap K c r (-1) (y₀, 1 / 2) ∈ col K c r α (-1) :=
    ⟨(y₀, 1 / 2), ⟨hy₀α, by norm_num, by norm_num⟩, rfl⟩
  have hz₁b : colMap K c r (-1) (y₀, 1 / 2) ∈ ball c r := by
    obtain ⟨-, s, hs0, -, hs⟩ := col_prop hK.isClosed hKc.nonempty hr (by norm_num)
      (connectedComponentIn_subset _ _) hz₁
    rw [mem_ball, dist_eq_norm, hs]; nlinarith
  have hBball : dgB (α ∪ K) ⊆ ball c r := by
    refine hBpre.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) (fun z hz => ?_)
      ⟨_, hcol hz₁, hz₁b⟩
    have hzS : dist z c ≠ r := fun h => hz.1 (Or.inl (hSα (mem_sphere.2 h)))
    rcases lt_or_gt_of_ne hzS with h | h
    · exact Or.inl h
    · exact Or.inr fun h' => absurd (mem_closedBall.1 h') (not_le.2 h)
  have hy := closure_ball_subset_closedBall (closure_mono (hVB.trans hBball) hyV)
  linarith [hBK y hyK, mem_closedBall.1 hy]

end LQGMetric.GM
