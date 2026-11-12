/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Low
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YSq
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XCell

/-!
# D97, packet P-3 (deterministic part): balls covered by 4 cells give `D'_{δ'} ≤ 4 D_δ`

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1162–1168): "Provided with
(eq-Euclidean-Ball-covering) [every Euclidean ball with LQG-measure `≤ δ²` can be covered by 4
cells in `𝒱_{δ'}`], it is clear that with high probability we have that
`D'_{γ,δ'}(u,v) ≤ 4 D_{γ,δ}(u,v)` for all `u, v ∈ 𝕍`."

Here, for the internal measure `dzzWall dzzV ν` of D97 (balls inside `𝕍`):

* `BallInCells m δ' B`: there are at most 4 cells of `𝒱_{δ'}` such that every fine enough dyadic
  square whose closure meets `B` lies in one of them (this is how the 4 closed dyadic boxes of
  DZZ l. 1174 cover `B`);
* **`approxDist_le_four_mul_lgd`**: if the cells partition `𝕍`, have bounded level, and every
  rational ball inside `𝕍` of `ν`-mass `≤ δ²` satisfies `BallInCells`, then
  `D'_{δ'}(u,v) ≤ 4 D^𝕍_δ(ν)(u,v)` for `u, v ∈ 𝕍` (the path of balls is turned into a 4-path of
  grid squares meeting it, `sq_reach_of_connected`, counted by `approxDist_le_card_of_path`).

Own elementary glue (DZZ: "it is clear").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- `B` is covered by at most 4 cells of `𝒱_{δ'}`: the fine squares meeting `B` have their
cell in a fixed set of at most 4 cells. -/
def BallInCells (m : DyBox → ℝ) (δ' : ℝ) (B : Set ℂ) : Prop :=
  ∃ S : Finset DyBox, S.card ≤ 4 ∧ ∃ N₁ : ℕ, ∀ t : DyBox, N₁ ≤ t.n →
    (t.closedBox ∩ B).Nonempty → ∀ T, IsSqCell m δ' t T → T ∈ S

/-- The count along one path of `N` balls. -/
theorem approxDist_le_four_mul_of_path {m : DyBox → ℝ} {δ' δ : ℝ} {ν : Measure ℂ}
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hball : ∀ (c : ℚ × ℚ) (ρ : ℝ), Metric.ball (ratPt c) ρ ⊆ dzzV →
      ν (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        BallInCells m δ' (Metric.ball (ratPt c) ρ))
    {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) (N : ℕ) (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ)
    (P : Path u v)
    (h1 : ∀ i, 0 < ρ i ∧ dzzWall dzzV ν (Metric.ball (ratPt (c i)) (ρ i)) ≤
      ENNReal.ofReal (δ ^ 2))
    (h2 : ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i)) :
    approxDist m δ' u v ≤ 4 * (N : ℕ∞) := by
  classical
  have hsub : ∀ i, Metric.ball (ratPt (c i)) (ρ i) ⊆ dzzV := by
    intro i
    by_contra h
    have := (h1 i).2
    rw [dzzWall_ball_of_not_subset isClosed_dzzV ν h] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
  have hcov : ∀ i, BallInCells m δ' (Metric.ball (ratPt (c i)) (ρ i)) := fun i =>
    hball _ _ (hsub i) (by rw [← dzzWall_ball_of_subset ν (hsub i)]; exact (h1 i).2)
  choose S hS4 N₁ hN₁ using hcov
  set Sall : Finset DyBox := Finset.univ.biUnion S with hSall
  have hcard : Sall.card ≤ 4 * N := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ i, (S i).card ≤ ∑ _i : Fin N, 4 := Finset.sum_le_sum fun i _ => hS4 i
      _ = 4 * N := by simp [mul_comm]
  set L : ℕ := max N₀ (Finset.univ.sup N₁) with hL
  set A : Set ℂ := range P with hA
  have hAV : A ⊆ dzzV := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := h2 t
    exact hsub i hi
  have huA : u ∈ A := ⟨0, P.source⟩
  have hvA : v ∈ A := ⟨1, P.target⟩
  have hreach := sq_reach_of_connected (isConnected_range P.continuous).isPreconnected hAV L
    huA hvA
  obtain ⟨M, p, hp0, hpM, hstep⟩ := rtg_to_fun hreach
  have hpn : ∀ t ≤ M, (p t).n = L := by
    intro t
    induction t with
    | zero => intro _; rw [hp0]; rfl
    | succ t ih =>
      intro ht
      rw [← ih (by omega)]
      exact ((hstep t (by omega)).1.1).symm
  have hmeet : ∀ t ≤ M, ((p t).closedBox ∩ A).Nonempty := by
    intro t ht
    rcases t with _ | t
    · rw [hp0]; exact ⟨u, mem_closedBox_boxAt hu, huA⟩
    · exact (hstep t (by omega)).2
  have hcell : ∀ t ≤ M, ∀ T, IsSqCell m δ' (p t) T → T ∈ Sall := by
    intro t ht T hT
    obtain ⟨z, hz, s, rfl⟩ := hmeet t ht
    obtain ⟨i, hi⟩ := h2 s
    have hNi : N₁ i ≤ (p t).n := by
      rw [hpn t ht]
      exact (Finset.le_sup (f := N₁) (Finset.mem_univ i)).trans (le_max_right _ _)
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hN₁ i (p t) hNi ⟨P s, hz, hi⟩ T hT⟩
  have hu0 : (p 0).Mem u := by rw [hp0]; exact ⟨hu, rfl⟩
  have hvM : (p M).Mem v := by rw [hpM]; exact ⟨hv, rfl⟩
  have key := approxDist_le_card_of_path hpart hN₀ p M
    (fun t ht => by rw [hpn t ht]; exact le_max_left _ _)
    (fun t ht => Or.inr (hstep t ht).1) Sall hcell hu0 hvM
  refine key.trans ?_
  exact_mod_cast hcard

/-- **DZZ l. 1166–1167**: (eq-Euclidean-Ball-covering) gives `D'_{δ'}(u, v) ≤ 4 D_δ(u, v)`. -/
theorem approxDist_le_four_mul_lgd {m : DyBox → ℝ} {δ' δ : ℝ} {ν : Measure ℂ}
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hball : ∀ (c : ℚ × ℚ) (ρ : ℝ), Metric.ball (ratPt c) ρ ⊆ dzzV →
      ν (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        BallInCells m δ' (Metric.ball (ratPt c) ρ))
    {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) :
    approxDist m δ' u v ≤ 4 * lgdDZZ (dzzWall dzzV ν) δ u v := by
  classical
  set Q : ℕ → Prop := fun N => ∃ (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ) (P : Path u v),
    (∀ i, 0 < ρ i ∧ dzzWall dzzV ν (Metric.ball (ratPt (c i)) (ρ i)) ≤
      ENNReal.ofReal (δ ^ 2)) ∧ ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i) with hQ
  by_cases hne : ∃ N, Q N
  · have hmin : ((Nat.find hne : ℕ) : ℕ∞) ≤ lgdDZZ (dzzWall dzzV ν) δ u v := by
      unfold lgdDZZ
      exact le_iInf₂ fun N hN => by exact_mod_cast Nat.find_min' hne hN
    obtain ⟨c, ρ, P, h1, h2⟩ := Nat.find_spec hne
    exact (approxDist_le_four_mul_of_path hpart hN₀ hball hu hv _ c ρ P h1 h2).trans
      (by gcongr)
  · have htop : lgdDZZ (dzzWall dzzV ν) δ u v = ⊤ := by
      unfold lgdDZZ
      exact iInf₂_eq_top.2 fun N hN => absurd ⟨N, hN⟩ hne
    rw [htop]
    exact le_top.trans (by simp)

end DZZ
end LQGMetric
