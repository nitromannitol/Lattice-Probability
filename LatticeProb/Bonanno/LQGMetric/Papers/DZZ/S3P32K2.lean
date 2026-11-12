/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32K2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K1

/-!
# Walled P3.2, K2: the lower-half input `L32BallCoverOn` at `dzzWall K μIn` (P2-DZZ317K)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1160–1168 with Remark 5.2 (l. 2281–2284), decision
D117 §3: on (eq-Euclidean-Ball-covering) every ball of mass `≤ δ²` inside `𝕍` is covered by 4
cells of `𝒱_{δ'}`. A `D^K_δ`-chain consists of balls inside `K ∩ 𝕍`; the cells covering them meet
`K`, so the cell chain built in `approxDist_le_four_mul_of_path` (S3P32W3) lies in the graph of
the cells meeting `K`:

* **`approxDistOn_le_four_mul_lgd`**: `D'_{S,δ'}(u,v) ≤ 4 D^K_δ(u,v)` for `u, v ∈ 𝕍` on the event,
  for any cell family `S` containing the `δ'`-cells that meet a ball inside `K` (deterministic;
  the proof of S3P32W3 with the cell set filtered to `S`);
* `L32BallCoverOn P γ W S μ`: the walled `L32BallCover` (S3P32Low) for a cell family `S`;
* **`l32BallCoverIn_dzzMuIn`**:
  `L32BallCoverOn P γ W (cellsMeeting K) (fun ω => dzzWall K (dzzMuIn γ W ω))`
  for every closed `K`, unconditional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

universe u

/-- Mass bound for the doubly walled measure: a ball of `dzzWall K (dzzWall 𝕍 ν)`-mass `≤ δ²`
lies in `K ∩ 𝕍` and has `ν`-mass `≤ δ²`. -/
lemma ball_facts_of_wall2 {K : Set ℂ} (hK : IsClosed K) {ν : Measure ℂ} {x : ℂ} {ρ δ : ℝ}
    (h : dzzWall K (dzzWall dzzV ν) (Metric.ball x ρ) ≤ ENNReal.ofReal (δ ^ 2)) :
    Metric.ball x ρ ⊆ K ∧ Metric.ball x ρ ⊆ dzzV ∧
      ν (Metric.ball x ρ) ≤ ENNReal.ofReal (δ ^ 2) := by
  have hK' : Metric.ball x ρ ⊆ K := by
    by_contra hn
    rw [dzzWall_ball_of_not_subset hK _ hn] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  have h2 : dzzWall dzzV ν (Metric.ball x ρ) ≤ ENNReal.ofReal (δ ^ 2) :=
    (Measure.le_iff'.1 (le_dzzWall K _) _).trans h
  have hV : Metric.ball x ρ ⊆ dzzV := by
    by_contra hn
    rw [dzzWall_ball_of_not_subset isClosed_dzzV _ hn] at h2
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h2)
  exact ⟨hK', hV, (Measure.le_iff'.1 (le_dzzWall dzzV ν) _).trans h2⟩

/-- The count along one path of `N` balls inside `K` (walled S3P32W3), for any cell family `S`
containing every `δ'`-cell that meets a ball inside `K`. -/
theorem approxDistOn_le_four_mul_of_path {K : Set ℂ} (hK : IsClosed K) {m : DyBox → ℝ}
    {δ' δ : ℝ} {ν : Measure ℂ} (S : Set DyBox)
    (hS : ∀ T, IsCell m δ' T → ∀ (x : ℂ) (ρ : ℝ) (z : ℂ), Metric.ball x ρ ⊆ K →
      z ∈ Metric.ball x ρ → z ∈ T.closedBox → T ∈ S)
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hball : ∀ (c : ℚ × ℚ) (ρ : ℝ), Metric.ball (ratPt c) ρ ⊆ dzzV →
      ν (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        BallInCells m δ' (Metric.ball (ratPt c) ρ))
    {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) (N : ℕ) (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ)
    (P : Path u v)
    (h1 : ∀ i, 0 < ρ i ∧ dzzWall K (dzzWall dzzV ν) (Metric.ball (ratPt (c i)) (ρ i)) ≤
      ENNReal.ofReal (δ ^ 2))
    (h2 : ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i)) :
    approxDistOn S m δ' u v ≤ 4 * (N : ℕ∞) := by
  classical
  have hf := fun i => ball_facts_of_wall2 hK (h1 i).2
  have hcov : ∀ i, BallInCells m δ' (Metric.ball (ratPt (c i)) (ρ i)) := fun i =>
    hball _ _ (hf i).2.1 (hf i).2.2
  choose Sb hS4 N₁ hN₁ using hcov
  set Sall : Finset DyBox := (Finset.univ.biUnion Sb).filter (· ∈ S) with hSall
  have hcard : Sall.card ≤ 4 * N := by
    refine (Finset.card_filter_le _ _).trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ i, (Sb i).card ≤ ∑ _i : Fin N, 4 := Finset.sum_le_sum fun i _ => hS4 i
      _ = 4 * N := by simp [mul_comm]
  set L : ℕ := max N₀ (Finset.univ.sup N₁) with hL
  set A : Set ℂ := range P with hA
  have hAK : A ⊆ K ∩ dzzV := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := h2 t
    exact ⟨(hf i).1 hi, (hf i).2.1 hi⟩
  have hAV : A ⊆ dzzV := fun z hz => (hAK hz).2
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
    rw [hSall, Finset.mem_filter]
    exact ⟨Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hN₁ i (p t) hNi ⟨P s, hz, hi⟩ T hT⟩,
      hS T hT.1 _ _ (P s) (hf i).1 hi (hT.sub hz)⟩
  have hu0 : (p 0).Mem u := by rw [hp0]; exact ⟨hu, rfl⟩
  have hvM : (p M).Mem v := by rw [hpM]; exact ⟨hv, rfl⟩
  have key := approxDistOn_le_card_of_path S hpart hN₀ p M
    (fun t ht => by rw [hpn t ht]; exact le_max_left _ _)
    (fun t ht => Or.inr (hstep t ht).1) Sall
    (fun T hT => (Finset.mem_filter.1 hT).2) hcell hu0 hvM
  refine key.trans ?_
  exact_mod_cast hcard

/-- **DZZ l. 1166–1167, walled**: (eq-Euclidean-Ball-covering) gives
`D'^K_{δ'}(u, v) ≤ 4 D^K_δ(u, v)`. -/
theorem approxDistOn_le_four_mul_lgd {K : Set ℂ} (hK : IsClosed K) {m : DyBox → ℝ}
    {δ' δ : ℝ} {ν : Measure ℂ} (S : Set DyBox)
    (hS : ∀ T, IsCell m δ' T → ∀ (x : ℂ) (ρ : ℝ) (z : ℂ), Metric.ball x ρ ⊆ K →
      z ∈ Metric.ball x ρ → z ∈ T.closedBox → T ∈ S)
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ' b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ' b → b.n ≤ N₀)
    (hball : ∀ (c : ℚ × ℚ) (ρ : ℝ), Metric.ball (ratPt c) ρ ⊆ dzzV →
      ν (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        BallInCells m δ' (Metric.ball (ratPt c) ρ))
    {u v : ℂ} (hu : u ∈ dzzV) (hv : v ∈ dzzV) :
    approxDistOn S m δ' u v ≤ 4 * lgdDZZ (dzzWall K (dzzWall dzzV ν)) δ u v := by
  classical
  set Q : ℕ → Prop := fun N => ∃ (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ) (P : Path u v),
    (∀ i, 0 < ρ i ∧ dzzWall K (dzzWall dzzV ν) (Metric.ball (ratPt (c i)) (ρ i)) ≤
      ENNReal.ofReal (δ ^ 2)) ∧ ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i) with hQ
  by_cases hne : ∃ N, Q N
  · have hmin : ((Nat.find hne : ℕ) : ℕ∞) ≤ lgdDZZ (dzzWall K (dzzWall dzzV ν)) δ u v := by
      unfold lgdDZZ
      exact le_iInf₂ fun N hN => by exact_mod_cast Nat.find_min' hne hN
    obtain ⟨c, ρ, P, h1, h2⟩ := Nat.find_spec hne
    exact (approxDistOn_le_four_mul_of_path hK S hS hpart hN₀ hball hu hv _ c ρ P h1 h2).trans
      (by gcongr)
  · have htop : lgdDZZ (dzzWall K (dzzWall dzzV ν)) δ u v = ⊤ := by
      unfold lgdDZZ
      exact iInf₂_eq_top.2 fun N hN => absurd ⟨N, hN⟩ hne
    rw [htop]
    exact le_top.trans (by simp)

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Walled (eq-Euclidean-Ball-covering) consequence** (DZZ l. 1164–1168 + Remark 5.2): with high
probability `D'^K_{γ,δ'}(u, v) ≤ 4 D^K_{γ,δ}(u, v)` for all `u, v ∈ 𝕍`, `δ' = p32Up δ`. -/
def L32BallCoverOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (S : Set DyBox)
    (μ : Ω → Measure ℂ) : Prop :=
  HighProb P fun δ => {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
    approxLGDOn S γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}

omit [MeasurableSpace Ω] in
/-- The walled version of `ballCover_inter_cellSize_subset` (S3P32W4). -/
theorem ballCover_inter_cellSize_subsetIn {K : Set ℂ} (hK : IsClosed K) (γ : ℝ)
    (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) {δ : ℝ} (hδ : 0 < p32Up δ) :
    ballCoverEvent γ W ν δ ∩ cellSizeEvent γ W (p32Up δ) ⊆
      {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        approxLGDIn K γ W (p32Up δ) u v ω ≤
          4 * lgdDZZ (dzzWall K (dzzWall dzzV (ν ω))) δ u v} := by
  rintro ω ⟨hcov, hpart, hside⟩ u hu v hv
  obtain ⟨N₀, hN₀⟩ := exists_level_bound (Real.rpow_pos_of_pos hδ (dzzCmc γ))
    fun b hb => (hside b hb).1
  exact approxDistOn_le_four_mul_lgd hK (cellsMeeting K)
    (fun _ _ _ _ z hK' hz hzT => ⟨z, hzT, hK' hz⟩) hpart hN₀ (hcov · ·) hu hv

/-- **The lower-half input of the walled P3.2 at `μIn`**, unconditional, for every closed `K`. -/
theorem l32BallCoverIn_dzzMuIn {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} (hK : IsClosed K) :
    L32BallCoverOn P γ W (cellsMeeting K) (fun ω => dzzWall K (dzzMuIn γ W ω)) := by
  have hcmp := highProb_cellCompare' hW hγ hγ2
    (l32CellCompareBox_of_lower hW hγ hγ2 (l32TildeMLower_wickQArea hW hγ hγ2))
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ :=
    (hcmp.inter (highProb_cellSize_p32Up hW hγ hγ2)).inter (highProb_cellSize_p32Up hW hγ hγ2)
  refine ⟨c, hc, δ₀, hδ₀, fun δ hδ => (measure_mono (compl_subset_compl.2 ?_)).trans (h δ hδ)⟩
  rintro ω ⟨hω1, hω2⟩
  exact ballCover_inter_cellSize_subsetIn hK γ W (wickQArea γ W) (p32Up_pos hδ.1)
    ⟨cellCompare'_inter_subset γ W _ δ hω1, hω2⟩

end DZZ
end LQGMetric
