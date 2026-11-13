/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SBridge

/-!
# The three root cells for the inner-degree window

The contact point, rather than the whole root cell, must stay inside the
covered disk. This keeps the graph paths in a polynomial finite region.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace MatedCRTHarmonic.GMS4b

/-- The two-unit-time window at `t₀` is covered by the three cells adjacent
to `⌈t₀/ε⌉`. -/
theorem locWindow_subset_three_cellOf {ε : ℝ} (hε : 0 < ε)
    (η : ℝ → ℂ) (t₀ : ℝ) :
    locWindow ε η t₀ ⊆
      cellOf ε η (⌈t₀ / ε⌉ - 1) ∪ cellOf ε η ⌈t₀ / ε⌉ ∪
        cellOf ε η (⌈t₀ / ε⌉ + 1) := by
  rintro w ⟨t, ht, rfl⟩
  set x : ℤ := ⌈t₀ / ε⌉ with hx
  have hx₀ := mem_Icc_ceil hε t₀
  rw [← hx] at hx₀
  have hlo : ε * ((x : ℝ) - 2) ≤ t := by linarith [ht.1, hx₀.1]
  have hhi : t ≤ ε * ((x : ℝ) + 1) := by linarith [ht.2, hx₀.2]
  rcases le_total t (ε * ((x : ℝ) - 1)) with h₁ | h₁
  · left
    left
    exact ⟨t, ⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩
  rcases le_total t (ε * (x : ℝ)) with h₂ | h₂
  · left
    right
    exact ⟨t, ⟨h₁, h₂⟩, rfl⟩
  · right
    exact ⟨t, ⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩

/-- The three root cells of a window inside the covered disk have indices
in the interval confining all visits to that disk. -/
theorem three_root_indices_mem_covered_interval {η : ℝ → ℂ}
    {ε M R t₀ : ℝ} (hε : 0 < ε)
    (hwindow : locWindow ε η t₀ ⊆ Metric.ball (0 : ℂ) R)
    (hconf : η ⁻¹' Metric.ball (0 : ℂ) R ⊆ Icc (-M) M) :
    let x : ℤ := ⌈t₀ / ε⌉
    x - 1 ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) ∧
      x ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) ∧
      x + 1 ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
  dsimp
  set x : ℤ := ⌈t₀ / ε⌉ with hx
  have hx₀ := mem_Icc_ceil hε t₀
  rw [← hx] at hx₀
  have hlefttime : ε * ((x : ℝ) - 1) ∈ Icc (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith [hx₀.1, hx₀.2]
  have hrighttime : ε * (x : ℝ) ∈ Icc (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith [hx₀.1, hx₀.2]
  have hleft : x - 1 ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
    have hz : η (ε * ((x : ℝ) - 1)) ∈ Metric.ball (0 : ℂ) R :=
      hwindow ⟨_, hlefttime, rfl⟩
    apply cell_index_mem_interval_of_preimage_ball_bound hε hconf hz
    refine ⟨ε * ((x : ℝ) - 1), ?_, rfl⟩
    constructor <;> push_cast <;> nlinarith [hε.le]
  have hmiddle : x ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
    have hz : η t₀ ∈ Metric.ball (0 : ℂ) R :=
      hwindow ⟨t₀, ⟨by linarith, by linarith⟩, rfl⟩
    exact cell_index_mem_interval_of_preimage_ball_bound hε hconf hz
      ⟨t₀, hx₀, rfl⟩
  have hright : x + 1 ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
    have hz : η (ε * (x : ℝ)) ∈ Metric.ball (0 : ℂ) R :=
      hwindow ⟨_, hrighttime, rfl⟩
    apply cell_index_mem_interval_of_preimage_ball_bound hε hconf hz
    refine ⟨ε * (x : ℝ), ?_, rfl⟩
    constructor <;> push_cast <;> nlinarith [hε.le]
  exact ⟨hleft, hmiddle, hright⟩

private theorem l46s_length_induce {V : Type*} {G : SimpleGraph V}
    {S : Set V} {u v : V} (p : G.Walk u v)
    (hp : ∀ w ∈ p.support, w ∈ S) :
    (p.induce S hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
    congr 1
    exact ih _

/-- The deterministic graph-ball consequence of finite visits, disk
confinement, and a degree bound on the confined finite graph. -/
theorem locDegIn_le_three_graph_balls {ω : MatedCRT.Path2}
    {η : ℝ → ℂ} (P : RouteM.Peanosphere ω η)
    {ε : ℝ} (hε : 0 < ε) (h : MatedCRT.IsLocallyFinite ε ω)
    {k : ℕ} (hvisit : ∀ z : ℂ, (η ⁻¹' {z}).encard ≤ k)
    {M R t₀ : ℝ}
    (hwindow : locWindow ε η t₀ ⊆ Metric.ball (0 : ℂ) R)
    (hconf : η ⁻¹' Metric.ball (0 : ℂ) R ⊆ Icc (-M) M)
    {D : ℕ}
    (hD : ∀ v : {x : ℤ // x ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1)},
      (((MatedCRT.graph ε ω h).adj.induce
        (Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1))).neighborSet v).ncard ≤ D) :
    locDegIn ε η t₀ ≤ 9 * ((D + 1) ^ (2 * k) : ℕ∞) := by
  let S : Set ℤ := Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1)
  let G : SimpleGraph ℤ := (MatedCRT.graph ε ω h).adj
  let GS : SimpleGraph S := G.induce S
  have hSfinite : S.Finite := Set.finite_Icc _ _
  letI : Fintype S := hSfinite.fintype
  classical
  let x : ℤ := ⌈t₀ / ε⌉
  obtain ⟨hr₁, hr₂, hr₃⟩ := three_root_indices_mem_covered_interval hε hwindow hconf
  let r₁ : S := ⟨x - 1, hr₁⟩
  let r₂ : S := ⟨x, hr₂⟩
  let r₃ : S := ⟨x + 1, hr₃⟩
  let B₁ := l46sGraphBall GS r₁ (2 * k)
  let B₂ := l46sGraphBall GS r₂ (2 * k)
  let B₃ := l46sGraphBall GS r₃ (2 * k)
  have hD' : ∀ v : S, (Finset.univ.filter (fun w => GS.Adj v w)).card ≤ D := by
    intro v
    rw [← GS.neighborFinset_eq_filter]
    rw [GS.card_neighborFinset_eq_degree, ← GS.ncard_neighborSet]
    exact hD v
  have hBcard : ((B₁ ∪ B₂) ∪ B₃).card ≤ 3 * (D + 1) ^ (2 * k) :=
    l46sGraphBall_three_card_le GS r₁ r₂ r₃ (2 * k) D hD'
  have hWsub : windowCells ε η t₀ ⊆ Subtype.val '' (((B₁ ∪ B₂) ∪ B₃ : Finset S) : Set S) := by
    intro n hn
    obtain ⟨z, hzn, hzw⟩ := hn
    have hz : z ∈ Metric.ball (0 : ℂ) R := hwindow hzw
    have hnS : n ∈ S := cell_index_mem_interval_of_preimage_ball_bound hε hconf hz hzn
    have hroot := locWindow_subset_three_cellOf hε η t₀ hzw
    rcases hroot with hroot | hroot
    · rcases hroot with hroot | hroot
      · obtain ⟨p, hp, hs⟩ := contact_cells_short_path_in_interval P hε h hvisit hconf hz hroot hzn
        let pS := p.induce S hs
        have hpS : pS.length ≤ 2 * k := by
          have heq : pS.length = p.length := l46s_length_induce p hs
          omega
        have hmem := l46sGraphBall_mem_of_walk_le GS pS hpS
        exact ⟨⟨n, hnS⟩, Finset.mem_union_left _ (Finset.mem_union_left _ hmem), rfl⟩
      · obtain ⟨p, hp, hs⟩ := contact_cells_short_path_in_interval P hε h hvisit hconf hz hroot hzn
        let pS := p.induce S hs
        have hpS : pS.length ≤ 2 * k := by
          have heq : pS.length = p.length := l46s_length_induce p hs
          omega
        have hmem := l46sGraphBall_mem_of_walk_le GS pS hpS
        exact ⟨⟨n, hnS⟩, Finset.mem_union_left _ (Finset.mem_union_right _ hmem), rfl⟩
    · obtain ⟨p, hp, hs⟩ := contact_cells_short_path_in_interval P hε h hvisit hconf hz hroot hzn
      let pS := p.induce S hs
      have hpS : pS.length ≤ 2 * k := by
        have heq : pS.length = p.length := l46s_length_induce p hs
        omega
      have hmem := l46sGraphBall_mem_of_walk_le GS pS hpS
      exact ⟨⟨n, hnS⟩, Finset.mem_union_right _ hmem, rfl⟩
  have hWcard : (windowCells ε η t₀).encard ≤
      3 * ((D + 1) ^ (2 * k) : ℕ∞) := by
    calc
      (windowCells ε η t₀).encard ≤
          (Subtype.val '' (((B₁ ∪ B₂) ∪ B₃ : Finset S) : Set S)).encard :=
        Set.encard_le_encard hWsub
      _ ≤ (((B₁ ∪ B₂) ∪ B₃ : Finset S) : Set S).encard :=
        Set.encard_image_le _ _
      _ = ((((B₁ ∪ B₂) ∪ B₃).card : ℕ) : ℕ∞) :=
        Set.encard_coe_eq_coe_finsetCard _
      _ ≤ 3 * ((D + 1) ^ (2 * k) : ℕ∞) := by exact_mod_cast hBcard
  calc
    locDegIn ε η t₀ ≤ 3 * (windowCells ε η t₀).encard :=
      locDegIn_le_three_mul_encard hε η t₀
    _ ≤ 3 * (3 * ((D + 1) ^ (2 * k) : ℕ∞)) := by gcongr
    _ = 9 * ((D + 1) ^ (2 * k) : ℕ∞) := by ring

end MatedCRTHarmonic.GMS4b
