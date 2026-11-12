/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53I3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I2

/-!
# Walled DZZ Lemma 3.12, step 3: the localized surgery (P2-DZZ53I)

DZZ arXiv:1807.00422, proof of Lemma 3.12 (eq. Sequence-good-cells), l. 1436–1458, run from an
arbitrary loop-free chain `𝒞_0` of cells within distance `0` of a set `K` (the walled geodesic of
`D'^K_δ`, in place of DZZ's `D'_δ`-geodesic). Own elementary addition (DV-P2-DZZ53I): the iteration
keeps every cell within `ρ ≥ 8 δ^{C_Mc}` of `K`; the key point is that a cell becoming bad in a
step has side `≥ 2 s_𝖢` and meets `𝖢_large`, so along a chain of consecutive processed new bad
cells the displacements `4 s_𝖢` are dominated by the side of the next bad cell (invariant: every
bad cell `b` is within `4 s_b` of `K`).

* `L53Near K r c`, `L53Near.mono`, `l53Near_of_meet`;
* **`l312StepLoc`** (one step), **`l312SurgeryLoc`** (the iteration, `l312_iterate`; copy of
  `l312SurgeryCR_of_stepR`, S3L12W1, with the invariant added).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- `c` has a point within distance `r` of `K`. -/
def L53Near (K : Set ℂ) (r : ℝ) (c : DyBox) : Prop :=
  ∃ z ∈ c.closedBox, ∃ k ∈ K, dist z k ≤ r

lemma L53Near.mono {K : Set ℂ} {r r' : ℝ} {c : DyBox} (h : L53Near K r c) (hr : r ≤ r') :
    L53Near K r' c := by
  obtain ⟨z, hz, k, hk, hd⟩ := h
  exact ⟨z, hz, k, hk, hd.trans hr⟩

/-- Copy of `dist_le_of_mem_largeBox` (S3L5Main, not imported here). -/
lemma l53_dist_le_of_mem_largeBox {b : DyBox} {x y : ℂ} (hx : x ∈ b.largeBox)
    (hy : y ∈ b.largeBox) : dist x y ≤ 4 * b.side := by
  obtain ⟨x1, x2⟩ := hx
  obtain ⟨y1, y2⟩ := hy
  rw [Complex.dist_eq]
  have a1 : |(x - y).re| ≤ 2 * b.side := by
    rw [Complex.sub_re]; have := abs_le.1 x1; have := abs_le.1 y1
    rw [abs_le]; constructor <;> linarith
  have a2 : |(x - y).im| ≤ 2 * b.side := by
    rw [Complex.sub_im]; have := abs_le.1 x2; have := abs_le.1 y2
    rw [abs_le]; constructor <;> linarith
  linarith [Complex.norm_le_abs_re_add_abs_im (x - y)]

lemma l53Near_of_meet {K : Set ℂ} {t : ℝ} {C c : DyBox} (hC : L53Near K t C)
    (h : (c.closedBox ∩ C.largeBox).Nonempty) : L53Near K (t + 4 * C.side) c := by
  obtain ⟨z, hz, k, hk, hd⟩ := hC
  obtain ⟨p, hp1, hp2⟩ := h
  refine ⟨p, hp1, k, hk, ?_⟩
  have := l53_dist_le_of_mem_largeBox hp2 (mem_largeBox_of_mem_self hz)
  linarith [dist_triangle p z k]

variable {m : DyBox → ℝ} {δ : ℝ}

/-- **One localized surgery step** (DZZ l. 1436–1499 with the invariant of DV-P2-DZZ53I). -/
theorem l312StepLoc {γ αs : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hsize : ∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ)
    (hring : ∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C)
    {u v : ℂ} (hgu : IsGoodPoint m δ (epsStar αs δ) u) (hgv : IsGoodPoint m δ (epsStar αs δ) v)
    {K : Set ℂ} {ρ : ℝ} (hρ : 8 * δ ^ dzzCMc γ ≤ ρ)
    {l : List DyBox} (hj : JoinsCells m δ u v l) (hch : l.IsChain Neighbour) (hnd : l.Nodup)
    (hne : (l312Bad (epsStar αs δ) l).Nonempty) (h1 : ∀ c ∈ l, L53Near K ρ c)
    (h2 : ∀ b ∈ l312Bad (epsStar αs δ) l, L53Near K (4 * b.side) b) :
    ∃ l' : List DyBox, JoinsCells m δ u v l' ∧ l'.IsChain Neighbour ∧ l'.Nodup ∧
      l'.length ≤ l.length + 32 * 4 ^ epsStarN αs δ ∧ L312Progress (epsStar αs δ) l l' ∧
      (∀ c ∈ l', L53Near K ρ c) ∧
      ∀ b ∈ l312Bad (epsStar αs δ) l', L53Near K (4 * b.side) b := by
  set ε := epsStar αs δ
  have hε : 0 < ε := by simp only [ε, epsStar]; positivity
  obtain ⟨C, hC, hmax⟩ := exists_max_side hne
  obtain ⟨A, M, B, R, x, y, hl, hCM, hW, hRnd, hR, hx, hy, hcard, hxm, hym⟩ :=
    l312CoreLoc hδ hsize hring hgu hgv hj hch hnd hC hmax
  have hWs : ∀ c ∈ x :: R ++ [y], ε * C.side ≤ c.side := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · exact hx
    · exact (hR c hc).2.1
    · exact hy
  have hWm : ∀ c ∈ x :: R ++ [y], (c.closedBox ∩ C.largeBox).Nonempty := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · exact hxm
    · exact (hR c hc).2.2
    · exact hym
  have hRlen : R.length ≤ 32 * 4 ^ epsStarN αs δ :=
    length_le_of_near hRnd (fun c hc => (hR c hc).1) (fun c hc => (hR c hc).2.1)
      (fun c hc => (hR c hc).2.2)
  have hCW : C ∉ l312Bad ε (x :: R ++ [y]) := by
    intro hCW
    have := side_gt_of_mem_l312Bad hε hWs hCW
    linarith
  have hD1 : (l312Bad ε (x :: R ++ [y]) \ l312Bad ε l).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans hcard
  have hD2 : ∀ c ∈ l312Bad ε (x :: R ++ [y]) \ l312Bad ε l, 2 * C.side ≤ c.side := fun c hc =>
    two_mul_side_le_of_lt (side_gt_of_mem_l312Bad hε hWs (Finset.mem_sdiff.1 hc).1)
  obtain ⟨l', hj', hch', hnd', hlen', hprog, hmem, hbad⟩ :=
    l312_spliceLoc hj hch hnd hC hmax hl hCM hW (fun c hc => (hR c hc).1) hCW hD1 hD2
  have hCcell : IsCell m δ C := hj.2.1 C (mem_of_mem_l312Bad hC)
  have hCs : C.side ≤ δ ^ dzzCMc γ := (hsize C hCcell).2
  have hWnear : ∀ c ∈ x :: R ++ [y], L53Near K (8 * C.side) c := fun c hc =>
    (l53Near_of_meet (h2 C hC) (hWm c hc)).mono (by linarith)
  refine ⟨l', hj', hch', hnd', by omega, hprog, ?_, ?_⟩
  · intro c hc
    rcases hmem c hc with h | h
    · exact h1 c h
    · exact (hWnear c h).mono (by linarith)
  · intro b hb
    rcases Finset.mem_union.1 (hbad hb) with h | h
    · exact h2 b (Finset.mem_of_mem_erase h)
    · have := hD2 b h
      exact (hWnear b (mem_of_mem_l312Bad (Finset.mem_sdiff.1 h).1)).mono (by linarith)

/-- **The localized surgery** (DZZ (Sequence-good-cells), l. 1436–1458, from an arbitrary
loop-free chain `l₀` of cells meeting `K`): a good sequence of cells joining `u`, `v`, all within
`ρ` of `K`, with at most `|l₀| e^{(log δ⁻¹)^{0.6}}` cells. -/
theorem l312SurgeryLoc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {αs : ℝ} (hαs : 0 < αs) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u v : ℂ, IsGoodPoint m δ (epsStar αs δ) u → IsGoodPoint m δ (epsStar αs δ) v →
    ∀ (K : Set ℂ) (ρ : ℝ), 8 * δ ^ dzzCMc γ ≤ ρ →
    ∀ l₀ : List DyBox, JoinsCells m δ u v l₀ → l₀.IsChain Neighbour → l₀.Nodup →
      (∀ c ∈ l₀, L53Near K 0 c) →
      ∃ l : List DyBox, JoinsCells m δ u v l ∧ IsGoodSeq (epsStar αs δ) l ∧
        (∀ c ∈ l, L53Near K ρ c) ∧
        ((l.length : ℕ∞) : ℝ≥0∞) ≤ ((l₀.length : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ))) := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  obtain ⟨δ₂, hδ₂, hδ₂1, hA⟩ := l312_count_asym hC hαs
  refine ⟨δ₂, hδ₂, fun δ hδ m hsize hring u v hgu hgv K ρ hρ l0 hj0 hch0 hnd0 hK0 => ?_⟩
  have hδ0 := hδ.1
  have hδI : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ0, hδ.2.trans hδ₂1⟩
  set ε := epsStar αs δ
  set M := ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊
  set K' := 32 * 4 ^ epsStarN αs δ
  have hlev : ∀ c, IsCell m δ c → c.n ≤ M := fun c hc =>
    Nat.le_floor (n_le_of_rpow_le_side hδ0 (hsize c hc).1)
  obtain ⟨l1, ⟨hj1, hch1, -, hloc1, -⟩, hbad, hlen1⟩ := l312_iterate
    (Q := fun l => JoinsCells m δ u v l ∧ l.IsChain Neighbour ∧ l.Nodup ∧
      (∀ c ∈ l, L53Near K ρ c) ∧ ∀ b ∈ l312Bad ε l, L53Near K (4 * b.side) b) ε M K'
    (fun l hl c hc => hlev c (hl.1.2.1 c hc))
    (fun l hl hne => by
      obtain ⟨l', a, b, b', c, d, e, f⟩ := l312StepLoc hδI hsize hring hgu hgv hρ hl.1 hl.2.1
        hl.2.2.1 hne hl.2.2.2.1 hl.2.2.2.2
      exact ⟨l', ⟨a, b, b', e, f⟩, c, d⟩) l0
    ⟨hj0, hch0, hnd0, fun c hc => (hK0 c hc).mono (by
        have : (0 : ℝ) ≤ δ ^ dzzCMc γ := by positivity
        linarith),
      fun b hb => (hK0 b (mem_of_mem_l312Bad hb)).mono (by
        have := b.side_pos'; linarith)⟩
  have hε : 0 < ε := by unfold ε epsStar; positivity
  refine ⟨l1, hj1, isGoodSeq_of_bad_empty hε hch1 hbad, hloc1, ?_⟩
  have hpot := l312Pot_le (ε := ε) (fun c hc => hlev c (hj0.2.1 c hc))
  have hpos : 1 ≤ l0.length := by
    obtain ⟨hne, -⟩ := hj0; exact List.length_pos_iff.2 hne
  have hnat : l1.length ≤ l0.length * (1 + K' * (2 * M + 1)) := by
    have h1 := Nat.mul_le_mul_left K' hpot
    have h2 : K' * M ≤ K' * M * l0.length := Nat.le_mul_of_pos_right _ hpos
    have e : l0.length * (1 + K' * (2 * M + 1)) =
        l0.length + K' * (l0.length * (M + 1)) + K' * M * l0.length := by ring
    rw [e]; nlinarith
  have hA' := hA δ hδ
  rw [ENat.toENNReal_coe, ENat.toENNReal_coe]
  calc (l1.length : ℝ≥0∞) ≤ (l0.length : ℝ≥0∞) * ((1 + K' * (2 * M + 1) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hnat
    _ ≤ (l0.length : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ))) := by
      refine mul_le_mul' le_rfl ?_
      rw [← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [K', M]
      push_cast
      push_cast at hA'
      exact hA'

end DZZ
end LQGMetric
