/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12S5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S3

/-!
# DZZ Lemma 3.12, one-step claim: good points avoid `𝖢_large` of bad cells (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1443–1444: "Since `u` and `v` are good,
we see that `u, v ∉ 𝖢_large`" for the bad cell `𝖢 ∈ ψ(𝒞_i)` (so `𝒞_i` enters and exits
`𝖢_large`). Own elementary proof: the small neighbour `𝖢'` of `𝖢` (side `< ε s_𝖢`) has its centre
in `𝖢_large°`, where the goodness of `x ∈ 𝖢_large` would force `s_{𝖢'} ≥ ε s_𝖢`.

* `boxAt_center_self`, `mem_center_self`: `𝖢` contains its centre (half-open convention).
* **`not_mem_largeBox_of_bad`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma closedBox_sub_dzzV316 (b : DyBox) : b.closedBox ⊆ dzzV := by
  rintro z ⟨h1, h2, h3, h4⟩
  have s0 := side_pos' b
  have e : (2 : ℝ) ^ b.n * b.side = 1 := by
    unfold DyBox.side; rw [mul_comm]; exact pow_inv_mul_pow b.n
  have hj : (b.j : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hj
  have hk : (b.k : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hk
  refine ⟨le_trans (by positivity) h1, ?_, le_trans (by positivity) h3, ?_⟩ <;> nlinarith

lemma boxAt_center_self (b : DyBox) : boxAt b.n b.center = b := by
  have key : ∀ i : ℕ, i < 2 ^ b.n → idx b.n ((i + 1 / 2) * b.side) = i := by
    intro i hi
    unfold idx
    have e : (i + 1 / 2 : ℝ) * b.side * 2 ^ b.n = i + 1 / 2 := by
      unfold DyBox.side; rw [mul_assoc, pow_inv_mul_pow, mul_one]
    rw [e]
    have hf : ⌊(i : ℝ) + 1 / 2⌋₊ = i := by
      rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
    rw [hf]; omega
  ext
  · rfl
  · exact key b.j b.hj
  · exact key b.k b.hk

lemma mem_center_self (b : DyBox) : b.Mem b.center :=
  ⟨closedBox_sub_dzzV316 b (center_mem_closedBox b), boxAt_center_self b⟩

lemma abs_re_sub_center_le {b : DyBox} {z : ℂ} (hz : z ∈ b.closedBox) :
    |z.re - b.center.re| ≤ b.side / 2 := by
  obtain ⟨h1, h2, -, -⟩ := hz
  simp only [DyBox.center]; rw [abs_le]; constructor <;> linarith

lemma abs_im_sub_center_le {b : DyBox} {z : ℂ} (hz : z ∈ b.closedBox) :
    |z.im - b.center.im| ≤ b.side / 2 := by
  obtain ⟨-, -, h3, h4⟩ := hz
  simp only [DyBox.center]; rw [abs_le]; constructor <;> linarith

/-- A box neighbouring `C` and smaller than `C` has its centre in `𝖢_large°`. -/
lemma center_mem_largeBoxOpen {C c : DyBox} (h : Neighbour C c) (hs : c.side < C.side) :
    c.center ∈ C.largeBoxOpen := by
  obtain ⟨z, ⟨hzC, hzc⟩⟩ : (C.closedBox ∩ c.closedBox).Nonempty := by
    by_contra hne
    exact h.2 (Set.not_nonempty_iff_eq_empty.1 hne ▸ Set.subsingleton_empty)
  have a1 := abs_re_sub_center_le hzC; have a2 := abs_im_sub_center_le hzC
  have b1 := abs_re_sub_center_le hzc; have b2 := abs_im_sub_center_le hzc
  have s0 := side_pos' C
  constructor
  · calc |c.center.re - C.center.re| = |(z.re - C.center.re) - (z.re - c.center.re)| := by
          ring_nf
      _ ≤ |z.re - C.center.re| + |z.re - c.center.re| := abs_sub _ _
      _ < C.side := by linarith
  · calc |c.center.im - C.center.im| = |(z.im - C.center.im) - (z.im - c.center.im)| := by
          ring_nf
      _ ≤ |z.im - C.center.im| + |z.im - c.center.im| := abs_sub _ _
      _ < C.side := by linarith

/-- **DZZ l. 1443**: a good point does not lie in `𝖢_large` for a bad cell `𝖢` of a
`Neighbour`-chain of cells. -/
theorem not_mem_largeBox_of_bad {ε : ℝ} (hε1 : ε ≤ 1) {l : List DyBox}
    (hcells : ∀ c ∈ l, IsCell m δ c) (hch : l.IsChain Neighbour) {C : DyBox}
    (hC : C ∈ l312Bad ε l) {x : ℂ} (hx : IsGoodPoint m δ ε x) : x ∉ C.largeBox := by
  intro hxC
  simp only [l312Bad, Finset.mem_filter, List.mem_toFinset] at hC
  obtain ⟨hCl, c, hinf, hlt⟩ := hC
  have hN : Neighbour C c := by
    rcases hinf with h | h
    · exact List.isChain_pair.1 (hch.infix h)
    · exact (List.isChain_pair.1 (hch.infix h)).symm
  have hcl : c ∈ l := by
    rcases hinf with h | h
    · exact infix_mem_right h
    · exact infix_mem_left h
  have s0 := side_pos' C
  have hs : c.side < C.side := lt_of_lt_of_le hlt (by nlinarith)
  have hgood := hx C (hcells C hCl) hxC c.center (center_mem_largeBoxOpen hN hs)
    (closedBox_sub_dzzV316 c (center_mem_closedBox c))
  rw [cellSide_eq_of_isCell (hcells c hcl) (mem_center_self c)] at hgood
  linarith

end DZZ
end LQGMetric
