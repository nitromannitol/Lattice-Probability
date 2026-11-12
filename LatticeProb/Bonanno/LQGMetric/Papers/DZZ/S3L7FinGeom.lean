/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7PercChain
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusPeierls

/-!
# DZZ Lemma 3.7: from a percolation enclosure in `ℤ²` to `HasEnclosure` (P2-DZZ3F)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1005–1015): the boxes of
`𝓑(B, ε)` (`ε = 2^{-k}`, `2^k = 2h`) are identified with the sites `z ∈ ℤ²` through
`z ↦ siteBox (B.n + k) (l37c B h) z` (the box with lower-left index `l37c B h + z`, so that the
site `0` has the centre `c_B` as lower-left corner). DZZ's open enclosure in `B_large \ B`
becomes a `4`-connected set `U` of good sites in the annulus `h + 2 ≤ ‖z‖_∞ ≤ 2h - 2` meeting
every `*`-path of grid sites from the hole to the outside of `annBox (2h - 2)`.

* `neighbour_siteBox`: `4`-adjacent grid sites give `Neighbour` boxes.
* `siteBox_mem_boxColl`, `disjoint_siteBox`: annulus sites are boxes of `𝓑(B, ε)` disjoint from `B`.
* `boxSite_step`: points at distance `< 2^{-L}` lie in equal or `*`-adjacent boxes of level `L`
  (the discretisation of a continuous path, DZZ's "separates `B` from `∂B_large`").
* `hasEnclosure_of_sites`: the encoding (DZZ Def 3.6 from the percolation enclosure).

Own elementary arguments (DZZ do not spell out the discretisation); see DEVIATIONS.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

/-- An integer index clamped into `[0, 2^L)`. -/
def idxZ (L : ℕ) (t : ℤ) : ℕ := min t.toNat (2 ^ L - 1)

lemma idxZ_lt (L : ℕ) (t : ℤ) : idxZ L t < 2 ^ L :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Nat.two_pow_pos L) one_pos)

lemma idxZ_eq {L : ℕ} {t : ℤ} (h0 : 0 ≤ t) (h1 : t < 2 ^ L) : (idxZ L t : ℤ) = t := by
  have e : ((2 ^ L : ℕ) : ℤ) = 2 ^ L := by push_cast; rfl
  rw [← e] at h1
  unfold idxZ
  generalize 2 ^ L = P at *
  have : t.toNat ≤ P - 1 := by omega
  rw [min_eq_left this]; exact Int.toNat_of_nonneg h0

/-- The box of level `L` with lower-left index `c + z` (clamped into the grid). -/
def siteBox (L : ℕ) (c z : ℤ × ℤ) : DyBox :=
  ⟨L, idxZ L (c.1 + z.1), idxZ L (c.2 + z.2), idxZ_lt _ _, idxZ_lt _ _⟩

/-- `c + z` is a grid index of level `L`. -/
def InGrid (L : ℕ) (c z : ℤ × ℤ) : Prop :=
  0 ≤ c.1 + z.1 ∧ c.1 + z.1 < 2 ^ L ∧ 0 ≤ c.2 + z.2 ∧ c.2 + z.2 < 2 ^ L

/-- The site of a box relative to `c`. -/
def boxSite (c : ℤ × ℤ) (b : DyBox) : ℤ × ℤ := ((b.j : ℤ) - c.1, (b.k : ℤ) - c.2)

/-- The base index: `c_B` is the lower-left corner of the box of site `0` (`2^k = 2h`). -/
def l37c (B : DyBox) (h : ℕ) : ℤ × ℤ := (2 * h * B.j + h, 2 * h * B.k + h)

lemma inGrid_boxSite (c : ℤ × ℤ) (b : DyBox) : InGrid b.n c (boxSite c b) := by
  have h1 : (b.j : ℤ) < 2 ^ b.n := by exact_mod_cast b.hj
  have h2 : (b.k : ℤ) < 2 ^ b.n := by exact_mod_cast b.hk
  refine ⟨by simp [boxSite], by simpa [boxSite] using h1, by simp [boxSite],
    by simpa [boxSite] using h2⟩

lemma siteBox_boxSite (c : ℤ × ℤ) {L : ℕ} (b : DyBox) (hb : b.n = L) :
    siteBox L c (boxSite c b) = b := by
  subst hb
  have hj := Nat.le_sub_one_of_lt b.hj
  have hk := Nat.le_sub_one_of_lt b.hk
  ext <;> simp [siteBox, boxSite, idxZ, hj, hk]

lemma siteBox_j {L : ℕ} {c z : ℤ × ℤ} (hz : InGrid L c z) :
    ((siteBox L c z).j : ℤ) = c.1 + z.1 := idxZ_eq hz.1 hz.2.1

lemma siteBox_k {L : ℕ} {c z : ℤ × ℤ} (hz : InGrid L c z) :
    ((siteBox L c z).k : ℤ) = c.2 + z.2 := idxZ_eq hz.2.2.1 hz.2.2.2

lemma siteBox_j_real {L : ℕ} {c z : ℤ × ℤ} (hz : InGrid L c z) :
    ((siteBox L c z).j : ℝ) = ((c.1 + z.1 : ℤ) : ℝ) := by
  rw [← siteBox_j hz]; push_cast; rfl

lemma siteBox_k_real {L : ℕ} {c z : ℤ × ℤ} (hz : InGrid L c z) :
    ((siteBox L c z).k : ℝ) = ((c.2 + z.2 : ℤ) : ℝ) := by
  rw [← siteBox_k hz]; push_cast; rfl

lemma side_pos' (b : DyBox) : 0 < b.side := by unfold DyBox.side; positivity

/-- Vertically adjacent boxes of one level are neighbours. -/
lemma neighbour_of_k_succ {b b' : DyBox} (hn : b'.n = b.n) (hj : b'.j = b.j)
    (hk : b'.k = b.k + 1) : DyBox.Neighbour b b' := by
  have hs : b'.side = b.side := by unfold DyBox.side; rw [hn]
  have s0 := side_pos' b
  refine ⟨fun h => by have := congrArg DyBox.k h; omega, fun hsub => ?_⟩
  have hj' : (b'.j : ℝ) = b.j := by exact_mod_cast hj
  have hk' : (b'.k : ℝ) = b.k + 1 := by exact_mod_cast hk
  have hp : (⟨b.j * b.side, (b.k + 1) * b.side⟩ : ℂ) ∈ b.closedBox ∩ b'.closedBox := by
    refine ⟨⟨le_rfl, by simp only; nlinarith, by simp only; nlinarith, le_rfl⟩, ?_⟩
    simp only [DyBox.closedBox, hs, hj', hk', mem_ofPred_eq]
    refine ⟨le_rfl, by nlinarith, le_rfl, by nlinarith⟩
  have hq : (⟨(b.j + 1) * b.side, (b.k + 1) * b.side⟩ : ℂ) ∈ b.closedBox ∩ b'.closedBox := by
    refine ⟨⟨by simp only; nlinarith, le_rfl, by simp only; nlinarith, le_rfl⟩, ?_⟩
    simp only [DyBox.closedBox, hs, hj', hk', mem_ofPred_eq]
    refine ⟨by nlinarith, le_rfl, le_rfl, by nlinarith⟩
  have := congrArg Complex.re (hsub hp hq)
  simp only at this
  nlinarith

/-- Horizontally adjacent boxes of one level are neighbours. -/
lemma neighbour_of_j_succ {b b' : DyBox} (hn : b'.n = b.n) (hk : b'.k = b.k)
    (hj : b'.j = b.j + 1) : DyBox.Neighbour b b' := by
  have hs : b'.side = b.side := by unfold DyBox.side; rw [hn]
  have s0 := side_pos' b
  refine ⟨fun h => by have := congrArg DyBox.j h; omega, fun hsub => ?_⟩
  have hj' : (b'.j : ℝ) = b.j + 1 := by exact_mod_cast hj
  have hk' : (b'.k : ℝ) = b.k := by exact_mod_cast hk
  have hp : (⟨(b.j + 1) * b.side, b.k * b.side⟩ : ℂ) ∈ b.closedBox ∩ b'.closedBox := by
    refine ⟨⟨by simp only; nlinarith, le_rfl, le_rfl, by simp only; nlinarith⟩, ?_⟩
    simp only [DyBox.closedBox, hs, hj', hk', mem_ofPred_eq]
    refine ⟨le_rfl, by nlinarith, le_rfl, by nlinarith⟩
  have hq : (⟨(b.j + 1) * b.side, (b.k + 1) * b.side⟩ : ℂ) ∈ b.closedBox ∩ b'.closedBox := by
    refine ⟨⟨by simp only; nlinarith, le_rfl, by simp only; nlinarith, le_rfl⟩, ?_⟩
    simp only [DyBox.closedBox, hs, hj', hk', mem_ofPred_eq]
    refine ⟨le_rfl, by nlinarith, by nlinarith, le_rfl⟩
  have := congrArg Complex.im (hsub hp hq)
  simp only at this
  nlinarith

/-- `4`-adjacent grid sites give neighbouring boxes. -/
lemma neighbour_siteBox {L : ℕ} {c x y : ℤ × ℤ} (hx : InGrid L c x) (hy : InGrid L c y)
    (hxy : PercAdj4 x y) : DyBox.Neighbour (siteBox L c x) (siteBox L c y) := by
  have jx := siteBox_j hx; have jy := siteBox_j hy
  have kx := siteBox_k hx; have ky := siteBox_k hy
  rcases hxy with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact (neighbour_of_k_succ (b := siteBox L c y) (b' := siteBox L c x) rfl (by omega) (by omega)).symm
  · exact neighbour_of_k_succ rfl (by omega) (by omega)
  · exact (neighbour_of_j_succ (b := siteBox L c y) (b' := siteBox L c x) rfl (by omega) (by omega)).symm
  · exact neighbour_of_j_succ rfl (by omega) (by omega)

/-- `s_B · 2^{n_B + k} = 2h` when `2^k = 2h`. -/
lemma side_mul_pow (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) :
    B.side * (2 : ℝ) ^ (B.n + k) = 2 * h := by
  unfold DyBox.side
  rw [pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (two_ne_zero), one_pow, one_mul]
  exact_mod_cast hK

lemma pow_inv_mul_pow (L : ℕ) : (2 : ℝ)⁻¹ ^ L * 2 ^ L = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]

/-- Annulus sites are boxes of `𝓑(B, 2^{-k})`. -/
lemma siteBox_mem_boxColl (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) {z : ℤ × ℤ}
    (hz : InGrid (B.n + k) (l37c B h) z) (hN : annBox (2 * (h : ℤ) - 2) z) :
    siteBox (B.n + k) (l37c B h) z ∈ boxColl B k := by
  refine ⟨rfl, fun w hw => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hw
  rw [siteBox_j_real hz] at a1 a2
  rw [siteBox_k_real hz] at a3 a4
  have e : (siteBox (B.n + k) (l37c B h) z).side = (2 : ℝ)⁻¹ ^ (B.n + k) := rfl
  rw [e] at a1 a2 a3 a4
  set s := (2 : ℝ)⁻¹ ^ (B.n + k)
  have hs0 : 0 < s := by positivity
  have hside : B.side = 2 * h * s := by
    have h1 := side_mul_pow B hK
    have h2 := pow_inv_mul_pow (B.n + k)
    calc B.side = B.side * ((2 : ℝ)⁻¹ ^ (B.n + k) * 2 ^ (B.n + k)) := by rw [h2, mul_one]
      _ = 2 * h * s := by rw [mul_comm ((2 : ℝ)⁻¹ ^ (B.n + k)), ← mul_assoc, h1]
  obtain ⟨b1, b2, b3, b4⟩ := hN
  have c1 : (-(2 * (h : ℝ) - 2)) ≤ z.1 := by exact_mod_cast b1
  have c2 : (z.1 : ℝ) ≤ 2 * h - 2 := by exact_mod_cast b2
  have c3 : (-(2 * (h : ℝ) - 2)) ≤ z.2 := by exact_mod_cast b3
  have c4 : (z.2 : ℝ) ≤ 2 * h - 2 := by exact_mod_cast b4
  simp only [l37c] at a1 a2 a3 a4
  push_cast at a1 a2 a3 a4
  simp only [DyBox.largeBox, DyBox.center, hside, mem_ofPred_eq, abs_le]
  refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- Sites with `‖z‖_∞ ≥ h + 2` give boxes disjoint from `B`. -/
lemma disjoint_siteBox (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) {z : ℤ × ℤ}
    (hz : InGrid (B.n + k) (l37c B h) z) {d : PercDir}
    (hd : (h : ℤ) + 2 ≤ annDir d z) :
    Disjoint (interior (siteBox (B.n + k) (l37c B h) z).closedBox) B.closedBox := by
  refine Disjoint.mono_left interior_subset (Set.disjoint_left.2 fun w hw hwB => ?_)
  obtain ⟨a1, a2, a3, a4⟩ := hw
  obtain ⟨d1, d2, d3, d4⟩ := hwB
  rw [siteBox_j_real hz] at a1 a2
  rw [siteBox_k_real hz] at a3 a4
  have e : (siteBox (B.n + k) (l37c B h) z).side = (2 : ℝ)⁻¹ ^ (B.n + k) := rfl
  rw [e] at a1 a2 a3 a4
  set s := (2 : ℝ)⁻¹ ^ (B.n + k)
  have hs0 : 0 < s := by positivity
  have hside : B.side = 2 * h * s := by
    have h1 := side_mul_pow B hK
    have h2 := pow_inv_mul_pow (B.n + k)
    calc B.side = B.side * ((2 : ℝ)⁻¹ ^ (B.n + k) * 2 ^ (B.n + k)) := by rw [h2, mul_one]
      _ = 2 * h * s := by rw [mul_comm ((2 : ℝ)⁻¹ ^ (B.n + k)), ← mul_assoc, h1]
  rw [hside] at d1 d2 d3 d4
  simp only [l37c] at a1 a2 a3 a4
  push_cast at a1 a2 a3 a4
  cases d <;> simp only [annDir] at hd
  · have : (h : ℝ) + 2 ≤ z.2 := by exact_mod_cast hd
    nlinarith
  · have : (h : ℝ) + 2 ≤ -z.2 := by exact_mod_cast hd
    nlinarith
  · have : (h : ℝ) + 2 ≤ z.1 := by exact_mod_cast hd
    nlinarith
  · have : (h : ℝ) + 2 ≤ -z.1 := by exact_mod_cast hd
    nlinarith

end DZZ
end LQGMetric
