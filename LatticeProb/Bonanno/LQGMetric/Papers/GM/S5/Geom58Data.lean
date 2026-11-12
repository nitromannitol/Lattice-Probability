/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Data at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Asm

/-!
# GM Lemma 5.8: the data of Step 2 and the chains of tubes and paths (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3079–3092) and Step 3 (l. 3110–3126).

`L58Data`: the tubes `V_j = int ⋃_{F_j} S` around `z_j` (`j < m`), the paths `P_i` (`i ≤ m`), and
the square sets `Q_i` of the paths, with the properties provided by `TubeProps` and `L58Paths`.
`U = int ⋃_{G} S`, `G = ⋃_j F_j ∪ ⋃_i Q_i` (GM (5.24)). `chain_left`/`chain_right`: GM's
`W_k(x)`, `W_k(y)` are joined to `z_k ∓ 2R` in `U ∖ B` ("since the `V_r(z_k)`'s are connected").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

/-- the data of GM Lemma 5.8, Step 2, for one pair `x, y` -/
structure L58Data where
  s : ℝ
  R : ℝ
  m : ℕ
  zs : ℕ → ℂ
  P : ℕ → Set ℂ
  F : ℕ → Finset (ℤ × ℤ)
  Q : ℕ → Finset (ℤ × ℤ)
  hs : 0 < s
  hsR : 100 * s ≤ R
  zsep : ∀ j < m, ∀ j' < m, j ≠ j' → 8 * R ≤ dist (zs j) (zs j')
  hF : ∀ j < m, (↑(F j) : Set (ℤ × ℤ)) ⊆ squareSet s (closedBall (zs j) (2 * R))
  hFl : ∀ j < m, zs j - 2 * (R : ℂ) ∈ interior (⋃ g ∈ F j, gridSquare s g)
  hFr : ∀ j < m, zs j + 2 * (R : ℂ) ∈ interior (⋃ g ∈ F j, gridSquare s g)
  hFc : ∀ j < m, IsPreconnected (interior (⋃ g ∈ F j, gridSquare s g))
  hQ : ∀ i ≤ m, ∀ g, g ∈ Q i ↔ (gridSquare s g ∩ P i).Nonempty
  hPc : ∀ i ≤ m, IsPreconnected (P i)
  hPl : ∀ j < m, zs j - 2 * (R : ℂ) ∈ P j
  hPr : ∀ j < m, zs j + 2 * (R : ℂ) ∈ P (j + 1)
  hPsep : ∀ i ≤ m, ∀ i' ≤ m, i ≠ i' → ∀ p ∈ P i, ∀ q ∈ P i', R ≤ dist p q
  hPstub : ∀ i ≤ m, ∀ j < m, ∀ p ∈ P i, dist p (zs j) < 3 * R →
    (i = j ∧ p.im = (zs j).im ∧ p.re ≤ (zs j).re - 2 * R) ∨
    (i = j + 1 ∧ p.im = (zs j).im ∧ (zs j).re + 2 * R ≤ p.re)

namespace L58Data

variable (D : L58Data)

/-- the tube `V_j` -/
def Vs (j : ℕ) : Set ℂ := interior (⋃ g ∈ D.F j, gridSquare D.s g)

/-- the squares of `U` -/
def G : Finset (ℤ × ℤ) :=
  (Finset.range D.m).biUnion D.F ∪ (Finset.range (D.m + 1)).biUnion D.Q

/-- `U_r^{x,y}` of GM (5.24) -/
def U : Set ℂ := interior (⋃ g ∈ D.G, gridSquare D.s g)

lemma hR : 0 < D.R := by have := D.hs; have := D.hsR; linarith

lemma isOpen_U : IsOpen D.U := isOpen_interior

lemma Vs_subset_U {j : ℕ} (hj : j < D.m) : D.Vs j ⊆ D.U := by
  refine interior_mono (fun w hw => ?_)
  rw [mem_iUnion₂] at hw ⊢
  obtain ⟨g, hg, hwg⟩ := hw
  exact ⟨g, Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hg⟩), hwg⟩

lemma P_subset_U {i : ℕ} (hi : i ≤ D.m) : D.P i ⊆ D.U := by
  refine (subset_interior_squares D.hs (Q := ↑D.G) (fun g hg => ?_)).trans
    (interior_mono (fun w hw => ?_))
  · exact Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), (D.hQ i hi g).2 hg⟩))
  · rw [mem_iUnion₂] at hw ⊢
    obtain ⟨g, hg, hwg⟩ := hw
    exact ⟨g, Finset.mem_coe.1 hg, hwg⟩

/-- the paths stay at distance `≥ 2R` from the centres `z_j` -/
lemma P_far {i : ℕ} (hi : i ≤ D.m) {j : ℕ} (hj : j < D.m) {p : ℂ} (hp : p ∈ D.P i) :
    2 * D.R ≤ dist p (D.zs j) := by
  by_contra hlt
  push Not at hlt
  have hR := D.hR
  have h1 := Complex.abs_re_le_norm (p - D.zs j)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  rcases D.hPstub i hi j hj p hp (by linarith) with ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [abs_le] at h1; linarith [h1.1]
  · rw [abs_le] at h1; linarith [h1.2]

/-- points of a square are within `2s` of each other -/
lemma dist_le_of_mem_sq {s : ℝ} {g : ℤ × ℤ} {p c : ℂ} (hp : p ∈ gridSquare s g)
    (hc : c ∈ gridSquare s g) : dist p c ≤ 2 * s := by
  obtain ⟨a1, a2, a3, a4⟩ := hp
  obtain ⟨b1, b2, b3, b4⟩ := hc
  rw [dist_eq_norm]
  refine norm_le_of_re_im (A := s) (B := s) ?_ ?_ |>.trans (by linarith)
  · rw [Complex.sub_re]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [Complex.sub_im]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- the tubes lie in `B_{2R+2s}(z_j)` -/
lemma dist_le_of_F {j : ℕ} (hj : j < D.m) {g : ℤ × ℤ} (hg : g ∈ D.F j) {p : ℂ}
    (hp : p ∈ gridSquare D.s g) : dist p (D.zs j) ≤ 2 * D.R + 2 * D.s := by
  obtain ⟨c, hcS, hcB⟩ := D.hF j hj hg
  rw [mem_closedBall] at hcB
  linarith [dist_triangle p c (D.zs j), dist_le_of_mem_sq hp hcS]

lemma Vs_subset_sq (j : ℕ) : D.Vs j ⊆ ⋃ g ∈ D.F j, gridSquare D.s g := interior_subset

lemma dist_le_of_Vs {j : ℕ} (hj : j < D.m) {p : ℂ} (hp : p ∈ D.Vs j) :
    dist p (D.zs j) ≤ 2 * D.R + 2 * D.s := by
  have := D.Vs_subset_sq j hp
  rw [mem_iUnion₂] at this
  obtain ⟨g, hg, hpg⟩ := this
  exact D.dist_le_of_F hj hg hpg

/-- a preconnected set meeting a component lies in it -/
lemma subset_comp {W A : Set ℂ} {t a : ℂ} (hA : IsPreconnected A) (hAW : A ⊆ W) (ha : a ∈ A)
    (hat : a ∈ connectedComponentIn W t) : A ⊆ connectedComponentIn W t := by
  rw [connectedComponentIn_eq hat]
  exact hA.subset_connectedComponentIn ha hAW

/-- **the `x`-side chain**: `P_0, V_0, …, V_{k−1}, P_k` lie in the component of `z_k − 2R` in
`U ∖ B` -/
lemma chain_left {B : Set ℂ} {k : ℕ} (hk : k < D.m)
    (hPB : ∀ i ≤ D.m, Disjoint (D.P i) B) (hVB : ∀ j < k, Disjoint (D.Vs j) B) :
    ∀ d ≤ k, D.P (k - d) ⊆ connectedComponentIn (D.U \ B) (D.zs k - 2 * (D.R : ℂ)) ∧
      ∀ j, k - d ≤ j → j < k →
        D.Vs j ⊆ connectedComponentIn (D.U \ B) (D.zs k - 2 * (D.R : ℂ)) := by
  have hPUB : ∀ i ≤ D.m, D.P i ⊆ D.U \ B := fun i hi w hw =>
    ⟨D.P_subset_U hi hw, Set.disjoint_left.1 (hPB i hi) hw⟩
  have hVUB : ∀ j < k, D.Vs j ⊆ D.U \ B := fun j hj w hw =>
    ⟨D.Vs_subset_U (hj.trans hk) hw, Set.disjoint_left.1 (hVB j hj) hw⟩
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨?_, fun j h1 h2 => absurd h2 (by omega)⟩
    simp only [Nat.sub_zero]
    exact (D.hPc k hk.le).subset_connectedComponentIn (D.hPl k hk) (hPUB k hk.le)
  | succ d ih =>
    intro hd
    obtain ⟨hP, hV⟩ := ih (by omega)
    set j := k - (d + 1) with hjdef
    have hj1 : j + 1 = k - d := by omega
    have hjm : j < D.m := by omega
    have hVj : D.Vs j ⊆ connectedComponentIn (D.U \ B) (D.zs k - 2 * (D.R : ℂ)) :=
      subset_comp (D.hFc j hjm) (hVUB j (by omega)) (D.hFr j hjm)
        (hP (by rw [← hj1]; exact D.hPr j hjm))
    refine ⟨subset_comp (D.hPc j hjm.le) (hPUB j hjm.le) (D.hPl j hjm) (hVj (D.hFl j hjm)), ?_⟩
    intro j' h1 h2
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hVj
    · exact hV j' (by omega) h2

/-- **the `y`-side chain**: `P_{k+1}, V_{k+1}, …, P_m` lie in the component of `z_k + 2R` in
`U ∖ B` -/
lemma chain_right {B : Set ℂ} {k : ℕ} (hk : k < D.m)
    (hPB : ∀ i ≤ D.m, Disjoint (D.P i) B) (hVB : ∀ j < D.m, k < j → Disjoint (D.Vs j) B) :
    ∀ d, k + 1 + d ≤ D.m →
      D.P (k + 1 + d) ⊆ connectedComponentIn (D.U \ B) (D.zs k + 2 * (D.R : ℂ)) ∧
      ∀ j, k < j → j < k + 1 + d →
        D.Vs j ⊆ connectedComponentIn (D.U \ B) (D.zs k + 2 * (D.R : ℂ)) := by
  have hPUB : ∀ i ≤ D.m, D.P i ⊆ D.U \ B := fun i hi w hw =>
    ⟨D.P_subset_U hi hw, Set.disjoint_left.1 (hPB i hi) hw⟩
  have hVUB : ∀ j < D.m, k < j → D.Vs j ⊆ D.U \ B := fun j hj hkj w hw =>
    ⟨D.Vs_subset_U hj hw, Set.disjoint_left.1 (hVB j hj hkj) hw⟩
  intro d
  induction d with
  | zero =>
    intro hd
    refine ⟨?_, fun j h1 h2 => absurd h2 (by omega)⟩
    exact (D.hPc (k + 1) hd).subset_connectedComponentIn (D.hPr k hk) (hPUB (k + 1) hd)
  | succ d ih =>
    intro hd
    obtain ⟨hP, hV⟩ := ih (by omega)
    set j := k + 1 + d with hjdef
    have hjm : j < D.m := by omega
    have hVj : D.Vs j ⊆ connectedComponentIn (D.U \ B) (D.zs k + 2 * (D.R : ℂ)) :=
      subset_comp (D.hFc j hjm) (hVUB j hjm (by omega)) (D.hFl j hjm) (hP (D.hPl j hjm))
    refine ⟨?_, ?_⟩
    · have e : k + 1 + (d + 1) = j + 1 := by omega
      rw [e]
      exact subset_comp (D.hPc (j + 1) (by omega)) (hPUB (j + 1) (by omega)) (D.hPr j hjm)
        (hVj (D.hFr j hjm))
    · intro j' h1 h2
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (show j' < j + 1 by omega)) with h | h
      · exact hV j' h1 h
      · rw [h]; exact hVj

end L58Data

end LQGMetric.GM
