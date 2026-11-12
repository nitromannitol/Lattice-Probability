/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes56Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes56Diam
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Pigeonhole

/-!
# GM Lemma 5.6: the deterministic geometry, as a statement, and the square count (task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6 (l. 2959–2995).

* (removed, see D69) `L56Geom`: the deterministic (planar) part of GM's proof, l. 2963–2968 and 2980–2994: given the
  half-annulus `H = H_r(z) ⊂ 𝔸_{αr,r}(z)`, the endpoints `u ∈ ∂B_{αr}(z)`, `v ∈ ∂B_r(z)` and the
  geodesic `T = P̃ ⊂ cl H` from `u` to `v`, the set `𝒦` of squares of `𝓢_{ε₁r}(B_{2r}(z))` meeting
  `P̃′ = π₋ ∪ L₋ ∪ P̃ ∪ L₊ ∪ π₊` gives a tube `V = int ⋃𝒦` which is connected, contains
  `z ± 2r` and `P̃`, satisfies condition 2 (separation, l. 2984–2989) and condition 3's deterministic
  part (l. 2991–2994: each point of `O_u` is reached from `u` through a bounded number of squares).
  GM's (5.17) bounds the internal diameters of the squares `S ∈ 𝓢_{ε₁r}`, with `D̃_h(·,·;S)` for the
  closed square `S`; a closed square of `𝒦` may meet `∂V`, where `D̃_h(·,·;S)` paths leave `V`.
  The statement therefore takes the bound at every dyadic level `2^{-j}ε₁r` (which DFGPS Lemma 3.20
  provides, `sqDiamEvent`), with a geometric factor `2^{-jχ}`, so that chains of dyadic squares
  inside `V` can be used (deviation P2-M2L3-2). It is an open node (own statement; GM's argument).
* `squareSet_ball_subset_box`: `𝓢_s(B_R(z))` lies in an explicit box of `L × L` indices with
  `L = ⌈2R/s⌉₊ + 1` (the count "the number of subsets of `𝓢_{ε₁r}(B_{2r}(z))` is bounded by a
  constant depending only on `ε₁`", l. 2975).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the tube `int ⋃_{m ∈ F} S_m` of a finite set of grid squares of side `s` -/
def tubeOf (s : ℝ) (F : Finset (ℤ × ℤ)) : Set ℂ := interior (⋃ m ∈ F, gridSquare s m)

/-! The former node `L56Geom` (open ball `𝓢_{ε₁r}(B_{2r}(z))`, pointwise condition (2)) was false
(z = 2r: z − 2r is a grid corner and not in the tube; P2-M2L4) and is replaced by `L56GeomN`
(`SepMeas56.lean`: closed ball, robust condition (2) `SepNear`; decision D69, decisions/DEC-SEP.md). -/

/-- the side length of the index box -/
def boxLen (s R : ℝ) : ℕ := ⌈2 * R / s⌉₊ + 1

/-- the index box containing `𝓢_s(B_R(z))` -/
def sqBox (s R : ℝ) (z : ℂ) : Finset (ℤ × ℤ) :=
  Finset.Ico ⌊(z.re - R) / s⌋ (⌊(z.re - R) / s⌋ + boxLen s R) ×ˢ
    Finset.Ico ⌊(z.im - R) / s⌋ (⌊(z.im - R) / s⌋ + boxLen s R)

lemma card_sqBox (s R : ℝ) (z : ℂ) : (sqBox s R z).card = boxLen s R * boxLen s R := by
  simp [sqBox, Finset.card_product]

/-- one coordinate: `m s ≤ x ≤ (m+1) s` and `|x − c| < R` force `m ∈ [⌊(c−R)/s⌋, ⌊(c−R)/s⌋ + L)` -/
lemma mem_Ico_of_coord {s R c x : ℝ} (hs : 0 < s) {m : ℤ} (h1 : m * s ≤ x) (h2 : x ≤ (m + 1) * s)
    (hx : |x - c| < R) : m ∈ Finset.Ico ⌊(c - R) / s⌋ (⌊(c - R) / s⌋ + boxLen s R) := by
  rw [abs_lt] at hx
  have f1 := Int.floor_le ((c - R) / s)
  have f2 := Int.lt_floor_add_one ((c - R) / s)
  have hc := Nat.le_ceil (2 * R / s)
  have a1 : (c - R) / s < m + 1 := by rw [div_lt_iff₀ hs]; linarith
  have a2 : (m : ℝ) < (c + R) / s := by rw [lt_div_iff₀ hs]; linarith
  have a3 : (c + R) / s = (c - R) / s + 2 * R / s := by field_simp; ring
  rw [Finset.mem_Ico]
  constructor
  · have : (⌊(c - R) / s⌋ : ℝ) < m + 1 := lt_of_le_of_lt f1 a1
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
  · have : (m : ℝ) < ⌊(c - R) / s⌋ + boxLen s R := by
      simp only [boxLen]; push_cast; linarith
    exact_mod_cast this

lemma squareSet_ball_subset_box {s : ℝ} (hs : 0 < s) (R : ℝ) (z : ℂ) :
    squareSet s (ball z R) ⊆ ↑(sqBox s R z) := by
  rintro m ⟨x, ⟨h1, h2, h3, h4⟩, hx⟩
  have hx' : ‖x - z‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hx
  have hre : |x.re - z.re| < R := lt_of_le_of_lt (by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hx'
  have him : |x.im - z.im| < R := lt_of_le_of_lt (by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hx'
  simp only [sqBox, Finset.coe_product, mem_prod, Finset.mem_coe]
  exact ⟨mem_Ico_of_coord hs h1 h2 hre, mem_Ico_of_coord hs h3 h4 him⟩

end LQGMetric.GM
