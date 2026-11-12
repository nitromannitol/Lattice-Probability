/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Junc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Sep

/-!
# GM Lemma 5.8: the junction of a path with `V_{ρr}(z)` (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 3, condition 2 (l. 3120–3126), with the routing of decision D69: the paths `L_k`,
`L̂_x` arrive at `z − 2ρr` horizontally from the left.

`junction_left`: let `V = int ⋃_{m ∈ F} S_m` with squares `S_m` (side `s`) meeting `cl B_{2R}(z)`
and `a = z − 2R ∈ V`. If `p` lies in a square `S_j` meeting the horizontal half-line
`{w : Im w = Im a, Re w ≤ Re a}`, then every `q ∈ V` with `|p − q| < s` has its component of
`V ∖ B_{1.7R}(z)` within distance `< s` of that of `a` (`CompNear`). This is the hypothesis `hAX` of
`geom58_perZ` / `L58Junction` (D69: "the junction squares touch only the component of `z ∓ 2ρr`").
Own elementary argument (GM leave the step implicit): every square containing `a` is in `F`; the
square `S_{m'} ∋ q` touches the square `S_{(⌊Re a/s⌋, j₂)} ∋ a`; points of the two open squares
near the common corner are at distance `≤ 2s/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

/-- the open square `(m₁ s, (m₁+1) s) × (m₂ s, (m₂+1) s)` -/
def openSq (s : ℝ) (m : ℤ × ℤ) : Set ℂ :=
  {x | m.1 * s < x.re ∧ x.re < (m.1 + 1) * s ∧ m.2 * s < x.im ∧ x.im < (m.2 + 1) * s}

lemma openSq_subset (s : ℝ) (m : ℤ × ℤ) : openSq s m ⊆ gridSquare s m :=
  fun _ hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩

lemma isOpen_openSq (s : ℝ) (m : ℤ × ℤ) : IsOpen (openSq s m) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)))

lemma convex_openSq (s : ℝ) (m : ℤ × ℤ) : Convex ℝ (openSq s m) :=
  (convex_halfSpace_gt Complex.reLm.isLinear _).inter
    ((convex_halfSpace_lt Complex.reLm.isLinear _).inter
    ((convex_halfSpace_gt Complex.imLm.isLinear _).inter
    (convex_halfSpace_lt Complex.imLm.isLinear _)))

lemma norm_le_of_re_im {w : ℂ} {A B : ℝ} (h1 : |w.re| ≤ A) (h2 : |w.im| ≤ B) : ‖w‖ ≤ A + B :=
  (Complex.norm_le_abs_re_add_abs_im w).trans (add_le_add h1 h2)

/-- points of the open square near a point of the closed square -/
lemma exists_openSq_near {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ} {w : ℂ} (hw : w ∈ gridSquare s m)
    {η : ℝ} (hη : 0 < η) : ∃ v ∈ openSq s m, dist v w < η := by
  set t : ℝ := min 1 (η / (4 * s))
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ η / (4 * s) := min_le_right _ _
  obtain ⟨a1, a2, a3, a4⟩ := hw
  refine ⟨⟨w.re + t * ((m.1 + 1 / 2) * s - w.re), w.im + t * ((m.2 + 1 / 2) * s - w.im)⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a1), mul_pos ht hs]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a2), mul_pos ht hs]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a3), mul_pos ht hs]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a4), mul_pos ht hs]
  · rw [dist_eq_norm]
    have hts : t * s ≤ η / 4 := by
      calc t * s ≤ η / (4 * s) * s := mul_le_mul_of_nonneg_right ht2 hs.le
        _ = η / 4 := by field_simp
    refine lt_of_le_of_lt (norm_le_of_re_im (A := t * s) (B := t * s) ?_ ?_) (by linarith)
    · simp only [Complex.sub_re, add_sub_cancel_left]
      rw [abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by nlinarith, by nlinarith⟩) ht.le
    · simp only [Complex.sub_im, add_sub_cancel_left]
      rw [abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by nlinarith, by nlinarith⟩) ht.le

/-- a point of an open square lies in no other closed square -/
lemma eq_of_openSq {s : ℝ} (hs : 0 < s) {k m : ℤ × ℤ} {v : ℂ} (hk : v ∈ openSq s k)
    (hm : v ∈ gridSquare s m) : m = k := by
  obtain ⟨b1, b2, b3, b4⟩ := hk
  obtain ⟨c1, c2, c3, c4⟩ := hm
  have h1 : (k.1 : ℝ) < m.1 + 1 := lt_of_mul_lt_mul_right (by linarith) hs.le
  have h2 : (m.1 : ℝ) < k.1 + 1 := lt_of_mul_lt_mul_right (by linarith) hs.le
  have h3 : (k.2 : ℝ) < m.2 + 1 := lt_of_mul_lt_mul_right (by linarith) hs.le
  have h4 : (m.2 : ℝ) < k.2 + 1 := lt_of_mul_lt_mul_right (by linarith) hs.le
  have e1 : k.1 < m.1 + 1 := by exact_mod_cast h1
  have e2 : m.1 < k.1 + 1 := by exact_mod_cast h2
  have e3 : k.2 < m.2 + 1 := by exact_mod_cast h3
  have e4 : m.2 < k.2 + 1 := by exact_mod_cast h4
  exact Prod.ext (by omega) (by omega)

/-- every square containing an interior point of a finite union of squares belongs to it -/
lemma mem_of_mem_interior_squares {F : Finset (ℤ × ℤ)} {s : ℝ} (hs : 0 < s) {a : ℂ}
    (ha : a ∈ interior (⋃ m ∈ F, gridSquare s m)) {k : ℤ × ℤ} (hk : a ∈ gridSquare s k) :
    k ∈ F := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  obtain ⟨v, hvo, hvd⟩ := exists_openSq_near hs hk hε
  have hv : v ∈ ⋃ m ∈ F, gridSquare s m := interior_subset (hεU (mem_ball.2 hvd))
  rw [mem_iUnion₂] at hv
  obtain ⟨m, hm, hvm⟩ := hv
  rwa [← eq_of_openSq hs hvo hvm]

lemma openSq_subset_interior {F : Finset (ℤ × ℤ)} {s : ℝ} {m : ℤ × ℤ} (hm : m ∈ F) :
    openSq s m ⊆ interior (⋃ m ∈ F, gridSquare s m) :=
  interior_maximal (fun v hv => mem_iUnion₂.2 ⟨m, hm, openSq_subset s m hv⟩) (isOpen_openSq s m)

/-- a point `w` of the closed square `S_m ⊆ cl W` lies in the component of `W ∖ B` of the open
square, if `B` is far from `w` -/
lemma openSq_subset_comp {W B : Set ℂ} (hW : IsOpen W) {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ}
    (hSW : openSq s m ⊆ W) {w : ℂ} (hw : w ∈ gridSquare s m) (hwW : w ∈ W)
    (hfar : ∀ v, dist v w < 2 * s → v ∉ B) : openSq s m ⊆ connectedComponentIn (W \ B) w := by
  obtain ⟨η, hη, hηW⟩ := Metric.isOpen_iff.1 hW w hwW
  have hη' : 0 < min η s := lt_min hη hs
  obtain ⟨v, hvo, hvd⟩ := exists_openSq_near hs hw hη'
  have hC : IsPreconnected (ball w (min η s) ∪ openSq s m) :=
    IsPreconnected.union' ⟨v, mem_ball.2 hvd, hvo⟩ (convex_ball w _).isPreconnected
      (convex_openSq s m).isPreconnected
  have hCsub : ball w (min η s) ∪ openSq s m ⊆ W \ B := by
    rintro u (hu | hu)
    · rw [mem_ball] at hu
      exact ⟨hηW (mem_ball.2 (lt_of_lt_of_le hu (min_le_left _ _))),
        hfar u (by linarith [min_le_right η s])⟩
    · refine ⟨hSW hu, hfar u ?_⟩
      obtain ⟨a1, a2, a3, a4⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hu
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      rw [Complex.sub_re, Complex.sub_im]
      have h1 : |u.re - w.re| < s := abs_lt.2 ⟨by nlinarith, by nlinarith⟩
      have h2 : |u.im - w.im| < s := abs_lt.2 ⟨by nlinarith, by nlinarith⟩
      linarith
  exact fun u hu => hC.subset_connectedComponentIn (Or.inl (mem_ball_self hη')) hCsub (Or.inr hu)

/-- the point of `S_m` two thirds of the way from its centre to the grid point `g s` -/
def jPt (s : ℝ) (m g : ℤ × ℤ) : ℂ :=
  ⟨((m.1 + 1 / 2) * s + 2 * (g.1 * s)) / 3, ((m.2 + 1 / 2) * s + 2 * (g.2 * s)) / 3⟩

lemma jPt_mem {s : ℝ} (hs : 0 < s) {m g : ℤ × ℤ} (h1 : m.1 ≤ g.1) (h2 : g.1 ≤ m.1 + 1)
    (h3 : m.2 ≤ g.2) (h4 : g.2 ≤ m.2 + 1) : jPt s m g ∈ openSq s m := by
  have r1 : (m.1 : ℝ) ≤ g.1 := by exact_mod_cast h1
  have r2 : (g.1 : ℝ) ≤ m.1 + 1 := by exact_mod_cast h2
  have r3 : (m.2 : ℝ) ≤ g.2 := by exact_mod_cast h3
  have r4 : (g.2 : ℝ) ≤ m.2 + 1 := by exact_mod_cast h4
  simp only [jPt, openSq, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma dist_jPt_lt {s : ℝ} (hs : 0 < s) {m m₀ g : ℤ × ℤ} (h1 : m.1 ≤ m₀.1 + 1)
    (h2 : m₀.1 ≤ m.1 + 1) (h3 : m.2 ≤ m₀.2 + 1) (h4 : m₀.2 ≤ m.2 + 1) :
    dist (jPt s m g) (jPt s m₀ g) < s := by
  have r1 : (m.1 : ℝ) ≤ m₀.1 + 1 := by exact_mod_cast h1
  have r2 : (m₀.1 : ℝ) ≤ m.1 + 1 := by exact_mod_cast h2
  have r3 : (m.2 : ℝ) ≤ m₀.2 + 1 := by exact_mod_cast h3
  have r4 : (m₀.2 : ℝ) ≤ m.2 + 1 := by exact_mod_cast h4
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_le_of_re_im (A := s / 3) (B := s / 3) ?_ ?_) (by linarith)
  · simp only [jPt, Complex.sub_re]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · simp only [jPt, Complex.sub_im]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- **the left junction** (GM l. 3120–3126 with D69's horizontal routing); see the module
docstring -/
theorem junction_left {F : Finset (ℤ × ℤ)} {s R : ℝ} {z : ℂ} (hs : 0 < s) (hsR : 100 * s ≤ R)
    (hF : (↑F : Set (ℤ × ℤ)) ⊆ squareSet s (closedBall z (2 * R)))
    (ha : z - 2 * (R : ℂ) ∈ interior (⋃ m ∈ F, gridSquare s m))
    {j : ℤ × ℤ} (hj1 : (j.1 : ℝ) * s ≤ z.re - 2 * R) (hj2 : (j.2 : ℝ) * s ≤ z.im)
    (hj3 : z.im ≤ (j.2 + 1) * s) {p q : ℂ} (hp : p ∈ gridSquare s j)
    (hq : q ∈ interior (⋃ m ∈ F, gridSquare s m)) (hpq : dist p q < s) :
    CompNear (interior (⋃ m ∈ F, gridSquare s m) \ ball z (17 / 10 * R)) s q
      (z - 2 * (R : ℂ)) := by
  have hR : 0 < R := by linarith
  have hare : (z - 2 * (R : ℂ)).re = z.re - 2 * R := by simp
  have haim : (z - 2 * (R : ℂ)).im = z.im := by simp
  have hqU := interior_subset hq
  rw [mem_iUnion₂] at hqU
  obtain ⟨m', hm'F, hqm'⟩ := hqU
  obtain ⟨w, hwS, hwB⟩ := hF hm'F
  have hwre : z.re - 2 * R ≤ w.re := by
    have h1 := Complex.abs_re_le_norm (w - z)
    rw [mem_closedBall, dist_eq_norm] at hwB
    rw [Complex.sub_re, abs_le] at h1
    linarith [h1.1]
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hqm'
  obtain ⟨w1, w2, w3, w4⟩ := hwS
  rw [dist_eq_norm] at hpq
  have hre := Complex.abs_re_le_norm (p - q)
  have him := Complex.abs_im_le_norm (p - q)
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  set c0 : ℤ := ⌊(z.re - 2 * R) / s⌋ with hc0def
  have hc0 : (c0 : ℝ) * s ≤ z.re - 2 * R := by
    have := Int.floor_le ((z.re - 2 * R) / s); rwa [le_div_iff₀ hs] at this
  have hc0' : z.re - 2 * R < (c0 + 1) * s := by
    have := Int.lt_floor_add_one ((z.re - 2 * R) / s); rwa [div_lt_iff₀ hs] at this
  -- index bounds
  have i1 : m'.1 ≤ j.1 + 1 := by
    have : (m'.1 : ℝ) < j.1 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : m'.1 < j.1 + 2 := by exact_mod_cast this
    omega
  have i1' : m'.1 ≤ c0 + 1 := by
    have e : (m'.1 : ℝ) ≤ j.1 + 1 := by exact_mod_cast i1
    have : (m'.1 : ℝ) < c0 + 2 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
    have : m'.1 < c0 + 2 := by exact_mod_cast this
    omega
  have i2 : c0 ≤ m'.1 + 1 := by
    have : (c0 : ℝ) ≤ m'.1 + 1 := le_of_mul_le_mul_right (by linarith) hs
    exact_mod_cast this
  have i3 : m'.2 ≤ j.2 + 1 := by
    have : (m'.2 : ℝ) < j.2 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : m'.2 < j.2 + 2 := by exact_mod_cast this
    omega
  have i4 : j.2 ≤ m'.2 + 1 := by
    have : (j.2 : ℝ) < m'.2 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : j.2 < m'.2 + 2 := by exact_mod_cast this
    omega
  -- the square of `a`
  have haS : z - 2 * (R : ℂ) ∈ gridSquare s (c0, j.2) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hare, haim] <;> push_cast <;> linarith
  have hm0F : (c0, j.2) ∈ F := mem_of_mem_interior_squares hs ha haS
  -- distances to `z`
  have r1 : (m'.1 : ℝ) ≤ c0 + 1 := by exact_mod_cast i1'
  have r2 : (c0 : ℝ) ≤ m'.1 + 1 := by exact_mod_cast i2
  have r3 : (m'.2 : ℝ) ≤ j.2 + 1 := by exact_mod_cast i3
  have r4 : (j.2 : ℝ) ≤ m'.2 + 1 := by exact_mod_cast i4
  have hqa : ‖q - (z - 2 * (R : ℂ))‖ ≤ 4 * s := by
    refine (norm_le_of_re_im (A := 2 * s) (B := 2 * s) ?_ ?_).trans (by linarith)
    · rw [Complex.sub_re, hare]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
    · rw [Complex.sub_im, haim]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have haz : ‖z - 2 * (R : ℂ) - z‖ = 2 * R := by
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    norm_num
  have hfar : ∀ c : ℂ, ‖c - (z - 2 * (R : ℂ))‖ ≤ 4 * s → ∀ v, dist v c < 2 * s →
      v ∉ ball z (17 / 10 * R) := by
    intro c hc v hv hvB
    rw [mem_ball, dist_eq_norm] at hvB; rw [dist_eq_norm] at hv
    have h6 : ‖z - 2 * (R : ℂ) - z‖ ≤ ‖z - 2 * (R : ℂ) - c‖ + ‖c - v‖ + ‖v - z‖ := by
      calc ‖z - 2 * (R : ℂ) - z‖ ≤ ‖z - 2 * (R : ℂ) - v‖ + ‖v - z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖z - 2 * (R : ℂ) - c‖ + ‖c - v‖ + ‖v - z‖ := by
            gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (z - 2 * (R : ℂ)) c, norm_sub_rev c v, haz] at h6
    linarith
  set g : ℤ × ℤ := (max m'.1 c0, max m'.2 j.2)
  refine ⟨jPt s m' g, ?_, jPt s (c0, j.2) g, ?_, dist_jPt_lt hs i1' i2 i3 i4⟩
  · exact openSq_subset_comp isOpen_interior hs (openSq_subset_interior hm'F) ⟨q1, q2, q3, q4⟩ hq
      (hfar q hqa) (jPt_mem hs (le_max_left _ _) (max_le (by omega) (by omega)) (le_max_left _ _)
        (max_le (by omega) (by omega)))
  · exact openSq_subset_comp isOpen_interior hs (openSq_subset_interior hm0F) haS ha
      (hfar _ (by rw [sub_self, norm_zero]; positivity))
      (jPt_mem hs (le_max_right _ _) (max_le (by omega) (by omega)) (le_max_right _ _)
        (max_le (by omega) (by omega)))

/-- **the right junction**: the mirror image of `junction_left` at `z + 2R`, for squares meeting
the horizontal half-line to the right of `z + 2R` -/
theorem junction_right {F : Finset (ℤ × ℤ)} {s R : ℝ} {z : ℂ} (hs : 0 < s) (hsR : 100 * s ≤ R)
    (hF : (↑F : Set (ℤ × ℤ)) ⊆ squareSet s (closedBall z (2 * R)))
    (ha : z + 2 * (R : ℂ) ∈ interior (⋃ m ∈ F, gridSquare s m))
    {j : ℤ × ℤ} (hj1 : z.re + 2 * R ≤ (j.1 + 1) * s) (hj2 : (j.2 : ℝ) * s ≤ z.im)
    (hj3 : z.im ≤ (j.2 + 1) * s) {p q : ℂ} (hp : p ∈ gridSquare s j)
    (hq : q ∈ interior (⋃ m ∈ F, gridSquare s m)) (hpq : dist p q < s) :
    CompNear (interior (⋃ m ∈ F, gridSquare s m) \ ball z (17 / 10 * R)) s q
      (z + 2 * (R : ℂ)) := by
  have hR : 0 < R := by linarith
  have hare : (z + 2 * (R : ℂ)).re = z.re + 2 * R := by simp
  have haim : (z + 2 * (R : ℂ)).im = z.im := by simp
  have hqU := interior_subset hq
  rw [mem_iUnion₂] at hqU
  obtain ⟨m', hm'F, hqm'⟩ := hqU
  obtain ⟨w, hwS, hwB⟩ := hF hm'F
  have hwre : w.re ≤ z.re + 2 * R := by
    have h1 := Complex.abs_re_le_norm (w - z)
    rw [mem_closedBall, dist_eq_norm] at hwB
    rw [Complex.sub_re, abs_le] at h1
    linarith [h1.2]
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hqm'
  obtain ⟨w1, w2, w3, w4⟩ := hwS
  rw [dist_eq_norm] at hpq
  have hre := Complex.abs_re_le_norm (p - q)
  have him := Complex.abs_im_le_norm (p - q)
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  set c0 : ℤ := ⌈(z.re + 2 * R) / s⌉ - 1 with hc0def
  have hc0r : (c0 : ℝ) = ⌈(z.re + 2 * R) / s⌉ - 1 := by rw [hc0def]; push_cast; ring
  have hc0 : (c0 : ℝ) * s < z.re + 2 * R := by
    rw [← lt_div_iff₀ hs, hc0r]; linarith [Int.ceil_lt_add_one ((z.re + 2 * R) / s)]
  have hc0' : z.re + 2 * R ≤ (c0 + 1) * s := by
    rw [← div_le_iff₀ hs, hc0r]; linarith [Int.le_ceil ((z.re + 2 * R) / s)]
  -- index bounds
  have i1 : j.1 ≤ m'.1 + 1 := by
    have : (j.1 : ℝ) < m'.1 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : j.1 < m'.1 + 2 := by exact_mod_cast this
    omega
  have i2 : c0 ≤ m'.1 + 1 := by
    have e : (j.1 : ℝ) ≤ m'.1 + 1 := by exact_mod_cast i1
    have : (c0 : ℝ) < m'.1 + 2 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
    have : c0 < m'.1 + 2 := by exact_mod_cast this
    omega
  have i1' : m'.1 ≤ c0 + 1 := by
    have : (m'.1 : ℝ) ≤ c0 + 1 := le_of_mul_le_mul_right (by linarith) hs
    exact_mod_cast this
  have i3 : m'.2 ≤ j.2 + 1 := by
    have : (m'.2 : ℝ) < j.2 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : m'.2 < j.2 + 2 := by exact_mod_cast this
    omega
  have i4 : j.2 ≤ m'.2 + 1 := by
    have : (j.2 : ℝ) < m'.2 + 2 := lt_of_mul_lt_mul_right (by linarith) hs.le
    have : j.2 < m'.2 + 2 := by exact_mod_cast this
    omega
  -- the square of `a`
  have haS : z + 2 * (R : ℂ) ∈ gridSquare s (c0, j.2) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hare, haim] <;> push_cast <;> linarith
  have hm0F : (c0, j.2) ∈ F := mem_of_mem_interior_squares hs ha haS
  -- distances to `z`
  have r1 : (m'.1 : ℝ) ≤ c0 + 1 := by exact_mod_cast i1'
  have r2 : (c0 : ℝ) ≤ m'.1 + 1 := by exact_mod_cast i2
  have r3 : (m'.2 : ℝ) ≤ j.2 + 1 := by exact_mod_cast i3
  have r4 : (j.2 : ℝ) ≤ m'.2 + 1 := by exact_mod_cast i4
  have hqa : ‖q - (z + 2 * (R : ℂ))‖ ≤ 4 * s := by
    refine (norm_le_of_re_im (A := 2 * s) (B := 2 * s) ?_ ?_).trans (by linarith)
    · rw [Complex.sub_re, hare]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
    · rw [Complex.sub_im, haim]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have haz : ‖z + 2 * (R : ℂ) - z‖ = 2 * R := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    norm_num
  have hfar : ∀ c : ℂ, ‖c - (z + 2 * (R : ℂ))‖ ≤ 4 * s → ∀ v, dist v c < 2 * s →
      v ∉ ball z (17 / 10 * R) := by
    intro c hc v hv hvB
    rw [mem_ball, dist_eq_norm] at hvB; rw [dist_eq_norm] at hv
    have h6 : ‖z + 2 * (R : ℂ) - z‖ ≤ ‖z + 2 * (R : ℂ) - c‖ + ‖c - v‖ + ‖v - z‖ := by
      calc ‖z + 2 * (R : ℂ) - z‖ ≤ ‖z + 2 * (R : ℂ) - v‖ + ‖v - z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖z + 2 * (R : ℂ) - c‖ + ‖c - v‖ + ‖v - z‖ := by
            gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (z + 2 * (R : ℂ)) c, norm_sub_rev c v, haz] at h6
    linarith
  set g : ℤ × ℤ := (max m'.1 c0, max m'.2 j.2)
  refine ⟨jPt s m' g, ?_, jPt s (c0, j.2) g, ?_, dist_jPt_lt hs i1' i2 i3 i4⟩
  · exact openSq_subset_comp isOpen_interior hs (openSq_subset_interior hm'F) ⟨q1, q2, q3, q4⟩ hq
      (hfar q hqa) (jPt_mem hs (le_max_left _ _) (max_le (by omega) (by omega)) (le_max_left _ _)
        (max_le (by omega) (by omega)))
  · exact openSq_subset_comp isOpen_interior hs (openSq_subset_interior hm0F) haS ha
      (hfar _ (by rw [sub_self, norm_zero]; positivity))
      (jPt_mem hs (le_max_right _ _) (max_le (by omega) (by omega)) (le_max_right _ _)
        (max_le (by omega) (by omega)))

end LQGMetric.GM
