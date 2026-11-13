/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Squares at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma34

/-!
# Squares, horizontal segments, connectedness along lines, and crossings along walks

Geometric inputs of GMS [18] Lemma 3.8 in a square-based form: the circles `∂B_{5(sr+t)}(z)` and the radial
segments of [18] are replaced by boundaries of axis-parallel squares and horizontal segments, so that the
only cell-topology input is **connectedness along lines** ([19] hypothesis 3, `[19]`):
The cells meeting a horizontal or vertical segment induce a connected sub-graph.

* `supNorm u = max |Re u| |Im u|`, `sqLoop z a = {u : supNorm (u − z) = a}` (the boundary of the square of
  half-side `a`), its four sides `sqSide`, `sqLoop_eq_iUnion_sqSide`, and the separation
  `abs_sub_le_dist_of_mem_sqLoop` (`dist(∂Q_a, ∂Q_b) ≥ |a − b|`);
* `hSeg z x₁ x₂ t`: the horizontal segment `{z + x + i t : x ∈ [x₁, x₂]}`, with
  `abs_sub_le_dist_of_mem_hSeg` (`dist ≥ |t − t'|`);
* `ConnectedAlongLines H` (CAL, a cell-topology property of the embedding, an explicit hypothesis of
  Lemma 3.8) and `reachable_sqLoop` (CAL makes the cells meeting a square loop a connected
  sub-graph: the four sides share their corners);
* `exists_crossing_of_walk`: along a walk of `G` (consecutive vertices equal or adjacent), if the first cell
  has a point with `φ ≤ t` and the last one a point with `φ ≥ t` (`φ` continuous), some cell of the walk
  meets `{φ = t}` (cells are connected and adjacent cells intersect).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

/-! ### The sup norm and square loops -/

/-- `max |Re u| |Im u|`. -/
def supNorm (u : ℂ) : ℝ := max |u.re| |u.im|

theorem continuous_supNorm : Continuous supNorm :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

theorem supNorm_nonneg (u : ℂ) : 0 ≤ supNorm u := le_max_of_le_left (abs_nonneg _)

theorem supNorm_le_norm (u : ℂ) : supNorm u ≤ ‖u‖ :=
  max_le (Complex.abs_re_le_norm u) (Complex.abs_im_le_norm u)

theorem norm_le_sqrt_two_mul_supNorm (u : ℂ) : ‖u‖ ≤ Real.sqrt 2 * supNorm u := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, show Real.sqrt 2 * supNorm u = Real.sqrt (2 * supNorm u ^ 2) by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (supNorm_nonneg u)]]
  refine Real.sqrt_le_sqrt ?_
  have h1 : u.re ^ 2 ≤ supNorm u ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have h2 : u.im ^ 2 ≤ supNorm u ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  linarith

theorem supNorm_sub_le (u v : ℂ) : |supNorm u - supNorm v| ≤ dist u v := by
  have hre : |u.re - v.re| ≤ ‖u - v‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have him : |u.im - v.im| ≤ ‖u - v‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [dist_eq_norm]
  unfold supNorm
  rw [abs_le]
  constructor
  · have := abs_sub_abs_le_abs_sub v.re u.re
    have := abs_sub_abs_le_abs_sub v.im u.im
    rw [abs_sub_comm] at hre him
    rcases le_total |u.re| |u.im| with h | h <;> rcases le_total |v.re| |v.im| with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;> linarith
  · have := abs_sub_abs_le_abs_sub u.re v.re
    have := abs_sub_abs_le_abs_sub u.im v.im
    rcases le_total |u.re| |u.im| with h | h <;> rcases le_total |v.re| |v.im| with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;> linarith

/-- The boundary of the square of half-side `a` centred at `z`. -/
def sqLoop (z : ℂ) (a : ℝ) : Set ℂ := {u | supNorm (u - z) = a}

/-- **Separation of square loops**: `dist(∂Q_a(z), ∂Q_b(z)) ≥ |a − b|`. -/
theorem abs_sub_le_dist_of_mem_sqLoop {z u v : ℂ} {a b : ℝ} (hu : u ∈ sqLoop z a)
    (hv : v ∈ sqLoop z b) : |a - b| ≤ dist u v := by
  rw [← hu, ← hv]
  have := supNorm_sub_le (u - z) (v - z)
  rwa [dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm] at this

/-- Points of a horizontal segment, by coordinates. -/
theorem mem_segment_horizontal {p : ℂ} {x₁ x₂ y : ℝ} (hx : x₁ ≤ x₂) :
    p ∈ segment ℝ (⟨x₁, y⟩ : ℂ) ⟨x₂, y⟩ ↔ p.im = y ∧ x₁ ≤ p.re ∧ p.re ≤ x₂ := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.sub_re,
      Complex.sub_im, smul_eq_mul, sub_self, mul_zero, add_zero]
    exact ⟨trivial, by nlinarith, by nlinarith⟩
  · rintro ⟨him, h1, h2⟩
    rcases eq_or_lt_of_le hx with heq | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul, zero_mul,
          add_zero]
        linarith
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul, zero_mul,
          add_zero]
        exact him.symm
    · refine ⟨(p.re - x₁) / (x₂ - x₁), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith)⟩, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
        field_simp
        ring
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul, sub_self, mul_zero,
          add_zero]
        exact him.symm

/-- Points of a vertical segment, by coordinates. -/
theorem mem_segment_vertical {p : ℂ} {x y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    p ∈ segment ℝ (⟨x, y₁⟩ : ℂ) ⟨x, y₂⟩ ↔ p.re = x ∧ y₁ ≤ p.im ∧ p.im ≤ y₂ := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.sub_re,
      Complex.sub_im, smul_eq_mul, sub_self, mul_zero, add_zero]
    exact ⟨trivial, by nlinarith, by nlinarith⟩
  · rintro ⟨hre, h1, h2⟩
    rcases eq_or_lt_of_le hy with heq | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul, zero_mul,
          add_zero]
        exact hre.symm
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul, zero_mul,
          add_zero]
        linarith
    · refine ⟨(p.im - y₁) / (y₂ - y₁), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith)⟩, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul, sub_self, mul_zero,
          add_zero]
        exact hre.symm
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
        field_simp
        ring

/-! ### Sides and corners of a square loop -/

/-- The four sides of the square of half-side `a` centred at `z` (`0, 1, 2, 3`: right, top, left,
bottom), as segments. -/
def sqSide (z : ℂ) (a : ℝ) : Fin 4 → Set ℂ
  | 0 => segment ℝ (⟨z.re + a, z.im - a⟩ : ℂ) ⟨z.re + a, z.im + a⟩
  | 1 => segment ℝ (⟨z.re - a, z.im + a⟩ : ℂ) ⟨z.re + a, z.im + a⟩
  | 2 => segment ℝ (⟨z.re - a, z.im - a⟩ : ℂ) ⟨z.re - a, z.im + a⟩
  | 3 => segment ℝ (⟨z.re - a, z.im - a⟩ : ℂ) ⟨z.re + a, z.im - a⟩

/-- The corner shared by the sides `k` and `k + 1`. -/
def sqCorner (z : ℂ) (a : ℝ) : Fin 4 → ℂ
  | 0 => ⟨z.re + a, z.im + a⟩
  | 1 => ⟨z.re - a, z.im + a⟩
  | 2 => ⟨z.re - a, z.im - a⟩
  | 3 => ⟨z.re + a, z.im - a⟩

theorem sqSide_isAxisParallel (z : ℂ) (a : ℝ) (k : Fin 4) :
    ∃ p q : ℂ, sqSide z a k = segment ℝ p q ∧ (p.re = q.re ∨ p.im = q.im) := by
  fin_cases k
  · exact ⟨_, _, rfl, Or.inl rfl⟩
  · exact ⟨_, _, rfl, Or.inr rfl⟩
  · exact ⟨_, _, rfl, Or.inl rfl⟩
  · exact ⟨_, _, rfl, Or.inr rfl⟩

theorem corner_mem_sqSide {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (k : Fin 4) :
    sqCorner z a k ∈ sqSide z a k ∧ sqCorner z a k ∈ sqSide z a (k + 1) := by
  fin_cases k <;> simp only [sqCorner, sqSide, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd] <;>
    first
    | (constructor <;>
        first
        | exact (mem_segment_vertical (by linarith)).mpr ⟨rfl, by linarith, by linarith⟩
        | exact (mem_segment_horizontal (by linarith)).mpr ⟨rfl, by linarith, by linarith⟩)

theorem sqSide_subset_sqLoop {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (k : Fin 4) :
    sqSide z a k ⊆ sqLoop z a := by
  intro u hu
  unfold sqLoop supNorm
  simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  fin_cases k <;> simp only [sqSide] at hu
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_vertical (by linarith)).mp hu
    rw [h1, add_sub_cancel_left, abs_of_nonneg ha, max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_horizontal (by linarith)).mp hu
    rw [h1, add_sub_cancel_left, abs_of_nonneg ha, max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)]
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_vertical (by linarith)).mp hu
    rw [h1, sub_sub_cancel_left, abs_neg, abs_of_nonneg ha,
      max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_horizontal (by linarith)).mp hu
    rw [h1, sub_sub_cancel_left, abs_neg, abs_of_nonneg ha,
      max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)]

theorem sqLoop_subset_iUnion_sqSide {z : ℂ} {a : ℝ} (ha : 0 ≤ a) :
    sqLoop z a ⊆ ⋃ k, sqSide z a k := by
  intro u hu
  unfold sqLoop supNorm at hu
  simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.sub_im] at hu
  rw [Set.mem_iUnion]
  have hre : |u.re - z.re| ≤ a := hu ▸ le_max_left _ _
  have him : |u.im - z.im| ≤ a := hu ▸ le_max_right _ _
  rcases le_total |u.re - z.re| |u.im - z.im| with h | h
  · rw [max_eq_right h] at hu
    rcases abs_eq ha |>.mp hu with h' | h'
    · refine ⟨1, (mem_segment_horizontal (by linarith)).mpr ⟨by linarith, ?_, ?_⟩⟩ <;>
        linarith [abs_le.mp hre]
    · refine ⟨3, (mem_segment_horizontal (by linarith)).mpr ⟨by linarith, ?_, ?_⟩⟩ <;>
        linarith [abs_le.mp hre]
  · rw [max_eq_left h] at hu
    rcases abs_eq ha |>.mp hu with h' | h'
    · refine ⟨0, (mem_segment_vertical (by linarith)).mpr ⟨by linarith, ?_, ?_⟩⟩ <;>
        linarith [abs_le.mp him]
    · refine ⟨2, (mem_segment_vertical (by linarith)).mpr ⟨by linarith, ?_, ?_⟩⟩ <;>
        linarith [abs_le.mp him]

/-! ### Connectedness along lines -/

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- **Connectedness along lines** ([19] hypothesis 3, `[19]`;
for SLE cells verified in [20] §3.1 and TF2's Theorem B): the cells meeting any horizontal or vertical
segment induce a connected sub-graph of `G`. A cell-topology property of the embedding, an explicit
hypothesis of Lemma 3.8. -/
def ConnectedAlongLines (H : CellularEmbedding G o) : Prop :=
  ∀ a b : ℂ, (a.re = b.re ∨ a.im = b.im) →
    (G.adj.induce (verticesMeeting H.cell (segment ℝ a b))).Connected

/-- Reachability in an induced sub-graph passes to larger vertex sets. -/
theorem reachable_induce_of_subset {S T : Set V} (hST : S ⊆ T)
    (hconn : (G.adj.induce S).Connected) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (G.adj.induce T).Reachable ⟨x, hST hx⟩ ⟨y, hST hy⟩ :=
  (hconn.preconnected ⟨x, hx⟩ ⟨y, hy⟩).map (SimpleGraph.induceHomOfLE G.adj hST).toHom

theorem coe_vFin {H : CellularEmbedding G o} {D : Set ℂ} (hD : Bornology.IsBounded D) :
    (vFin H D : Set V) = verticesMeeting H.cell D := by
  ext x
  rw [Finset.mem_coe, mem_vFin H hD]
  rfl

theorem isBounded_sqLoop (z : ℂ) (a : ℝ) : Bornology.IsBounded (sqLoop z a) := by
  refine (isBounded_closedBall (x := z) (r := Real.sqrt 2 * a)).subset fun u hu => ?_
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_le_sqrt_two_mul_supNorm (u - z)).trans ?_
  rw [hu]

/-- **Cells meeting a square loop form a connected sub-graph** (under CAL): the four sides are connected
and consecutive sides share the cell containing their common corner. -/
theorem reachable_sqLoop {H : CellularEmbedding G o} (hcal : ConnectedAlongLines H) {z : ℂ}
    {a : ℝ} (ha : 0 ≤ a) {x y : V} (hx : x ∈ vFin H (sqLoop z a)) (hy : y ∈ vFin H (sqLoop z a)) :
    (G.adj.induce (vFin H (sqLoop z a) : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hb := isBounded_sqLoop z a
  -- the cells of a side lie in the vertex set of the loop
  have hsub : ∀ k, verticesMeeting H.cell (sqSide z a k) ⊆ (vFin H (sqLoop z a) : Set V) := by
    intro k w hw
    rw [coe_vFin hb]
    obtain ⟨u, hu1, hu2⟩ := hw
    exact ⟨u, hu1, sqSide_subset_sqLoop ha k hu2⟩
  have hside : ∀ k, (G.adj.induce (verticesMeeting H.cell (sqSide z a k))).Connected := by
    intro k
    obtain ⟨p, q, hpq, hax⟩ := sqSide_isAxisParallel z a k
    rw [hpq]
    exact hcal p q hax
  -- a cell containing each corner
  have hcorner : ∀ k, ∃ c : V, sqCorner z a k ∈ H.cell c := by
    intro k
    have : sqCorner z a k ∈ ⋃ c, H.cell c := by rw [H.iUnion_cell]; trivial
    simpa using this
  choose c hc using hcorner
  have hcmem : ∀ k, c k ∈ verticesMeeting H.cell (sqSide z a k) ∧
      c k ∈ verticesMeeting H.cell (sqSide z a (k + 1)) := fun k =>
    ⟨⟨_, hc k, (corner_mem_sqSide ha k).1⟩, ⟨_, hc k, (corner_mem_sqSide ha k).2⟩⟩
  -- every vertex of the loop is reachable from `c 3`
  have hreach : ∀ w (hw : w ∈ (vFin H (sqLoop z a) : Set V)),
      (G.adj.induce (vFin H (sqLoop z a) : Set V)).Reachable ⟨c 3, hsub 3 (hcmem 3).1⟩ ⟨w, hw⟩ := by
    intro w hw
    have hw' := hw
    rw [coe_vFin hb] at hw'
    obtain ⟨u, hu1, hu2⟩ := hw'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (sqLoop_subset_iUnion_sqSide ha hu2)
    have hwk : w ∈ verticesMeeting H.cell (sqSide z a k) := ⟨u, hu1, hk⟩
    have r30 := reachable_induce_of_subset (hsub 0) (hside 0) (hcmem 3).2 (hcmem 0).1
    have r01 := reachable_induce_of_subset (hsub 1) (hside 1) (hcmem 0).2 (hcmem 1).1
    have r12 := reachable_induce_of_subset (hsub 2) (hside 2) (hcmem 1).2 (hcmem 2).1
    fin_cases k
    · exact r30.trans (reachable_induce_of_subset (hsub 0) (hside 0) (hcmem 0).1 hwk)
    · exact (r30.trans r01).trans (reachable_induce_of_subset (hsub 1) (hside 1) (hcmem 1).1 hwk)
    · exact ((r30.trans r01).trans r12).trans
        (reachable_induce_of_subset (hsub 2) (hside 2) (hcmem 2).1 hwk)
    · exact reachable_induce_of_subset (hsub 3) (hside 3) (hcmem 3).1 hwk
  exact (hreach x hx).symm.trans (hreach y hy)

/-! ### Crossings along walks -/

/-- **Crossing along a walk.** Along a path of vertices in which consecutive vertices are equal or
adjacent, if the first cell has a point with `φ ≤ t` and the last one a point with `φ ≥ t` (`φ`
continuous), some cell of the path meets the level set `{φ = t}`. -/
theorem exists_crossing_of_walk (H : CellularEmbedding G o) {φ : ℂ → ℝ} (hφ : Continuous φ)
    {t : ℝ} : ∀ (n : ℕ) (X : ℕ → V), (∀ j < n, X (j + 1) = X j ∨ G.adj.Adj (X j) (X (j + 1))) →
      (∃ u ∈ H.cell (X 0), φ u ≤ t) → (∃ u ∈ H.cell (X n), t ≤ φ u) →
      ∃ j ≤ n, (H.cell (X j) ∩ {u | φ u = t}).Nonempty := by
  intro n
  induction n with
  | zero =>
    intro X _ ⟨a, ha, hat⟩ ⟨b, hb, htb⟩
    obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell (X 0)).isPreconnected
      hφ ha hb hat htb
    exact ⟨0, le_rfl, c, hc, hct⟩
  | succ n ih =>
    intro X hstep ⟨a, ha, hat⟩ hlast
    by_cases hmeet : (H.cell (X 0) ∩ {u | φ u = t}).Nonempty
    · exact ⟨0, Nat.zero_le _, hmeet⟩
    -- every point of the first cell has `φ < t`
    have hlt : ∀ u ∈ H.cell (X 0), φ u < t := by
      intro u hu
      by_contra hge
      push Not at hge
      obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected
        (H.isConnected_cell (X 0)).isPreconnected hφ ha hu hat hge
      exact hmeet ⟨c, hc, hct⟩
    -- the second cell meets the first one
    have h1 : ∃ u ∈ H.cell (X 1), φ u ≤ t := by
      rcases hstep 0 (Nat.succ_pos n) with h | h
      · rw [zero_add] at h
        exact ⟨a, h ▸ ha, hat⟩
      · obtain ⟨c, hc0, hc1⟩ := H.inter_of_adj _ _ h
        exact ⟨c, hc1, (hlt c hc0).le⟩
    obtain ⟨j, hj, hjm⟩ := ih (fun k => X (k + 1)) (fun j hj => hstep (j + 1) (by omega)) h1
      (by simpa using hlast)
    exact ⟨j + 1, by omega, hjm⟩

end MatedCRTHarmonic.GMS3
