import Mathlib

/-!
# Shells of a distance function to a set

Elementary facts about the distance function `x ↦ infDist x K` to a set `K` of the complex plane, and about the
thickenings, balls and level sets it generates. They control the shells `{|infDist · K - r / 2| = λ}` of the
distance function at a fixed scale `r` (the level sets of the centred distance `|infDist · K - r / 2|`), and the
discrete cells that a path meets near such a shell:

* a preconnected set that misses the frontier of a set `D` and meets `D` lies in `D`;
* the distance function is 1-Lipschitz, so the centred distance of two points of a set of diameter `d` differs by
  at most `d` (potential theory of the distance function, Armitage-Gardiner);
* the frontier of the `t`-thickening of a compact set is the level set `{infDist · K = t}`;
* arithmetic of radii, of enlarged balls, and of sparse counts for the choice of scales;
* a compact set inside a ball has its level sets inside a larger ball, and the rational points are dense in an
  interval;
* a bound on a conditional expectation that holds almost everywhere on an event transfers to any smaller event.
-/

open Set Metric

namespace LatticeProb

namespace ShellGeometry

/-! ### Preconnected sets and the frontier of a set -/

/-- A preconnected set that misses the frontier of `D` and meets `D` lies in `D`. -/
lemma subset_of_isPreconnected_of_disjoint_frontier {D S : Set ℂ} (hS : IsPreconnected S)
    (hfr : Disjoint S (frontier D)) (hSD : (S ∩ D).Nonempty) : S ⊆ D := by
  have hcov : S ⊆ interior D ∪ (closure D)ᶜ := by
    intro p hp
    by_cases hc : p ∈ closure D
    · refine Or.inl ?_
      by_contra hi
      exact (Set.disjoint_left.1 hfr hp) (show p ∈ closure D \ interior D from ⟨hc, hi⟩)
    · exact Or.inr hc
  have hdisj : Disjoint (interior D) (closure D)ᶜ :=
    Set.disjoint_left.2 fun p hp hp' => hp' (subset_closure (interior_subset hp))
  obtain ⟨p, hpS, hpD⟩ := hSD
  have hpint : p ∈ interior D := by
    by_contra hi
    exact (Set.disjoint_left.1 hfr hpS) (show p ∈ closure D \ interior D from ⟨subset_closure hpD, hi⟩)
  exact (hS.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hcov
    ⟨p, hpS, hpint⟩).trans interior_subset

/-! ### The distance to a set is 1-Lipschitz; levels of the centred distance -/

/-- The distance to a set is 1-Lipschitz: `|infDist x K - infDist y K| ≤ dist x y`. -/
lemma abs_infDist_sub_infDist_le (K : Set ℂ) (x y : ℂ) :
    |infDist x K - infDist y K| ≤ dist x y := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [infDist_le_infDist_add_dist (x := x) (y := y) (s := K), dist_comm x y]
  · linarith [infDist_le_infDist_add_dist (x := y) (y := x) (s := K), dist_comm x y]

/-- The centred distance `|infDist · K - r / 2|` is 1-Lipschitz: the two levels differ by at most `dist u v`. -/
lemma abs_level_sub_le (K : Set ℂ) (r : ℝ) (u v : ℂ) :
    |(|infDist u K - r / 2| - |infDist v K - r / 2|)| ≤ dist u v := by
  have h1 : |infDist u K - infDist v K| ≤ dist u v := abs_infDist_sub_infDist_le K u v
  calc |(|infDist u K - r / 2| - |infDist v K - r / 2|)|
      ≤ |(infDist u K - r / 2) - (infDist v K - r / 2)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |infDist u K - infDist v K| := by congr 1; ring
    _ ≤ dist u v := h1

/-- If the level set `{|infDist · K - r / 2| = lam}` passes within `R / 50` of `z`, and `R ≤ s`, then on the ball of
radius `2 R` about `z` the centred distance stays within `3 s` of `lam`. -/
theorem level_near_centre {K : Set ℂ} {r lam s R : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) {u : ℂ} (hu : dist u z < 2 * R) :
    |(|infDist u K - r / 2| - lam)| < 3 * s := by
  subst hy
  have h2 : dist u y ≤ dist u z + dist z y := dist_triangle u z y
  have h3 : dist u y < 3 * s := by linarith
  exact lt_of_le_of_lt (abs_level_sub_le K r u y) h3

/-- A point `p` of a set of diameter at most `h` that contains a point `q` of the ball of radius `2 R` about `z`
has centred distance within `3 s + h` of `lam`. -/
theorem cell_level_within {K : Set ℂ} {r lam s R h : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) {q p : ℂ} (hq : dist q z < 2 * R)
    (hpq : dist p q ≤ h) : |(|infDist p K - r / 2| - lam)| < 3 * s + h := by
  have A := level_near_centre hy hzy hRs hs hq
  have B := abs_level_sub_le K r p q
  have C := abs_sub_le (|infDist p K - r / 2|) (|infDist q K - r / 2|) lam
  linarith [B, C, A, hpq]

/-- Under the hypotheses of `cell_level_within`, with `h ≤ s`, no point `p` of such a set lies on the next shell
`{|infDist · K - r / 2| = lam + 20 s}`. -/
theorem cell_misses_next_shell {K : Set ℂ} {r lam s R h : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) (hhs : h ≤ s) {q p : ℂ}
    (hq : dist q z < 2 * R) (hpq : dist p q ≤ h) : |infDist p K - r / 2| ≠ lam + 20 * s := by
  intro hp
  have A := cell_level_within (K := K) (r := r) hy hzy hRs hs hq hpq
  rw [hp] at A
  have e : lam + 20 * s - lam = 20 * s := by ring
  rw [e, abs_of_pos (by linarith : (0:ℝ) < 20 * s)] at A
  linarith

/-! ### Radii, shell levels and enlarged balls -/

/-- If `j ≤ N` and `N (400 s) ≤ r`, then the level `20 j s` is at most `r / 20`. -/
theorem shell_level_le {r s : ℝ} {N j : ℕ} (hs : 0 ≤ s) (hN : (N : ℝ) * (400 * s) ≤ r) (hj : j ≤ N) :
    20 * (j : ℝ) * s ≤ r / 20 := by
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have := mul_le_mul_of_nonneg_right hjN hs
  linarith

/-- If `lam ≤ r / 20`, `s ≤ r / 4000` and `|x - r / 2| < lam + 4 s`, then `0 < x < r`. -/
theorem level_window {r s lam x : ℝ} (hlam : lam ≤ r / 20) (hs4 : s ≤ r / 4000)
    (hx : |x - r / 2| < lam + 4 * s) : 0 < x ∧ x < r := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  constructor <;> linarith

/-- If `r ^ 2 ≤ d ≤ R ≤ s ≤ r / 4000` and `0 < r`, then `r ^ 2 ≤ R`, `R ≤ s` and `R < r`. -/
theorem shell_radius_bounds {r d R s : ℝ} (hd : r ^ 2 ≤ d) (hdR : d ≤ R) (hRs : R ≤ s) (hs4 : s ≤ r / 4000)
    (hr : 0 < r) : r ^ 2 ≤ R ∧ R ≤ s ∧ R < r :=
  ⟨le_trans hd hdR, hRs, by linarith⟩

/-- If `|dist x' z - 4 R / 3| ≤ h` and `h + e ≤ R / 12`, then the ball of radius `R / 4 + e` about `x'` lies in the
annulus `{p | R < dist p z ∧ dist p z < 2 R}`. -/
theorem enlarged_ball_in_annulus {x' z : ℂ} {R h e : ℝ} (hR : 0 < R) (hrad : |dist x' z - 4 * R / 3| ≤ h)
    (hhe : h + e ≤ R / 12) :
    ball x' (R / 4 + e) ⊆ {p | R < dist p z ∧ dist p z < 2 * R} := by
  intro w hw
  have hwd := mem_ball.1 hw
  have hab := abs_le.1 hrad
  have t1 := dist_triangle x' w z
  have t2 := dist_triangle w x' z
  rw [dist_comm x' w] at t1
  show R < dist w z ∧ dist w z < 2 * R
  constructor <;> linarith [hab.1, hab.2]

/-- If `ε · cnt ≤ s₁ r ^ (2 β)`, `r ^ 2 ≤ R`, `cv c₀ ^ β R ^ β ≤ m` and `4 s₁ ≤ cv c₀ ^ β`, then the sparse count
satisfies `ε · cnt ≤ m / 4`: the first-moment bound of a sparsity hypothesis at a volume lower bound. -/
theorem first_moment_of_sparsity {cnt m ε s1 cv c0 β R r : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hs1 : 0 ≤ s1) (hr2 : r ^ 2 ≤ R) (hcnt : ε * cnt ≤ s1 * r ^ (2 * β))
    (hvol : cv * c0 ^ β * R ^ β ≤ m) (hcs : 4 * s1 ≤ cv * c0 ^ β) : ε * cnt ≤ m / 4 := by
  have hpow : r ^ (2 * β) ≤ R ^ β := by
    rw [Real.rpow_mul hr, Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg r) hr2 hβ
  have hRb : 0 ≤ R ^ β := Real.rpow_nonneg hR β
  have h1 : s1 * r ^ (2 * β) ≤ s1 * R ^ β := mul_le_mul_of_nonneg_left hpow hs1
  have h2 : 4 * s1 * R ^ β ≤ cv * c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hcs hRb
  linarith

/-! ### Thickenings of a compact set and the level sets of the distance -/

/-- For a nonempty compact set `K` and `t > 0`, the frontier of the `t`-thickening of `K` is the level set
`{x | infDist x K = t}`. -/
theorem frontier_thickening_eq {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ} (ht : 0 < t) :
    frontier (thickening t K) = {x | infDist x K = t} := by
  ext x
  have hop : interior (thickening t K) = thickening t K := isOpen_thickening.interior_eq
  simp only [Set.mem_ofPred_eq, frontier, Set.mem_sdiff, hop]
  constructor
  · rintro ⟨hcl, hnot⟩
    have h1 : t ≤ infDist x K :=
      not_lt.1 fun h => hnot (mem_thickening_iff.2 ((infDist_lt_iff hne).1 h))
    have h2 : infDist x K ≤ t := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.1 hcl ε hε
      have hb' : infDist b K < t := (infDist_lt_iff hne).2 (mem_thickening_iff.1 hb)
      have := infDist_le_infDist_add_dist (x := x) (y := b) (s := K)
      linarith
    exact le_antisymm h2 h1
  · intro hx
    refine ⟨?_, fun hmem => ?_⟩
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne x
      have hl0 : 0 < min (1 / 2 : ℝ) (ε / (2 * t)) := lt_min one_half_pos (div_pos hε (by linarith))
      have hl1 : min (1 / 2 : ℝ) (ε / (2 * t)) ≤ 1 / 2 := min_le_left _ _
      have hl2 : min (1 / 2 : ℝ) (ε / (2 * t)) * t ≤ ε / 2 := by
        have h3 : min (1 / 2 : ℝ) (ε / (2 * t)) ≤ ε / (2 * t) := min_le_right _ _
        have h4 : ε / (2 * t) * t = ε / 2 := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero two_ne_zero ht.ne') two_ne_zero]
          ring
        have h5 := mul_le_mul_of_nonneg_right h3 ht.le
        linarith
      set l := min (1 / 2 : ℝ) (ε / (2 * t)) with hl
      refine ⟨x + (l : ℂ) * (k - x), ?_, ?_⟩
      · rw [mem_thickening_iff]
        refine ⟨k, hk, ?_⟩
        have e : x + (l : ℂ) * (k - x) - k = ((1 - l : ℝ) : ℂ) * (x - k) := by push_cast; ring
        have hl1' : 0 ≤ 1 - l := by linarith
        rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl1',
          ← dist_eq_norm, ← hkd, hx]
        nlinarith [mul_pos hl0 ht]
      · have e : x - (x + (l : ℂ) * (k - x)) = -((l : ℂ) * (k - x)) := by ring
        rw [dist_eq_norm, e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le,
          norm_sub_rev, ← dist_eq_norm, ← hkd, hx]
        linarith
    · obtain ⟨z, hz, hzd⟩ := mem_thickening_iff.1 hmem
      have : infDist x K < t := (infDist_lt_iff hne).2 ⟨z, hz, hzd⟩
      linarith

/-- If a set `H` has diameter at most `d` and contains a point `y` with `infDist y K = t`, then every `x0 ∈ H`
satisfies `|infDist x0 K - t| ≤ d`. -/
theorem abs_infDist_sub_le_of_mem_level {K H : Set ℂ} {d t : ℝ} {x0 y : ℂ}
    (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hx0 : x0 ∈ H) (hy : y ∈ H) (hyt : infDist y K = t) :
    |infDist x0 K - t| ≤ d := by
  have h := abs_infDist_sub_infDist_le K x0 y
  rw [hyt] at h
  exact h.trans (hH x0 hx0 y hy)

/-- If `K ⊆ ball 0 (ρ / 2)` is compact and nonempty, then the level set `{infDist · K = t}` with `t < ρ / 2`
lies in `ball 0 ρ`. -/
theorem norm_lt_of_infDist_eq {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {ρ t : ℝ}
    (hKρ : K ⊆ ball 0 (ρ / 2)) {y : ℂ} (hy : infDist y K = t) (ht : t < ρ / 2) :
    ‖y‖ < ρ := by
  obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne y
  have hkn : ‖k‖ < ρ / 2 := by simpa using hKρ hk
  have h := norm_sub_norm_le y k
  have hyk : ‖y - k‖ = t := by rw [← dist_eq_norm, ← hkd, hy]
  linarith

/-! ### Windows: the centred distance at nearby points -/

/-- If `|infDist x0 K - r / 2| ≤ d`, `dist xj x0 ≤ 3 j s`, `N s ≤ r / 100` and `j ≤ N`, then
`|infDist xj K - r / 2| ≤ d + 3 r / 100`. -/
theorem infDist_xj_bound {K : Set ℂ} {x0 xj : ℂ} {r d s : ℝ} {j N : ℕ}
    (hx0 : |infDist x0 K - r / 2| ≤ d) (hs : 0 ≤ s) (hjN : j ≤ N) (hN : (N : ℝ) * s ≤ r / 100)
    (hxj : dist xj x0 ≤ 3 * j * s) :
    |infDist xj K - r / 2| ≤ d + 3 * r / 100 := by
  have h1 := abs_infDist_sub_infDist_le K xj x0
  have hjN' : (j : ℝ) * s ≤ N * s := mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) hs
  have h2 : |infDist xj K - infDist x0 K| ≤ 3 * r / 100 := by linarith
  rw [abs_le] at h1 h2 hx0 ⊢
  constructor <;> linarith [h2.1, h2.2, hx0.1, hx0.2]

/-- If `K` is nonempty and compact with `K ⊆ ball 0 (ρ / 2)`, `ball 0 s0 ⊆ K`, and the radii satisfy the window
bounds, then every `x` with `|infDist x K - r / 2| ≤ d + 3 r / 100` satisfies `s0 ≤ ‖x‖ < ρ / 2 + r`. -/
theorem xj_norm_bounds {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {ρ s0 r d δ s : ℝ}
    (hδ : 0 < δ) (hs : s = Real.sqrt δ) (hρ1 : ρ < 1)
    (hKρ : K ⊆ ball 0 (ρ / 2)) (hBs : ball 0 s0 ⊆ K)
    (hC1 : r ≤ ρ / 100 ∧ s ≤ r / 1000 ∧ 10 * s < s0 / 4 ∧ d ≤ δ / 100)
    {x : ℂ} (hx : |infDist x K - r / 2| ≤ d + 3 * r / 100) :
    s0 ≤ ‖x‖ ∧ ‖x‖ < ρ / 2 + r := by
  obtain ⟨h1, h2, h3, h4⟩ := hC1
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg δ
  have hsp : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hδ
  have hsq : s ^ 2 = δ := by rw [hs]; exact Real.sq_sqrt hδ.le
  have hr1 : r < 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hδs : δ < s := by rw [← hsq]; nlinarith
  have hdr : d ≤ r / 100000 := by linarith
  obtain ⟨hxa, hxb⟩ := abs_le.1 hx
  have hpos : 0 < infDist x K := by linarith
  have hxK : x ∉ K := fun h => (ne_of_gt hpos) (infDist_zero_of_mem h)
  have hs0x : s0 ≤ ‖x‖ := by
    by_contra h
    exact hxK (hBs (mem_ball_zero_iff.2 (not_le.1 h)))
  obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne x
  have hkn : ‖k‖ < ρ / 2 := by simpa using hKρ hk
  have hxk : ‖x - k‖ = infDist x K := by rw [hkd, dist_eq_norm]
  have hn := norm_sub_norm_le x k
  exact ⟨hs0x, by linarith⟩

/-- If `r ≤ ρ / 100`, `s ≤ r / 1000`, `δ < s`, `‖z‖ < ρ / 2 + r + δ / 100` and `R ≤ s`, then
`‖z‖ + 2 R < 3 ρ / 4`. -/
theorem norm_add_two_radius_lt {ρ r δ s R : ℝ} {z : ℂ} (hρ0 : 0 < ρ)
    (hC : r ≤ ρ / 100 ∧ s ≤ r / 1000) (hδ : δ < s) (hz : ‖z‖ < ρ / 2 + r + δ / 100) (hR : R ≤ s) :
    ‖z‖ + 2 * R < 3 * ρ / 4 := by
  obtain ⟨h1, h2⟩ := hC
  linarith

/-- If `H` has diameter at most `d ≤ δ / 100`, `δ ≤ R`, and `x ∈ H` lies within `δ / 100` of `z`, then every
`u ∈ H` satisfies `dist u z < 4 R / 3`. -/
theorem cell_sub_testDisk {H : Set ℂ} {d δ R : ℝ} {x z u : ℂ} (hδ : 0 ≤ δ) (hd : d ≤ δ / 100)
    (hR : δ ≤ R) (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hx : x ∈ H) (hu : u ∈ H)
    (hzx : dist z x < δ / 100) :
    dist u z < 4 * R / 3 := by
  have h1 := hH u hu x hx
  have h2 := dist_triangle u x z
  rw [dist_comm x z] at h2
  linarith

/-- Deterministic window bound. Let `y ∈ H` with `dist y xj < 3 s`, where `dist xj x0 ≤ 3 j s`, `j + 1 ≤ N`,
`N s ≤ r / 100`, `s ≤ r / 1000` and `d ≤ s / 100`, and let `|infDist x0 K - r / 2| ≤ d`. Then every `u ∈ H`
satisfies `2 r / 5 < infDist u K < 3 r / 5`. -/
theorem infDist_mem_Ioo_of_window {K H : Set ℂ} {x0 xj y u : ℂ} {r d s : ℝ} {j N : ℕ}
    (hx0 : |infDist x0 K - r / 2| ≤ d) (hs : 0 ≤ s) (hd : d ≤ s / 100) (hs' : s ≤ r / 1000)
    (hjN : j + 1 ≤ N) (hNs : (N : ℝ) * s ≤ r / 100) (hxj : dist xj x0 ≤ 3 * j * s)
    (hyj : dist y xj < 3 * s)
    (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hy : y ∈ H) (hu : u ∈ H) :
    2 * r / 5 < infDist u K ∧ infDist u K < 3 * r / 5 := by
  have hjN' : ((j : ℝ) + 1) * s ≤ N * s :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) hs
  have hyx : dist y x0 < 3 * r / 100 := by
    have := dist_triangle y xj x0
    nlinarith
  have hux : dist u x0 < d + 3 * r / 100 := by
    have := dist_triangle u y x0
    have := hH u hu y hy
    linarith
  have h := abs_infDist_sub_infDist_le K u x0
  have hx' := abs_le.1 hx0
  have h' := abs_le.1 h
  constructor <;> linarith [h'.1, h'.2, hx'.1, hx'.2]

/-! ### Rational points are dense in an interval -/

/-- Every point of `[a, b]` lies in the closure of the image of the rational points of `[a, b]`, when `a < b`. -/
theorem mem_closure_ratInt_image {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    t ∈ closure (((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) ∈ Icc a b}) := by
  rw [Metric.mem_closure_iff]
  intro e he
  have h1 : max a (t - e) < min b (t + e) :=
    max_lt (lt_min hab (by linarith [ht.1])) (lt_min (by linarith [ht.2]) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  have hq1' : a < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq1'' : t - e < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
  have hq2' : (q : ℝ) < b := lt_of_lt_of_le hq2 (min_le_left _ _)
  have hq2'' : (q : ℝ) < t + e := lt_of_lt_of_le hq2 (min_le_right _ _)
  refine ⟨(q : ℝ), ⟨q, ⟨hq1'.le, hq2'.le⟩, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ### Conditional bounds along an inclusion of events -/

open MeasureTheory in
/-- If `P ⊆ G` and the bound `μ[1_F | 𝓖] ≤ 1 - q` holds almost everywhere on `G`, then it holds almost everywhere
on `P`. -/
lemma ae_condExp_indicator_le_of_subset {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {𝓖 : MeasurableSpace Ω} {F P G : Set Ω} {q : ℝ} (hPG : P ⊆ G)
    (hS5 : ∀ᵐ ω ∂μ, ω ∈ G → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q :=
  hS5.mono fun _ h hω => h (hPG hω)

end ShellGeometry

end LatticeProb
