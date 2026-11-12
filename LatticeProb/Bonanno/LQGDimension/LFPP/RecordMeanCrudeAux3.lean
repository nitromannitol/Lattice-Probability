/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanCrudeAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanCrudeAux2

/-!
# Node `M45`, auxiliary file 3: parametrizations of the local families

Chaining parameters (sup norm on `Fin (2n+1) → ℝ`): real and imaginary parts of the vertices,
and one extra coordinate.

* Small family: `psm M c` = the vertices of the child polygon (padded by `0` up to `3M + 1`
  vertices) and the number of vertices.  Two polygons with parameters at distance `τ < 1` have the
  same number of vertices and `2τ`-close vertices, so `abs_logCov_aligned_le` applies (the edge
  weights move by `O(Mτ)`); for `τ ≥ 1` the crude bound suffices.  Hence
  `logCov(D, D) ≤ Ksm M · τ` (`small_canon`).  The parameters have diameter
  `≤ 2M(3M+14) δ √(k+1)` (`small_diam`): if `4M(k+1)δ² < 1` all polygons are near-straight
  with exactly `M` edges, otherwise the trivial diameter bound suffices.
* Large family: `pl c` = the four endpoints; `logCov(D, D) ≤ Kl M · τ` (`large_canon`) and the
  diameter is at most `18` (`large_diam`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RMCrude

open Blueprint.Draft TwoScale

/-! ## Parameter vectors -/

/-- Real parts of `W 0, …, W (n-1)`, imaginary parts of the same, then `r`. -/
def cpar (n : ℕ) (W : ℕ → ℂ) (r : ℝ) : Fin (2 * n + 1) → ℝ := fun j =>
  if j.1 < n then (W j.1).re else if j.1 < 2 * n then (W (j.1 - n)).im else r

lemma cpar_close {n : ℕ} {W W' : ℕ → ℂ} {r r' τ : ℝ} (h : ‖cpar n W r - cpar n W' r'‖ ≤ τ) :
    (∀ i < n, ‖W i - W' i‖ ≤ 2 * τ) ∧ |r - r'| ≤ τ := by
  have hc : ∀ j : Fin (2 * n + 1), |cpar n W r j - cpar n W' r' j| ≤ τ := fun j => by
    have := norm_le_pi_norm (cpar n W r - cpar n W' r') j
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    exact this.trans h
  refine ⟨fun i hi => ?_, ?_⟩
  · have h1 := hc ⟨i, by omega⟩
    have h2 := hc ⟨n + i, by omega⟩
    have hni : ¬ (n + i < n) := by omega
    have hni2 : n + i < 2 * n := by omega
    simp only [cpar, hi, if_true] at h1
    simp only [cpar, hni, hni2, if_false, if_true, Nat.add_sub_cancel_left] at h2
    calc ‖W i - W' i‖ ≤ |(W i - W' i).re| + |(W i - W' i).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ τ + τ := by rw [Complex.sub_re, Complex.sub_im]; exact add_le_add h1 h2
      _ = 2 * τ := by ring
  · have h3 := hc ⟨2 * n, by omega⟩
    have hn1 : ¬ (2 * n < n) := by omega
    have hn2 : ¬ (2 * n < 2 * n) := lt_irrefl _
    simp only [cpar, hn1, hn2, if_false] at h3
    exact h3

lemma cpar_diam {n : ℕ} {W W' : ℕ → ℂ} {r r' a : ℝ} (ha : 0 ≤ a)
    (hW : ∀ i < n, ‖W i - W' i‖ ≤ a) (hr : |r - r'| ≤ a) :
    ‖cpar n W r - cpar n W' r'‖ ≤ a := by
  rw [pi_norm_le_iff_of_nonneg ha]
  intro j
  rw [Pi.sub_apply, Real.norm_eq_abs]
  unfold cpar
  split_ifs with h1 h2
  · rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans (hW _ h1)
  · rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans (hW _ (by omega))
  · exact hr

/-! ## Combinations in `range` form -/

lemma mass_range (N : ℕ) (g : ℕ → ℝ × ℂ × ℂ) :
    SegComb.mass ((List.range N).map g) = ∑ i ∈ Finset.range N, (g i).1 := by
  unfold SegComb.mass
  rw [List.map_map, list_sum_map_range]
  rfl

lemma tv_range (N : ℕ) (g : ℕ → ℝ × ℂ × ℂ) :
    tv ((List.range N).map g) = ∑ i ∈ Finset.range N, |(g i).1| := by
  unfold tv
  rw [List.map_map, list_sum_map_range]
  rfl

lemma mem_range_map {N : ℕ} {g : ℕ → ℝ × ℂ × ℂ} {p : ℝ × ℂ × ℂ}
    (hp : p ∈ (List.range N).map g) : ∃ i < N, g i = p := by
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, List.mem_range.1 hi, rfl⟩

lemma cfgG_sum {x y : ℂ} {V : ℕ → ℂ} {m : ℕ} (hL : plen V m ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), (cfgG x y V (plen V m) i).1 = 0 := by
  rw [Finset.sum_range_succ']
  simp only [cfgG]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  change -(plen V m / plen V m) + 1 = 0
  rw [div_self hL]; ring

lemma cfgG_tv {x y : ℂ} {V : ℕ → ℂ} {m : ℕ} (hL : 0 < plen V m) :
    ∑ i ∈ Finset.range (m + 1), |(cfgG x y V (plen V m) i).1| = 2 := by
  rw [Finset.sum_range_succ']
  simp only [cfgG]
  have : ∀ i ∈ Finset.range m, |-(‖V (i + 1) - V i‖ / plen V m)| = ‖V (i + 1) - V i‖ / plen V m :=
    fun i _ => by rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  change plen V m / plen V m + |(1 : ℝ)| = 2
  rw [div_self hL.ne', abs_one]; norm_num

/-! ## Small family -/

/-- The chord and edge segments of a small-excess configuration have length `≥ 1/(4M)` and lie
in the disc of radius `7`. -/
lemma small_segs {M : ℕ} {δ : ℝ} {k : ℕ} {x y : ℂ} {V : ℕ → ℂ} {m : ℕ}
    (hg : SmallGeom M δ k x y V m) (hM : 16 ≤ M) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∀ i < m + 1, 1 / (4 * (M : ℝ)) ≤ ‖(cfgG x y V (plen V m) i).2.2 - (cfgG x y V (plen V m) i).2.1‖ ∧
      ‖(cfgG x y V (plen V m) i).2.1‖ ≤ 7 ∧ ‖(cfgG x y V (plen V m) i).2.2‖ ≤ 7 := by
  obtain ⟨hR1, hR2, -, -, hV7, hedge, hx, hy⟩ := hg.basic hM hδ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  intro i hi
  cases i with
  | zero =>
    simp only [cfgG]
    refine ⟨?_, by linarith, by linarith⟩
    have : 1 / (4 * (M : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (16 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    linarith
  | succ j =>
    simp only [cfgG]
    exact ⟨hedge j (by omega), hV7 j, hV7 (j + 1)⟩

/-- Parameters of the small family. -/
def psm (M : ℕ) (c : Config) : Fin (2 * (3 * M + 1) + 1) → ℝ :=
  cpar (3 * M + 1) (vx c.2) (c.2.length : ℝ)

/-- Crude constant. -/
def Kc (M : ℕ) : ℝ := 256 * gcst (1 / (4 * (M : ℝ))) * (4 * √(2 * 7) + 4 * √(2 * 7)) ^ 2

/-- Aligned constant. -/
def Ka (M : ℕ) : ℝ := 256 * gcst (1 / (4 * (M : ℝ))) * (2 * √2 + 48 * (M : ℝ) * √(2 * 7)) ^ 2

/-- Canonical-distance constant of the small family. -/
def Ksm (M : ℕ) : ℝ := Kc M + Ka M

lemma Kc_nonneg (M : ℕ) : 0 ≤ Kc M := by
  unfold Kc; have := gcst_nonneg (1 / (4 * (M : ℝ))); positivity

lemma Ka_nonneg (M : ℕ) : 0 ≤ Ka M := by
  unfold Ka; have := gcst_nonneg (1 / (4 * (M : ℝ))); positivity

lemma Ksm_nonneg (M : ℕ) : 0 ≤ Ksm M := add_nonneg (Kc_nonneg M) (Ka_nonneg M)

lemma nat_eq_of_abs_lt_one {a b : ℕ} (h : |(a : ℝ) - b| < 1) : a = b := by
  rw [abs_lt] at h
  have h1 : (a : ℝ) < b + 1 := by linarith
  have h2 : (b : ℝ) < a + 1 := by linarith
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  omega

/-- **Canonical distance of the small family.** -/
theorem small_canon {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {k : ℕ}
    {c c' : Config} (hc : c ∈ smallFamily M δ k) (hc' : c' ∈ smallFamily M δ k) :
    SegComb.logCov (SegComb.sub (cfgComb c) (cfgComb c')) (SegComb.sub (cfgComb c) (cfgComb c'))
      ≤ Ksm M * ‖psm M c - psm M c'‖ := by
  obtain ⟨x, y, z, rfl, hg⟩ := small_data hc
  obtain ⟨x', y', z', rfl, hg'⟩ := small_data hc'
  obtain ⟨hR1, hR2, hRL, hL3, hV7, hedge, hx, hy⟩ := hg.basic hM hδ
  obtain ⟨hR1', hR2', hRL', hL3', hV7', hedge', hx', hy'⟩ := hg'.basic hM hδ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hxy : x ≠ y := by
    intro h; rw [h, sub_self, norm_zero] at hR1; linarith
  have hxy' : x' ≠ y' := by
    intro h; rw [h, sub_self, norm_zero] at hR1'; linarith
  rw [cfgComb_eq hxy z, cfgComb_eq hxy' z']
  set m := z.length - 1 with hmdef
  set m' := z'.length - 1 with hm'def
  set V := vx z with hVdef
  set V' := vx z' with hV'def
  have hLpos : 0 < plen V m := by linarith
  have hLpos' : 0 < plen V' m' := by linarith
  set τ := ‖psm M ([x, y], z) - psm M ([x', y'], z')‖ with hτdef
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hℓ : (0 : ℝ) < 1 / (4 * (M : ℝ)) := by positivity
  have hseg := small_segs hg hM hδ
  have hseg' := small_segs hg' hM hδ
  rcases le_or_gt 1 τ with hτ | hτ
  · -- crude bound
    have hD := abs_logCov_self_le
      (SegComb.sub ((List.range (m + 1)).map (cfgG x y V (plen V m)))
        ((List.range (m' + 1)).map (cfgG x' y' V' (plen V' m'))))
      (x, y) (ℓ := 1 / (4 * (M : ℝ))) (ρ := 7) (A := 4) hℓ ?_ ?_ ?_ ?_ ?_ ?_
    · calc _ ≤ |SegComb.logCov _ _| := le_abs_self _
        _ ≤ Kc M := hD
        _ ≤ Kc M * τ := le_mul_of_one_le_right (Kc_nonneg M) hτ
        _ ≤ Ksm M * τ := by unfold Ksm; nlinarith [Ka_nonneg M]
    · rw [mass_sub, mass_range, mass_range, cfgG_sum hLpos.ne', cfgG_sum hLpos'.ne', sub_zero]
    · intro p hp
      unfold SegComb.sub at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := mem_range_map hp
        exact (hseg i hi).1
      · rw [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        obtain ⟨i, hi, rfl⟩ := mem_range_map hq
        exact (hseg' i hi).1
    · exact (hseg 0 (by omega)).1
    · intro p hp
      unfold SegComb.sub at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := mem_range_map hp
        exact (hseg i hi).2
      · rw [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        obtain ⟨i, hi, rfl⟩ := mem_range_map hq
        exact (hseg' i hi).2
    · exact (hseg 0 (by omega)).2
    · rw [tv_sub, tv_range, tv_range, cfgG_tv hLpos, cfgG_tv hLpos']; norm_num
  · -- aligned bound
    have hcl := cpar_close (le_refl τ)
    have hVc : ∀ i < 3 * M + 1, ‖V i - V' i‖ ≤ 2 * τ := hcl.1
    have hlen : z.length = z'.length := nat_eq_of_abs_lt_one (lt_of_le_of_lt hcl.2 hτ)
    have hmm : m' = m := by rw [hmdef, hm'def, hlen]
    rw [hmm] at hLpos' hseg' ⊢
    have hm3 := hg.m3
    have hvm' : V' m = y' := by rw [← hmm]; exact hg'.vm
    have hclose : ∀ i < m + 1,
        ‖(cfgG x y V (plen V m) i).2.1 - (cfgG x' y' V' (plen V' m) i).2.1‖ ≤ 2 * τ ∧
        ‖(cfgG x y V (plen V m) i).2.2 - (cfgG x' y' V' (plen V' m) i).2.2‖ ≤ 2 * τ := by
      intro i hi
      cases i with
      | zero =>
        simp only [cfgG]
        refine ⟨?_, ?_⟩
        · rw [← hg.v0, ← hg'.v0]; exact hVc 0 (by omega)
        · rw [← hg.vm, ← hvm']; exact hVc m (by omega)
      | succ j =>
        simp only [cfgG]
        exact ⟨hVc j (by omega), hVc (j + 1) (by omega)⟩
    -- weights
    have hS : ∑ i ∈ Finset.range m, |‖V (i + 1) - V i‖ - ‖V' (i + 1) - V' i‖| ≤ m * (4 * τ) := by
      calc _ ≤ ∑ i ∈ Finset.range m, 4 * τ := Finset.sum_le_sum fun i hi => by
            rw [Finset.mem_range] at hi
            refine (abs_norm_sub_norm_le _ _).trans ?_
            have e : (V (i + 1) - V i) - (V' (i + 1) - V' i) =
                (V (i + 1) - V' (i + 1)) - (V i - V' i) := by ring
            rw [e]
            refine (norm_sub_le _ _).trans ?_
            linarith [hVc (i + 1) (by omega), hVc i (by omega)]
        _ = m * (4 * τ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hW := sum_abs_div_sub_div_le m (fun i => ‖V (i + 1) - V i‖)
      (fun i => ‖V' (i + 1) - V' i‖) (fun i => norm_nonneg _) hLpos hLpos'
    have hB : ∑ i ∈ Finset.range (m + 1),
        |(cfgG x y V (plen V m) i).1 - (cfgG x' y' V' (plen V' m) i).1| ≤ 16 * m * τ := by
      rw [Finset.sum_range_succ']
      simp only [cfgG, sub_self, abs_zero, add_zero]
      have e : ∀ i ∈ Finset.range m, |-(‖V (i + 1) - V i‖ / plen V m) -
          -(‖V' (i + 1) - V' i‖ / plen V' m)| =
          |‖V (i + 1) - V i‖ / plen V m - ‖V' (i + 1) - V' i‖ / plen V' m| := fun i _ => by
        rw [← abs_neg]; ring_nf
      rw [Finset.sum_congr rfl e]
      calc _ ≤ 2 * (∑ i ∈ Finset.range m, |‖V (i + 1) - V i‖ - ‖V' (i + 1) - V' i‖|) /
            plen V m := hW
        _ ≤ 2 * (m * (4 * τ)) / (1 / 2) := by
            gcongr
            linarith
        _ = 16 * m * τ := by ring
    have key := abs_logCov_aligned_le (N := m + 1) (cfgG x y V (plen V m))
      (cfgG x' y' V' (plen V' m)) (x', y') (ℓ := 1 / (4 * (M : ℝ))) (ρ := 7) (u := 2 * τ)
      (A := 2) (B := 16 * m * τ) hℓ (by linarith)
      (by rw [cfgG_sum hLpos.ne', cfgG_sum hLpos'.ne'])
      (fun i hi => ⟨(hseg i hi).1, (hseg' i hi).1⟩) (hseg' 0 (by omega)).1
      (fun i hi => ⟨(hseg' i hi).2.1, (hseg' i hi).2.2⟩)
      (hseg' 0 (by omega)).2 hclose (by rw [cfgG_tv hLpos]) hB
    refine (le_abs_self _).trans (key.trans ?_)
    -- `(2 √(2τ) + 16 m τ √14)² ≤ (2√2 + 48 M √14)² τ`
    have hsτ : √τ ≤ 1 := by rw [Real.sqrt_le_one]; exact hτ.le
    have hsτ0 : 0 ≤ √τ := Real.sqrt_nonneg _
    have hττ : τ ≤ √τ := by
      calc τ = √τ * √τ := (Real.mul_self_sqrt hτ0).symm
        _ ≤ √τ * 1 := by gcongr
        _ = √τ := mul_one _
    have hm3' : (m : ℝ) ≤ 3 * M := by exact_mod_cast hm3
    have hX0 : 0 ≤ 2 * √(2 * τ) + 16 * m * τ * √(2 * 7) := by positivity
    have hX : 2 * √(2 * τ) + 16 * m * τ * √(2 * 7) ≤ (2 * √2 + 48 * (M : ℝ) * √(2 * 7)) * √τ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : 16 * (m : ℝ) * τ * √(2 * 7) ≤ 48 * M * √(2 * 7) * √τ := by
        have hs14 : 0 ≤ √(2 * 7 : ℝ) := Real.sqrt_nonneg _
        calc 16 * (m : ℝ) * τ * √(2 * 7) ≤ 16 * (3 * M) * √τ * √(2 * 7) := by gcongr
          _ = 48 * M * √(2 * 7) * √τ := by ring
      nlinarith
    have hG := gcst_nonneg (1 / (4 * (M : ℝ)))
    calc 256 * gcst (1 / (4 * (M : ℝ))) * (2 * √(2 * τ) + 16 * m * τ * √(2 * 7)) ^ 2
        ≤ 256 * gcst (1 / (4 * (M : ℝ))) * ((2 * √2 + 48 * (M : ℝ) * √(2 * 7)) * √τ) ^ 2 := by
          gcongr
      _ = Ka M * τ := by
          unfold Ka; rw [mul_pow, Real.sq_sqrt hτ0]; ring
      _ ≤ Ksm M * τ := by unfold Ksm; nlinarith [Kc_nonneg M]

/-- Diameter constant of the small family. -/
def Dsm (M : ℕ) : ℝ := 2 * M * (3 * M + 14)

/-- **Diameter of the small family.** -/
theorem small_diam {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {k : ℕ}
    {c c' : Config} (hc : c ∈ smallFamily M δ k) (hc' : c' ∈ smallFamily M δ k) :
    ‖psm M c - psm M c'‖ ≤ Dsm M * (δ * √((k : ℝ) + 1)) := by
  obtain ⟨x, y, z, rfl, hg⟩ := small_data hc
  obtain ⟨x', y', z', rfl, hg'⟩ := small_data hc'
  obtain ⟨-, -, -, -, hV7, -, -, -⟩ := hg.basic hM hδ
  obtain ⟨-, -, -, -, hV7', -, -, -⟩ := hg'.basic hM hδ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hsk0 : 0 ≤ δ * √((k : ℝ) + 1) := mul_nonneg hδ.1.le (Real.sqrt_nonneg _)
  unfold psm
  rcases le_or_gt 1 (4 * M * ((k : ℝ) + 1) * δ ^ 2) with hbig | hsm
  · -- trivial diameter
    have h2 : 1 ≤ 2 * M * (δ * √((k : ℝ) + 1)) := by
      have hsq : (2 * M * (δ * √((k : ℝ) + 1))) ^ 2 = 4 * M * M * ((k : ℝ) + 1) * δ ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
      have h3 : 1 ≤ (2 * M * (δ * √((k : ℝ) + 1))) ^ 2 := by
        rw [hsq]
        have : 4 * M * ((k : ℝ) + 1) * δ ^ 2 ≤ 4 * M * M * ((k : ℝ) + 1) * δ ^ 2 := by
          have : 0 ≤ 4 * M * ((k : ℝ) + 1) * δ ^ 2 := by positivity
          nlinarith
        linarith
      have h4 : 0 ≤ 2 * M * (δ * √((k : ℝ) + 1)) := by positivity
      nlinarith
    have hA : (3 * M + 14 : ℝ) ≤ Dsm M * (δ * √((k : ℝ) + 1)) := by
      unfold Dsm
      have : (3 * M + 14 : ℝ) * 1 ≤ (3 * M + 14) * (2 * M * (δ * √((k : ℝ) + 1))) := by
        gcongr
      nlinarith
    refine le_trans (cpar_diam (by positivity) (fun i _ => ?_) ?_) hA
    · calc ‖vx z i - vx z' i‖ ≤ ‖vx z i‖ + ‖vx z' i‖ := norm_sub_le _ _
        _ ≤ 7 + 7 := add_le_add (hV7 i) (hV7' i)
        _ ≤ 3 * M + 14 := by linarith
    · have h1 : 2 ≤ z.length := by have := hg.m1; omega
      have h2 : 2 ≤ z'.length := by have := hg'.m1; omega
      have h3 : z.length ≤ 3 * M + 1 := by have := hg.m3; omega
      have h4 : z'.length ≤ 3 * M + 1 := by have := hg'.m3; omega
      have h1' : (2 : ℝ) ≤ z.length := by exact_mod_cast h1
      have h2' : (2 : ℝ) ≤ z'.length := by exact_mod_cast h2
      have h3' : (z.length : ℝ) ≤ 3 * M + 1 := by exact_mod_cast h3
      have h4' : (z'.length : ℝ) ≤ 3 * M + 1 := by exact_mod_cast h4
      rw [abs_le]; constructor <;> linarith
  · -- near-straight polygons
    obtain ⟨hmM, hstr⟩ := hg.straight hM hδ hsm
    obtain ⟨hmM', hstr'⟩ := hg'.straight hM hδ hsm
    have hD14 : (14 : ℝ) ≤ Dsm M := by
      unfold Dsm; nlinarith
    refine cpar_diam (by positivity) (fun i _ => ?_) ?_
    · rcases le_or_gt i M with hiM | hiM
      · calc ‖vx z i - vx z' i‖ = ‖(vx z i - (((i : ℝ) / M : ℝ) : ℂ)) -
              (vx z' i - (((i : ℝ) / M : ℝ) : ℂ))‖ := by ring_nf
          _ ≤ ‖vx z i - (((i : ℝ) / M : ℝ) : ℂ)‖ + ‖vx z' i - (((i : ℝ) / M : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ 7 * δ * √((k : ℝ) + 1) + 7 * δ * √((k : ℝ) + 1) :=
              add_le_add (hstr i hiM) (hstr' i hiM)
          _ = 14 * (δ * √((k : ℝ) + 1)) := by ring
          _ ≤ Dsm M * (δ * √((k : ℝ) + 1)) := by gcongr
      · rw [hg.pad i (by omega), hg'.pad i (by omega), sub_self, norm_zero]
        positivity
    · have hl : z.length = z'.length := by omega
      rw [hl, sub_self, abs_zero]; positivity

/-! ## Large family -/

/-- Parameters of the large family: the four endpoints. -/
def pl (c : Config) : Fin (2 * 4 + 1) → ℝ := cpar 4 (vx (c.1 ++ c.2)) 0

/-- Canonical-distance constant of the large family. -/
def Kl (M : ℕ) : ℝ := 256 * gcst (1 / (4 * (M : ℝ))) * 8

lemma Kl_nonneg (M : ℕ) : 0 ≤ Kl M := by
  unfold Kl; have := gcst_nonneg (1 / (4 * (M : ℝ))); positivity

/-- Geometry of a large-excess configuration. -/
lemma large_geom {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {x y x' y' : ℂ}
    (hx : ‖x‖ ≤ cellRad M * δ) (hy : ‖y - 1‖ ≤ cellRad M * δ) (h1 : ‖x' - x‖ ≤ 4 * ‖y - x‖)
    (h2 : ‖y' - x‖ ≤ 4 * ‖y - x‖) (h3 : ‖y - x‖ / (2 * M) ≤ ‖y' - x'‖) :
    1 / (4 * (M : ℝ)) ≤ ‖y - x‖ ∧ 1 / (4 * (M : ℝ)) ≤ ‖y' - x'‖ ∧ ‖x‖ ≤ 9 ∧ ‖y‖ ≤ 9 ∧
      ‖x'‖ ≤ 9 ∧ ‖y'‖ ≤ 9 := by
  obtain ⟨hR1, hR2, hx64, hy2⟩ := chord_bounds (cellRad_mul_le hM hδ) hx hy
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hq : 1 / (4 * (M : ℝ)) ≤ ‖y - x‖ / (2 * M) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hq2 : 1 / (4 * (M : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (16 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hx' : ‖x'‖ ≤ ‖x' - x‖ + ‖x‖ := by
    calc ‖x'‖ = ‖(x' - x) + x‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have hy' : ‖y'‖ ≤ ‖y' - x‖ + ‖x‖ := by
    calc ‖y'‖ = ‖(y' - x) + x‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  refine ⟨by linarith, hq.trans h3, by linarith, by linarith, by linarith, by linarith⟩

lemma cfgComb_large {x y x' y' : ℂ} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    cfgComb ([x, y], [x', y']) = (List.range 2).map (cfgG x y (vx [x', y']) (‖y' - x'‖)) := by
  rw [cfgComb_eq hxy [x', y']]
  have : plen (vx [x', y']) ([x', y'].length - 1) = ‖y' - x'‖ := by
    simp [plen, vx]
  rw [this]
  rfl

/-- **Canonical distance of the large family.** -/
theorem large_canon {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {c c' : Config} (hc : c ∈ largeFamily M δ) (hc' : c' ∈ largeFamily M δ) :
    SegComb.logCov (SegComb.sub (cfgComb c) (cfgComb c')) (SegComb.sub (cfgComb c) (cfgComb c'))
      ≤ Kl M * ‖pl c - pl c'‖ := by
  obtain ⟨x, y, x', y', rfl, hx, hy, h1, h2, h3, -⟩ := hc
  obtain ⟨u, v, u', v', rfl, hu, hv, g1, g2, g3, -⟩ := hc'
  obtain ⟨l1, l2, b1, b2, b3, b4⟩ := large_geom hM hδ hx hy h1 h2 h3
  obtain ⟨m1, m2, c1, c2, c3, c4⟩ := large_geom hM hδ hu hv g1 g2 g3
  have hℓ : (0 : ℝ) < 1 / (4 * (M : ℝ)) := by
    have : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  have ne1 : x ≠ y := by intro h; rw [h, sub_self, norm_zero] at l1; linarith
  have ne2 : x' ≠ y' := by intro h; rw [h, sub_self, norm_zero] at l2; linarith
  have ne3 : u ≠ v := by intro h; rw [h, sub_self, norm_zero] at m1; linarith
  have ne4 : u' ≠ v' := by intro h; rw [h, sub_self, norm_zero] at m2; linarith
  rw [cfgComb_large ne1 ne2, cfgComb_large ne3 ne4]
  set τ := ‖pl ([x, y], [x', y']) - pl ([u, v], [u', v'])‖ with hτdef
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hcl := (cpar_close (le_refl τ)).1
  have e0 := hcl 0 (by norm_num)
  have e1 := hcl 1 (by norm_num)
  have e2 := hcl 2 (by norm_num)
  have e3 := hcl 3 (by norm_num)
  simp only [vx, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ] at e0 e1 e2 e3
  have hn2 : ‖y' - x'‖ ≠ 0 := by linarith
  have hn4 : ‖v' - u'‖ ≠ 0 := by linarith
  have key := abs_logCov_aligned_le (N := 2) (cfgG x y (vx [x', y']) (‖y' - x'‖))
    (cfgG u v (vx [u', v']) (‖v' - u'‖)) (u, v) (ℓ := 1 / (4 * (M : ℝ))) (ρ := 9) (u := 2 * τ)
    (A := 2) (B := 0) hℓ (by linarith) ?_ ?_ m1 ?_ ⟨c1, c2⟩ ?_ ?_ ?_
  · refine (le_abs_self _).trans (key.trans (le_of_eq ?_))
    rw [zero_mul, add_zero, mul_pow, Real.sq_sqrt (by linarith)]
    unfold Kl; ring
  · simp [Finset.sum_range_succ, cfgG, vx, div_self hn2, div_self hn4]
  · intro i hi
    interval_cases i
    · exact ⟨l1, m1⟩
    · exact ⟨l2, m2⟩
  · intro i hi
    interval_cases i
    · exact ⟨c1, c2⟩
    · exact ⟨c3, c4⟩
  · intro i hi
    interval_cases i
    · exact ⟨e0, e1⟩
    · exact ⟨e2, e3⟩
  · simp [Finset.sum_range_succ, cfgG, vx, div_self hn2]; norm_num
  · simp [Finset.sum_range_succ, cfgG, vx, div_self hn2, div_self hn4]

/-- **Diameter of the large family.** -/
theorem large_diam {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {c c' : Config} (hc : c ∈ largeFamily M δ) (hc' : c' ∈ largeFamily M δ) :
    ‖pl c - pl c'‖ ≤ 18 := by
  obtain ⟨x, y, x', y', rfl, hx, hy, h1, h2, h3, -⟩ := hc
  obtain ⟨u, v, u', v', rfl, hu, hv, g1, g2, g3, -⟩ := hc'
  obtain ⟨-, -, b1, b2, b3, b4⟩ := large_geom hM hδ hx hy h1 h2 h3
  obtain ⟨-, -, c1, c2, c3, c4⟩ := large_geom hM hδ hu hv g1 g2 g3
  refine cpar_diam (by norm_num) (fun i hi => ?_) (by simp)
  have hb : ∀ p q : ℂ, ‖p‖ ≤ 9 → ‖q‖ ≤ 9 → ‖p - q‖ ≤ 18 := fun p q hp hq =>
    (norm_sub_le _ _).trans (by linarith)
  interval_cases i
  · simpa [vx] using hb _ _ b1 c1
  · simpa [vx] using hb _ _ b2 c2
  · simpa [vx] using hb _ _ b3 c3
  · simpa [vx] using hb _ _ b4 c4

end LQGDimension.RMCrude
