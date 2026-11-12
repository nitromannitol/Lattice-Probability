/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16D1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16C
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16, lower bound: tools for the covering argument (packet P-126, DEC-126 §4)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.16
(DG:1443–1512). DG's loop erasure (DG:1458–1476) is replaced by a covering argument (DEC-126 §4,
DV-D126-2): squares met by a sampled path form a chain (`p16d_chain_of_samples`, the walk/bypass
construction of `p17_exists_chain`); each square `S` either sees an arc of the path of
displacement `≥ a` inside the `2a`-neighbourhood `N(S)` (`p16d_exit`, the `sInf` pattern of
`p17_exit`; `p16d_arc_ge`, chord ≤ arclength `DFGPS.L36.dgPath_chord_le`), or the path stays in
`N(S)`; each point lies in at most `36` of the `N(S)` (`p16d_card_near`), and
`p16d_sum_restrict_le` sums the arcs.

Conventions: `a = 2^{-m}`, sup norm `p16dSup x = max |x.re| |x.im|`,
`N(S) = {x : p16dSup (x − v_S) ≤ 5a/2}`. (`m_δ`: `p17s_dgM` gives `2^{-m_δ} ≤ δ < 2·2^{-m_δ}`.)
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint

/-! ## The sup norm -/

/-- the sup norm `‖x‖_∞ = max |Re x| |Im x|` -/
def p16dSup (x : ℂ) : ℝ := max |x.re| |x.im|

lemma p16d_sup_le_norm (x : ℂ) : p16dSup x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm x) (Complex.abs_im_le_norm x)

lemma p16d_norm_le_sup (x : ℂ) : ‖x‖ ≤ 2 * p16dSup x := by
  have h := p16_norm_le (x := x) (y := 0) (r := p16dSup x) (by simp [p16dSup])
    (by simp [p16dSup])
  simpa using h

lemma p16d_sup_sub (x y : ℂ) : p16dSup x ≤ p16dSup (x - y) + p16dSup y := by
  unfold p16dSup
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 := abs_sub_abs_le_abs_sub x.re y.re
  have h2 := abs_sub_abs_le_abs_sub x.im y.im
  refine max_le ?_ ?_
  · linarith [le_max_left |x.re - y.re| |x.im - y.im|, le_max_left |y.re| |y.im|]
  · linarith [le_max_right |x.re - y.re| |x.im - y.im|, le_max_right |y.re| |y.im|]

lemma p16d_sup_comm (x y : ℂ) : p16dSup (x - y) = p16dSup (y - x) := by
  simp only [p16dSup, Complex.sub_re, Complex.sub_im, abs_sub_comm x.re, abs_sub_comm x.im]

lemma p16d_continuous_sup : Continuous p16dSup :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

/-! ## Grid geometry -/

lemma p16d_coord_near {a x y : ℝ} (ha : 0 < a) {i j : ℤ} (hx1 : (i : ℝ) * a ≤ x)
    (hx2 : x ≤ (i + 1) * a) (hy1 : (j : ℝ) * a ≤ y) (hy2 : y ≤ (j + 1) * a) (h : |x - y| < a) :
    |i - j| ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  have f1 : (i : ℝ) - j < 2 := by
    by_contra hc; push Not at hc; nlinarith
  have f2 : (j : ℝ) - i < 2 := by
    by_contra hc; push Not at hc; nlinarith
  have g1 : i - j < 2 := by exact_mod_cast f1
  have g2 : j - i < 2 := by exact_mod_cast f2
  rw [abs_le]; constructor <;> omega

/-- squares containing points at sup-distance `< a` are within index distance `1` -/
lemma p16d_idx_near {m : ℕ} {k k' : ℤ × ℤ} {x y : ℂ} (hx : x ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k)
    (hy : y ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k') (h : p16dSup (x - y) < (2 : ℝ)⁻¹ ^ m) :
    |k.1 - k'.1| ≤ 1 ∧ |k.2 - k'.2| ≤ 1 := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have hre : |x.re - y.re| < (2 : ℝ)⁻¹ ^ m := by
    have := le_max_left |(x - y).re| |(x - y).im|
    simp only [Complex.sub_re] at this; unfold p16dSup at h; simp only [Complex.sub_re] at h
    linarith
  have him : |x.im - y.im| < (2 : ℝ)⁻¹ ^ m := by
    have := le_max_right |(x - y).re| |(x - y).im|
    simp only [Complex.sub_im] at this; unfold p16dSup at h; simp only [Complex.sub_im] at h
    linarith
  exact ⟨p16d_coord_near ha x1 x2 y1 y2 hre, p16d_coord_near ha x3 x4 y3 y4 him⟩

lemma p16d_coord_center {a x : ℝ} (ha : 0 < a) {i j : ℤ} (h1 : (i : ℝ) * a ≤ x)
    (h2 : x ≤ (i + 1) * a) (hij : |j - i| ≤ 1) : |x - (j + 1 / 2) * a| ≤ 3 * a / 2 := by
  obtain ⟨c1, c2⟩ := abs_le.1 hij
  have d1 : (-1 : ℝ) ≤ j - i := by exact_mod_cast c1
  have d2 : (j : ℝ) - i ≤ 1 := by exact_mod_cast c2
  rw [abs_le]; constructor <;> nlinarith

/-- a point of a square is within sup-distance `3a/2` of the centre of a neighbouring square -/
lemma p16d_sup_center_near {m : ℕ} {k k' : ℤ × ℤ} {x : ℂ}
    (hx : x ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k') (h1 : |k.1 - k'.1| ≤ 1) (h2 : |k.2 - k'.2| ≤ 1) :
    p16dSup (x - dgCenter m k) ≤ 3 * (2 : ℝ)⁻¹ ^ m / 2 := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  obtain ⟨x1, x2, x3, x4⟩ := hx
  exact max_le (by simpa [dgCenter] using p16d_coord_center ha x1 x2 h1)
    (by simpa [dgCenter] using p16d_coord_center ha x3 x4 h2)

lemma p16d_sup_center {m : ℕ} {k : ℤ × ℤ} {x : ℂ} (hx : x ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k) :
    p16dSup (x - dgCenter m k) ≤ (2 : ℝ)⁻¹ ^ m / 2 := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  refine max_le ?_ ?_ <;> simp only [dgCenter, Complex.sub_re, Complex.sub_im] <;>
    rw [abs_le] <;> constructor <;> linarith

lemma p16d_center_mem {m : ℕ} {k : ℤ × ℤ} (hk : k ∈ dgIdx m) : dgCenter m k ∈ closedUnitSquare :=
  p16_sq_sub hk (p16_center_mem_sq m k)

/-! ## Chains from sampled points -/

lemma p16d_walk_eq_or_adj {V : Type} {G : SimpleGraph V} {u v : V} (h : u = v ∨ G.Adj u v) :
    ∃ q : G.Walk u v, ∀ x ∈ q.support, x = u ∨ x = v := by
  rcases h with rfl | h
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, by simp⟩

lemma p16d_abs_one {i j : ℤ} (h : |i - j| ≤ 1) (hne : i ≠ j) : |i - j| = 1 := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  rw [abs_eq zero_le_one]; omega

/-- one step between squares at index distance `≤ 1` (through `(k'.1, k.2)` at a diagonal step) -/
lemma p16d_walk_step {m : ℕ} (u v : {k : ℤ × ℤ // k ∈ dgIdx m}) (h1 : |u.1.1 - v.1.1| ≤ 1)
    (h2 : |u.1.2 - v.1.2| ≤ 1) :
    ∃ q : (p17Grid m).Walk u v, ∀ x ∈ q.support, |x.1.1 - u.1.1| ≤ 1 ∧ |x.1.2 - u.1.2| ≤ 1 := by
  set c : {k : ℤ × ℤ // k ∈ dgIdx m} :=
    ⟨(v.1.1, u.1.2), ⟨v.2.1, v.2.2.1, u.2.2.2.1, u.2.2.2.2⟩⟩ with hc
  have huc : u = c ∨ (p17Grid m).Adj u c := by
    by_cases h : u.1.1 = v.1.1
    · left; exact Subtype.ext (Prod.ext h rfl)
    · right
      show |u.1.1 - v.1.1| + |u.1.2 - u.1.2| = 1
      rw [p16d_abs_one h1 h]; simp
  have hcv : c = v ∨ (p17Grid m).Adj c v := by
    by_cases h : u.1.2 = v.1.2
    · left; exact Subtype.ext (Prod.ext rfl h)
    · right
      show |v.1.1 - v.1.1| + |u.1.2 - v.1.2| = 1
      rw [p16d_abs_one h2 h]; simp
  obtain ⟨q1, hq1⟩ := p16d_walk_eq_or_adj huc
  obtain ⟨q2, hq2⟩ := p16d_walk_eq_or_adj hcv
  have hu : |u.1.1 - u.1.1| ≤ 1 ∧ |u.1.2 - u.1.2| ≤ 1 := by simp
  have hcu : |c.1.1 - u.1.1| ≤ 1 ∧ |c.1.2 - u.1.2| ≤ 1 := by
    simp only [hc]; rw [abs_sub_comm]; simpa using h1
  have hvu : |v.1.1 - u.1.1| ≤ 1 ∧ |v.1.2 - u.1.2| ≤ 1 := by
    rw [abs_sub_comm, abs_sub_comm v.1.2]; exact ⟨h1, h2⟩
  refine ⟨q1.append q2, fun x hx => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff q1 q2).1 hx with hx | hx
  · rcases hq1 x hx with rfl | rfl
    · exact hu
    · exact hcu
  · rcases hq2 x hx with rfl | rfl
    · exact hcu
    · exact hvu

/-- a walk through a sequence of squares at index distance `≤ 1` -/
lemma p16d_walk_samples {m : ℕ} (k : ℕ → {k : ℤ × ℤ // k ∈ dgIdx m}) :
    ∀ n : ℕ, (∀ i < n, |(k i).1.1 - (k (i + 1)).1.1| ≤ 1 ∧ |(k i).1.2 - (k (i + 1)).1.2| ≤ 1) →
      ∃ q : (p17Grid m).Walk (k 0) (k n), ∀ x ∈ q.support,
        ∃ i ≤ n, |x.1.1 - (k i).1.1| ≤ 1 ∧ |x.1.2 - (k i).1.2| ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨SimpleGraph.Walk.nil, fun x hx => ⟨0, le_rfl, ?_⟩⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst hx; simp
  | succ n ih =>
    intro hk
    obtain ⟨q, hq⟩ := ih fun i hi => hk i (by omega)
    obtain ⟨q', hq'⟩ := p16d_walk_step (k n) (k (n + 1)) (hk n (by omega)).1 (hk n (by omega)).2
    refine ⟨q.append q', fun x hx => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff q q').1 hx with hx | hx
    · obtain ⟨i, hi, h⟩ := hq x hx; exact ⟨i, by omega, h⟩
    · exact ⟨n, by omega, hq' x hx⟩

/-- the bypass of a grid walk is a chain of squares (as in `p17_exists_chain`) -/
lemma p16d_chain_of_walk {m : ℕ} {a b : {k : ℤ × ℤ // k ∈ dgIdx m}} (q : (p17Grid m).Walk a b)
    {z w : ℂ} (hz : z ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) a.1) (hw : w ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) b.1) :
    IsDGSqChain m z w (q.bypass.support.map Subtype.val) ∧
      ∀ k ∈ q.bypass.support.map Subtype.val, ∃ x ∈ q.support, x.1 = k := by
  classical
  have hq : q.bypass.IsPath := q.bypass_isPath
  refine ⟨⟨(List.nodup_map_iff Subtype.val_injective).2 hq.support_nodup,
    fun k hk => ?_, ?_, ⟨a.1, ?_, hz⟩, ⟨b.1, ?_, hw⟩⟩, fun k hk => ?_⟩
  · obtain ⟨k', -, rfl⟩ := List.mem_map.1 hk; exact k'.2
  · exact List.isChain_map_of_isChain (R := (p17Grid m).Adj) Subtype.val (fun x y h => h)
      q.bypass.isChain_adj_support
  · rw [← SimpleGraph.Walk.cons_tail_support]; exact Option.mem_def.2 rfl
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _),
      SimpleGraph.Walk.getLast_support]; simp
  · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
    exact ⟨k', q.support_bypass_subset_support hk', rfl⟩

/-- **chain through sampled points**: if `x 0 = z`, `x n = w`, all `x i ∈ 𝕊` and consecutive
samples are at sup-distance `< a`, there is a chain of squares from `z` to `w` each of whose
squares has its centre within sup-distance `3a/2` of some sample -/
theorem p16d_chain_of_samples (m : ℕ) {z w : ℂ} (x : ℕ → ℂ) (n : ℕ)
    (hx : ∀ i ≤ n, x i ∈ closedUnitSquare) (h0 : x 0 = z) (hn : x n = w)
    (hstep : ∀ i < n, p16dSup (x i - x (i + 1)) < (2 : ℝ)⁻¹ ^ m) :
    ∃ L : List (ℤ × ℤ), IsDGSqChain m z w L ∧
      ∀ k ∈ L, ∃ i ≤ n, p16dSup (x i - dgCenter m k) ≤ 3 * (2 : ℝ)⁻¹ ^ m / 2 := by
  have hsq : ∀ i, ∃ k : {k : ℤ × ℤ // k ∈ dgIdx m}, i ≤ n → x i ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k.1 :=
    fun i => by
      by_cases hi : i ≤ n
      · obtain ⟨k, hk, hxk⟩ := p17_exists_sq m (hx i hi); exact ⟨⟨k, hk⟩, fun _ => hxk⟩
      · obtain ⟨k, hk, -⟩ := p17_exists_sq m (hx 0 (Nat.zero_le _))
        exact ⟨⟨k, hk⟩, fun h => absurd h hi⟩
  choose K hK using hsq
  obtain ⟨q, hq⟩ := p16d_walk_samples K n fun i hi =>
    p16d_idx_near (hK i hi.le) (hK (i + 1) hi) (hstep i hi)
  obtain ⟨hL, hLs⟩ := p16d_chain_of_walk q (z := z) (w := w) (by rw [← h0]; exact hK 0 (Nat.zero_le _))
    (by rw [← hn]; exact hK n le_rfl)
  refine ⟨_, hL, fun k hk => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hLs k hk
  obtain ⟨i, hi, h1, h2⟩ := hq y hy
  exact ⟨i, hi, p16d_sup_center_near (hK i hi) h1 h2⟩

/-! ## Exit from a neighbourhood -/

/-- first passage above `β` after `t` (the `sInf` pattern of `p17_exit`) -/
lemma p16d_exit_fwd {g : ℝ → ℝ} {t s β : ℝ} (hts : t ≤ s) (hg : ContinuousOn g (Icc t s))
    (ht : g t < β) (hs : β ≤ g s) :
    ∃ v ∈ Icc t s, β ≤ g v ∧ ∀ r ∈ Icc t v, g r ≤ β := by
  set T := Icc t s ∩ g ⁻¹' Ici β
  have hTc : IsClosed T := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsT : s ∈ T := ⟨⟨hts, le_rfl⟩, hs⟩
  have hTb : BddBelow T := ⟨t, fun r hr => hr.1.1⟩
  have hvT : sInf T ∈ T := hTc.csInf_mem ⟨s, hsT⟩ hTb
  set v := sInf T
  have hbefore : ∀ r ∈ Icc t v, r < v → g r < β := fun r hr hrv => by
    by_contra hc; push Not at hc
    exact absurd (csInf_le hTb ⟨⟨hr.1, hr.2.trans hvT.1.2⟩, hc⟩) (not_le.2 hrv)
  have htv : t < v := by
    rcases hvT.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hvT.2; rw [← h] at this; exact absurd this (not_le.2 ht)
  refine ⟨v, hvT.1, hvT.2, fun r hr => ?_⟩
  rcases hr.2.lt_or_eq with h | h
  · exact (hbefore r hr h).le
  · have hC : IsClosed (Icc t v ∩ g ⁻¹' Iic β) :=
      (hg.mono (Icc_subset_Icc le_rfl hvT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Iic
    have hsub : closure (Ico t v) ⊆ Icc t v ∩ g ⁻¹' Iic β :=
      hC.closure_subset_iff.2 fun y hy => ⟨Ico_subset_Icc_self hy,
        (hbefore y (Ico_subset_Icc_self hy) hy.2).le⟩
    rw [closure_Ico htv.ne] at hsub
    rw [h]; exact (hsub ⟨htv.le, le_rfl⟩).2

/-- **exit from `N(c)`**: if `p t` is within sup-distance `3a/2` of `c` and `p s` is at
sup-distance `≥ 5a/2`, an arc of `p` inside `{p16dSup (· − c) ≤ 5a/2}` has displacement `≥ a` -/
theorem p16d_exit {S : Set ℂ} {z w : ℂ} {p : ℝ → ℂ} (hp : IsDGPath S z w p) {a : ℝ} (ha : 0 < a)
    {c : ℂ} {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hpt : p16dSup (p t - c) ≤ 3 * a / 2) (hps : 5 * a / 2 ≤ p16dSup (p s - c)) :
    ∃ u v : ℝ, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧ (∀ r ∈ Icc u v, p16dSup (p r - c) ≤ 5 * a / 2) ∧
      a ≤ ‖p v - p u‖ := by
  have hgc : ContinuousOn (fun r => p16dSup (p r - c)) (Icc 0 1) :=
    p16d_continuous_sup.comp_continuousOn (hp.continuousOn.sub continuousOn_const)
  have hlt : p16dSup (p t - c) < 5 * a / 2 := by linarith
  rcases le_total t s with hts | hst
  · obtain ⟨v, hv, hv1, hv2⟩ := p16d_exit_fwd hts (hgc.mono (Icc_subset_Icc ht.1 hs.2)) hlt hps
    refine ⟨t, v, ht.1, hv.1, hv.2.trans hs.2, hv2, ?_⟩
    have := p16d_sup_sub (p v - c) (p t - c)
    rw [sub_sub_sub_cancel_right] at this
    linarith [p16d_sup_le_norm (p v - p t)]
  · have hg' : ContinuousOn (fun r => p16dSup (p (-r) - c)) (Icc (-t) (-s)) := by
      refine hgc.comp continuousOn_neg fun r hr => ?_
      exact ⟨by linarith [hr.2, hs.1], by linarith [hr.1, ht.2]⟩
    obtain ⟨v, hv, hv1, hv2⟩ := p16d_exit_fwd (neg_le_neg hst) hg' (by simpa using hlt)
      (by simpa using hps)
    refine ⟨-v, t, by linarith [hv.2, hs.1], by linarith [hv.1], ht.2, fun r hr => ?_, ?_⟩
    · have := hv2 (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
      simpa using this
    · have := p16d_sup_sub (p (-v) - c) (p t - c)
      rw [sub_sub_sub_cancel_right] at this
      linarith [p16d_sup_le_norm (p (-v) - p t), norm_sub_rev (p t) (p (-v))]

/-! ## Integrals along the path -/

/-- the LFPP integrand of a DG path in `S` is integrable for `φ` continuous on `S` -/
lemma p16d_integrableOn {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ} (hφ : ContinuousOn φ S) {z w : ℂ}
    {p : ℝ → ℂ} (hp : IsDGPath S z w p) :
    IntegrableOn (fun r => Real.exp (ξ * φ (p r)) * ‖deriv p r‖) (Icc 0 1) := by
  have hd : IntegrableOn (fun r => ‖deriv p r‖) (Icc (0 : ℝ) 1) := by
    have h := (DFGPS.L36.dgPath_deriv_intervalIntegrable hp).norm
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 h
  have hg : ContinuousOn (fun r => Real.exp (ξ * φ (p r))) (Icc 0 1) :=
    Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hφ.comp hp.continuousOn hp.mapsTo))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact hd.bdd_mul (c := C) (hg.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hC))

/-- **arc bound**: `e^{ξ c} |p(v) − p(u)| ≤ ∫_u^v e^{ξ φ(p)} |p'|` if `φ ∘ p ≥ c` on `[u, v]` -/
theorem p16d_arc_ge {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : ℂ → ℝ} {S : Set ℂ} (hφ : ContinuousOn φ S)
    {z w : ℂ} {p : ℝ → ℂ} (hp : IsDGPath S z w p) {u v c : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) (hc : ∀ r ∈ Icc u v, c ≤ φ (p r)) :
    Real.exp (ξ * c) * ‖p v - p u‖ ≤ ∫ r in u..v, Real.exp (ξ * φ (p r)) * ‖deriv p r‖ := by
  have hI := DFGPS.L36.intervalIntegrable_sub01
    (DFGPS.L36.dgPath_deriv_intervalIntegrable hp).norm hu huv hv
  have hJ : IntervalIntegrable (fun r => Real.exp (ξ * φ (p r)) * ‖deriv p r‖) volume u v := by
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le huv]
    exact (p16d_integrableOn hφ hp).mono_set (Icc_subset_Icc hu hv)
  calc Real.exp (ξ * c) * ‖p v - p u‖
      ≤ Real.exp (ξ * c) * ∫ r in u..v, ‖deriv p r‖ :=
        mul_le_mul_of_nonneg_left (DFGPS.L36.dgPath_chord_le hp hu huv hv) (Real.exp_pos _).le
    _ = ∫ r in u..v, Real.exp (ξ * c) * ‖deriv p r‖ := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ _ := intervalIntegral.integral_mono_on huv (hI.const_mul _) hJ fun r hr =>
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hc r hr) hξ))
          (norm_nonneg _)

/-- an interval integral of a nonnegative function over `[u, v] ⊆ A` is at most its integral over
`A` -/
lemma p16d_interval_le_set {f : ℝ → ℝ} (hf : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ f r)
    (hint : IntegrableOn f (Icc 0 1)) {A : Set ℝ} (hAm : MeasurableSet A) (hA : A ⊆ Icc 0 1)
    {u v : ℝ} (huv : u ≤ v) (hsub : Icc u v ⊆ A) : ∫ r in u..v, f r ≤ ∫ r in A, f r := by
  rw [intervalIntegral.integral_of_le huv]
  exact setIntegral_mono_set (hint.mono_set hA)
    (ae_restrict_of_forall_mem hAm fun r hr => hf r (hA hr))
    (Ioc_subset_Icc_self.trans hsub).eventuallyLE

/-- **bounded multiplicity**: `Σ_i ∫_{A_i} f ≤ M ∫_{[0,1]} f` if every `r` lies in at most `M`
of the sets `A_i ⊆ [0,1]` -/
theorem p16d_sum_restrict_le {ι : Type} (F : Finset ι) (A : ι → Set ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) (hAs : ∀ i ∈ F, A i ⊆ Icc 0 1) {f : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ f r) (hint : IntegrableOn f (Icc 0 1)) {M : ℝ}
    (hM : ∀ r ∈ Icc (0 : ℝ) 1, ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ)) r ≤ M) :
    ∑ i ∈ F, ∫ r in A i, f r ≤ M * ∫ r in Icc 0 1, f r := by
  have e : ∀ i ∈ F, ∫ r in A i, f r = ∫ r in Icc 0 1, (A i).indicator f r := fun i hi => by
    rw [setIntegral_indicator (hA i hi), inter_eq_right.2 (hAs i hi)]
  rw [Finset.sum_congr rfl e, ← integral_finsetSum _ fun i hi => hint.indicator (hA i hi),
    ← integral_const_mul]
  refine setIntegral_mono_on (integrable_finsetSum _ fun i hi => hint.indicator (hA i hi))
    (hint.const_mul M) measurableSet_Icc fun r hr => ?_
  have e2 : ∀ i, (A i).indicator f r = f r * (A i).indicator (fun _ => (1 : ℝ)) r := fun i => by
    by_cases h : r ∈ A i <;> simp [h]
  simp only [e2]
  rw [← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM r hr) (hf r hr)

/-- **at most 36 centres** within sup-distance `5a/2` of a point -/
theorem p16d_card_near (m : ℕ) (F : Finset (ℤ × ℤ)) (x : ℂ) :
    (F.filter fun k => p16dSup (x - dgCenter m k) ≤ 5 * (2 : ℝ)⁻¹ ^ m / 2).card ≤ 36 := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ m
  have ha : 0 < a := by positivity
  set j1 := ⌊x.re / a⌋
  set j2 := ⌊x.im / a⌋
  have e1 : (j1 : ℝ) * a ≤ x.re := by
    have := Int.floor_le (x.re / a); rwa [le_div_iff₀ ha] at this
  have e1' : x.re < (j1 + 1) * a := by
    have := Int.lt_floor_add_one (x.re / a); rwa [div_lt_iff₀ ha] at this
  have e2 : (j2 : ℝ) * a ≤ x.im := by
    have := Int.floor_le (x.im / a); rwa [le_div_iff₀ ha] at this
  have e2' : x.im < (j2 + 1) * a := by
    have := Int.lt_floor_add_one (x.im / a); rwa [div_lt_iff₀ ha] at this
  have key : ∀ (j : ℤ) (y : ℝ) (i : ℤ), (j : ℝ) * a ≤ y → y < (j + 1) * a →
      |y - (i + 1 / 2) * a| ≤ 5 * a / 2 → i ∈ Finset.Icc (j - 3) (j + 2) := by
    intro j y i h1 h2 h3
    obtain ⟨h3, h4⟩ := abs_le.1 h3
    have f1 : (j : ℝ) - 3 ≤ i := by by_contra hc; push Not at hc; nlinarith
    have f2 : (i : ℝ) < j + 3 := by by_contra hc; push Not at hc; nlinarith
    have g1 : j - 3 ≤ i := by exact_mod_cast f1
    have g2 : i < j + 3 := by exact_mod_cast f2
    rw [Finset.mem_Icc]; omega
  have hsub : (F.filter fun k => p16dSup (x - dgCenter m k) ≤ 5 * a / 2) ⊆
      Finset.Icc (j1 - 3) (j1 + 2) ×ˢ Finset.Icc (j2 - 3) (j2 + 2) := by
    intro k hk
    have hk := (Finset.mem_filter.1 hk).2
    rw [Finset.mem_product]
    refine ⟨key j1 x.re k.1 e1 e1' ?_, key j2 x.im k.2 e2 e2' ?_⟩
    · have := (le_max_left _ _).trans hk; simpa only [dgCenter, Complex.sub_re] using this
    · have := (le_max_right _ _).trans hk; simpa only [dgCenter, Complex.sub_im] using this
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have : (j1 + 2 + 1 - (j1 - 3)).toNat = 6 := by omega
  have h2 : (j2 + 2 + 1 - (j2 - 3)).toNat = 6 := by omega
  rw [this, h2]

/-- the centre of a square containing `z` has `φ̂(v_S) ≤ ĥ_δ(v_{S_z})` (`dgMaxSq`) -/
theorem p16d_le_dgMaxSq {δ : ℝ} (φh : ℂ → ℝ) {z : ℂ} {k : ℤ × ℤ} (hk : k ∈ dgIdx (dgM δ))
    (hz : z ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k) : φh (dgCenter (dgM δ) k) ≤ dgMaxSq δ φh z := by
  unfold dgMaxSq
  have hfin : (dgIdx (dgM δ)).Finite :=
    ((Set.finite_Icc (0 : ℤ) (2 ^ dgM δ)).prod (Set.finite_Icc (0 : ℤ) (2 ^ dgM δ))).subset
      fun k hk => ⟨⟨hk.1, hk.2.1.le⟩, ⟨hk.2.2.1, hk.2.2.2.le⟩⟩
  have : Finite (dgIdx (dgM δ)) := hfin.to_subtype
  have : Finite {k : ℤ × ℤ // k ∈ dgIdx (dgM δ) ∧ z ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : dgIdx (dgM δ)))
      fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)
  exact le_ciSup (f := fun k : {k : ℤ × ℤ // k ∈ dgIdx (dgM δ) ∧
      z ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k} => φh (dgCenter (dgM δ) k.1))
    (Set.finite_range _).bddAbove ⟨k, hk, hz⟩

end LQGMetric.DG
