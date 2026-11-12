/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Glue3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue2

/-!
# DDDF Prop 26, Step 1: the gluing `S6Step1Glue` (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1289–1294: "`Γ_{k,n} := ⋃_{P ∈ π_k^k} S^{(k,n+k)}(P)` contains a left-right crossing of `[0,1]²`
whose length is bounded above by `Σ_P L^{(n+k)}(S^{(k,n+k)}(P)) ≤ Σ_P L^{(k,n+k)}(S(P)) e^{ξ max φ_{0,k}}`".
Proof (own elementary argument; DDDF leave the gluing to the reader): at unit scale (field
`(f+g)(2^{-k} ·)` on `[0, 2^k]²`, `rectLen_rectAB_mul`), the visited blocks form a `*`-connected
graph joining a block at the left side to one at the right side (`S6.exists_blk`, `S6.reach_end`);
around the clamped site `clampB 1 (2^k − 2) P` (so that the circuit lies in `[0,1]²`, cf. DDDF's
silence at the boundary, D-DDDF-22) we take near-optimal long crossings of the four site rectangles
for `g`, whose `(f+g)`-length is at most `w(P)` times their `g`-length (`S6U.lfppLen_add_le`), and
glue them (`rectLen_le_glue`). Constant `C₁ = 12` (factor 3 from the gluing, 4 rectangles).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP S6U

/-- **DDDF Prop 26, Step 1, the gluing** (l. 1289–1294). -/
theorem s6_step1_glue (ξ : ℝ) : S6Step1Glue ξ := by
  classical
  refine ⟨12, by norm_num, fun k hk => ?_⟩
  set N : ℕ := 2 ^ k with hNdef
  set h : ℝ := (2 : ℝ)⁻¹ ^ k with hhdef
  have hp : 0 < h := by positivity
  have hNr : (N : ℝ) = (2 : ℝ) ^ k := by simp [N]
  have hhN : h * (N : ℝ) = 1 := by rw [hNr, hhdef, ← mul_pow]; norm_num
  have hN4 : 4 ≤ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hN3 : 3 ≤ N := by omega
  set circ : ℤ × ℤ → Finset (Circle × ℂ) := fun b =>
    Finset.univ.image (siteJ k (clampB 1 ((N : ℤ) - 2) b)) with hcirc
  refine ⟨circ, fun b => ?_, fun f g hf hg γ hγ w hw => ?_⟩
  · have : (circ b).card ≤ 4 := (Finset.card_image_le).trans (by simp)
    have : ((circ b).card : ℝ) ≤ 4 := by exact_mod_cast this
    linarith
  set S := T20.coarseBlocks k γ with hSdef
  set gs : ℂ → ℝ := fun x => g ((h : ℂ) * x) with hgs
  set fs : ℂ → ℝ := fun x => f ((h : ℂ) * x) with hfs
  have hgsc : Continuous gs := hg.comp (continuous_const.mul continuous_id)
  -- the walk of visited blocks
  obtain ⟨z0, hz0, w1, hw1, hpc, hU⟩ := hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨u, huI, hu0⟩ := S6.exists_blk (K := k) (hU 0 h0)
  have huS : u ∈ S := Finset.mem_filter.2 ⟨huI, 0, h0, hu0⟩
  obtain ⟨v, hvS, hv1, hreach⟩ := S6.reach_end ⟨z0, hz0, w1, hw1, hpc, hU⟩ huS hu0
  obtain ⟨p⟩ := hreach
  have hG : ∀ x y, (S6.blkGraph S).Adj x y → |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1 :=
    fun x y hxy => ⟨hxy.2.2.2.1, hxy.2.2.2.2⟩
  have hSupp : ∀ x ∈ p.support, x ∈ S := by
    have key : ∀ {a b : ℤ × ℤ} (q : (S6.blkGraph S).Walk a b), a ∈ S → ∀ x ∈ q.support, x ∈ S := by
      intro a b q
      induction q with
      | nil => intro ha x hx; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
               exact hx ▸ ha
      | cons hadj q ih =>
        intro ha x hx
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih hadj.2.2.1 x hx
    exact key p huS
  have hu : u.1 ≤ 1 := by
    have e0 : (γ 0).re = 0 := by rw [hpc.source]; exact (mem_rectAB_side₁.1 hz0).1
    have := (S6.mem_dyBlock hu0).1
    rw [e0] at this
    have : (u.1 : ℝ) ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : u.1 ≤ 0 := by exact_mod_cast this
    omega
  have hv : (N : ℤ) - 2 ≤ v.1 := by
    have e1 : (γ 1).re = 1 := by rw [hpc.target]; exact (mem_rectAB_side₂.1 hw1).1
    have := (S6.mem_dyBlock hv1).2.1
    rw [e1, ← hhdef] at this
    have : (N : ℝ) ≤ (v.1 : ℝ) + 1 := by
      have h2 := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ N)
      have e : ((v.1 : ℝ) + 1) * h * N = (v.1 : ℝ) + 1 := by rw [mul_assoc, hhN, mul_one]
      linarith
    have : (N : ℤ) ≤ v.1 + 1 := by exact_mod_cast this
    omega
  -- the circuits
  set m : ℤ × ℤ → Fin 4 → ℝ := fun x i =>
    T20B.mrectLen ξ g k (siteJ k (clampB 1 ((N : ℤ) - 2) x) i).1
      (siteJ k (clampB 1 ((N : ℤ) - 2) x) i).2 3 1 with hmdef
  have hm0 : ∀ x i, 0 ≤ m x i := fun x i => ENNReal.toReal_nonneg
  have hcircs : ∀ ε : ℝ, 0 < ε → ∀ x : ℤ × ℤ, ∃ c : ℝ≥0∞,
      Nonempty (SiteCirc ξ (fun y => fs y + gs y) (clampB 1 ((N : ℤ) - 2) x) c) ∧
      (x ∈ S → c ≤ ENNReal.ofReal (w x * ((N : ℝ) * ∑ i, m x i + 4 * ε))) := by
    intro ε hε x
    set z := clampB 1 ((N : ℤ) - 2) x
    have hpath : ∀ i : Fin 4, ∃ P, AdmPath (siteR z i).toSet (siteR z i).side₁ (siteR z i).side₂ P ∧
        lfppLen ξ gs P < rectLen ξ gs (siteR z i) + ENNReal.ofReal ε := fun i =>
      exists_admPath_lt (ENNReal.lt_add_right
        (rectLen_ne_top _ (siteR_wh z i).1 (siteR_wh z i).2 hgsc)
        (by simpa using hε))
    choose P hPa hPl using hpath
    refine ⟨∑ i, lfppLen ξ (fun y => fs y + gs y) (P i),
      ⟨⟨P 0, P 1, P 2, P 3, hPa 0, hPa 1, hPa 2, hPa 3, by simp [Fin.sum_univ_four]⟩⟩, ?_⟩
    intro hxS
    have hxI : x ∈ T20.blkIdx k := (Finset.mem_filter.1 hxS).1
    obtain ⟨y0, hy0⟩ := nonempty_glueBox k x
    have hw0 : 0 ≤ w x := (Real.exp_pos _).le.trans (hw x hxS y0 hy0)
    have hone : ∀ i, lfppLen ξ (fun y => fs y + gs y) (P i) ≤
        ENNReal.ofReal (w x * ((N : ℝ) * m x i + ε)) := by
      intro i
      have hW : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp (ξ * fs (P i t)) ≤ w x := by
        intro t ht
        obtain ⟨_, _, _, _, _, hPU⟩ := hPa i
        exact hw x hxS _ (scaled_mem_glueBox hk hxI i (hPU t ht))
      calc lfppLen ξ (fun y => fs y + gs y) (P i) ≤ ENNReal.ofReal (w x) * lfppLen ξ gs (P i) :=
            lfppLen_add_le hW
        _ ≤ ENNReal.ofReal (w x) * (rectLen ξ gs (siteR z i) + ENNReal.ofReal ε) := by
            gcongr; exact (hPl i).le
        _ = ENNReal.ofReal (w x * ((N : ℝ) * m x i + ε)) := by
            rw [rectLen_siteR hg k z i, ← hNr, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (mul_nonneg (by positivity) (hm0 x i)) hε.le,
              ← ENNReal.ofReal_mul hw0]
    calc ∑ i, lfppLen ξ (fun y => fs y + gs y) (P i)
        ≤ ∑ i, ENNReal.ofReal (w x * ((N : ℝ) * m x i + ε)) := Finset.sum_le_sum fun i _ => hone i
      _ = ENNReal.ofReal (∑ i, w x * ((N : ℝ) * m x i + ε)) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg hw0 (add_nonneg (mul_nonneg (by positivity) (hm0 x i)) hε.le)).symm
      _ = ENNReal.ofReal (w x * ((N : ℝ) * ∑ i, m x i + 4 * ε)) := by
          congr 1; simp only [Fin.sum_univ_four]; ring
  -- assembling, for each `ε > 0`
  have hS0 : ∀ x ∈ S, 0 ≤ w x := fun x hx => by
    obtain ⟨y0, hy0⟩ := nonempty_glueBox k x
    exact (Real.exp_pos _).le.trans (hw x hx y0 hy0)
  set Wsum : ℝ := ∑ b ∈ S, w b with hWsum
  have hW0 : 0 ≤ Wsum := Finset.sum_nonneg hS0
  have hm4 : ∀ x, ∑ i, m x i ≤ 4 * ∑ j ∈ circ x, T20B.mrectLen ξ g k j.1 j.2 3 1 := by
    intro x
    have hle : ∀ i, m x i ≤ ∑ j ∈ circ x, T20B.mrectLen ξ g k j.1 j.2 3 1 := fun i =>
      Finset.single_le_sum (f := fun j : Circle × ℂ => T20B.mrectLen ξ g k j.1 j.2 3 1)
        (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    calc ∑ i, m x i ≤ ∑ _i : Fin 4, ∑ j ∈ circ x, T20B.mrectLen ξ g k j.1 j.2 3 1 :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 4 * ∑ j ∈ circ x, T20B.mrectLen ξ g k j.1 j.2 3 1 := by simp
  have hscale : rectLen ξ (fun x => f x + g x) (rectAB 1 1) =
      ENNReal.ofReal h * rectLen ξ (fun y => fs y + gs y) (rectAB N N) := by
    have := rectLen_rectAB_mul (ξ := ξ) (fun x => f x + g x) hp (N : ℝ) (N : ℝ)
    rw [hhN] at this
    exact this
  have hε : ∀ ε : ℝ, 0 < ε → (rectLen ξ (fun x => f x + g x) (rectAB 1 1)).toReal ≤
      12 * ∑ b ∈ S, w b * ∑ j ∈ circ b, T20B.mrectLen ξ g k j.1 j.2 3 1 + 12 * h * ε * Wsum := by
    intro ε hε
    choose c hc using hcircs ε hε
    have C : ∀ x, SiteCirc ξ (fun y => fs y + gs y) (clampB 1 ((N : ℤ) - 2) x) (c x) :=
      fun x => (hc x).1.some
    have hglue := rectLen_le_glue (ξ := ξ) (f := fun y => fs y + gs y) hN3 hG S p hSupp hu hv c C
    have hcv : c v ≤ ∑ x ∈ S, c x :=
      Finset.single_le_sum (f := c) (fun _ _ => by positivity) hvS
    have hT0 : ∀ x ∈ S, 0 ≤ w x * ((N : ℝ) * ∑ i, m x i + 4 * ε) := fun x hx =>
      mul_nonneg (hS0 x hx) (add_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => hm0 x i)) (by positivity))
    have hsum : ∑ x ∈ S, c x ≤
        ENNReal.ofReal (∑ x ∈ S, w x * ((N : ℝ) * ∑ i, m x i + 4 * ε)) := by
      rw [ENNReal.ofReal_sum_of_nonneg hT0]
      exact Finset.sum_le_sum fun x hx => (hc x).2 hx
    have hbd : rectLen ξ (fun x => f x + g x) (rectAB 1 1) ≤
        ENNReal.ofReal (3 * h * ∑ x ∈ S, w x * ((N : ℝ) * ∑ i, m x i + 4 * ε)) := by
      rw [hscale]
      calc ENNReal.ofReal h * rectLen ξ (fun y => fs y + gs y) (rectAB N N)
          ≤ ENNReal.ofReal h * (2 * ∑ x ∈ S, c x + c v) := by gcongr
        _ ≤ ENNReal.ofReal h * (3 * ∑ x ∈ S, c x) := by
            gcongr
            calc 2 * ∑ x ∈ S, c x + c v ≤ 2 * ∑ x ∈ S, c x + ∑ x ∈ S, c x := by gcongr
              _ = 3 * ∑ x ∈ S, c x := by ring
        _ ≤ ENNReal.ofReal h *
              (3 * ENNReal.ofReal (∑ x ∈ S, w x * ((N : ℝ) * ∑ i, m x i + 4 * ε))) := by gcongr
        _ = _ := by
            rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul hp.le]
            congr 1; ring
    have hreal := ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by positivity) (Finset.sum_nonneg hT0)) hbd
    refine hreal.trans ?_
    have e : 3 * h * ∑ x ∈ S, w x * ((N : ℝ) * ∑ i, m x i + 4 * ε) =
        3 * ∑ x ∈ S, w x * ∑ i, m x i + 12 * h * ε * Wsum := by
      rw [hWsum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [show 3 * h * (w x * ((N : ℝ) * ∑ i, m x i + 4 * ε)) =
        3 * (w x * ∑ i, m x i) * (h * N) + 12 * h * ε * w x by ring, hhN]
      ring
    rw [e]
    have : 3 * ∑ x ∈ S, w x * ∑ i, m x i ≤
        12 * ∑ b ∈ S, w b * ∑ j ∈ circ b, T20B.mrectLen ξ g k j.1 j.2 3 1 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x hx => ?_
      have := mul_le_mul_of_nonneg_left (hm4 x) (hS0 x hx)
      nlinarith
    linarith
  -- `ε → 0`
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hK : 0 ≤ 12 * h * Wsum := mul_nonneg (by positivity) hW0
  refine (hε (δ / (12 * h * Wsum + 1)) (by positivity)).trans ?_
  have h1 : (12 * h * Wsum) / (12 * h * Wsum + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h2 : 12 * h * (δ / (12 * h * Wsum + 1)) * Wsum =
      δ * ((12 * h * Wsum) / (12 * h * Wsum + 1)) := by ring
  have h3 : δ * ((12 * h * Wsum) / (12 * h * Wsum + 1)) ≤ δ := by
    have := mul_le_mul_of_nonneg_left h1 hδ.le
    linarith
  linarith

end DDDF
end LQGMetric
