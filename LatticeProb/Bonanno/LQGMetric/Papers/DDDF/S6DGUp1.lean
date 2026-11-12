/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGUp1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Graph

/-!
# DDDF (5.78), deterministic part: a graph path of `(0,1)² ∩ δℤ²` gives a crossing (P2-DDDFDG)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1276–1281 (`eq:DGupperQuantile`, "follows the same
lines as" (5.54)). The upper bound is taken from DFGPS Lemma 3.6 (upper half at `𝕣 = 1`,
`DFGPS.L36.Lem3_6UpperOne`, proved from DG Prop 3.21): a path `π` of the graph `(0,1)² ∩ δℤ²`
(steps `δ` or `√2 δ`) from a leftmost to a rightmost vertex with `Σ_{x∈π} e^{ξ h_δ(x)}` small.
Here (`rectLen_le_graph`): the polygon through the vertices of `π`, extended by horizontal
segments of length `≤ δ` to the two sides of `[0,1]²`, is a left–right crossing of `[0,1]²`, and
if `|g(z) − f(w)| ≤ c` whenever `|z − w| ≤ 2δ`, then
`L_{1,1}(f) ≤ 6δ Σ_{x∈π} e^{ξ g(x)} e^{ξ c}`. (Own elementary argument, the continuum/graph
comparison DFGPS T:1612–1626 leave implicit; it is the mirror of
`DFGPS.L36.dgSetDist_le_graphPath`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open LFPP DFGPS Blueprint

variable {ξ : ℝ} {f : ℂ → ℝ}

lemma norm_segPath_sub_left_le (x y : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segPath x y t - x‖ ≤ ‖x - y‖ := by
  simp only [segPath, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [norm_sub_rev]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

lemma norm_segPath_sub_right_le (x y : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segPath x y t - y‖ ≤ ‖x - y‖ := by
  have e : segPath x y t - y = (1 - t) • (x - y) := by
    simp only [segPath, Complex.real_smul]; push_cast; ring
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])

/-- the polygon through a chain of points of a convex set, with steps `≤ d` -/
lemma list_path {S : Set ℂ} (hS : Convex ℝ S) {d : ℝ} (hd : 0 ≤ d) {B : ℂ → ℝ}
    (hB : ∀ x ∈ S, ∀ u ∈ S, ‖u - x‖ ≤ d → Real.exp (ξ * f u) ≤ B x) :
    ∀ (L : List ℂ) (x : ℂ), (∀ y ∈ x :: L, y ∈ S) →
      (x :: L).IsChain (fun a b => ‖a - b‖ ≤ d) →
      ∃ Γ : ℝ → ℂ, IsPiecewiseC1Path Γ x ((x :: L).getLast (List.cons_ne_nil x L)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Γ t ∈ S) ∧
        lfppLen ξ f Γ ≤ ENNReal.ofReal (d * ((x :: L).map B).sum) := by
  intro L
  induction L with
  | nil =>
    intro x hx _
    have hxS : x ∈ S := hx x List.mem_cons_self
    refine ⟨segPath x x, isPiecewiseC1Path_segPath x x, fun t ht => ?_, ?_⟩
    · unfold segPath; exact hS.add_smul_sub_mem hxS hxS ht
    · refine (S6.lfppLen_seg_le (B := B x) x x fun u hu => hB x hxS _ ?_ ?_).trans ?_
      · unfold segPath; exact hS.add_smul_sub_mem hxS hxS hu
      · simpa [segPath] using hd
      · simp
  | cons y L ih =>
    intro x hx hch
    rw [List.isChain_cons_cons] at hch
    have hxS : x ∈ S := hx x List.mem_cons_self
    have hyS : y ∈ S := hx y (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨Γ', h1, h2, h3⟩ := ih y (fun z hz => hx z (List.mem_cons_of_mem _ hz)) hch.2
    have hBx : 0 ≤ B x := (Real.exp_pos _).le.trans (hB x hxS x hxS (by simpa using hd))
    have hsum : 0 ≤ ((y :: L).map B).sum := List.sum_nonneg fun b hb => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
      have hzS : z ∈ S := hx z (List.mem_cons_of_mem _ hz)
      exact (Real.exp_pos _).le.trans (hB z hzS z hzS (by simpa using hd))
    have hj : segPath x y 1 = Γ' 0 := by rw [h1.source]; simp [segPath]
    have hsegS : ∀ t ∈ Icc (0 : ℝ) 1, segPath x y t ∈ S := fun t ht => by
      unfold segPath; exact hS.add_smul_sub_mem hxS hyS ht
    refine ⟨concatPath (segPath x y) Γ', isPiecewiseC1Path_concatPath
      (isPiecewiseC1Path_segPath x y) h1, S6.concat_mem hsegS h2, ?_⟩
    rw [lfppLen_concatPath hj]
    have hseg : lfppLen ξ f (segPath x y) ≤ ENNReal.ofReal (B x * ‖y - x‖) :=
      S6.lfppLen_seg_le x y fun u hu => hB x hxS _ (hsegS u hu)
        ((norm_segPath_sub_left_le x y hu).trans hch.1)
    calc lfppLen ξ f (segPath x y) + lfppLen ξ f Γ'
        ≤ ENNReal.ofReal (B x * ‖y - x‖) + ENNReal.ofReal (d * ((y :: L).map B).sum) :=
          add_le_add hseg h3
      _ = ENNReal.ofReal (B x * ‖y - x‖ + d * ((y :: L).map B).sum) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (d * ((x :: y :: L).map B).sum) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e : ((x :: y :: L).map B).sum = B x + ((y :: L).map B).sum := by simp
          rw [e]
          have : ‖y - x‖ ≤ d := by rw [norm_sub_rev]; exact hch.1
          nlinarith [mul_le_mul_of_nonneg_left this hBx]

/-- the vertices of `(0,1)² ∩ δℤ²` furthest to the right are within `δ` of the right side -/
lemma one_sub_le_re_of_mem_rightVerts {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {x : ℂ}
    (hx : x ∈ rightVerts δ 1) : 1 - δ ≤ x.re := by
  set a : ℤ := ⌈1 / δ⌉ - 1 with ha
  have h1 : 1 / δ ≤ (⌈1 / δ⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈1 / δ⌉ : ℝ) < 1 / δ + 1 := Int.ceil_lt_add_one _
  have e : 1 / δ * δ = 1 := by field_simp
  have hlo : 1 - δ ≤ (a : ℝ) * δ := by
    rw [ha]; push_cast; nlinarith
  have hhi : (a : ℝ) * δ < 1 := by
    rw [ha]; push_cast; nlinarith
  have hy : (⟨(a : ℝ) * δ, ((1 : ℤ) : ℝ) * δ⟩ : ℂ) ∈ rS 1 ∩ gridPts δ :=
    ⟨L36.mem_rS_one.2 ⟨by linarith, hhi, by simp [hδ], by simp [hδ1]⟩, ⟨a, 1, rfl⟩⟩
  have := hx.2 _ hy
  simp only at this
  linarith

lemma mem_unit_of_mem_rS {x : ℂ} (hx : x ∈ rS 1) : x ∈ (rectAB 1 1).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := L36.mem_rS_one.1 hx
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add]
  exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

/-- **Graph path to crossing.** If `|g(z) − f(w)| ≤ c` for `z, w ∈ [0,1]²` with `|z − w| ≤ 2δ`,
then a graph path `π` of `(0,1)² ∩ δℤ²` from a leftmost to a rightmost vertex gives
`L_{1,1}(f) ≤ 6δ Σ_{x∈π} e^{ξ g(x)} e^{ξ c}`. -/
theorem rectLen_le_graph (hξ : 0 ≤ ξ) {δ c : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {g : ℂ → ℝ}
    (hfg : ∀ z ∈ (rectAB 1 1).toSet, ∀ w ∈ (rectAB 1 1).toSet, ‖z - w‖ ≤ 2 * δ →
      |g z - f w| ≤ c)
    {L : List ℂ} (hL : IsGraphPath δ (rS 1) L)
    (hl : ∃ x ∈ L.head?, x ∈ leftVerts δ 1) (hr : ∃ y ∈ L.getLast?, y ∈ rightVerts δ 1) :
    rectLen ξ f (rectAB 1 1) ≤
      ENNReal.ofReal (6 * δ * (L.map fun x => Real.exp (ξ * g x) * Real.exp (ξ * c)).sum) := by
  set S := (rectAB 1 1).toSet with hSdef
  have hS : Convex ℝ S := S6.convex_unit
  set B : ℂ → ℝ := fun x => Real.exp (ξ * g x) * Real.exp (ξ * c) with hBdef
  have hB : ∀ x ∈ S, ∀ u ∈ S, ‖u - x‖ ≤ 2 * δ → Real.exp (ξ * f u) ≤ B x := by
    intro x hx u hu hux
    rw [norm_sub_rev] at hux
    have h := (abs_le.1 (hfg x hx u hu hux)).1
    simp only [hBdef, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  obtain ⟨hne, hmem, hch⟩ := hL
  obtain ⟨x, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨x', hx', hxl⟩ := hl
  obtain ⟨y, hy, hyr⟩ := hr
  have hxx : x' = x := by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx'
    exact hx'.symm
  rw [hxx] at hxl
  replace hy : (x :: L').getLast (List.cons_ne_nil x L') = y := by
    rw [Option.mem_def, List.getLast?_eq_some_getLast (List.cons_ne_nil x L')] at hy
    exact Option.some.inj hy
  have hLS : ∀ z ∈ x :: L', z ∈ S := fun z hz => mem_unit_of_mem_rS (hmem z hz).1
  have hch2 : (x :: L').IsChain (fun a b => ‖a - b‖ ≤ 2 * δ) := hch.imp fun a b h => by
    rcases h with h | h
    · rw [h]; linarith
    · rw [h]; have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith
  obtain ⟨Γ, hΓ1, hΓ2, hΓ3⟩ := list_path hS (by linarith) hB L' x hLS hch2
  rw [hy] at hΓ1
  have hxS := hLS x List.mem_cons_self
  have hyS : y ∈ S := hy ▸ hLS _ (List.getLast_mem _)
  have hxre := L36.re_le_of_mem_leftVerts hδ hδ1 hxl
  have hyre := one_sub_le_re_of_mem_rightVerts hδ hδ1 hyr
  have hx0 := (L36.mem_rS_one.1 (hmem x List.mem_cons_self).1)
  have hy0 := (L36.mem_rS_one.1 (hmem _ (List.getLast_mem (List.cons_ne_nil x L'))).1)
  rw [hy] at hy0
  set a : ℂ := ⟨0, x.im⟩ with ha
  set b : ℂ := ⟨1, y.im⟩ with hb
  have haS : a ∈ S := by
    simp only [hSdef, MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add, ha]
    exact ⟨⟨le_rfl, zero_le_one⟩, hx0.2.2.1.le, hx0.2.2.2.le⟩
  have hbS : b ∈ S := by
    simp only [hSdef, MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add, hb]
    exact ⟨⟨zero_le_one, le_rfl⟩, hy0.2.2.1.le, hy0.2.2.2.le⟩
  have hax : ‖a - x‖ ≤ δ := by
    have : a - x = ((-x.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [ha]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hx0.1]; exact hxre
  have hyb : ‖y - b‖ ≤ δ := by
    have : y - b = ((y.re - 1 : ℝ) : ℂ) := by apply Complex.ext <;> simp [hb]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [hy0.2.1])]
    linarith
  have hseg1S : ∀ t ∈ Icc (0 : ℝ) 1, segPath a x t ∈ S := fun t ht => by
    unfold segPath; exact hS.add_smul_sub_mem haS hxS ht
  have hseg2S : ∀ t ∈ Icc (0 : ℝ) 1, segPath y b t ∈ S := fun t ht => by
    unfold segPath; exact hS.add_smul_sub_mem hyS hbS ht
  have hBnn : ∀ z, 0 ≤ B z := fun z => by positivity
  have hsum0 : 0 ≤ ((x :: L').map B).sum := List.sum_nonneg fun b hb => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hb; exact hBnn z
  have hBx : B x ≤ ((x :: L').map B).sum := by
    rw [List.map_cons, List.sum_cons]
    have : 0 ≤ (L'.map B).sum := List.sum_nonneg fun b hb => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hb; exact hBnn z
    linarith
  have hBy : B y ≤ ((x :: L').map B).sum :=
    List.single_le_sum (fun b hb => by obtain ⟨z, -, rfl⟩ := List.mem_map.1 hb; exact hBnn z)
      _ (List.mem_map_of_mem (hy ▸ List.getLast_mem _))
  have hl1 : lfppLen ξ f (segPath a x) ≤ ENNReal.ofReal (B x * ‖x - a‖) :=
    S6.lfppLen_seg_le a x fun u hu => hB x hxS _ (hseg1S u hu)
      ((norm_segPath_sub_right_le a x hu).trans (by linarith))
  have hl2 : lfppLen ξ f (segPath y b) ≤ ENNReal.ofReal (B y * ‖b - y‖) :=
    S6.lfppLen_seg_le y b fun u hu => hB y hyS _ (hseg2S u hu)
      ((norm_segPath_sub_left_le y b hu).trans (by linarith))
  have hj1 : Γ 1 = segPath y b 0 := by rw [hΓ1.target]; simp [segPath]
  have hj2 : segPath a x 1 = concatPath Γ (segPath y b) 0 := by
    simp [segPath, concatPath, hΓ1.source]
  have hpath : AdmPath S (rectAB 1 1).side₁ (rectAB 1 1).side₂
      (concatPath (segPath a x) (concatPath Γ (segPath y b))) := by
    refine ⟨a, ?_, b, ?_, isPiecewiseC1Path_concatPath (isPiecewiseC1Path_segPath a x)
      (isPiecewiseC1Path_concatPath hΓ1 (isPiecewiseC1Path_segPath y b)),
      S6.concat_mem hseg1S (S6.concat_mem hΓ2 hseg2S)⟩
    · simp only [MarkedRect.side₁, rectAB, ite_true, Complex.mem_reProdIm, mem_singleton_iff,
        mem_Icc, zero_add, ha]
      exact ⟨trivial, hx0.2.2.1.le, hx0.2.2.2.le⟩
    · simp only [MarkedRect.side₂, rectAB, ite_true, Complex.mem_reProdIm, mem_singleton_iff,
        mem_Icc, zero_add, hb]
      exact ⟨trivial, hy0.2.2.1.le, hy0.2.2.2.le⟩
  refine (crossLenIn_le_lfppLen hpath).trans ?_
  rw [lfppLen_concatPath hj2, lfppLen_concatPath hj1]
  have e1 : ‖x - a‖ ≤ δ := by rw [norm_sub_rev]; exact hax
  have e2 : ‖b - y‖ ≤ δ := by rw [norm_sub_rev]; exact hyb
  calc lfppLen ξ f (segPath a x) + (lfppLen ξ f Γ + lfppLen ξ f (segPath y b))
      ≤ ENNReal.ofReal (B x * ‖x - a‖) + (ENNReal.ofReal (2 * δ * ((x :: L').map B).sum) +
          ENNReal.ofReal (B y * ‖b - y‖)) := add_le_add hl1 (add_le_add hΓ3 hl2)
    _ = ENNReal.ofReal (B x * ‖x - a‖ + (2 * δ * ((x :: L').map B).sum + B y * ‖b - y‖)) := by
        rw [ENNReal.ofReal_add (by positivity) (by have := hBnn y; positivity),
          ENNReal.ofReal_add (by have := hBnn x; positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (6 * δ * ((x :: L').map B).sum) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := hBnn x
        have := hBnn y
        have t1 : B x * ‖x - a‖ ≤ B x * δ := mul_le_mul_of_nonneg_left e1 (hBnn x)
        have t2 : B y * ‖b - y‖ ≤ B y * δ := mul_le_mul_of_nonneg_left e2 (hBnn y)
        nlinarith

end S6DG
end DDDF
end LQGMetric
