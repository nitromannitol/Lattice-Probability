/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10TailGeom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Chain
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10, Steps 1–2 (T:1875–1904, Figure `fig-diam`): paths crossing rectangles
inside each dyadic square `S ⊆ 𝕣𝕊` form a `#`-shaped set `X_S`; `X_S ∩ X_{S'} ≠ ∅` for every
dyadic child `S'` of `S`; since `X_{S_n(z)} → z`, `D_h(z, X_{S_0}; 𝕣𝕊)` is bounded by the sum over
`n` of the `D_h`-lengths of the paths forming `X_{S_n(z)}`.

**Modified geometry** (proposed DEVIATIONS entry). The paper crosses the `s × s/2` rectangles of
`S` between their short sides, which are not inside the open rectangle, so Proposition 3.1
(which needs `K₁, K₂ ⊆ U`) does not literally apply. In relative coordinates of a dyadic square
`w + s[0,1]²` we use instead:
* horizontal crossings `HCr … e`, `e ∈ {0, 1/2}`: paths from `{re = 1/16}` to `{re = 15/16}`
  staying in the strip `im ∈ [1/8 + e, 3/8 + e]` (given by Prop 3.1 with `U = (0,1) × (1/8+e, 3/8+e)`
  and `K₁, K₂` the segments `{1/16} × [3/16+e, 5/16+e]`, `{15/16} × [3/16+e, 5/16+e]`);
* a vertical crossing `VCr`: from `{im = 1/16}` to `{im = 15/16}` inside `re ∈ [1/8, 3/8]`.
Every horizontal crossing of `S` meets its vertical crossing (`meet_in`), and the horizontal
crossing of `S` at the height of a child `S'` meets the vertical crossing of `S'` (`meet_child`).
Three crossings per square suffice for the chaining (the paper's `#` uses four).
-/

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- **Crossing lemma in a box**: a horizontal crossing of `[a,b]` inside the horizontal strip
`[c,d]` meets a vertical crossing of `[c,d]` inside the vertical strip `[a,b]`. -/
lemma HV_meet_box {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {H V : ℝ → ℂ}
    (hH : ContinuousOn H (Icc 0 1)) (hV : ContinuousOn V (Icc 0 1))
    (hH0 : (H 0).re ≤ a) (hH1 : b ≤ (H 1).re) (hHm : ∀ t ∈ Icc (0 : ℝ) 1, (H t).im ∈ Icc c d)
    (hV0 : (V 0).im ≤ c) (hV1 : d ≤ (V 1).im) (hVm : ∀ t ∈ Icc (0 : ℝ) 1, (V t).re ∈ Icc a b) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, H t = V t' := by
  obtain ⟨a₁, b₁, ha, hab₁, hb, hHa, hHb, hHab⟩ :=
    RectCross.exists_sub_crossing (f := fun t => (H t).re)
    zero_le_one (Complex.continuous_re.comp_continuousOn hH) hab hH0 hH1
  obtain ⟨a', b', ha', hab', hb', hVa, hVb, hVab⟩ :=
    RectCross.exists_sub_crossing (f := fun t => (V t).im)
    zero_le_one (Complex.continuous_im.comp_continuousOn hV) hcd hV0 hV1
  have hsub : Icc a₁ b₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hb
  have hsub' : Icc a' b' ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha' hb'
  obtain ⟨u, hu, w, hw, huw⟩ := RectMeet.rect_crossings_meet a b c d
    (fun u => H (a₁ + u * (b₁ - a₁))) (fun u => V (b' - u * (b' - a')))
    (hH.comp (by fun_prop) fun u hu => hsub (affine_mem_Icc hab₁ hu))
    (hV.comp (by fun_prop) fun u hu => hsub' (affine_mem_Icc' hab' hu))
    (fun u hu => ⟨hHab _ (affine_mem_Icc hab₁ hu), hHm _ (hsub (affine_mem_Icc hab₁ hu))⟩)
    (fun u hu => ⟨hVm _ (hsub' (affine_mem_Icc' hab' hu)), hVab _ (affine_mem_Icc' hab' hu)⟩)
    (by simpa using hHa) (by simpa using hHb) (by simpa using hVb) (by simpa using hVa)
  exact ⟨_, hsub (affine_mem_Icc hab₁ hu), _, hsub' (affine_mem_Icc' hab' hw), huw⟩

/-- a horizontal crossing of the dyadic square `w + s[0,1]²` at relative height `e` -/
def HCr (D : ContMetric) (Y : Set ℂ) (s : ℝ) (w : ℂ) (e : ℝ) (P : ℝ → ℂ) (L : ℝ) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ (P 0).re = w.re + s * (1 / 16) ∧ (P 1).re = w.re + s * (15 / 16) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, (P t).im ∈ Icc (w.im + s * (1 / 8 + e)) (w.im + s * (3 / 8 + e))) ∧
    MapsTo P (Icc 0 1) Y ∧ D.len P 0 1 ≤ ENNReal.ofReal L

/-- the vertical crossing of the dyadic square `w + s[0,1]²` -/
def VCr (D : ContMetric) (Y : Set ℂ) (s : ℝ) (w : ℂ) (P : ℝ → ℂ) (L : ℝ) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ (P 0).im = w.im + s * (1 / 16) ∧ (P 1).im = w.im + s * (15 / 16) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, (P t).re ∈ Icc (w.re + s * (1 / 8)) (w.re + s * (3 / 8))) ∧
    MapsTo P (Icc 0 1) Y ∧ D.len P 0 1 ≤ ENNReal.ofReal L

variable {D : ContMetric} {Y : Set ℂ}

lemma meet_in {s : ℝ} (hs : 0 < s) {w : ℂ} {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2)
    {H V : ℝ → ℂ} {L L' : ℝ} (hH : HCr D Y s w e H L) (hV : VCr D Y s w V L') :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, H t = V t' :=
  HV_meet_box (by nlinarith) (by nlinarith) hH.1 hV.1 (by rw [hH.2.1]; nlinarith)
    (by rw [hH.2.2.1]; nlinarith) hH.2.2.2.1 (by rw [hV.2.1]; nlinarith)
    (by rw [hV.2.2.1]; nlinarith) hV.2.2.2.1

lemma meet_child {s : ℝ} (hs : 0 < s) {w : ℂ} {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {H V : ℝ → ℂ} {L L' : ℝ} (hH : HCr D Y s w (β / 2) H L)
    (hV : VCr D Y (s / 2) (w + ⟨s / 2 * α, s / 2 * β⟩) V L') :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, H t = V t' := by
  obtain ⟨hVc, hV0, hV1, hVm, -⟩ := hV
  simp only [Complex.add_re, Complex.add_im] at hV0 hV1 hVm
  exact HV_meet_box (by nlinarith) (by nlinarith) hH.1 hVc (by rw [hH.2.1]; nlinarith)
    (by rw [hH.2.2.1]; nlinarith) hH.2.2.2.1 (by rw [hV0]; nlinarith) (by rw [hV1]; nlinarith) hVm

/-! ## Dyadic squares -/

/-- the bottom-left corner of the dyadic square `(j, k)` of side `𝕣 / 2ⁿ` -/
def dyCorner (𝕣 : ℝ) (n j k : ℕ) : ℂ := ⟨j * (𝕣 / 2 ^ n), k * (𝕣 / 2 ^ n)⟩

/-- the dyadic index of `x ∈ [0, 𝕣)` at level `n` -/
def dyIdx (𝕣 : ℝ) (n : ℕ) (x : ℝ) : ℕ := ⌊x * 2 ^ n / 𝕣⌋₊

lemma dyIdx_bounds {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyIdx 𝕣 n x : ℝ) * (𝕣 / 2 ^ n) ≤ x ∧ x < ((dyIdx 𝕣 n x : ℝ) + 1) * (𝕣 / 2 ^ n) := by
  have hy : 0 ≤ x * 2 ^ n / 𝕣 := by positivity
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one (x * 2 ^ n / 𝕣)
  unfold dyIdx
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ h2n]
    rw [le_div_iff₀ h𝕣] at h1; linarith
  · rw [← mul_div_assoc, lt_div_iff₀ h2n]
    rw [div_lt_iff₀ h𝕣] at h2; linarith

lemma dyIdx_lt {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx𝕣 : x < 𝕣) :
    dyIdx 𝕣 n x < 2 ^ n := by
  have h := (dyIdx_bounds h𝕣 n hx).1
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have : (dyIdx 𝕣 n x : ℝ) < 2 ^ n := by
    by_contra hc; push_neg at hc
    have : (2 : ℝ) ^ n * (𝕣 / 2 ^ n) ≤ (dyIdx 𝕣 n x : ℝ) * (𝕣 / 2 ^ n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    rw [mul_div_cancel₀ _ h2n.ne'] at this; linarith
  exact_mod_cast this

lemma dyIdx_succ {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∃ b : ℕ, b ≤ 1 ∧ dyIdx 𝕣 (n + 1) x = 2 * dyIdx 𝕣 n x + b := by
  set y := x * 2 ^ n / 𝕣 with hy
  have hy0 : 0 ≤ y := by positivity
  have e : x * 2 ^ (n + 1) / 𝕣 = 2 * y := by rw [hy, pow_succ]; ring
  have h1 := Nat.floor_le hy0
  have h2 := Nat.lt_floor_add_one y
  unfold dyIdx
  rw [e, ← hy]
  set m := ⌊y⌋₊
  rcases lt_or_ge (2 * y) (2 * m + 1) with h | h
  · refine ⟨0, zero_le_one, ?_⟩
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  · refine ⟨1, le_rfl, ?_⟩
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith

lemma dyCorner_succ (𝕣 : ℝ) (n j k a b : ℕ) :
    dyCorner 𝕣 (n + 1) (2 * j + a) (2 * k + b) =
      dyCorner 𝕣 n j k + ⟨𝕣 / 2 ^ n / 2 * a, 𝕣 / 2 ^ n / 2 * b⟩ := by
  apply Complex.ext <;> simp [dyCorner, pow_succ] <;> ring

end LQGMetric.DFGPS
