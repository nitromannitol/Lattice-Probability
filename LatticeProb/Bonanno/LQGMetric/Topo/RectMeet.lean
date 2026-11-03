/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.RectMeet at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A left–right and a top–bottom crossing of a closed rectangle meet (node RECT-X of TOPO-ORD)

If `γ, δ : [0, 1] → rect x₀ x₁ y₀ y₁` are continuous, `γ` runs from the left side to the right
side and `δ` from the top side to the bottom side, then `γ s = δ t` for some `s, t`.

This is the lemma of R. Maehara, *The Jordan curve theorem via the Brouwer fixed point theorem*,
Amer. Math. Monthly 91 (1984), 641–643, equivalently the Poincaré–Miranda theorem in dimension
two (W. Kulpa, *The Poincaré–Miranda theorem*, Amer. Math. Monthly 104 (1997), 545–550). Both
published proofs go through the Brouwer fixed point theorem, which is not in mathlib at our pin.
We use instead the standard winding-number proof of the two-dimensional Poincaré–Miranda
theorem, built on the loop degree of QuantumZipper (`QuantumZipper.CA.Topo.loopDeg`, Burckel,
*Classical Analysis in the Complex Plane*, Def. 4.2):

If `F (s, t) = γ s - δ t` never vanished on `[0, 1]²`, consider the loop
`L u = F (β u)`, where `β` is the radial projection of the circle of radius `1/2` about
`(1/2, 1/2)` onto the boundary of the square. Contracting the square to the corner `(0, 0)`
gives a homotopy (in `ℂ \ {0}`) from `L` to a constant loop, so `deg L = 0`. On each side of the
square `F` lies in a closed half-plane (`Re F ≤ 0` on `s = 0`, `Re F ≥ 0` on `s = 1`,
`Im F ≤ 0` on `t = 0`, `Im F ≥ 0` on `t = 1`), and `e^{2πiu}` lies in the corresponding open
half-plane at the parameters `u` mapped there; so the straight-line homotopy from `L` to
`u ↦ e^{2πiu}` avoids `0` and `deg L = 1`. (Own write-up of this standard argument; recorded
in `DEVIATIONS.md`.)
-/

namespace LQGMetric

namespace RectMeet

open Set Real
open QuantumZipper.CA.Topo

/-- The radial normaliser `max |cos| |sin|` at angle `2πu`; it is positive. -/
noncomputable def mx (u : ℝ) : ℝ := max |Real.cos (2 * π * u)| |Real.sin (2 * π * u)|

lemma mx_pos (u : ℝ) : 0 < mx u := by
  unfold mx
  by_contra h
  rw [not_lt, max_le_iff] at h
  have hc : Real.cos (2 * π * u) = 0 := abs_nonpos_iff.1 h.1
  have hs : Real.sin (2 * π * u) = 0 := abs_nonpos_iff.1 h.2
  have := Real.sin_sq_add_cos_sq (2 * π * u)
  rw [hc, hs] at this; norm_num at this

lemma continuous_mx : Continuous mx := by unfold mx; fun_prop

/-- First coordinate of the radial projection onto the boundary of `[0, 1]²`. -/
noncomputable def b₁ (u : ℝ) : ℝ := 1 / 2 + Real.cos (2 * π * u) / (2 * mx u)

/-- Second coordinate of the radial projection onto the boundary of `[0, 1]²`. -/
noncomputable def b₂ (u : ℝ) : ℝ := 1 / 2 + Real.sin (2 * π * u) / (2 * mx u)

lemma continuous_b₁ : Continuous b₁ := by
  unfold b₁
  exact continuous_const.add ((by fun_prop : Continuous fun u : ℝ => Real.cos (2 * π * u)).div
    (continuous_const.mul continuous_mx) fun u => by have := mx_pos u; positivity)

lemma continuous_b₂ : Continuous b₂ := by
  unfold b₂
  exact continuous_const.add ((by fun_prop : Continuous fun u : ℝ => Real.sin (2 * π * u)).div
    (continuous_const.mul continuous_mx) fun u => by have := mx_pos u; positivity)

lemma half_add_mem {c m : ℝ} (hm : 0 < m) (hc : |c| ≤ m) : 1 / 2 + c / (2 * m) ∈ Icc (0 : ℝ) 1 := by
  rw [abs_le] at hc
  constructor
  · have : -(1 / 2) ≤ c / (2 * m) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · have : c / (2 * m) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith

lemma b₁_mem (u : ℝ) : b₁ u ∈ Icc (0 : ℝ) 1 := half_add_mem (mx_pos u) (le_max_left _ _)

lemma b₂_mem (u : ℝ) : b₂ u ∈ Icc (0 : ℝ) 1 := half_add_mem (mx_pos u) (le_max_right _ _)

lemma b₁_zero_one : b₁ 0 = b₁ 1 := by simp [b₁, mx]

lemma b₂_zero_one : b₂ 0 = b₂ 1 := by simp [b₂, mx]

lemma half_add_eq_one {c m : ℝ} (hc : 0 < c) (hm : m = |c|) : 1 / 2 + c / (2 * m) = 1 := by
  rw [hm, abs_of_pos hc, div_mul_cancel_right₀ hc.ne']; norm_num

lemma half_add_eq_zero {c m : ℝ} (hc : c < 0) (hm : m = |c|) : 1 / 2 + c / (2 * m) = 0 := by
  rw [hm, abs_of_neg hc, mul_neg, div_neg, div_mul_cancel_right₀ hc.ne]; norm_num

/-- A point `(1 - r) L + r c` is nonzero if `L ≠ 0` and `L`, `c` lie in a common closed
half-plane through `0` with `c` in its interior (stated for `Re (w * ·)`). -/
lemma comb_ne_zero {L c w : ℂ} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hL : L ≠ 0)
    (hLw : 0 ≤ (w * L).re) (hcw : 0 < (w * c).re) : (1 - r) * L + r * c ≠ 0 := by
  rcases eq_or_lt_of_le hr.1 with h | h
  · subst h; simpa using hL
  · intro h0
    have := congrArg (fun z => (w * z).re) h0
    have e1 : (w * ((1 - (r : ℂ)) * L)).re = (1 - r) * (w * L).re := by
      rw [mul_left_comm]; simp [Complex.mul_re]
    have e2 : (w * ((r : ℂ) * c)).re = r * (w * c).re := by
      rw [mul_left_comm]; simp [Complex.mul_re]
    rw [mul_add, Complex.add_re, e1, e2, mul_zero, Complex.zero_re] at this
    nlinarith [hr.2, mul_pos h hcw, mul_nonneg (sub_nonneg.2 hr.2) hLw]

theorem rect_crossings_meet : ∀ (x₀ x₁ y₀ y₁ : ℝ) (γ δ : ℝ → ℂ),
    ContinuousOn γ (Set.Icc 0 1) → ContinuousOn δ (Set.Icc 0 1) →
    Set.MapsTo γ (Set.Icc 0 1) (RectCross.rect x₀ x₁ y₀ y₁) →
    Set.MapsTo δ (Set.Icc 0 1) (RectCross.rect x₀ x₁ y₀ y₁) →
    (γ 0).re = x₀ → (γ 1).re = x₁ → (δ 0).im = y₁ → (δ 1).im = y₀ →
    ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, γ s = δ t := by
  intro x₀ x₁ y₀ y₁ γ δ hγc hδc hγm hδm hγ0 hγ1 hδ0 hδ1
  by_contra hno
  push Not at hno
  have hF : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, γ s - δ t ≠ 0 :=
    fun s hs t ht => sub_ne_zero.2 (hno s hs t ht)
  -- the contraction to the corner `(0, 0)`
  have hmul : ∀ (r : unitInterval) (x : ℝ), x ∈ Icc (0 : ℝ) 1 → (1 - (r : ℝ)) * x ∈ Icc (0 : ℝ) 1 :=
    fun r x hx => ⟨mul_nonneg (sub_nonneg.2 r.2.2) hx.1,
      by nlinarith [r.2.1, r.2.2, hx.1, hx.2]⟩
  have hc1 : Continuous fun p : unitInterval × unitInterval => γ ((1 - (p.2 : ℝ)) * b₁ p.1) :=
    hγc.comp_continuous (by have := continuous_b₁; fun_prop) fun p => hmul p.2 _ (b₁_mem _)
  have hc2 : Continuous fun p : unitInterval × unitInterval => δ ((1 - (p.2 : ℝ)) * b₂ p.1) :=
    hδc.comp_continuous (by have := continuous_b₂; fun_prop) fun p => hmul p.2 _ (b₂_mem _)
  let H1 : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ ((1 - (p.2 : ℝ)) * b₁ p.1) - δ ((1 - (p.2 : ℝ)) * b₂ p.1), hc1.sub hc2⟩
  have hH1 : ∀ p, H1 p ≠ 0 := fun p => hF _ (hmul p.2 _ (b₁_mem _)) _ (hmul p.2 _ (b₂_mem _))
  have hH1c : ∀ s, H1 (0, s) = H1 (1, s) := fun s => by
    simp only [H1, ContinuousMap.coe_mk, Icc.coe_zero, Icc.coe_one, b₁_zero_one, b₂_zero_one]
  have deg1 := loopDeg_homotopy H1 hH1 hH1c
  have hconst : slice H1 1 = ContinuousMap.const unitInterval (γ 0 - δ 0) := by
    ext u; simp [slice, H1]
  have hγ0' : γ 0 - δ 0 ≠ 0 := hF 0 (left_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
  have e1 : loopDeg (slice H1 1) (fun _ => hH1 _) = 0 := by
    rw [← loopDeg_const _ hγ0']
    congr 1
  -- the straight-line homotopy to the circle
  have hL : Continuous fun u : unitInterval => γ (b₁ u) - δ (b₂ u) :=
    (hγc.comp_continuous (continuous_b₁.comp continuous_subtype_val) fun u => b₁_mem _).sub
      (hδc.comp_continuous (continuous_b₂.comp continuous_subtype_val) fun u => b₂_mem _)
  let H2 : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => (1 - ((p.2 : ℝ) : ℂ)) * (γ (b₁ p.1) - δ (b₂ p.1)) + ((p.2 : ℝ) : ℂ) * circleLoop 1 p.1,
      ((continuous_const.sub (Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp continuous_snd))).mul (hL.comp continuous_fst)).add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul
          ((circleLoop 1).continuous.comp continuous_fst))⟩
  have hcl : ∀ u : unitInterval, circleLoop 1 u =
      ⟨Real.cos (2 * π * u), Real.sin (2 * π * u)⟩ := fun u => by
    have e : (2 : ℂ) * π * ((u : ℝ) : ℂ) * Complex.I = ((2 * π * u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    apply Complex.ext <;> simp [circleLoop, circleMap, e, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have hH2 : ∀ p, H2 p ≠ 0 := by
    rintro ⟨u, r⟩
    simp only [H2, ContinuousMap.coe_mk]
    have hLu := hF _ (b₁_mem u) _ (b₂_mem u)
    have hsq := Real.sin_sq_add_cos_sq (2 * π * (u : ℝ))
    set c := Real.cos (2 * π * (u : ℝ)) with hcdef
    set sn := Real.sin (2 * π * (u : ℝ)) with hsdef
    have hmx : mx u = max |c| |sn| := rfl
    have hδb := hδm (b₂_mem u)
    have hγb := hγm (b₁_mem u)
    simp only [RectCross.rect, mem_ofPred_eq, mem_Icc] at hδb hγb
    rcases le_total |sn| |c| with hcs | hcs
    · have hm : mx u = |c| := by rw [hmx, max_eq_left hcs]
      have hc0 : c ≠ 0 := by
        intro h; rw [h, abs_zero] at hcs
        have : sn = 0 := abs_nonpos_iff.1 hcs
        rw [this, h] at hsq; norm_num at hsq
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · have hb : b₁ u = 0 := half_add_eq_zero hneg hm
        apply comb_ne_zero r.2 hLu (w := -1)
        · rw [hb]; simp; linarith
        · rw [hcl]; simp; linarith
      · have hb : b₁ u = 1 := half_add_eq_one hpos hm
        apply comb_ne_zero r.2 hLu (w := 1)
        · rw [hb]; simp; linarith
        · rw [hcl]; simp; linarith
    · have hm : mx u = |sn| := by rw [hmx, max_eq_right hcs]
      have hs0 : sn ≠ 0 := by
        intro h; rw [h, abs_zero] at hcs
        have : c = 0 := abs_nonpos_iff.1 hcs
        rw [this, h] at hsq; norm_num at hsq
      rcases lt_or_gt_of_ne hs0 with hneg | hpos
      · have hb : b₂ u = 0 := half_add_eq_zero hneg hm
        apply comb_ne_zero r.2 hLu (w := Complex.I)
        · rw [hb]; simp; linarith
        · rw [hcl]; simp; linarith
      · have hb : b₂ u = 1 := half_add_eq_one hpos hm
        apply comb_ne_zero r.2 hLu (w := -Complex.I)
        · rw [hb]; simp; linarith
        · rw [hcl]; simp; linarith
  have hH2c : ∀ s, H2 (0, s) = H2 (1, s) := fun s => by
    have h01 : circleLoop 1 0 = circleLoop 1 1 := by
      simp only [circleLoop, ContinuousMap.coe_mk, Icc.coe_zero, Icc.coe_one]
      simpa using (periodic_circleMap 0 1 0).symm
    simp only [H2, ContinuousMap.coe_mk, Icc.coe_zero, Icc.coe_one, b₁_zero_one, b₂_zero_one, h01]
  have deg2 := loopDeg_homotopy H2 hH2 hH2c
  have hs0 : slice H2 0 = slice H1 0 := by ext u; simp [slice, H1, H2]
  have hs1 : slice H2 1 = circleLoop 1 := by ext u; simp [slice, H2]
  have e2 : loopDeg (slice H2 1) (fun _ => hH2 _) = 1 := by
    rw [← loopDeg_circle (r := 1) one_ne_zero]
    congr 1
  have e3 : loopDeg (slice H2 0) (fun _ => hH2 _) = loopDeg (slice H1 0) (fun _ => hH1 _) := by
    congr 1
  rw [e3, e2, deg1, e1] at deg2
  exact absurd deg2 (by norm_num)

end RectMeet

end LQGMetric
