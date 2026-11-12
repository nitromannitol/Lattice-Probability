/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16A
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16, upper bound: deterministic part (task P2-DG316)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.16,
"Upper bound" (DG:1452–1456): for a chain `S_0, …, S_k` of squares from `z` to `w`, let
`z_0 = z`, `z_{k+1} = w`, `z_j ∈ S_j ∩ S_{j-1}`; the polygon through the `z_j` has its `j`-th
segment in `S_j`, where `h^{𝕊(1)}_δ ≤ ĥ_δ(v_{S_j}) + (ζ/2ξ) log δ⁻¹` by (eqn-use-circle-avg-approx);
summing gives the bound "up to a deterministic constant factor". Here `z_j` is the midpoint of the
common side (`p16Mid`), the polygon bound is `dgLFPP_le_poly_convex` (P3.22, applied to the field
extended continuously off `𝕊` by clamping, `p16Clamp`), and the constant is `2` (segment length
`≤ 2 · 2^{-m_δ} ≤ 2δ`). DG take a chain within factor 2 of the minimum; we bound every chain and
take the infimum.

* `p16_upper_det`: if `φ x ≤ φ̂ y + η log δ⁻¹` for `x, y ∈ 𝕊`, `|x − y| ≤ δ`, then
  `D^δ_φ(z,w;𝕊) ≤ 2 e^{ξ η log δ⁻¹} D̂^δ_{φ̂}(z,w;𝕊)`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint LQGDimension.PolygonRiemannAux

/-- the LFPP distance in `C` only depends on the field on `C` -/
lemma p16_dgLFPP_congr {ξ : ℝ} {φ φ' : ℂ → ℝ} {C : Set ℂ} (h : EqOn φ φ' C) (z w : ℂ) :
    dgLFPP ξ φ C z w = dgLFPP ξ φ' C z w := by
  unfold dgLFPP
  congr 1
  funext p
  unfold LQGDimension.lfppLength
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h (p.2.mapsTo ht)]

/-- the retraction of `ℂ` onto `𝕊 = [0,1]²` clamping both coordinates -/
def p16Clamp (x : ℂ) : ℂ := (max 0 (min 1 x.re) : ℝ) + (max 0 (min 1 x.im) : ℝ) * Complex.I

lemma p16Clamp_continuous : Continuous p16Clamp := by unfold p16Clamp; fun_prop

lemma p16Clamp_mem (x : ℂ) : p16Clamp x ∈ closedUnitSquare := by
  simp only [closedUnitSquare, p16Clamp, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.add_im, Complex.mul_im, zero_add]
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

lemma p16Clamp_eq {x : ℂ} (hx : x ∈ closedUnitSquare) : p16Clamp x = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  apply Complex.ext <;> simp [p16Clamp, min_eq_right, max_eq_right, *]

/-- the midpoint of the common side of two squares (DG's `z_j ∈ S_j ∩ S_{j-1}`) -/
def p16Mid (m : ℕ) (k k' : ℤ × ℤ) : ℂ :=
  ⟨((k.1 + k'.1 + 1) / 2 : ℝ) * (2 : ℝ)⁻¹ ^ m, ((k.2 + k'.2 + 1) / 2 : ℝ) * (2 : ℝ)⁻¹ ^ m⟩

lemma p16_coord {a : ℝ} (ha : 0 < a) {i j : ℤ} (h : |i - j| ≤ 1) :
    (i : ℝ) * a ≤ ((i + j + 1) / 2 : ℝ) * a ∧ ((i + j + 1) / 2 : ℝ) * a ≤ (i + 1) * a := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have e1 : (-1 : ℝ) ≤ i - j := by exact_mod_cast h1
  have e2 : (i : ℝ) - j ≤ 1 := by exact_mod_cast h2
  constructor <;> refine mul_le_mul_of_nonneg_right ?_ ha.le <;> linarith

lemma p16Mid_mem {m : ℕ} {k k' : ℤ × ℤ} (hk : dgAdj k k') :
    p16Mid m k k' ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k ∧ p16Mid m k k' ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k' := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  unfold dgAdj at hk
  have h1 : |k.1 - k'.1| ≤ 1 := by linarith [abs_nonneg (k.2 - k'.2)]
  have h2 : |k.2 - k'.2| ≤ 1 := by linarith [abs_nonneg (k.1 - k'.1)]
  have h1' : |k'.1 - k.1| ≤ 1 := by rwa [abs_sub_comm]
  have h2' : |k'.2 - k.2| ≤ 1 := by rwa [abs_sub_comm]
  obtain ⟨a1, a2⟩ := p16_coord ha h1
  obtain ⟨b1, b2⟩ := p16_coord ha h2
  obtain ⟨c1, c2⟩ := p16_coord ha h1'
  obtain ⟨d1, d2⟩ := p16_coord ha h2'
  have e1 : ((k'.1 + k.1 + 1) / 2 : ℝ) = ((k.1 + k'.1 + 1) / 2 : ℝ) := by ring
  have e2 : ((k'.2 + k.2 + 1) / 2 : ℝ) = ((k.2 + k'.2 + 1) / 2 : ℝ) := by ring
  rw [e1] at c1 c2
  rw [e2] at d1 d2
  exact ⟨⟨a1, a2, b1, b2⟩, ⟨c1, c2, d1, d2⟩⟩

lemma p16_norm_le {x y : ℂ} {r : ℝ} (h1 : |x.re - y.re| ≤ r) (h2 : |x.im - y.im| ≤ r) :
    ‖x - y‖ ≤ 2 * r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]; linarith

lemma p16_sq_diam {m : ℕ} {k : ℤ × ℤ} {x y : ℂ} (hx : x ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k)
    (hy : y ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k) : ‖x - y‖ ≤ 2 * (2 : ℝ)⁻¹ ^ m := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  exact p16_norm_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

lemma p16_center_mem_sq (m : ℕ) (k : ℤ × ℤ) :
    dgCenter m k ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [dgCenter] <;> nlinarith

lemma p16_sq_sub {m : ℕ} {k : ℤ × ℤ} (hk : k ∈ dgIdx m) :
    gridSquare ((2 : ℝ)⁻¹ ^ m) k ⊆ closedUnitSquare := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have e : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  obtain ⟨h1, h2, h3, h4⟩ := hk
  have f1 : (0 : ℝ) ≤ k.1 := by exact_mod_cast h1
  have f3 : (0 : ℝ) ≤ k.2 := by exact_mod_cast h3
  have f2 : (k.1 : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
    have : k.1 + 1 ≤ 2 ^ m := h2
    exact_mod_cast this
  have f4 : (k.2 : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
    have : k.2 + 1 ≤ 2 ^ m := h4
    exact_mod_cast this
  rintro x ⟨x1, x2, x3, x4⟩
  refine ⟨by nlinarith, ?_, by nlinarith, ?_⟩ <;> nlinarith

lemma p16_convex_gridSquare (s : ℝ) (k : ℤ × ℤ) : Convex ℝ (gridSquare s k) := by
  intro x hx y hy u v hu hv huv
  simp only [gridSquare, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hx hy ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h5, h6, h7, h8⟩ := hy
  have e : ∀ c : ℝ, c = u * c + v * c := fun c => by rw [← add_mul, huv, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e (k.1 * s)]; exact add_le_add (mul_le_mul_of_nonneg_left h1 hu)
      (mul_le_mul_of_nonneg_left h5 hv)
  · rw [e ((k.1 + 1) * s)]; exact add_le_add (mul_le_mul_of_nonneg_left h2 hu)
      (mul_le_mul_of_nonneg_left h6 hv)
  · rw [e (k.2 * s)]; exact add_le_add (mul_le_mul_of_nonneg_left h3 hu)
      (mul_le_mul_of_nonneg_left h7 hv)
  · rw [e ((k.2 + 1) * s)]; exact add_le_add (mul_le_mul_of_nonneg_left h4 hu)
      (mul_le_mul_of_nonneg_left h8 hv)

lemma p16_sum_range_getD (f : ℤ × ℤ → ℝ) (L : List (ℤ × ℤ)) :
    ∑ i ∈ Finset.range L.length, f (L.getD i 0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x r ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma p16_getD_of {L : List (ℤ × ℤ)} {i : ℕ} {k : ℤ × ℤ} (h : L[i]? = some k) :
    L.getD i 0 = k := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

lemma p16_center_dist {m : ℕ} {k : ℤ × ℤ} {x : ℂ} (hx : x ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k) :
    ‖x - dgCenter m k‖ ≤ (2 : ℝ)⁻¹ ^ m := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  have h := p16_norm_le (x := x) (y := dgCenter m k) (r := (2 : ℝ)⁻¹ ^ m / 2)
    (abs_le.2 ⟨by simp only [dgCenter]; linarith, by simp only [dgCenter]; linarith⟩)
    (abs_le.2 ⟨by simp only [dgCenter]; linarith, by simp only [dgCenter]; linarith⟩)
  linarith

/-- **DG P3.16, upper bound, for one chain** (DG:1452–1456): the polygon through the midpoints of
the common sides of a chain `S_0, …, S_k` from `z` to `w` -/
theorem p16_upper_chain {δ ξ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hξ : 0 ≤ ξ)
    {φ φh : ℂ → ℝ} (hφ : ContinuousOn φ closedUnitSquare)
    (H : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ δ →
      φ x ≤ φh y + η * Real.log δ⁻¹)
    {z w : ℂ} {L : List (ℤ × ℤ)} (hL : IsDGSqChain (dgM δ) z w L) :
    dgLFPP ξ φ closedUnitSquare z w ≤
      2 * Real.exp (ξ * (η * Real.log δ⁻¹)) *
        (L.map fun k => δ * Real.exp (ξ * φh (dgCenter (dgM δ) k))).sum := by
  classical
  set m := dgM δ with hm_def
  set a : ℝ := (2 : ℝ)⁻¹ ^ m with ha_def
  have ha : 0 < a := by positivity
  have haδ : a ≤ δ := (p17s_dgM hδ0 hδ1).1
  obtain ⟨-, hidx, hch, ⟨k0, hk0, hz0⟩, ⟨k1, hk1, hw1⟩⟩ := hL
  set n := L.length with hn_def
  set g : ℕ → ℤ × ℤ := fun i => L.getD i 0 with hg_def
  have hn : 0 < n := by
    rcases L with _ | ⟨x, r⟩
    · simp at hk0
    · simp [n]
  have hg0 : g 0 = k0 := p16_getD_of (by rw [← List.head?_eq_getElem?]; exact hk0)
  have hgl : g (n - 1) = k1 := p16_getD_of (by rw [← List.getLast?_eq_getElem?]; exact hk1)
  have hgmem : ∀ i < n, g i ∈ dgIdx m := fun i hi => hidx _ (by
    simp only [g]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have hadj : ∀ i, i + 1 < n → dgAdj (g i) (g (i + 1)) := fun i hi => by
    simp only [g]; rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact hch.getElem i hi
  set V : ℕ → ℂ := fun i => if i = 0 then z else if i < n then p16Mid m (g (i - 1)) (g i) else w
    with hV_def
  have hV : ∀ i < n, V i ∈ gridSquare a (g i) ∧ V (i + 1) ∈ gridSquare a (g i) := by
    intro i hi
    constructor
    · by_cases h0 : i = 0
      · subst h0; simp only [V, if_true]; rw [hg0]; exact hz0
      · simp only [V, h0, if_false, hi, if_true]
        have := (p16Mid_mem (m := m) (hadj (i - 1) (by omega))).2
        rwa [show i - 1 + 1 = i by omega] at this
    · by_cases h1 : i + 1 < n
      · simp only [V, Nat.add_one_ne_zero, if_false, h1, if_true, Nat.add_sub_cancel]
        exact (p16Mid_mem (hadj i h1)).1
      · simp only [V, Nat.add_one_ne_zero, if_false, h1]
        rw [show i = n - 1 by omega, hgl]; exact hw1
  have hVS : ∀ i ≤ n, V i ∈ closedUnitSquare := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact p16_sq_sub (hgmem i h) (hV i h).1
    · have := (hV (n - 1) (by omega)).2
      rw [show n - 1 + 1 = i by omega] at this
      exact p16_sq_sub (hgmem _ (by omega)) this
  have hV0 : V 0 = z := by simp [V]
  have hVn : V n = w := by simp [V, hn.ne']
  set φ' : ℂ → ℝ := fun x => φ (p16Clamp x) with hφ'_def
  have hφ' : Continuous φ' := hφ.comp_continuous p16Clamp_continuous p16Clamp_mem
  have hEq : EqOn φ φ' closedUnitSquare := fun x hx => by simp only [φ', p16Clamp_eq hx]
  set E : ℝ := Real.exp (ξ * (η * Real.log δ⁻¹)) with hE_def
  set K : ℕ → ℝ := fun i => Real.exp (ξ * φh (dgCenter m (g i))) * E with hK_def
  have hK : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1, Real.exp (ξ * φ' (segAff V i s)) ≤ K i := by
    intro i hi s hs
    have hx : segAff V i s ∈ gridSquare a (g i) :=
      (p16_convex_gridSquare a (g i)).add_smul_sub_mem (hV i hi).1 (hV i hi).2 hs
    have hxS := p16_sq_sub (hgmem i hi) hx
    have hcS := p16_sq_sub (hgmem i hi) (p16_center_mem_sq m (g i))
    rw [← hEq hxS]
    show _ ≤ Real.exp (ξ * φh (dgCenter m (g i))) * Real.exp (ξ * (η * Real.log δ⁻¹))
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (H _ hxS _ hcS ((p16_center_dist hx).trans haδ)) hξ)
  have hpoly := dgLFPP_le_poly_convex V n hn hφ' ξ p16_convex_sq hVS K hK
  rw [hV0, hVn, ← p16_dgLFPP_congr hEq] at hpoly
  refine hpoly.trans ?_
  have hE : 0 < E := Real.exp_pos _
  calc ∑ i ∈ Finset.range n, ‖V (i + 1) - V i‖ * K i
      ≤ ∑ i ∈ Finset.range n, 2 * E * (δ * Real.exp (ξ * φh (dgCenter m (g i)))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hd := p16_sq_diam (hV i hi').2 (hV i hi').1
        have hKp : 0 ≤ K i := by positivity
        calc ‖V (i + 1) - V i‖ * K i ≤ (2 * δ) * K i :=
              mul_le_mul_of_nonneg_right (hd.trans (by linarith)) hKp
          _ = _ := by rw [hK_def]; ring
    _ = 2 * E * (L.map fun k => δ * Real.exp (ξ * φh (dgCenter m k))).sum := by
        rw [← Finset.mul_sum, p16_sum_range_getD (fun k => δ * Real.exp (ξ * φh (dgCenter m k)))]

/-- **DG P3.16, upper bound, deterministic form** (DG:1452–1456): if `φ ≤ φ̂ + η log δ⁻¹` at
distance `≤ δ` in `𝕊`, then `D^δ_φ(z,w;𝕊) ≤ 2 e^{ξ η log δ⁻¹} D̂^δ_{φ̂}(z,w;𝕊)` -/
theorem p16_upper_det {δ ξ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hξ : 0 ≤ ξ)
    {φ φh : ℂ → ℝ} (hφ : ContinuousOn φ closedUnitSquare)
    (H : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ δ →
      φ x ≤ φh y + η * Real.log δ⁻¹)
    {z w : ℂ} (hz : z ∈ closedUnitSquare) (hw : w ∈ closedUnitSquare) :
    dgLFPP ξ φ closedUnitSquare z w ≤
      2 * Real.exp (ξ * (η * Real.log δ⁻¹)) * dgApproxLFPP ξ δ φh z w := by
  haveI := p17_exists_chain (dgM δ) hz hw
  have hE : 0 < 2 * Real.exp (ξ * (η * Real.log δ⁻¹)) := by positivity
  have h : dgLFPP ξ φ closedUnitSquare z w / (2 * Real.exp (ξ * (η * Real.log δ⁻¹))) ≤
      dgApproxLFPP ξ δ φh z w := by
    refine le_ciInf fun L => ?_
    rw [div_le_iff₀ hE, mul_comm]
    exact p16_upper_chain hδ0 hδ1 hξ hφ H L.2
  rw [div_le_iff₀ hE, mul_comm] at h
  exact h

end LQGMetric.DG
