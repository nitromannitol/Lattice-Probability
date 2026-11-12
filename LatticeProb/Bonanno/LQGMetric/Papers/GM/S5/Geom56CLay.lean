/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CLay at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CRect
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Cond3

/-!
# GM Lemma 5.6, condition (2) for a square tube with a corridor (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition (2)
(l. 2982–2989), decisions D69 (axis-parallel corridor near `u`) and D77 (`SepDiscNear`).

`sepDiscNear_of_layout`: the tube `V = tubeOf s (Fc ∪ Fp ∪ Fr)`, where the squares `Fc` tile a
rectangle corridor `rectC c e A W` whose far end contains `u`, the squares `Fp` meet a preconnected
set `P ∋ a` (GM's `π₋` and the rest of `L₋`) which meets the corridor, and `Fr` are the other
squares (GM's `P̃ ∪ L₊ ∪ π₊`). If the `Fp`-squares avoid `B_ρ(u')` and the `a`-side outside
`B_ρ(u')` is at distance `≥ s` from the `Fr`-squares, for all `u'` near `u`, then
`SepDiscNear V ρ u a b s` for every `b` off the `a`-side. Only metric hypotheses remain for the
caller. Own elementary argument (GM leave these steps implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM
open Blueprint

lemma convex_gridSquare56 (s : ℝ) (m : ℤ × ℤ) : Convex ℝ (gridSquare s m) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  simp only [gridSquare, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  obtain rfl : a = 1 - b := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left x2 ha,
    mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left x4 ha,
    mul_le_mul_of_nonneg_left y1 hb, mul_le_mul_of_nonneg_left y2 hb,
    mul_le_mul_of_nonneg_left y3 hb, mul_le_mul_of_nonneg_left y4 hb]

lemma gridSquare_subset_closure_interior {s : ℝ} (hs : 0 < s) (m : ℤ × ℤ) :
    gridSquare s m ⊆ closure (interior (gridSquare s m)) := by
  have hne : (interior (gridSquare s m)).Nonempty := by
    refine ⟨sqCenter s m, openBox_subset_interior s m ?_⟩
    simp only [sqCenter, mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  rw [(convex_gridSquare56 s m).closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- `V ∩ S` is preconnected for a grid square `S` whose interior lies in `V` -/
lemma inter_gridSquare_isPreconnected {V : Set ℂ} {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ}
    (hV : interior (gridSquare s m) ⊆ V) : IsPreconnected (V ∩ gridSquare s m) :=
  ((convex_gridSquare56 s m).interior.isPreconnected).subset_closure
    (subset_inter hV interior_subset)
    (inter_subset_right.trans (gridSquare_subset_closure_interior hs m))

/-- the squares meeting a preconnected set `P ⊆ V`, intersected with `V`, form a preconnected set -/
lemma inter_squares_isPreconnected {V P : Set ℂ} {s : ℝ} (hs : 0 < s) {Q : Finset (ℤ × ℤ)}
    (hP : IsPreconnected P) (hPV : P ⊆ V) (hPQ : P ⊆ ⋃ m ∈ Q, gridSquare s m)
    (hQ : ∀ m ∈ Q, (gridSquare s m ∩ P).Nonempty)
    (hQV : ∀ m ∈ Q, interior (gridSquare s m) ⊆ V) :
    IsPreconnected (V ∩ ⋃ m ∈ Q, gridSquare s m) := by
  rcases P.eq_empty_or_nonempty with hP0 | ⟨x, hx⟩
  · have hQ0 : ∀ m ∈ Q, False := fun m hm => by
      obtain ⟨p, -, hp⟩ := hQ m hm; rw [hP0] at hp; exact hp
    have : V ∩ ⋃ m ∈ Q, gridSquare s m = ∅ := by
      ext y; simp only [mem_inter_iff, mem_iUnion, mem_empty_iff_false, iff_false]
      rintro ⟨-, m, hm, -⟩; exact hQ0 m hm
    rw [this]; exact isPreconnected_empty
  have hPsub : P ⊆ V ∩ ⋃ m ∈ Q, gridSquare s m := subset_inter hPV hPQ
  refine isPreconnected_of_forall x ?_
  rintro y ⟨hyV, hyQ⟩
  rw [mem_iUnion₂] at hyQ
  obtain ⟨m, hm, hym⟩ := hyQ
  refine ⟨P ∪ (V ∩ gridSquare s m), union_subset hPsub ?_, Or.inl hx, Or.inr ⟨hyV, hym⟩, ?_⟩
  · exact inter_subset_inter_right _ (subset_biUnion_of_mem (u := fun m => gridSquare s m) hm)
  obtain ⟨p, hpS, hpP⟩ := hQ m hm
  exact hP.union' ⟨p, hpP, hPV hpP, hpS⟩ (inter_gridSquare_isPreconnected hs (hQV m hm))

lemma convex_rectC (c e : ℂ) (A W : ℝ) : Convex ℝ (rectC c e A W) := by
  intro x hx y hy a b ha hb hab
  have key : (a • x + b • y - c) * (starRingEnd ℂ) e =
      (a : ℂ) * ((x - c) * (starRingEnd ℂ) e) + (b : ℂ) * ((y - c) * (starRingEnd ℂ) e) := by
    have : (a : ℂ) + b = 1 := by exact_mod_cast hab
    simp only [Complex.real_smul]
    linear_combination (c * (starRingEnd ℂ) e) * this
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [rectC, mem_ofPred_eq, key, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul]
  constructor
  · calc |a * ((x - c) * (starRingEnd ℂ) e).re + b * ((y - c) * (starRingEnd ℂ) e).re|
        ≤ a * |((x - c) * (starRingEnd ℂ) e).re| + b * |((y - c) * (starRingEnd ℂ) e).re| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * A + b * A := by gcongr
      _ = A := by rw [← add_mul, hab, one_mul]
  · calc |a * ((x - c) * (starRingEnd ℂ) e).im + b * ((y - c) * (starRingEnd ℂ) e).im|
        ≤ a * |((x - c) * (starRingEnd ℂ) e).im| + b * |((y - c) * (starRingEnd ℂ) e).im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * W + b * W := by gcongr
      _ = W := by rw [← add_mul, hab, one_mul]

lemma continuous_rectCoord (c e : ℂ) : Continuous fun w : ℂ => (w - c) * (starRingEnd ℂ) e := by
  fun_prop

lemma isOpen_rectO (c e : ℂ) (A W : ℝ) : IsOpen (rectO c e A W) := by
  have h := continuous_rectCoord c e
  exact (isOpen_lt (continuous_abs.comp (Complex.continuous_re.comp h)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp h)) continuous_const)

lemma rectO_subset_rectC (c e : ℂ) (A W : ℝ) : rectO c e A W ⊆ rectC c e A W :=
  fun _ hw => ⟨hw.1.le, hw.2.le⟩

lemma rectO_subset_interior (c e : ℂ) (A W : ℝ) : rectO c e A W ⊆ interior (rectC c e A W) :=
  interior_maximal (rectO_subset_rectC c e A W) (isOpen_rectO c e A W)

/-- **condition (2) at `u` for a corridor tube**; see the module docstring -/
theorem sepDiscNear_of_layout {Fc Fp Fr : Finset (ℤ × ℤ)} {s ρ A W : ℝ} {P : Set ℂ}
    {c e u a b : ℂ} (hs : 0 < s) (he : ‖e‖ = 1) (hW : 0 < W) (hA : ρ + 3 * W ≤ A)
    (hρ : 4 * W ≤ ρ) (hc : ⋃ m ∈ Fc, gridSquare s m = rectC c e A W)
    (hP : IsPreconnected P) (hPV : P ⊆ tubeOf s (Fc ∪ Fp ∪ Fr))
    (hPF : P ⊆ ⋃ m ∈ Fp, gridSquare s m) (hFp : ∀ m ∈ Fp, (gridSquare s m ∩ P).Nonempty)
    (hPc : (P ∩ rectC c e A W).Nonempty)
    (hu : u ∈ rectO c e A W) (huA : |((u - c) * (starRingEnd ℂ) e).re - A| < W)
    (hball : ∀ᶠ u' in 𝓝 u, ∀ m ∈ Fp, Disjoint (gridSquare s m) (ball u' ρ))
    (hfar : ∀ᶠ u' in 𝓝 u, ∀ x ∈ (rectC c e A W ∪ ⋃ m ∈ Fp, gridSquare s m) \ ball u' ρ,
      ∀ y ∈ ⋃ m ∈ Fr, gridSquare s m, s ≤ dist x y)
    (ha : a ∈ P) (hb : b ∉ rectC c e A W ∪ ⋃ m ∈ Fp, gridSquare s m) :
    SepDiscNear (tubeOf s (Fc ∪ Fp ∪ Fr)) ρ u a b s := by
  set V := tubeOf s (Fc ∪ Fp ∪ Fr)
  set Ka := rectC c e A W ∪ ⋃ m ∈ Fp, gridSquare s m
  set R := interior (rectC c e A W)
  have hVK : V ⊆ Ka ∪ ⋃ m ∈ Fr, gridSquare s m := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := mem_tubeOf_exists hx
    rcases Finset.mem_union.1 hm with hm | hm
    · rcases Finset.mem_union.1 hm with hm | hm
      · left; left; rw [← hc]; exact mem_biUnion hm hxm
      · left; right; exact mem_biUnion hm hxm
    · right; exact mem_biUnion hm hxm
  have hRV : R ⊆ V := by
    show interior (rectC c e A W) ⊆ V
    rw [← hc]
    refine interior_mono (biUnion_subset_biUnion_left ?_)
    intro m hm; exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
  have hcl : rectC c e A W ⊆ closure R := by
    rw [(convex_rectC c e A W).closure_interior_eq_closure_of_nonempty_interior
      ⟨u, rectO_subset_interior c e A W hu⟩]
    exact subset_closure
  have hopen : IsOpen {w : ℂ | w ∈ rectO c e A W ∧ |((w - c) * (starRingEnd ℂ) e).re - A| < W} :=
    (isOpen_rectO c e A W).inter (isOpen_lt
      (continuous_abs.comp ((Complex.continuous_re.comp (continuous_rectCoord c e)).sub
        continuous_const)) continuous_const)
  have hnear := hopen.mem_nhds ⟨hu, huA⟩
  have hFpV : ∀ m ∈ Fp, interior (gridSquare s m) ⊆ V := fun m hm =>
    interior_gridSquare_subset_tubeOf (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  refine sepDiscNear_of_corridor hs hVK hb ((hball.and hfar).and hnear |>.mono ?_)
  rintro u' ⟨⟨hb', hf'⟩, hu'R, hu'A⟩
  have hFpB : ∀ x ∈ ⋃ m ∈ Fp, gridSquare s m, x ∉ ball u' ρ := by
    intro x hx hxB
    rw [mem_iUnion₂] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    exact (hb' m hm).ne_of_mem hxm hxB rfl
  refine ⟨R, isOpen_interior, (convex_rectC c e A W).interior, hRV,
    rectO_subset_interior c e A W hu'R, ?_, hf', ?_, ⟨⟨hPV ha, Or.inr (hPF ha)⟩, hFpB _ (hPF ha)⟩⟩
  · rintro x ⟨hx | hx, hxB⟩
    · exact hcl hx
    · exact absurd hxB (hFpB x hx)
  · have hS1 : IsPreconnected ((V ∩ rectC c e A W) \ ball u' ρ) := by
      refine corridor_isPreconnected he hW hA hρ hu'A.le hu'R.2.le ?_
        (fun x hx => ⟨hx.1.2, hx.2⟩)
      · rintro w ⟨hwR, hwB⟩
        refine ⟨⟨hRV (rectO_subset_interior c e A W hwR), rectO_subset_rectC c e A W hwR⟩, ?_⟩
        exact fun h => hwB (ball_subset_closedBall h)
    have hS2 : IsPreconnected (V ∩ ⋃ m ∈ Fp, gridSquare s m) :=
      inter_squares_isPreconnected hs hP (hPV) hPF hFp hFpV
    have heq : (V ∩ Ka) \ ball u' ρ =
        ((V ∩ rectC c e A W) \ ball u' ρ) ∪ (V ∩ ⋃ m ∈ Fp, gridSquare s m) := by
      ext x
      constructor
      · rintro ⟨⟨hxV, hx | hx⟩, hxB⟩
        · exact Or.inl ⟨⟨hxV, hx⟩, hxB⟩
        · exact Or.inr ⟨hxV, hx⟩
      · rintro (⟨⟨hxV, hx⟩, hxB⟩ | ⟨hxV, hx⟩)
        · exact ⟨⟨hxV, Or.inl hx⟩, hxB⟩
        · exact ⟨⟨hxV, Or.inr hx⟩, hFpB x hx⟩
    rw [heq]
    obtain ⟨p, hpP, hpR⟩ := hPc
    exact hS1.union' ⟨p, ⟨⟨hPV hpP, hpR⟩, hFpB p (hPF hpP)⟩, hPV hpP, hPF hpP⟩ hS2

end LQGMetric.GM
