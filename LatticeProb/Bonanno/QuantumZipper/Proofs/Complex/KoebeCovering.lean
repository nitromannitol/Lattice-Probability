/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.KoebeCovering at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic

/-!
# Koebe covering and Koebe's estimate on a disk (EXT-CA nodes K3, K5a-disk; EXT-JS node D2)

For `f` injective and holomorphic on `ball c r`:

* `ball_subset_image_koebe`: `ball (f c) (r ‖f'(c)‖ / 48) ⊆ f '' ball c r` (Koebe covering with
  the non-sharp constant `koebeCovConst = 1/48` instead of `1/4`);
* `image_ball_ne_univ`: `f '' ball c r ≠ univ`;
* `koebeCovConst_mul_le_infDist` and `infDist_le_mul_norm_deriv`: Koebe's estimate
  `r ‖f'(c)‖ / 48 ≤ dist (f c, ∂ f(B)) ≤ r ‖f'(c)‖`.

## Sources and deviations

Statement: Koebe's estimate, Garnett–Marshall, *Harmonic Measure* (CUP 2005), Ch. I,
Theorem 4.3, eq. (4.13), p. 19 (the disk `ball c r` is the unit disk after the affine change
`z ↦ c + r z`, evaluated at the center); Pommerenke, *Boundary Behaviour of Conformal Maps*
(1992), Cor. 1.4. Koebe [1907] himself proved the left inequality with some constant `≤ 1/4`
(Garnett–Marshall, Notes to Ch. I, p. 26); `1/4` is Bieberbach's.

* The right inequality follows Garnett–Marshall's proof of Thm 4.3 (Schwarz lemma for the inverse
  map), see `radius_mul_norm_deriv_le_of_ball_subset_image`.
* The left inequality follows Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser
  2021), Theorem 7.27 (step (4)), Corollary 7.28 and the remark after it ("latent in the proof
  of 7.27 is a lower bound of 1/24"), pp. 481–483 (PDF pp. 506–508): with `w₀` a nearest
  omitted point and `G = √(f − w₀)`, the sets `G(B)` and `−G(B)` are disjoint, `G(B)` contains a
  disk around `G c` of radius comparable to `|G c|`, and the Schwarz lemma (Burckel 6.1) applied
  to `1/(G + G c)` bounds `|f'(c)|`. We take the disk of radius `|G c|/3` (Burckel: `(√2 − 1)|G c|`)
  and the Schwarz lemma with target radius `2`, which gives `1/48` instead of Burckel's `1/24`.
  The area-theorem proofs of the sharp `1/4` (Garnett–Marshall Thm I.4.1, Pommerenke *Univalent
  Functions* Thm 1.3–1.5) need Green's formula, absent from mathlib (recorded in
  `DEVIATIONS.md`, D-KOEBE).
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real

namespace QuantumZipper.CA.Koebe

/-- The (non-sharp) Koebe covering constant used in this project: `1/48` (sharp value `1/4`). -/
def koebeCovConst : ℝ := 1 / 48

theorem koebeCovConst_pos : 0 < koebeCovConst := by norm_num [koebeCovConst]

/-- Core of the square-root trick. If `w₀ ∉ f(B)` while the disk `ball (f c) |f c − w₀|` lies
in `f(B)`, then `r ‖f'(c)‖ ≤ 48 ‖f c − w₀‖`. -/
theorem mul_norm_deriv_le_of_omitted {f : ℂ → ℂ} {c w₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hw₀ : w₀ ∉ f '' ball c r) (hball : ball (f c) ‖f c - w₀‖ ⊆ f '' ball c r) :
    r * ‖deriv f c‖ ≤ 48 * ‖f c - w₀‖ := by
  set B := ball c r with hB
  have hcB : c ∈ B := mem_ball_self hr
  have hne : ∀ z ∈ B, f z - w₀ ≠ 0 := fun z hz h => hw₀ ⟨z, hz, sub_eq_zero.1 h⟩
  obtain ⟨G, hGd, hG⟩ := exists_sq_eq_of_ne_zero_ball (hd.sub_const w₀) hne
  set a := G c with ha
  have ha2 : a ^ 2 = f c - w₀ := hG c hcB
  have ha0 : a ≠ 0 := by
    intro h; apply hne c hcB; rw [← ha2, h]; ring
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hna : ‖a‖ ^ 2 = ‖f c - w₀‖ := by rw [← norm_pow, ha2]
  -- `G` is injective and `G(B) ∩ −G(B) = ∅`
  have hGinj : InjOn G B := by
    intro z₁ h₁ z₂ h₂ h
    apply hinj h₁ h₂
    have e1 := hG z₁ h₁
    have e2 := hG z₂ h₂
    rw [h] at e1
    linear_combination e2 - e1
  have hGanti : ∀ z₁ ∈ B, ∀ z₂ ∈ B, G z₁ ≠ -G z₂ := by
    intro z₁ h₁ z₂ h₂ h
    have e1 := hG z₁ h₁
    have e2 := hG z₂ h₂
    have hf : f z₁ = f z₂ := by
      rw [h] at e1
      linear_combination e2 - e1
    have hz := hinj h₁ h₂ hf
    subst hz
    have h0 : G z₁ = 0 := by linear_combination h / 2
    apply hne z₁ h₁
    rw [← e1, h0]; ring
  have hGopen : IsOpen (G '' B) := isOpen_image_of_injOn isOpen_ball hGd hGinj subset_rfl isOpen_ball
  have hNopen : IsOpen ((fun u : ℂ => -u) '' (G '' B)) :=
    (Homeomorph.neg ℂ).isOpenMap _ hGopen
  have hdisj : Disjoint (G '' B) ((fun u : ℂ => -u) '' (G '' B)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z₁, h₁, rfl⟩ ⟨_, ⟨z₂, h₂, rfl⟩, e⟩
    exact hGanti z₁ h₁ z₂ h₂ e.symm
  have hcov : ball a (‖a‖ / 3) ⊆ G '' B ∪ (fun u : ℂ => -u) '' (G '' B) := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    have hsum : ‖u + a‖ ≤ ‖u - a‖ + 2 * ‖a‖ := by
      calc ‖u + a‖ = ‖(u - a) + 2 * a‖ := by ring_nf
        _ ≤ ‖u - a‖ + ‖2 * a‖ := norm_add_le _ _
        _ = ‖u - a‖ + 2 * ‖a‖ := by rw [norm_mul]; norm_num
    have hlt : ‖u ^ 2 - a ^ 2‖ < ‖a‖ ^ 2 := by
      have : u ^ 2 - a ^ 2 = (u - a) * (u + a) := by ring
      rw [this, norm_mul]
      have h1 : ‖u - a‖ * ‖u + a‖ ≤ (‖a‖ / 3) * (‖a‖ / 3 + 2 * ‖a‖) := by
        apply mul_le_mul hu.le (by linarith) (norm_nonneg _) (by positivity)
      nlinarith
    have hmem : u ^ 2 + w₀ ∈ ball (f c) ‖f c - w₀‖ := by
      rw [mem_ball, dist_eq_norm, ← hna]
      have he : u ^ 2 + w₀ - f c = u ^ 2 - a ^ 2 := by rw [ha2]; ring
      rw [he]; exact hlt
    obtain ⟨z, hz, hfz⟩ := hball hmem
    have hsq : (G z - u) * (G z + u) = 0 := by
      have := hG z hz
      rw [hfz] at this
      linear_combination this
    rcases mul_eq_zero.1 hsq with h | h
    · left; exact ⟨z, hz, sub_eq_zero.1 h⟩
    · right; exact ⟨G z, ⟨z, hz, rfl⟩, by linear_combination -h⟩
  have hS : ball a (‖a‖ / 3) ⊆ G '' B :=
    (convex_ball a _).isPreconnected.subset_left_of_subset_union hGopen hNopen hdisj hcov
      ⟨a, mem_ball_self (by positivity), ⟨c, hcB, rfl⟩⟩
  have hlow : ∀ z ∈ B, ‖a‖ / 3 ≤ ‖G z + a‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hm : -G z ∈ ball a (‖a‖ / 3) := by
      rw [mem_ball, dist_eq_norm, show -G z - a = -(G z + a) by ring, norm_neg]
      exact hlt
    obtain ⟨z', hz', e⟩ := hS hm
    exact hGanti z' hz' z hz e
  have hGa0 : ∀ z ∈ B, G z + a ≠ 0 := by
    intro z hz h
    have := hlow z hz
    rw [h, norm_zero] at this
    linarith
  -- the Schwarz lemma for `φ = k / (G + a)`
  set k : ℂ := ((‖a‖ / 3 : ℝ) : ℂ) with hk
  have hknorm : ‖k‖ = ‖a‖ / 3 := by
    rw [hk, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  set φ : ℂ → ℂ := fun z => k * (G z + a)⁻¹ with hφ
  have hφd : DifferentiableOn ℂ φ B := fun z hz =>
    ((differentiableWithinAt_const k).mul
      (((hGd z hz).add_const a).inv (hGa0 z hz)))
  have hφle : ∀ z ∈ B, ‖φ z‖ ≤ 1 := by
    intro z hz
    rw [hφ]
    simp only [norm_mul, norm_inv, hknorm]
    have hp : 0 < ‖G z + a‖ := norm_pos_iff.2 (hGa0 z hz)
    rw [← div_eq_mul_inv, div_le_one hp]
    exact hlow z hz
  have hφmaps : MapsTo φ B (closedBall (φ c) 2) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖φ z - φ c‖ ≤ ‖φ z‖ + ‖φ c‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hφle z hz) (hφle c hcB)
      _ = 2 := by norm_num
  have hsch := norm_deriv_le_div_of_mapsTo_ball hφd hφmaps hr
  -- derivatives
  have hGc : HasDerivAt G (deriv G c) c :=
    (hGd.differentiableAt (isOpen_ball.mem_nhds hcB)).hasDerivAt
  have hfc : HasDerivAt f (deriv f c) c :=
    (hd.differentiableAt (isOpen_ball.mem_nhds hcB)).hasDerivAt
  have hderiv : deriv f c = 2 * a * deriv G c := by
    have h1 : HasDerivAt (fun z => G z ^ 2) (2 * G c * deriv G c) c := by
      exact (hGc.fun_pow 2).congr_deriv
        (by rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h2 : HasDerivAt (fun z => G z ^ 2) (deriv f c) c := by
      have := hfc.sub_const w₀
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hcB] with z hz
      exact hG z hz
    exact h2.unique h1
  have hφc : HasDerivAt φ (k * (-(deriv G c) / (G c + a) ^ 2)) c :=
    ((hGc.add_const a).inv (hGa0 c hcB)).const_mul k
  rw [hφc.deriv] at hsch
  have hGca : G c + a = 2 * a := by rw [← ha]; ring
  rw [hGca] at hsch
  have hnorm : ‖k * (-(deriv G c) / (2 * a) ^ 2)‖ = ‖deriv G c‖ / (12 * ‖a‖) := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, hknorm]
    norm_num
    field_simp
    ring
  rw [hnorm, div_le_div_iff₀ (by positivity) hr] at hsch
  rw [hderiv, norm_mul, norm_mul, ← hna]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hsch (norm_nonneg a), norm_nonneg (deriv G c)]

/-- **Koebe covering theorem** (non-sharp constant `1/48`). If `f` is injective and holomorphic on
`ball c r`, then `f '' ball c r ⊇ ball (f c) (r ‖f'(c)‖ / 48)`. -/
theorem ball_subset_image_koebe {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    ball (f c) (koebeCovConst * r * ‖deriv f c‖) ⊆ f '' ball c r := by
  rcases le_or_gt r 0 with hr | hr
  · have : koebeCovConst * r * ‖deriv f c‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos koebeCovConst_pos.le hr) (norm_nonneg _)
    rw [Metric.ball_eq_empty.2 this]
    exact empty_subset _
  set S := (f '' ball c r)ᶜ with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · intro w _
    by_contra hw
    have : w ∈ S := hw
    rw [hSe] at this
    exact this
  have hSc : IsClosed S :=
    (isOpen_image_of_injOn isOpen_ball hd hinj subset_rfl isOpen_ball).isClosed_compl
  obtain ⟨w₀, hw₀S, hw₀d⟩ := hSc.exists_infDist_eq_dist hSne (f c)
  have hball : ball (f c) ‖f c - w₀‖ ⊆ f '' ball c r := by
    intro w hw
    rw [mem_ball, ← dist_eq_norm, ← hw₀d] at hw
    have := notMem_of_dist_lt_infDist (x := f c) (y := w) (s := S) (by rwa [dist_comm])
    by_contra h
    exact this h
  have key := mul_norm_deriv_le_of_omitted hr hd hinj hw₀S hball
  intro w hw
  rw [mem_ball] at hw
  have hlt : dist (f c) w < infDist (f c) S := by
    rw [hw₀d, dist_comm (f c) w, dist_eq_norm (f c) w₀]
    unfold koebeCovConst at hw
    linarith
  have := notMem_of_dist_lt_infDist hlt
  by_contra h
  exact this h

/-- An injective holomorphic map on a disk is not onto `ℂ`. -/
theorem image_ball_ne_univ {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    f '' ball c r ≠ univ := by
  intro h
  have hcB : c ∈ ball c r := mem_ball_self hr
  set R := r * ‖deriv f c‖ + 1
  have hR : 0 < R := by positivity
  have := radius_mul_norm_deriv_le_of_ball_subset_image (ψ := id) isOpen_ball hd hinj hcB
    differentiableOn_id (ρ := r) (fun z hz => mem_closedBall.2 (le_of_lt (by simpa using hz)))
    hR (by rw [h]; exact subset_univ _)
  simp at this
  linarith

/-- **Koebe's estimate, upper half** (Garnett–Marshall, Thm I.4.3, right inequality):
`dist (f c, ∂ f(B)) ≤ r ‖f'(c)‖`. -/
theorem infDist_le_mul_norm_deriv {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    infDist (f c) (f '' ball c r)ᶜ ≤ r * ‖deriv f c‖ := by
  set d := infDist (f c) (f '' ball c r)ᶜ
  rcases le_or_gt d 0 with hd0 | hd0
  · exact hd0.trans (by positivity)
  have hsub : ball (f c) d ⊆ f '' ball c r := by
    intro w hw
    rw [mem_ball, dist_comm] at hw
    have := notMem_of_dist_lt_infDist hw
    by_contra h
    exact this h
  have hcB : c ∈ ball c r := mem_ball_self hr
  have := radius_mul_norm_deriv_le_of_ball_subset_image (ψ := id) isOpen_ball hd hinj hcB
    differentiableOn_id (ρ := r) (fun z hz => mem_closedBall.2 (le_of_lt (by simpa using hz)))
    hd0 hsub
  simpa using this

/-- **Koebe's estimate, lower half** (non-sharp constant; Garnett–Marshall, Thm I.4.3, left
inequality, with `1/48` for `1/4`). This is node D2 `weakKoebe` of `EXT_JS_BLUEPRINT.md`. -/
theorem koebeCovConst_mul_le_infDist {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    koebeCovConst * r * ‖deriv f c‖ ≤ infDist (f c) (f '' ball c r)ᶜ := by
  have hne : ((f '' ball c r)ᶜ).Nonempty := by
    rw [nonempty_compl]; exact image_ball_ne_univ hr hd hinj
  rw [le_infDist hne]
  intro y hy
  by_contra hlt
  push Not at hlt
  exact hy (ball_subset_image_koebe hd hinj (by rwa [mem_ball, dist_comm]))

end QuantumZipper.CA.Koebe
