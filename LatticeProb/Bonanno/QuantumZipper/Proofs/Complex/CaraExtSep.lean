/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraExtSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CarLengthArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Convex

/-!
# EXT-CA C3, separation step: the image of a half-disk lies in a small ball

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C3. This is the Janiszewski step of the proof of
Carathéodory's continuity theorem in Pommerenke, *Boundary Behaviour of Conformal Maps* (1992),
Thm 2.1, proof of (iv) ⇒ (i), printed pp. 21–22 (PDF pp. 29–30), transported to the upper
half-plane and to the bounded model of the blueprint:

* the crosscut is the image `C = ψ(γ)` of a semicircle `γ = {x₀ + r e^{iθ}}` (closed up by its
  end points `cb 0`, `cb π`, given here as a continuous curve `cb` on `[0, π]`);
* `β ⊆ E` is a preconnected set containing both end points (Pommerenke's continuum `B`);
* Pommerenke's complement `ℂ \ G` is replaced by the compact set `M = closedBall 0 R₀ \ D`,
  whose complement meets `closedBall 0 R₀` only in the connected set `D` (blueprint C3);
* Janiszewski's theorem is `Topo.janiszewski` (T3).

The only deviation from Pommerenke's text is this replacement of `ℂ \ G` by `M` (so that all sets
are compact) and the explicit separation of `(J ∪ M)ᶜ` into the disjoint open sets
`ψ(H ∩ ball x₀ r)`, `ψ(H ∩ {‖· - x₀‖ > r}) ∪ (closedBall 0 R₀)ᶜ` (the "three disjoint open sets"
of the blueprint, `not_mem_connectedComponentIn_of_subset_union`), where Pommerenke says "0 and
`z'` are not separated by `C ∪ 𝕋`, which is false because `|z - z'| < ρ < r`".
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

/-- **Three disjoint open sets.** If `S ⊆ U ∪ V` with `U`, `V` open and disjoint, then no point
of `V` lies in the component of `S` containing a point of `U`. -/
theorem not_mem_connectedComponentIn_of_subset_union {S U V : Set ℂ} (hU : IsOpen U)
    (hV : IsOpen V) (hUV : Disjoint U V) (hS : S ⊆ U ∪ V) {p q : ℂ} (hp : p ∈ U) (hq : q ∈ V) :
    q ∉ connectedComponentIn S p := by
  intro hmem
  have hpS : p ∈ S := connectedComponentIn_nonempty_iff.1 ⟨q, hmem⟩
  rcases isPreconnected_connectedComponentIn.subset_or_subset hU hV hUV
    ((connectedComponentIn_subset S p).trans hS) with h | h
  · exact Set.disjoint_left.1 hUV (h hmem) hq
  · exact Set.disjoint_left.1 hUV hp (h (mem_connectedComponentIn hpS))

/-- **T6, translated.** Two points at distance `> R` from `c` are not separated by a set
contained in `ball c R`. -/
theorem mem_connectedComponentIn_compl_of_lt_norm_sub {J : Set ℂ} {c : ℂ} {R : ℝ}
    (hJ : J ⊆ ball c R) {p q : ℂ} (hp : R < ‖p - c‖) (hq : R < ‖q - c‖) :
    q ∈ connectedComponentIn Jᶜ p := by
  have hS : IsPreconnected ((· + c) '' {z : ℂ | R < ‖z‖}) :=
    (isPreconnected_setOf_lt_norm R).image _ (continuous_id.add continuous_const).continuousOn
  have hmem : ∀ w, R < ‖w - c‖ → w ∈ (· + c) '' {z : ℂ | R < ‖z‖} := fun w hw =>
    ⟨w - c, hw, sub_add_cancel w c⟩
  refine hS.subset_connectedComponentIn (hmem p hp) ?_ (hmem q hq)
  rintro _ ⟨z, hz, rfl⟩ hzJ
  have := hJ hzJ
  rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at this
  exact lt_asymm this hz

private theorem semicircle_mem_H' (x₀ : ℝ) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 π) :
    ((x₀ : ℂ) + r * exp (θ * I)) ∈ H := by
  show 0 < ((x₀ : ℂ) + r * exp (θ * I)).im
  simp only [add_im, ofReal_im, zero_add, mul_im, ofReal_re, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, zero_mul, add_zero]
  exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private theorem norm_semicircle_sub (x₀ : ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖((x₀ : ℂ) + r * exp (θ * I)) - x₀‖ = r := by
  rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

/-- Every point of `H` at distance `r` from the real point `x₀` is on the semicircle. -/
theorem exists_eq_semicircle {x₀ r : ℝ} {ζ : ℂ} (hζ : ζ ∈ H) (hζr : ‖ζ - x₀‖ = r) :
    ∃ θ ∈ Ioo 0 π, ζ = (x₀ : ℂ) + r * exp (θ * I) := by
  have hζ' : 0 < ζ.im := hζ
  have him : 0 < (ζ - x₀).im := by simpa using hζ'
  refine ⟨arg (ζ - x₀), ⟨?_, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.2 him.le) fun h => ?_
    exact him.ne' (arg_eq_zero_iff.1 h.symm).2
  · exact arg_lt_pi_iff.2 (Or.inr him.ne')
  · rw [← hζr, norm_mul_exp_arg_mul_I]
    ring

/-- **C3, Janiszewski step** (Pommerenke 1992, Thm 2.1, proof of (iv) ⇒ (i), pp. 21–22).
Let `cb` be a continuous curve on `[0, π]` which on `(0, π)` is the image of the semicircle
`x₀ + r e^{iθ}`, with end points in `E`, and let `β ⊆ E` be preconnected and contain both end
points. If `J = cb[0, π] ∪ closure β` lies in `ball (cb 0) R` and the image of a reference point
`zr` outside the closed half-disk is at distance `> R` from `cb 0`, then the image of the open
half-disk `H ∩ ball x₀ r` lies in `closedBall (cb 0) R`. -/
theorem norm_sub_le_of_mem_halfDisk {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    {x₀ r : ℝ} (hr : 0 < r) {cb : ℝ → ℂ} (hcb : ContinuousOn cb (Icc 0 π))
    (hcbψ : ∀ θ ∈ Ioo 0 π, cb θ = ψ ((x₀ : ℂ) + r * exp (θ * I)))
    (ha : cb 0 ∈ E) (hb : cb π ∈ E) {β : Set ℂ} (hβE : β ⊆ E) (hβ : IsPreconnected β)
    (haβ : cb 0 ∈ β) (hbβ : cb π ∈ β) {R : ℝ} (hJ : cb '' Icc 0 π ∪ closure β ⊆ ball (cb 0) R)
    {zr : ℂ} (hzrH : zr ∈ H) (hzr : r < ‖zr - x₀‖) (hq : R < ‖ψ zr - cb 0‖)
    {z : ℂ} (hz : z ∈ H) (hzx : ‖z - x₀‖ < r) : ‖ψ z - cb 0‖ ≤ R := by
  by_contra hp
  replace hp := not_le.1 hp
  set A : Set ℂ := cb '' Icc 0 π ∪ closure β with hA
  set B : Set ℂ := closedBall 0 R₀ \ D with hB
  have hβc : closure β ⊆ E := closure_minimal hβE h.isClosed
  have hEB : E ⊆ B := fun w hw => ⟨h.E_bdd hw, h.sub_compl hw⟩
  have hEc : ∀ w ∈ E, w ∉ D := fun w hw => h.sub_compl hw
  have hAc : IsCompact A :=
    (isCompact_Icc.image_of_continuousOn hcb).union
      (isCompact_of_isClosed_isBounded isClosed_closure
        ((isBounded_closedBall (x := (0 : ℂ)) (r := R₀)).subset (hβc.trans h.E_bdd)))
  have hBc : IsCompact B := (isCompact_closedBall _ _).diff h.isOpen
  -- the points of the curve are in `D` except for the end points
  have hcbD : ∀ θ ∈ Icc 0 π, cb θ ∈ D → θ ∈ Ioo 0 π := by
    intro θ hθ hD
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · exact absurd (h0 ▸ hD) (hEc _ ha)
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · exact absurd (h1 ▸ hD) (hEc _ hb)
    exact ⟨h0, h1⟩
  have hAB : A ∩ B = closure β := by
    refine Subset.antisymm ?_ fun w hw => ⟨Or.inr hw, hEB (hβc hw)⟩
    rintro w ⟨hwA | hwA, hwB⟩
    · obtain ⟨θ, hθ, rfl⟩ := hwA
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · exact subset_closure (h0 ▸ haβ)
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · exact subset_closure (h1 ▸ hbβ)
      exact absurd (by rw [hcbψ θ ⟨h0, h1⟩]; exact h.bij.mapsTo (semicircle_mem_H' x₀ hr ⟨h0, h1⟩))
        hwB.2
    · exact hwA
  -- points `ψ ζ` with `‖ζ - x₀‖ ≠ r` are off `A ∪ B`
  have hoff : ∀ ζ ∈ H, ‖ζ - x₀‖ ≠ r → ψ ζ ∉ A ∪ B := by
    intro ζ hζ hne hmem
    have hD : ψ ζ ∈ D := h.bij.mapsTo hζ
    rcases hmem with (⟨θ, hθ, hθe⟩ | hβm) | hBm
    · have hθ' := hcbD θ hθ (hθe ▸ hD)
      rw [hcbψ θ hθ'] at hθe
      have := h.bij.injOn (semicircle_mem_H' x₀ hr hθ') hζ hθe
      exact hne (this ▸ norm_semicircle_sub x₀ hr θ)
    · exact hEc _ (hβc hβm) hD
    · exact hBm.2 hD
  have hpA := hoff z hz hzx.ne
  have hqA := hoff zr hzrH hzr.ne'
  -- `D` is preconnected and does not meet `B`
  have hDpre : IsPreconnected D := by
    rw [← h.bij.image_eq]
    exact (convex_halfSpace_im_gt 0).isPreconnected.image _ h.holo.continuousOn
  have h₂ : ψ zr ∈ connectedComponentIn Bᶜ (ψ z) :=
    hDpre.subset_connectedComponentIn (h.bij.mapsTo hz) (fun w hw hwB => hwB.2 hw : D ⊆ Bᶜ)
      (h.bij.mapsTo hzrH)
  have h₁ : ψ zr ∈ connectedComponentIn Aᶜ (ψ z) :=
    mem_connectedComponentIn_compl_of_lt_norm_sub hJ hp hq
  have hJan := janiszewski hAc hBc (hAB ▸ hβ.closure) hpA hqA h₁ h₂
  -- the three disjoint open sets
  set U : Set ℂ := ψ '' (H ∩ ball (x₀ : ℂ) r) with hU
  set V : Set ℂ := ψ '' (H ∩ {ζ | r < ‖ζ - x₀‖}) ∪ (closedBall 0 R₀)ᶜ with hV
  have hUo : IsOpen U :=
    isOpen_image_of_injOn isOpen_H h.holo h.bij.injOn (isOpen_H.inter isOpen_ball)
      inter_subset_left
  have hVo : IsOpen V :=
    (isOpen_image_of_injOn isOpen_H h.holo h.bij.injOn
      (isOpen_H.inter (isOpen_lt continuous_const (by fun_prop))) inter_subset_left).union
      isClosed_closedBall.isOpen_compl
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro _ ⟨ζ₁, ⟨hζ₁, hζ₁r⟩, rfl⟩ (⟨ζ₂, ⟨hζ₂, hζ₂r⟩, he⟩ | hout)
    · have := h.bij.injOn hζ₂ hζ₁ he
      rw [mem_ball, dist_eq_norm] at hζ₁r
      simp only [mem_ofPred_eq, this] at hζ₂r
      exact lt_asymm hζ₁r hζ₂r
    · exact hout (ball_subset_closedBall (h.bdd (h.bij.mapsTo hζ₁)))
  have hcover : (A ∪ B)ᶜ ⊆ U ∪ V := by
    intro w hw
    rw [mem_compl_iff, mem_union, not_or] at hw
    by_cases hwb : w ∈ closedBall (0 : ℂ) R₀
    · have hwD : w ∈ D := by
        by_contra hwD
        exact hw.2 ⟨hwb, hwD⟩
      obtain ⟨ζ, hζ, rfl⟩ := h.bij.surjOn hwD
      rcases lt_trichotomy ‖ζ - x₀‖ r with hlt | heq | hgt
      · exact Or.inl ⟨ζ, ⟨hζ, by rwa [mem_ball, dist_eq_norm]⟩, rfl⟩
      · obtain ⟨θ, hθ, rfl⟩ := exists_eq_semicircle hζ heq
        exact absurd (Or.inl ⟨θ, Ioo_subset_Icc_self hθ, hcbψ θ hθ⟩) hw.1
      · exact Or.inr (Or.inl ⟨ζ, ⟨hζ, hgt⟩, rfl⟩)
    · exact Or.inr (Or.inr hwb)
  exact not_mem_connectedComponentIn_of_subset_union hUo hVo hUV hcover
    ⟨z, ⟨hz, by rwa [mem_ball, dist_eq_norm]⟩, rfl⟩ (Or.inl ⟨zr, ⟨hzrH, hzr⟩, rfl⟩) hJan

end QuantumZipper.CA.Car
