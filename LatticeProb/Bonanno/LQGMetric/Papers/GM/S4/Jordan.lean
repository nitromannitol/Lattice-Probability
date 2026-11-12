/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Jordan at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct

/-!
# The boundary of a filled metric ball is a Jordan curve (GM.S-Jordan, DEC-B J1, J1d, J2)

Gwynne–Pfeffer–Sheffield arXiv:2010.07889 Lemma 2.4 (`zero-one.tex` l. 534–546) for filled
metric balls, by the argument of Miller–Sheffield arXiv:1506.03806 Prop 2.1
(`mapmaking_final.tex` l. 555–612), in the plane as GPS do. Decision D17.

Setting: `D` a continuous length metric on `ℂ` with bounded balls around `z`, `s > 0`,
`K = 𝓑^•_s(z; D)`, `U = ℂ ∖ K`, `Γ = ∂K`.

* **J1d** With `ι(x) = 1/(x − z)`, `Ω := ι(U) ∪ {0}` (`jordanOmega`, written as
  `{w | z + w⁻¹ ∉ K} ∪ {0}`) is open, bounded, preconnected, and `ℂ ∖ Ω = ι(K ∖ {z})` is
  connected and unbounded, so `Ω` has holomorphic square roots (QuantumZipper
  `hasHoloSqrt_of_unbounded_compl`); `∂Ω = ι(Γ)`.
* **J1** `gm_filledBall_frontier_isJordanCurve`: if `Γ` is locally connected (node **J1b**,
  `FilledBallBdyLC`: MS Prop 2.1 proof, l. 570–601, "Therefore Γ is locally connected"), then
  `Γ` is a Jordan curve. Proof: J1c (`jb_isPreconnected_frontier_diff`, no cut points) and J1b
  transported by `ι`, then Carathéodory (`JordanMap.jm_exists_closedDisc_extension`) for `Ω`,
  then back by `ι⁻¹ = (w ↦ z + w⁻¹)`.

J1b is the one step of MS's proof not formalized here (open node, verbatim MS l. 570–601).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open LQGMetric.Blueprint
open QuantumZipper QuantumZipper.CA

namespace LQGMetric.GM

/-- **J1b** (MS arXiv:1506.03806, proof of Prop 2.1, `mapmaking_final.tex` l. 570–601): the
boundary `Γ = ∂𝓑^•_s(z; D)` is locally connected, in Newman's form (points of `Γ` near `x` are
joined to `x` inside `Γ` by preconnected sets of small diameter). -/
def FilledBallBdyLC (D : ContMetric) (z : ℂ) (s : ℝ) : Prop :=
  ∀ x ∈ frontier (filledBall D z s), ∀ ε > 0, ∃ ρ > 0, ∀ a ∈ frontier (filledBall D z s),
    dist a x < ρ → ∃ β ⊆ frontier (filledBall D z s), IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧
      Metric.diam β ≤ ε

/-- `Ω = ι(ℂ ∖ 𝓑^•_s) ∪ {0}` with `ι(x) = 1/(x − z)` (DEC-B J1d). -/
def jordanOmega (D : ContMetric) (z : ℂ) (s : ℝ) : Set ℂ :=
  {w | z + w⁻¹ ∉ filledBall D z s} ∪ {0}

theorem jo_inv_sub_norm {p q z : ℂ} (hp : p ≠ z) (hq : q ≠ z) :
    ‖(p - z)⁻¹ - (q - z)⁻¹‖ * (‖p - z‖ * ‖q - z‖) = ‖p - q‖ := by
  have hp' : p - z ≠ 0 := sub_ne_zero.2 hp
  have hq' : q - z ≠ 0 := sub_ne_zero.2 hq
  rw [inv_sub_inv hp' hq', norm_div, norm_mul, div_mul_cancel₀ _
    (mul_ne_zero (norm_ne_zero_iff.2 hp') (norm_ne_zero_iff.2 hq')),
    show q - z - (p - z) = q - p by ring, norm_sub_rev]

theorem jo_inv_left {x z : ℂ} (hx : x ≠ z) : z + (x - z)⁻¹⁻¹ = x := by
  rw [inv_inv]; ring

theorem jo_inv_right {w z : ℂ} : (z + w⁻¹ - z)⁻¹ = w := by
  rw [add_sub_cancel_left, inv_inv]

variable {D : ContMetric} {z : ℂ} {s : ℝ}

theorem jo_mem_filledBall_self (hs : 0 < s) : z ∈ filledBall D z s :=
  Or.inl (subset_closure (jb_mem_ballM D z s hs))

theorem jo_not_mem_frontier_self (hs : 0 < s) : z ∉ frontier (filledBall D z s) :=
  disjoint_left.1 jb_disjoint_ballM_frontier (jb_mem_ballM D z s hs)

/-- small `w ≠ 0` lie in `Ω` -/
theorem jo_far (hbd : Bornology.IsBounded (ballM D z s)) :
    ∃ δ > 0, ∀ w : ℂ, w ≠ 0 → ‖w‖ < δ → z + w⁻¹ ∉ filledBall D z s := by
  obtain ⟨R, p, hR, -⟩ := jb_exists_far hbd
  have hK := jb_filledBall_subset_closedBall hR
  set A := |R| + ‖z‖ + 1 with hA
  have hApos : 0 < A := by positivity
  refine ⟨1 / A, by positivity, fun w hw0 hw hwK => ?_⟩
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have h1 : A < ‖w⁻¹‖ := by
    rw [norm_inv, lt_inv_comm₀ hApos hwpos, ← one_div]
    exact hw
  have h2 := hK hwK
  rw [mem_closedBall, dist_zero_right] at h2
  have h3 : ‖w⁻¹‖ ≤ ‖z + w⁻¹‖ + ‖z‖ := by
    calc ‖w⁻¹‖ = ‖(z + w⁻¹) - z‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖z + w⁻¹‖ + ‖z‖ := norm_sub_le _ _
  linarith [le_abs_self R]

/-- points of `Ω` other than `0` have `‖w‖ ≤ 1/r` -/
theorem jo_near (hs : 0 < s) :
    ∃ r > 0, ∀ w : ℂ, z + w⁻¹ ∉ filledBall D z s → w ≠ 0 ∧ r ≤ ‖w⁻¹‖ := by
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 (jb_isOpen_ballM D z s) z (jb_mem_ballM D z s hs)
  refine ⟨r, hr, fun w hw => ⟨fun h => ?_, ?_⟩⟩
  · apply hw
    rw [h, inv_zero, add_zero]
    exact jo_mem_filledBall_self hs
  by_contra h
  apply hw
  refine Or.inl (subset_closure (hrB ?_))
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
  exact not_le.1 h

theorem jo_omega_eq (hs : 0 < s) :
    jordanOmega D z s = (fun x => (x - z)⁻¹) '' (filledBall D z s)ᶜ ∪ {0} := by
  ext w
  simp only [jordanOmega, mem_union, mem_setOf_eq, mem_image, mem_compl_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨z + w⁻¹, h, jo_inv_right⟩
    · exact Or.inr h
  · rintro (⟨x, hx, rfl⟩ | h)
    · left
      have hxz : x ≠ z := fun e => hx (e ▸ jo_mem_filledBall_self hs)
      rwa [jo_inv_left hxz]
    · exact Or.inr h

theorem jo_isOpen_omega (hs : 0 < s) (hbd : Bornology.IsBounded (ballM D z s)) :
    IsOpen (jordanOmega D z s) := by
  obtain ⟨δ, hδ, hfar⟩ := jo_far (D := D) (z := z) (s := s) hbd
  have he : jordanOmega D z s = ({0}ᶜ ∩ (fun w => z + w⁻¹) ⁻¹' (filledBall D z s)ᶜ) ∪ ball 0 δ := by
    ext w
    simp only [jordanOmega, mem_union, mem_setOf_eq, mem_inter_iff, mem_compl_iff,
      mem_singleton_iff, mem_preimage, mem_ball_zero_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨fun e => h (by rw [e, inv_zero, add_zero]; exact jo_mem_filledBall_self hs), h⟩
      · exact Or.inr (by rw [h, norm_zero]; exact hδ)
    · rintro (⟨-, h⟩ | h)
      · exact Or.inl h
      · by_cases hw : w = 0
        · exact Or.inr hw
        · exact Or.inl (hfar w hw h)
  rw [he]
  refine (ContinuousOn.isOpen_inter_preimage ?_ isOpen_compl_singleton
    (jb_isClosed_filledBall hbd).isOpen_compl).union isOpen_ball
  exact continuousOn_const.add continuousOn_inv₀

theorem jo_omega_subset (hs : 0 < s) :
    ∃ r > 0, jordanOmega D z s ⊆ closedBall 0 (1 / r) := by
  obtain ⟨r, hr, hnear⟩ := jo_near (D := D) (z := z) hs
  refine ⟨r, hr, fun w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  rcases hw with hw | hw
  · obtain ⟨hw0, hwr⟩ := hnear w hw
    rw [norm_inv] at hwr
    rw [le_div_iff₀ hr]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    calc ‖w‖ * r ≤ ‖w‖ * ‖w‖⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hwpos.ne'
  · rw [mem_singleton_iff.1 hw, norm_zero]
    positivity

theorem jo_continuousOn_iota (A : Set ℂ) (hA : z ∉ A) : ContinuousOn (fun x => (x - z)⁻¹) A :=
  ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 fun e : x = z => hA (e ▸ hx)

theorem jo_isPreconnected_omega (hs : 0 < s) (hbd : Bornology.IsBounded (ballM D z s)) :
    IsPreconnected (jordanOmega D z s) := by
  obtain ⟨δ, hδ, hfar⟩ := jo_far (D := D) (z := z) (s := s) hbd
  have hzU : z ∉ (filledBall D z s)ᶜ := fun h => h (jo_mem_filledBall_self hs)
  have hI : IsPreconnected ((fun x => (x - z)⁻¹) '' (filledBall D z s)ᶜ) :=
    (jb_isPreconnected_compl hbd).image _ (jo_continuousOn_iota _ hzU)
  have he : jordanOmega D z s = (fun x => (x - z)⁻¹) '' (filledBall D z s)ᶜ ∪ ball 0 δ := by
    rw [jo_omega_eq hs]
    apply subset_antisymm
    · exact union_subset_union subset_rfl (singleton_subset_iff.2 (mem_ball_self hδ))
    · refine union_subset subset_union_left fun w hw => ?_
      by_cases hw0 : w = 0
      · exact Or.inr hw0
      · exact Or.inl ⟨z + w⁻¹, hfar w hw0 (mem_ball_zero_iff.1 hw), jo_inv_right⟩
  set w₀ : ℂ := ((δ / 2 : ℝ) : ℂ)
  have hw₀ : w₀ ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hw₀n : ‖w₀‖ < δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  rw [he]
  exact hI.union' ⟨w₀, ⟨z + w₀⁻¹, hfar w₀ hw₀ hw₀n, jo_inv_right⟩, mem_ball_zero_iff.2 hw₀n⟩
    isPreconnected_ball

theorem jo_compl_omega (hs : 0 < s) :
    (jordanOmega D z s)ᶜ = (fun x => (x - z)⁻¹) '' (filledBall D z s \ {z}) := by
  ext w
  simp only [jordanOmega, mem_compl_iff, mem_union, mem_setOf_eq, mem_singleton_iff, not_or,
    not_not, mem_image, mem_diff]
  constructor
  · rintro ⟨hK, hw0⟩
    refine ⟨z + w⁻¹, ⟨hK, fun e => hw0 ?_⟩, jo_inv_right⟩
    have : w⁻¹ = 0 := by
      have := congrArg (· - z) e
      simpa using this
    exact inv_eq_zero.1 this
  · rintro ⟨x, ⟨hxK, hxz⟩, rfl⟩
    refine ⟨by rwa [jo_inv_left hxz], inv_ne_zero (sub_ne_zero.2 hxz)⟩

theorem jo_hasHoloSqrt (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s)) :
    RMT.HasHoloSqrt (jordanOmega D z s) := by
  refine RMT.hasHoloSqrt_of_unbounded_compl (jo_isOpen_omega hs hbd)
    (jo_isPreconnected_omega hs hbd) fun a ha hb => ?_
  have hzK : z ∉ filledBall D z s \ {z} := fun h => h.2 rfl
  have hpc : IsPreconnected (jordanOmega D z s)ᶜ := by
    rw [jo_compl_omega hs]
    exact (jp_isPreconnected_filledBall_diff hs hL).image _ (jo_continuousOn_iota _ hzK)
  have hsub := hpc.subset_connectedComponentIn ha subset_rfl
  obtain ⟨r, hr, hΩ⟩ := jo_omega_subset (D := D) (z := z) (s := s) hs
  refine jb_not_isBounded_lt_norm (1 / r) (hb.subset (fun w hw => hsub fun hwΩ => ?_))
  have := hΩ hwΩ
  rw [mem_closedBall, dist_zero_right] at this
  exact not_le.2 hw this

theorem jo_frontier_omega (hs : 0 < s) (hbd : Bornology.IsBounded (ballM D z s)) :
    frontier (jordanOmega D z s) = (fun x => (x - z)⁻¹) '' frontier (filledBall D z s) := by
  have hΩo := jo_isOpen_omega hs hbd
  have hKc := jb_isClosed_filledBall hbd
  rw [hΩo.frontier_eq]
  apply subset_antisymm
  · rintro w ⟨hwcl, hwΩ⟩
    have hwK : z + w⁻¹ ∈ filledBall D z s := by
      by_contra h
      exact hwΩ (Or.inl h)
    have hw0 : w ≠ 0 := fun h => hwΩ (Or.inr h)
    have hcont : ContinuousAt (fun w : ℂ => z + w⁻¹) w :=
      continuousAt_const.add (continuousAt_inv₀ hw0)
    have h1 := mem_closure_image hcont hwcl
    have himg : (fun w : ℂ => z + w⁻¹) '' jordanOmega D z s ⊆ (filledBall D z s)ᶜ ∪ {z} := by
      rintro _ ⟨v, hv | hv, rfl⟩
      · exact Or.inl hv
      · rw [mem_singleton_iff.1 hv]
        show z + (0 : ℂ)⁻¹ ∈ _
        rw [inv_zero, add_zero]
        exact Or.inr rfl
    have h2 := closure_mono himg h1
    rw [closure_union, closure_singleton] at h2
    have hne : z + w⁻¹ ≠ z := fun e => hw0 (inv_eq_zero.1 (by simpa using congrArg (· - z) e))
    have h3 : z + w⁻¹ ∈ closure (filledBall D z s)ᶜ := h2.resolve_right hne
    refine ⟨z + w⁻¹, ?_, jo_inv_right⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hwK, h3⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxz : x ≠ z := fun e => jo_not_mem_frontier_self hs (e ▸ hx)
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun x : ℂ => (x - z)⁻¹) x :=
        (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hxz)
      have hxU : x ∈ closure (filledBall D z s)ᶜ := by
        rw [← frontier_compl] at hx
        exact frontier_subset_closure hx
      refine closure_mono ?_ (mem_closure_image (f := fun x : ℂ => (x - z)⁻¹) hcont hxU)
      rw [jo_omega_eq hs]
      exact subset_union_left
    · rintro (h | h)
      · exact h (by rw [jo_inv_left hxz]; exact hKc.frontier_subset hx)
      · exact inv_ne_zero (sub_ne_zero.2 hxz) (mem_singleton_iff.1 h)

/-- **J1b transported**: `∂Ω = ι(Γ)` is ULC when `Γ` is locally connected. -/
theorem jo_ulc (hs : 0 < s) (hbd : Bornology.IsBounded (ballM D z s))
    (hlc : FilledBallBdyLC D z s) :
    Topo.ULC ((fun x => (x - z)⁻¹) '' frontier (filledBall D z s)) := by
  set Γ := frontier (filledBall D z s) with hΓ
  have hKc := jb_isClosed_filledBall hbd
  have hzΓ : z ∉ Γ := jo_not_mem_frontier_self hs
  have hΓc : IsCompact Γ :=
    (jb_isCompact_filledBall hbd).of_isClosed_subset isClosed_frontier hKc.frontier_subset
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 (jb_isOpen_ballM D z s) z (jb_mem_ballM D z s hs)
  obtain ⟨R, p, hR, -⟩ := jb_exists_far hbd
  have hK := jb_filledBall_subset_closedBall hR
  set R' := |R| + ‖z‖ + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hlow : ∀ x ∈ Γ, r ≤ ‖x - z‖ := fun x hx => by
    by_contra h
    refine disjoint_left.1 jb_disjoint_ballM_frontier (hrB ?_) hx
    rw [mem_ball, dist_eq_norm]
    exact not_le.1 h
  have hup : ∀ x ∈ Γ, ‖x - z‖ ≤ R' := fun x hx => by
    have h := hK (hKc.frontier_subset hx)
    rw [mem_closedBall, dist_zero_right] at h
    linarith [norm_sub_le x z, le_abs_self R]
  have hne : ∀ x ∈ Γ, x ≠ z := fun x hx e => hzΓ (e ▸ hx)
  have hdist : ∀ x ∈ Γ, ∀ y ∈ Γ,
      dist (x - z)⁻¹ (y - z)⁻¹ * (‖x - z‖ * ‖y - z‖) = dist x y := fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm]
    exact jo_inv_sub_norm (hne x hx) (hne y hy)
  refine Topo.ULC.of_isCompact_of_forall (hΓc.image_of_continuousOn
    (jo_continuousOn_iota _ hzΓ)) ?_
  rintro _ ⟨x, hx, rfl⟩ ε hε
  obtain ⟨ρ, hρ, hβ⟩ := hlc x hx (ε * r ^ 2) (by positivity)
  refine ⟨ρ / R' ^ 2, by positivity, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ hax
  have hax' : dist a x < ρ := by
    have h1 := hdist a ha x hx
    have h2 : ‖a - z‖ * ‖x - z‖ ≤ R' ^ 2 := by
      rw [sq]
      exact mul_le_mul (hup a ha) (hup x hx) (norm_nonneg _) hR'pos.le
    have h3 : dist (a - z)⁻¹ (x - z)⁻¹ * R' ^ 2 < ρ := by
      rwa [lt_div_iff₀ (by positivity)] at hax
    nlinarith [dist_nonneg (x := (a - z)⁻¹) (y := (x - z)⁻¹)]
  obtain ⟨β, hβΓ, hβc, hxβ, haβ, hβd⟩ := hβ a ha hax'
  refine ⟨(fun x => (x - z)⁻¹) '' β, image_mono hβΓ,
    hβc.image _ ((jo_continuousOn_iota _ hzΓ).mono hβΓ), mem_image_of_mem _ hxβ,
    mem_image_of_mem _ haβ, ?_⟩
  have hβb : Bornology.IsBounded β := hΓc.isBounded.subset hβΓ
  refine Metric.diam_le_of_forall_dist_le hε.le ?_
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have h1 := hdist u (hβΓ hu) v (hβΓ hv)
  have h2 : r ^ 2 ≤ ‖u - z‖ * ‖v - z‖ := by
    rw [sq]
    exact mul_le_mul (hlow u (hβΓ hu)) (hlow v (hβΓ hv)) hr.le (norm_nonneg _)
  have h3 : dist u v ≤ ε * r ^ 2 := (dist_le_diam_of_mem hβb hu hv).trans hβd
  have h4 : 0 ≤ dist (u - z)⁻¹ (v - z)⁻¹ := dist_nonneg
  have hr2 : 0 < r ^ 2 := by positivity
  by_contra hc
  push_neg at hc
  nlinarith

/-- **J1c transported**: `ι(Γ) ∖ {q}` is preconnected. -/
theorem jo_cut (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s)) (q : ℂ) :
    IsPreconnected ((fun x => (x - z)⁻¹) '' frontier (filledBall D z s) \ {q}) := by
  set Γ := frontier (filledBall D z s) with hΓ
  have hzΓ : z ∉ Γ := jo_not_mem_frontier_self hs
  have he : (fun x => (x - z)⁻¹) '' Γ \ {q} = (fun x => (x - z)⁻¹) '' (Γ \ {z + q⁻¹}) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxq⟩
      refine ⟨x, ⟨hx, fun h => hxq ?_⟩, rfl⟩
      rw [mem_singleton_iff] at h ⊢
      rw [h]
      exact jo_inv_right
    · rintro ⟨x, ⟨hx, hxq⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, fun h => hxq ?_⟩
      rw [mem_singleton_iff] at h ⊢
      rw [← h]
      exact (jo_inv_left fun e : x = z => hzΓ (e ▸ hx)).symm
  rw [he]
  exact (jb_isPreconnected_frontier_diff hs hL hbd _).image _
    ((jo_continuousOn_iota _ hzΓ).mono diff_subset)

/-- **J1 = GM.S-Jordan** (GPS arXiv:2010.07889 Lemma 2.4 for filled balls; MS Prop 2.1):
for a continuous length metric `D` with bounded balls around `z` and `s > 0`, if
`∂𝓑^•_s(z; D)` is locally connected (node J1b, MS l. 570–601), then it is a Jordan curve. -/
theorem gm_filledBall_frontier_isJordanCurve (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) (hlc : FilledBallBdyLC D z s) :
    JordanMap.IsJordanCurve (frontier (filledBall D z s)) := by
  have hfr := jo_frontier_omega hs hbd
  obtain ⟨φ, hφc, hφi, -, -, -, hφs⟩ := JordanMap.jm_exists_closedDisc_extension
    (jo_isOpen_omega hs hbd) (jo_isPreconnected_omega hs hbd) (Or.inr rfl)
    ((isBounded_closedBall (x := (0 : ℂ))).subset (jo_omega_subset hs).choose_spec.2)
    (jo_hasHoloSqrt hs hL hbd) (hfr ▸ jo_ulc hs hbd hlc) (fun q => hfr ▸ jo_cut hs hL hbd q)
  have hzΓ : z ∉ frontier (filledBall D z s) := jo_not_mem_frontier_self hs
  have hφ0 : ∀ w ∈ sphere (0 : ℂ) 1, φ w ≠ 0 := fun w hw h => by
    have hm : φ w ∈ frontier (jordanOmega D z s) := hφs ▸ mem_image_of_mem φ hw
    rw [hfr] at hm
    obtain ⟨x, hx, hx0⟩ := hm
    rw [h] at hx0
    exact inv_ne_zero (sub_ne_zero.2 fun e : x = z => hzΓ (e ▸ hx)) hx0
  refine ⟨fun w => z + (φ w)⁻¹, continuousOn_const.add
    ((hφc.mono sphere_subset_closedBall).inv₀ hφ0), ?_, ?_⟩
  · intro a ha b hb h
    have h' : (φ a)⁻¹ = (φ b)⁻¹ := add_left_cancel h
    exact hφi (sphere_subset_closedBall ha) (sphere_subset_closedBall hb) (inv_inj.1 h')
  · rw [← image_image (fun w => z + w⁻¹) φ, hφs, hfr, image_image]
    refine (image_congr fun x hx => ?_).trans (image_id _)
    exact jo_inv_left fun e : x = z => hzΓ (e ▸ hx)

end LQGMetric.GM
