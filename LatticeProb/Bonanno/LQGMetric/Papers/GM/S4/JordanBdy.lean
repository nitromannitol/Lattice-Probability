/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanBdy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Jordan

/-!
# The conformal map of `ℂ ∖ 𝓑^•_s` and connectivity at the boundary (DEC-B node J2)

* `jo_disc_map`: Carathéodory's map for `Ω = ι(ℂ ∖ 𝓑^•_s) ∪ {0}` (`ι(x) = 1/(x − z)`): `φ`
  continuous and injective on the closed disc, holomorphic on `𝔻`, `φ 0 = 0`, `φ(𝔻) = Ω`,
  `φ(∂𝔻) = ι(Γ)`. Then `Ψ(b) = z + 1/φ(b)` is the conformal map `𝔻 ∖ {0} → ℂ ∖ 𝓑^•_s` extended
  homeomorphically to `∂𝔻 → Γ` (GPS arXiv:2010.07889, text after Lemma 2.4; Pommerenke 1992
  Thm 2.6) — `gm_filledBall_conformal` (equivalently `ζ ↦ Ψ(1/ζ)` on `ℂ ∖ 𝔻`, `∞ ↦ ∞`).
* `gm_filledBall_bdy_connect`: two points of `U = ℂ ∖ 𝓑^•_s` close to `w ∈ Γ` are joined in `U`
  by a connected set of small diameter whose closure contains `w` (pull back a segment through
  `Ψ`). This is the input for `d^U` (CONF (2.18), GM (4.38)) read with Euclidean closures
  (DV-B11), `DcSet.lean`.

All results are conditional on node J1b (`FilledBallBdyLC`, MS Prop 2.1 local connectivity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open LQGMetric.Blueprint
open QuantumZipper QuantumZipper.CA

namespace LQGMetric.GM

variable {D : ContMetric} {z : ℂ} {s : ℝ}

/-- Carathéodory's map onto `Ω` (DEC-B J2, disc form). -/
theorem jo_disc_map (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s))
    (hlc : FilledBallBdyLC D z s) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = 0 ∧ φ '' ball 0 1 = jordanOmega D z s ∧
      φ '' sphere 0 1 = (fun x => (x - z)⁻¹) '' frontier (filledBall D z s) := by
  have hfr := jo_frontier_omega hs hbd
  rw [← hfr]
  exact JordanMap.jm_exists_closedDisc_extension
    (jo_isOpen_omega hs hbd) (jo_isPreconnected_omega hs hbd) (Or.inr rfl)
    ((isBounded_closedBall (x := (0 : ℂ))).subset (jo_omega_subset hs).choose_spec.2)
    (jo_hasHoloSqrt hs hL hbd) (hfr ▸ jo_ulc hs hbd hlc) (fun q => hfr ▸ jo_cut hs hL hbd q)

theorem jo_phi_ne_zero {φ : ℂ → ℂ} (hφi : InjOn φ (closedBall 0 1)) (hφ0 : φ 0 = 0) {b : ℂ}
    (hb : b ∈ closedBall (0 : ℂ) 1) (hb0 : b ≠ 0) : φ b ≠ 0 := fun h =>
  hb0 (hφi hb (mem_closedBall_self zero_le_one) (h.trans hφ0.symm))

/-- **J2 (filled balls).** `Ψ(b) = z + 1/φ(b)` maps `𝔻 ∖ {0}` conformally onto
`ℂ ∖ 𝓑^•_s` and extends to a continuous injective map of `cl 𝔻 ∖ {0}`, sending `∂𝔻` onto
`∂𝓑^•_s`. -/
theorem gm_filledBall_conformal (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) (hlc : FilledBallBdyLC D z s) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closedBall 0 1 \ {0}) ∧ InjOn Ψ (closedBall 0 1 \ {0}) ∧
      DifferentiableOn ℂ Ψ (ball 0 1 \ {0}) ∧ Ψ '' (ball 0 1 \ {0}) = (filledBall D z s)ᶜ ∧
      Ψ '' sphere 0 1 = frontier (filledBall D z s) ∧
      Tendsto Ψ (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
  obtain ⟨φ, hφc, hφi, hφd, hφ0, hφB, hφs⟩ := jo_disc_map hs hL hbd hlc
  have hzΓ : z ∉ frontier (filledBall D z s) := jo_not_mem_frontier_self hs
  have hne : ∀ b ∈ closedBall (0 : ℂ) 1 \ {0}, φ b ≠ 0 := fun b hb =>
    jo_phi_ne_zero hφi hφ0 hb.1 hb.2
  refine ⟨fun b => z + (φ b)⁻¹, continuousOn_const.add ((hφc.mono diff_subset).inv₀ hne),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb h
    exact hφi ha.1 hb.1 (inv_inj.1 (add_left_cancel h))
  · intro b hb
    have hb' : b ∈ closedBall (0 : ℂ) 1 \ {0} := ⟨ball_subset_closedBall hb.1, hb.2⟩
    exact (differentiableAt_const _ |>.add ((hφd.differentiableAt
      (isOpen_ball.mem_nhds hb.1)).inv (hne b hb'))).differentiableWithinAt
  · apply subset_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      have hm : φ b ∈ jordanOmega D z s := hφB ▸ mem_image_of_mem φ hb.1
      rcases hm with h | h
      · exact h
      · exact (hne b ⟨ball_subset_closedBall hb.1, hb.2⟩ h).elim
    · intro x hx
      have hxz : x ≠ z := fun e => hx (e ▸ jo_mem_filledBall_self hs)
      have hm : (x - z)⁻¹ ∈ jordanOmega D z s := by
        rw [jo_omega_eq hs]
        exact Or.inl ⟨x, hx, rfl⟩
      rw [← hφB] at hm
      obtain ⟨b, hb, hbx⟩ := hm
      refine ⟨b, ⟨hb, fun h => ?_⟩, ?_⟩
      · rw [mem_singleton_iff.1 h, hφ0] at hbx
        exact inv_ne_zero (sub_ne_zero.2 hxz) hbx.symm
      · show z + (φ b)⁻¹ = x
        rw [hbx]
        exact jo_inv_left hxz
  · rw [← image_image (fun w => z + w⁻¹) φ, hφs, image_image]
    refine (image_congr fun x hx => ?_).trans (image_id _)
    exact jo_inv_left fun e : x = z => hzΓ (e ▸ hx)
  · -- `Ψ(b) → ∞` as `b → 0`
    have hB : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds 0 one_pos
    have hφt : Tendsto φ (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := ((hφc 0 (mem_closedBall_self zero_le_one)).continuousAt hB).tendsto
        rw [hφ0] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds hB, self_mem_nhdsWithin]
          with b hb hb0
        exact jo_phi_ne_zero hφi hφ0 hb hb0
    have h1 := (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hφt
    rw [← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
    refine tendsto_atTop_mono (fun b => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) h1)
    have h2 := norm_sub_le (z + (φ b)⁻¹) z
    rw [add_sub_cancel_left] at h2
    simp only [Function.comp_apply]
    linarith

/-- **J2, connectivity at the boundary.** Points `x₁, x₂ ∈ ℂ ∖ 𝓑^•_s` close to `w ∈ ∂𝓑^•_s`
are joined in `ℂ ∖ 𝓑^•_s` by a preconnected set of diameter `≤ ε` whose closure contains `w`
(image under `Ψ` of `[a₁, a₂] ∪ [a₁, p)`, `Ψ(p) = w`). -/
theorem gm_filledBall_bdy_connect (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) (hlc : FilledBallBdyLC D z s)
    {w : ℂ} (hw : w ∈ frontier (filledBall D z s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₁ ∉ filledBall D z s, ∀ x₂ ∉ filledBall D z s, dist x₁ w < δ → dist x₂ w < δ →
      ∃ X ⊆ (filledBall D z s)ᶜ, IsPreconnected X ∧ x₁ ∈ X ∧ x₂ ∈ X ∧ w ∈ closure X ∧
        Metric.ediam X ≤ ENNReal.ofReal ε := by
  obtain ⟨φ, hφc, hφi, -, hφ0, hφB, hφs⟩ := jo_disc_map hs hL hbd hlc
  have hzΓ : z ∉ frontier (filledBall D z s) := jo_not_mem_frontier_self hs
  have hwz : w ≠ z := fun e => hzΓ (e ▸ hw)
  -- the preimage `p ∈ ∂𝔻` of `w`
  obtain ⟨p, hp, hpw⟩ : (w - z)⁻¹ ∈ φ '' sphere 0 1 := hφs ▸ mem_image_of_mem _ hw
  have hpB : p ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hp
  have hφp : φ p ≠ 0 := by rw [hpw]; exact inv_ne_zero (sub_ne_zero.2 hwz)
  set Ψ : ℂ → ℂ := fun b => z + (φ b)⁻¹ with hΨ
  have hΨp : Ψ p = w := by simp only [hΨ, hpw]; exact jo_inv_left hwz
  have hΨc : ContinuousWithinAt Ψ (closedBall 0 1) p :=
    continuousWithinAt_const.add ((hφc p hpB).inv₀ hφp)
  obtain ⟨η₀, hη₀, hη₀Ψ⟩ := Metric.continuousWithinAt_iff.1 hΨc (ε / 2) (half_pos hε)
  set η := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  -- `φ(cl 𝔻 ∖ B(p, η))` is a compact set missing `φ p`
  have hC' : IsCompact (φ '' (closedBall 0 1 \ ball p η)) :=
    ((isCompact_closedBall 0 1).diff isOpen_ball).image_of_continuousOn (hφc.mono diff_subset)
  have hyC : (w - z)⁻¹ ∉ φ '' (closedBall 0 1 \ ball p η) := by
    rintro ⟨b, hb, hbp⟩
    rw [← hpw] at hbp
    exact hb.2 (hφi hb.1 hpB hbp ▸ mem_ball_self hη)
  obtain ⟨δ₁, hδ₁, hδ₁C⟩ := Metric.isOpen_iff.1 hC'.isClosed.isOpen_compl _ hyC
  have hιc : ContinuousAt (fun x : ℂ => (x - z)⁻¹) w :=
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hwz)
  obtain ⟨δ, hδ, hδι⟩ := Metric.continuousAt_iff.1 hιc δ₁ hδ₁
  refine ⟨δ, hδ, fun x₁ hx₁ x₂ hx₂ h₁ h₂ => ?_⟩
  -- preimages `a₁, a₂ ∈ 𝔻 ∩ B(p, η)`
  have hpre : ∀ x ∉ filledBall D z s, dist x w < δ →
      ∃ a ∈ ball (0 : ℂ) 1, a ∈ ball p η ∧ φ a = (x - z)⁻¹ := fun x hx hxw => by
    have hm : (x - z)⁻¹ ∈ φ '' ball 0 1 := by
      rw [hφB, jo_omega_eq hs]
      exact Or.inl ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hax⟩ := hm
    refine ⟨a, ha, ?_, hax⟩
    by_contra hap
    exact hδ₁C (hδι hxw) ⟨a, ⟨ball_subset_closedBall ha, hap⟩, hax⟩
  obtain ⟨a₁, ha₁, ha₁p, hφa₁⟩ := hpre x₁ hx₁ h₁
  obtain ⟨a₂, ha₂, ha₂p, hφa₂⟩ := hpre x₂ hx₂ h₂
  -- the set `S = [a₁, a₂] ∪ [a₁, p)` in `𝔻 ∩ B(p, η)`
  set g : ℝ → ℂ := fun t => a₁ + (t : ℂ) * (p - a₁) with hg
  have hgc : Continuous g := by fun_prop
  set S : Set ℂ := segment ℝ a₁ a₂ ∪ g '' Ico 0 1 with hS
  have hg1 : g 1 = p := by simp [hg]
  have hgB : ∀ t ∈ Ico (0 : ℝ) 1, g t ∈ ball (0 : ℂ) 1 ∧ g t ∈ ball p η := fun t ht => by
    have heq : g t = ((1 - t : ℝ) : ℂ) * a₁ + (t : ℂ) * p := by
      simp only [hg]; push_cast; ring
    have ha₁n : ‖a₁‖ < 1 := mem_ball_zero_iff.1 ha₁
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, heq]
      calc ‖((1 - t : ℝ) : ℂ) * a₁ + (t : ℂ) * p‖
          ≤ ‖((1 - t : ℝ) : ℂ) * a₁‖ + ‖(t : ℂ) * p‖ := norm_add_le _ _
        _ = (1 - t) * ‖a₁‖ + t := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hpn, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2]),
            abs_of_nonneg ht.1]
        _ < 1 := by nlinarith [ht.2, ht.1]
    · have hseg : g t ∈ segment ℝ a₁ p := by
        refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
        rw [heq]
        simp [Complex.real_smul]
      exact (convex_ball p η).segment_subset ha₁p (mem_ball_self hη) hseg
  have hSB : S ⊆ ball (0 : ℂ) 1 ∩ ball p η := by
    rintro b (hb | ⟨t, ht, rfl⟩)
    · exact ⟨(convex_ball (0 : ℂ) 1).segment_subset ha₁ ha₂ hb,
        (convex_ball p η).segment_subset ha₁p ha₂p hb⟩
    · exact hgB t ht
  have hS0 : ∀ b ∈ S, b ≠ 0 := fun b hb h => by
    have := (hSB hb).2
    rw [h, mem_ball, dist_comm, dist_zero_right, hpn] at this
    linarith [min_le_right η₀ (1 / 2)]
  have hSc : S ⊆ closedBall (0 : ℂ) 1 \ {0} := fun b hb =>
    ⟨ball_subset_closedBall (hSB hb).1, hS0 b hb⟩
  have hφne : ∀ b ∈ S, φ b ≠ 0 := fun b hb =>
    jo_phi_ne_zero hφi hφ0 (hSc hb).1 (hS0 b hb)
  have hΨcS : ContinuousOn Ψ S :=
    continuousOn_const.add ((hφc.mono fun b hb => (hSc hb).1).inv₀ hφne)
  have hSpc : IsPreconnected S :=
    IsPreconnected.union' ⟨a₁, left_mem_segment ℝ a₁ a₂, ⟨0, ⟨le_rfl, zero_lt_one⟩, by simp [hg]⟩⟩
      (convex_segment a₁ a₂).isPreconnected (isPreconnected_Ico.image _ hgc.continuousOn)
  have hΨa : ∀ {x a : ℂ}, x ≠ z → φ a = (x - z)⁻¹ → Ψ a = x := fun hxz ha => by
    simp only [hΨ, ha]
    exact jo_inv_left hxz
  have hx₁z : x₁ ≠ z := fun e => hx₁ (e ▸ jo_mem_filledBall_self hs)
  have hx₂z : x₂ ≠ z := fun e => hx₂ (e ▸ jo_mem_filledBall_self hs)
  refine ⟨Ψ '' S, ?_, hSpc.image _ hΨcS, ⟨a₁, Or.inl (left_mem_segment ℝ a₁ a₂), hΨa hx₁z hφa₁⟩,
    ⟨a₂, Or.inl (right_mem_segment ℝ a₁ a₂), hΨa hx₂z hφa₂⟩, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hm : φ b ∈ jordanOmega D z s := hφB ▸ mem_image_of_mem φ (hSB hb).1
    rcases hm with h | h
    · exact h
    · exact (hφne b hb h).elim
  · -- `w = Ψ p` is a limit of `Ψ (g t)`, `t ↑ 1`
    have hpcl : p ∈ closure S := by
      have h1 : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
        rw [closure_Ico zero_ne_one]
        exact ⟨zero_le_one, le_rfl⟩
      have h2 := mem_closure_image hgc.continuousAt h1
      rw [hg1] at h2
      exact closure_mono subset_union_right h2
    rw [← hΨp]
    exact (hΨc.mono fun b hb => (hSc hb).1).mem_closure_image hpcl
  · have hnear : ∀ b ∈ S, dist (Ψ b) w < ε / 2 := fun b hb => by
      rw [← hΨp]
      exact hη₀Ψ (hSc hb).1 (lt_of_lt_of_le (hSB hb).2 (min_le_left _ _))
    refine Metric.ediam_le fun u hu v hv => ?_
    obtain ⟨b, hb, rfl⟩ := hu
    obtain ⟨c, hc, rfl⟩ := hv
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    calc dist (Ψ b) (Ψ c) ≤ dist (Ψ b) w + dist w (Ψ c) := dist_triangle _ _ _
      _ ≤ ε := by
        rw [dist_comm w]
        linarith [hnear b hb, hnear c hc]

end LQGMetric.GM
