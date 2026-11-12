/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Complex.JordanMap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdry
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep

/-!
# The conformal map onto a domain with Jordan-type boundary, extended to the closed disc

Decision D17 / `decisions/DEC-B.md` node **J2** (Carathéodory's theorem for Jordan domains,
Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.6; used in GPS
arXiv:2010.07889, text after Lemma 2.4). Generic form, shared with the CONF tasks.

`jm_exists_closedDisc_extension`: let `U ⊆ ℂ` be open, bounded, preconnected, `0 ∈ U`, with
holomorphic square roots (`HasHoloSqrt`, QuantumZipper's form of simple connectivity used by its
Riemann mapping theorem), whose frontier is uniformly locally connected and has no cut points
(`frontier U ∖ {q}` preconnected for every `q`). Then there is `φ : ℂ → ℂ`, continuous and
injective on the closed unit disc, holomorphic on the open disc, `φ 0 = 0`, with
`φ '' ball 0 1 = U` and `φ '' sphere 0 1 = frontier U`.

Proof (no new mathematics; assembly of QuantumZipper results): the Riemann map
`CA.RMT.riemann_mapping_of_hasHoloSqrt`, normalized by a disc automorphism `CA.diskMobius`,
precomposed with the Cayley map `CA.cayley : ℍ → 𝔻`; Carathéodory's continuity theorem in
half-plane form `CA.Car.continuousOn_extension` (ULC boundary) and its Jordan case
`CA.Car.isClosedEmbedding_bdryMap` (no cut points); then transport back to the disc by
`CA.cayleyInv`, the point `1 ∈ ∂𝔻` corresponding to `∞ ∈ ∂ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open QuantumZipper QuantumZipper.CA QuantumZipper.CA.Car

namespace LQGMetric.JordanMap

theorem jm_bijOn_diskMobius {b : ℂ} (hb : ‖b‖ < 1) :
    BijOn (diskMobius b) (ball 0 1) (ball 0 1) := by
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  refine ⟨fun w hw => diskMobius_mem_ball hb hw, fun x hx y hy h => ?_, fun w hw => ?_⟩
  · rw [← diskMobius_neg_diskMobius hb (mem_ball_zero_iff.1 hx).le, h,
      diskMobius_neg_diskMobius hb (mem_ball_zero_iff.1 hy).le]
  · refine ⟨diskMobius (-b) w, diskMobius_mem_ball hb' hw, ?_⟩
    have := diskMobius_neg_diskMobius hb' (mem_ball_zero_iff.1 hw).le
    rwa [neg_neg] at this

/-- The Riemann map `𝔻 → U` normalized by `ψ 0 = 0` (QuantumZipper `riemann_mapping_of_hasHoloSqrt`
composed with a disc automorphism). -/
theorem jm_riemann_normalized {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hU : U ≠ univ) (hsq : RMT.HasHoloSqrt U) :
    ∃ ψ : ℂ → ℂ, BijOn ψ (ball 0 1) U ∧ DifferentiableOn ℂ ψ (ball 0 1) ∧ ψ 0 = 0 := by
  obtain ⟨φ, hφ, -, ψ₀, hψ₀, hψ₀d, hleft⟩ :=
    RMT.riemann_mapping_of_hasHoloSqrt hUo hUc ⟨0, h0⟩ hU hsq
  have ha' : ‖φ 0‖ < 1 := mem_ball_zero_iff.1 (hφ.mapsTo h0)
  have hna : ‖-φ 0‖ < 1 := by rwa [norm_neg]
  have hbij := jm_bijOn_diskMobius hna
  refine ⟨ψ₀ ∘ diskMobius (-φ 0), hψ₀.comp hbij, hψ₀d.comp
    ((differentiableOn_diskMobius hna).mono ball_subset_closedBall) hbij.mapsTo, ?_⟩
  have h1 : diskMobius (-φ 0) 0 = φ 0 := by simp [diskMobius]
  simp only [Function.comp_apply, h1]
  exact hleft h0

/-- `F` tends to `wInf` at `∞` within `ℍ̄` (same argument as QuantumZipper
`tendsto_extension_cocompact`, which treats `ℝ`). -/
theorem jm_tendsto_extension_Hbar {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar)
    {wInf : ℂ} (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 wInf) := by
  refine (nhds_basis_closedBall.tendsto_right_iff).2 fun ε hε => ?_
  have hmem := hInf (closedBall_mem_nhds wInf hε)
  rw [mem_map, mem_inf_principal] at hmem
  set S : Set ℂ := {z | z ∈ H → z ∈ ψ ⁻¹' closedBall wInf ε} with hS
  have hSb : Bornology.IsBounded Sᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
  obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
  rw [Filter.Eventually, mem_inf_principal]
  refine mem_of_superset ((Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_of_mem
    (i := R) trivial) fun x hx hxH => ?_
  have hx' : R < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hx
  have hcl := mem_closure_image_of_mem_nhdsWithin hEq hF hxH
    (inter_mem_nhdsWithin H ((isOpen_lt continuous_const continuous_norm).mem_nhds hx'))
  refine closure_minimal ?_ isClosed_closedBall hcl
  rintro _ ⟨w, ⟨hwH, hwR⟩, rfl⟩
  have hwS : w ∈ S := by
    by_contra hwS
    have := hR hwS
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.2 hwR this
  exact hwS hwH

theorem jm_cayleyInv_real {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    cayleyInv w = ((cayleyInv w).re : ℂ) := by
  have h : (cayleyInv w).im = 0 := by
    rw [im_cayleyInv, mem_sphere_zero_iff_norm.1 hw]
    simp
  exact Complex.ext rfl (by simp [h])

theorem jm_cayley_real (x : ℝ) : cayley x ∈ sphere (0 : ℂ) 1 ∧ cayley x ≠ 1 := by
  have hx : (x : ℂ) + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  refine ⟨?_, cayley_ne_one hx⟩
  have h := one_sub_sq_norm_cayley (x : ℂ) hx
  rw [Complex.ofReal_im, mul_zero, zero_div, sub_eq_zero] at h
  rw [mem_sphere_zero_iff_norm]
  have h0 := norm_nonneg (cayley x)
  nlinarith


/-- **J2 (generic).** Carathéodory's theorem for a bounded simply connected (`HasHoloSqrt`)
domain `U ∋ 0` whose frontier is ULC and has no cut points: the normalized conformal map
`𝔻 → U` extends to a continuous injective map of the closed disc onto `U ∪ ∂U`, mapping the
circle onto `∂U`. -/
theorem jm_exists_closedDisc_extension {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0 : ℂ) ∈ U) (hUb : Bornology.IsBounded U) (hsq : RMT.HasHoloSqrt U)
    (hulc : Topo.ULC (frontier U)) (hcut : ∀ q, IsPreconnected (frontier U \ {q})) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = 0 ∧ φ '' ball 0 1 = U ∧
      φ '' sphere 0 1 = frontier U := by
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hUb
  have hUne : U ≠ univ := by
    intro h
    have hm : ((|R₀| : ℝ) : ℂ) ∈ ball (0 : ℂ) R₀ := hR₀ (h ▸ mem_univ _)
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_abs] at hm
    exact lt_irrefl _ (lt_of_lt_of_le hm (le_abs_self R₀))
  obtain ⟨ψ₀, hψ₀, hψ₀d, hψ₀0⟩ := jm_riemann_normalized hUo hUc h0 hUne hsq
  have hHHbar : H ⊆ Hbar := H_subset_Hbar
  have hC : CarHyp (ψ₀ ∘ cayley) U (frontier U) R₀ :=
    { holo := hψ₀d.comp (differentiableOn_cayley_Hbar.mono hHHbar) bijOn_cayley_H.mapsTo
      bij := hψ₀.comp bijOn_cayley_H
      isOpen := hUo
      bdd := hR₀
      isClosed := isClosed_frontier
      frontier_sub := subset_rfl
      sub_compl := fun x hx hxU => hx.2 (hUo.interior_eq.symm ▸ hxU)
      E_bdd := frontier_subset_closure.trans ((closure_mono hR₀).trans closure_ball_subset_closedBall) }
  obtain ⟨F, hEq, hFc, -, wInf, -, hInf⟩ := continuousOn_extension hC hulc
  obtain ⟨hemb, hrange⟩ := isClosedEmbedding_bdryMap hC hEq hFc hInf hcut
  have hFinf := jm_tendsto_extension_Hbar hEq hFc hInf
  set φ : ℂ → ℂ := fun w => if w = 1 then wInf else F (cayleyInv w) with hφdef
  -- on the open disc, `φ = ψ₀`
  have hball : ∀ w ∈ ball (0 : ℂ) 1, φ w = ψ₀ w := fun w hw => by
    have hw1 : w ≠ 1 := fun h => by
      rw [h, mem_ball_zero_iff, norm_one] at hw
      exact lt_irrefl _ hw
    simp only [hφdef, if_neg hw1]
    rw [hEq (cayleyInv_mem_H hw), Function.comp_apply, cayley_cayleyInv hw1]
  -- on the circle, `φ` is the boundary map composed with `w ↦ ∞ or Re (cayleyInv w)`
  set g : ℂ → OnePoint ℝ := fun w => if w = 1 then OnePoint.infty else ((cayleyInv w).re : ℝ)
    with hgdef
  have hsph : ∀ w ∈ sphere (0 : ℂ) 1, φ w = bdryMap F wInf (g w) := fun w hw => by
    by_cases hw1 : w = 1
    · simp only [hφdef, hgdef, if_pos hw1]
      rfl
    · simp only [hφdef, hgdef, if_neg hw1]
      show F (cayleyInv w) = F ((cayleyInv w).re : ℂ)
      rw [← jm_cayleyInv_real hw]
  have hginj : InjOn g (sphere (0 : ℂ) 1) := by
    intro w₁ h₁ w₂ h₂ h
    by_cases e₁ : w₁ = 1 <;> by_cases e₂ : w₂ = 1
    · rw [e₁, e₂]
    · simp only [hgdef, if_pos e₁, if_neg e₂] at h
      exact (OnePoint.infty_ne_coe _ h).elim
    · simp only [hgdef, if_neg e₁, if_pos e₂] at h
      exact (OnePoint.coe_ne_infty _ h).elim
    · simp only [hgdef, if_neg e₁, if_neg e₂] at h
      have hre : (cayleyInv w₁).re = (cayleyInv w₂).re := OnePoint.coe_injective h
      have hc : cayleyInv w₁ = cayleyInv w₂ := by
        rw [jm_cayleyInv_real h₁, jm_cayleyInv_real h₂, hre]
      rw [← cayley_cayleyInv e₁, hc, cayley_cayleyInv e₂]
  have himB : φ '' ball 0 1 = U := (image_congr hball).trans hψ₀.image_eq
  have hdisj : ∀ w ∈ ball (0 : ℂ) 1, φ w ∉ frontier U := fun w hw hf =>
    hf.2 (hUo.interior_eq.symm ▸ (himB ▸ mem_image_of_mem φ hw))
  refine ⟨φ, ?_, ?_, ?_, ?_, himB, ?_⟩
  · -- continuity on the closed disc
    intro w hw
    have hmaps : MapsTo cayleyInv (closedBall (0 : ℂ) 1 \ {1}) Hbar :=
      fun x hx => cayleyInv_mem_Hbar hx.1
    by_cases hw1 : w = 1
    · subst hw1
      rw [← continuousWithinAt_diff_self]
      have ht : Tendsto cayleyInv (𝓝[closedBall (0 : ℂ) 1 \ {1}] 1)
          (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) :=
        tendsto_inf.2 ⟨tendsto_cayleyInv_nhdsNE_one.mono_left
          (nhdsWithin_mono _ fun x hx => hx.2), tendsto_principal.2
          (eventually_nhdsWithin_of_forall fun x hx => hmaps hx)⟩
      have h1 : φ 1 = wInf := by simp [hφdef]
      show Tendsto φ _ (𝓝 (φ 1))
      rw [h1]
      refine (hFinf.comp ht).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
      simp only [Function.comp_apply, hφdef, if_neg (show x ≠ 1 from hx.2)]
    · have hcont : ContinuousWithinAt (F ∘ cayleyInv) (closedBall (0 : ℂ) 1 \ {1}) w :=
        (hFc.continuousWithinAt (hmaps ⟨hw, hw1⟩)).comp
          ((continuousOn_cayleyInv.continuousAt
            (isOpen_ne.mem_nhds hw1)).continuousWithinAt) hmaps
      have hcont' : ContinuousWithinAt φ (closedBall (0 : ℂ) 1 \ {1}) w :=
        hcont.congr (fun x hx => by simp only [Function.comp_apply, hφdef, if_neg (show x ≠ 1 from hx.2)])
          (by simp only [Function.comp_apply, hφdef, if_neg hw1])
      rw [diff_eq, continuousWithinAt_inter (isOpen_compl_singleton.mem_nhds hw1)] at hcont'
      exact hcont'
  · -- injectivity on the closed disc
    intro w₁ h₁ w₂ h₂ h
    have hsplit : ∀ w ∈ closedBall (0 : ℂ) 1, w ∈ ball (0 : ℂ) 1 ∨ w ∈ sphere (0 : ℂ) 1 :=
      fun w hw => by
        rcases (mem_closedBall.1 hw).lt_or_eq with h | h
        · exact Or.inl (mem_ball.2 h)
        · exact Or.inr (mem_sphere.2 h)
    have hfr : ∀ w ∈ sphere (0 : ℂ) 1, φ w ∈ frontier U := fun w hw => by
      rw [hsph w hw, ← hrange]
      exact mem_range_self _
    rcases hsplit w₁ h₁ with b₁ | s₁ <;> rcases hsplit w₂ h₂ with b₂ | s₂
    · rw [hball w₁ b₁, hball w₂ b₂] at h
      exact hψ₀.injOn b₁ b₂ h
    · exact (hdisj w₁ b₁ (h ▸ hfr w₂ s₂)).elim
    · exact (hdisj w₂ b₂ (h ▸ hfr w₁ s₁)).elim
    · rw [hsph w₁ s₁, hsph w₂ s₂] at h
      exact hginj s₁ s₂ (hemb.injective h)
  · exact hψ₀d.congr fun w hw => hball w hw
  · rw [hball 0 (mem_ball_self one_pos), hψ₀0]
  · -- the circle goes onto the frontier
    apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      rw [hsph w hw, ← hrange]
      exact mem_range_self _
    · rw [← hrange]
      rintro _ ⟨o, rfl⟩
      induction o using OnePoint.rec with
      | infty =>
        refine ⟨1, by simp, ?_⟩
        simp [hφdef]
        rfl
      | coe x =>
        obtain ⟨hxs, hx1⟩ := jm_cayley_real x
        refine ⟨cayley x, hxs, ?_⟩
        simp only [hφdef, if_neg hx1]
        rw [cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (by simp))]
        rfl

end LQGMetric.JordanMap
