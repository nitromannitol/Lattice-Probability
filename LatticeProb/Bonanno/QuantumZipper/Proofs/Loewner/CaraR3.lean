/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Conn

/-!
# EXT-CA node R3: the continuous boundary extension of `revMap W T` for a simple hull

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R3**. For a continuous driver `W`
with `W 0 = 0`, `T > 0` and a simple arc `γ` with `revHull W T = γ '' Ioc 0 1`, the map
`revMap W T` has a continuous extension `F` to `ℍ̄` with the boundary correspondence facts
collected in `RevExt` (`CaraR3Defs.lean`): `extExists : ExtExists`.

Proof: Carathéodory's theorem in the bounded model (`CaraR3Hyp.lean`): C3
(`CA.Car.continuousOn_extension`) extends `ψ = cayley ∘ revMap W T` to `Fψ`, continuous on
`ℍ̄`; `Fψ` never takes the value `1 = cayley ∞` (because `revMap W T` is bounded on bounded
sets, R2), so `F := cayleyInv ∘ Fψ` is continuous on `ℍ̄`; C7 (`frontier_eq_insert_range`)
gives surjectivity onto `ℝ ∪ γ [0,1]`, C4 (`not_forall_eq_const_Ioo`), C5 (`fold`) and C6
(`eq_of_isPreconnected_diff`, with `CaraR3Conn.lean`) are transported through `cayley`.
Sources: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.1, Prop. 2.5,
Thm 2.6, pp. 20–24 (via the C nodes; route: DEVIATIONS L-CA-TOPO).
-/

noncomputable section

open Set Metric Filter Topology Complex

namespace QuantumZipper

namespace CaraR

open CA CA.Topo CA.Car

/-- The extension of `cayley ∘ revMap W T` never takes the value `cayley ∞ = 1` on `ℍ̄`
(`revMap W T` is bounded on bounded subsets of `ℍ`, R2). -/
theorem extension_ne_one {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {Fψ : ℂ → ℂ} (hEq : EqOn Fψ (cayley ∘ revMap W T) H) (hFc : ContinuousOn Fψ Hbar)
    {z : ℂ} (hz : z ∈ Hbar) : Fψ z ≠ 1 := by
  obtain ⟨M, hM⟩ :=
    (isBounded_image_revMap hW hT (Metric.isBounded_ball (x := z) (r := 1))).subset_closedBall 0
  have hT' := tendsto_nhdsWithin_H_of_extension hEq hFc hz
  intro h1
  rw [h1] at hT'
  have hNe : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H_eq_Hbar ▸ hz)
  have hδ : 0 < 2 / (|M| + 1) := by positivity
  have hev1 := hT'.eventually (ball_mem_nhds 1 hδ)
  have hev2 : ∀ᶠ w in 𝓝[H] z, w ∈ H ∩ ball z 1 :=
    inter_mem_nhdsWithin H (ball_mem_nhds z one_pos)
  obtain ⟨w, hw1, hw2⟩ := (hev1.and hev2).exists
  have hfw : ‖revMap W T w‖ ≤ |M| := by
    have := hM ⟨w, ⟨hw2.2, hw2.1⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_abs_self M)
  have hfH : revMap W T w ∈ H := ((bijOn_revMap_revHull hW hT.le).mapsTo hw2.1).1
  have hI := add_I_ne_zero_of_im_nonneg (le_of_lt (show (0 : ℝ) < (revMap W T w).im from hfH))
  have h2I : ‖(2 : ℂ) * I‖ = 2 := by simp
  have hdist : dist (cayley (revMap W T w)) 1 = 2 / ‖revMap W T w + I‖ := by
    rw [dist_comm, dist_eq_norm, one_sub_cayley hI, norm_div, h2I]
  have hle : ‖revMap W T w + I‖ ≤ |M| + 1 :=
    (norm_add_le _ _).trans (by rw [norm_I]; linarith)
  have hpos : 0 < ‖revMap W T w + I‖ := norm_pos_iff.2 hI
  have hcmp : 2 / (|M| + 1) ≤ 2 / ‖revMap W T w + I‖ :=
    div_le_div_of_nonneg_left (by norm_num) hpos hle
  have hw1' : dist (cayley (revMap W T w)) 1 < 2 / (|M| + 1) := hw1
  linarith

/-- **R3.** Every simple reverse hull has a continuous boundary extension `F` of `revMap W T`
with the boundary correspondence facts `RevExt`. -/
theorem extExists : ExtExists := by
  intro W hW hW0 T hT γ hγc hγi hγ0 hγH hK
  have h := carHyp_model hW hT hγc hγ0 hγH hK
  obtain ⟨Fψ, hEq, hFc, hfr, wInf, -, hInf⟩ := continuousOn_extension h (ulc_modelE hγc hγ0 hγH)
  have hw1 : wInf = 1 := by
    have := neBot_cobounded_inf_H
    exact tendsto_nhds_unique hInf
      (tendsto_cayley_cobounded.comp (tendsto_revMap_cobounded hW hT))
  subst hw1
  have hne1 : ∀ z ∈ Hbar, Fψ z ≠ 1 := fun z hz => extension_ne_one hW hT hEq hFc hz
  set F : ℂ → ℂ := fun z => cayleyInv (Fψ z) with hFdef
  have hψF : ∀ z ∈ Hbar, Fψ z = cayley (F z) := fun z hz =>
    (cayley_cayleyInv (hne1 z hz)).symm
  have hreal : ∀ x : ℝ, ((x : ℝ) : ℂ) ∈ Hbar := ofReal_mem_Hbar'
  have hbdry : ∀ x : ℝ, (F x).im = 0 ∨ F x ∈ γ '' Icc 0 1 := by
    intro x
    rcases h.frontier_sub (hfr x) with hs | ⟨p, hp, hpx⟩
    · left; exact im_cayleyInv_of_mem_sphere hs
    · right
      show cayleyInv (Fψ x) ∈ _
      rw [← hpx, cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (arc_subset_Hbar hγ0 hγH hp))]
      exact hp
  have hmemHbar : ∀ p : ℂ, (p.im = 0 ∨ p ∈ γ '' Icc 0 1) → p ∈ Hbar := fun p hp =>
    hp.elim (fun h0 => show (0 : ℝ) ≤ p.im from h0.ge) (fun hA => arc_subset_Hbar hγ0 hγH hA)
  refine ⟨F, ⟨?_, ?_, hbdry, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    show cayleyInv (Fψ z) = revMap W T z
    rw [hEq hz, Function.comp_apply]
    exact cayleyInv_cayley (add_I_ne_zero_of_im_nonneg
      (le_of_lt (show (0 : ℝ) < (revMap W T z).im from
        ((bijOn_revMap_revHull hW hT.le).mapsTo hz).1)))
  · exact continuousOn_cayleyInv.comp hFc fun z hz => hne1 z hz
  · intro p hp
    have hpHbar := hmemHbar p hp
    have hpD : p ∉ H \ γ '' Icc 0 1 := by
      rintro ⟨hpH, hpA⟩
      rcases hp with h0 | hA
      · exact not_mem_H_of_im_eq_zero h0 hpH
      · exact hpA hA
    have hfr' := cayley_mem_frontier hγc hγi hγ0 hpHbar hpD
    rw [frontier_eq_insert_range h hEq hFc hInf] at hfr'
    rcases hfr' with h1 | ⟨x, hx⟩
    · exact absurd h1 (cayley_ne_one (add_I_ne_zero_of_im_nonneg hpHbar))
    · refine ⟨x, ?_⟩
      show cayleyInv (Fψ x) = p
      rw [show Fψ x = cayley p from hx, cayleyInv_cayley (add_I_ne_zero_of_im_nonneg hpHbar)]
  · intro a b hab c hc
    apply not_forall_eq_const_Ioo h.holo h.bij.injOn hEq hFc hab (cayley c)
    intro t ht
    rw [hψF t (hreal t), hc t ht]
  · intro p hp hpγ x y hx hy
    have hp' : ((p.re : ℝ) : ℂ) = p := ofReal_re_of_im_eq_zero hp
    have hc := isPreconnected_modelE_diff_real hγc hγ0 hγH (p := p.re) (by rw [hp']; exact hpγ)
    refine (eq_of_isPreconnected_diff h hEq hFc hInf hc).1 x y ?_ ?_
    · rw [hψF x (hreal x), hx, hp']
    · rw [hψF y (hreal y), hy, hp']
  · intro x y hx hy
    have hc := isPreconnected_modelE_diff_tip hγc hγi hγ0 hγH
    refine (eq_of_isPreconnected_diff h hEq hFc hInf hc).1 x y ?_ ?_
    · rw [hψF x (hreal x), hx]
    · rw [hψF y (hreal y), hy]
  · intro x y hxy q hx hy Z hZ hZc
    have hqHbar : q ∈ Hbar := hx ▸ hmemHbar _ (hbdry x)
    have hZHbar : ∀ z ∈ Z, z ∈ Hbar := fun z hz => hmemHbar z (hZ hz).1
    have hZ' : cayley '' Z ⊆ modelE γ \ {cayley q} := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rcases (hZ hz).1 with h0 | hA
        · left; rw [← ofReal_re_of_im_eq_zero h0]; exact cayley_ofReal_mem_sphere _
        · right; exact mem_image_of_mem _ hA
      · intro h'
        rw [mem_singleton_iff] at h'
        exact (hZ hz).2 (cayley_injOn_Hbar (hZHbar z hz) hqHbar h')
    have hZc' : IsPreconnected (cayley '' Z) :=
      hZc.image _ (continuousOn_cayley.mono fun z hz => ne_neg_I_of_Hbar (hZHbar z hz))
    rcases fold h hEq hFc hInf hxy (q := cayley q) (by rw [hψF x (hreal x), hx])
      (by rw [hψF y (hreal y), hy]) hZ' hZc' with h1 | ⟨h2, -⟩
    · left
      intro t ht htZ
      exact h1 t ht (by rw [hψF t (hreal t)]; exact mem_image_of_mem _ htZ)
    · right
      intro s hs hsZ
      exact h2 s hs (by rw [hψF s (hreal s)]; exact mem_image_of_mem _ hsZ)

end CaraR

end QuantumZipper
