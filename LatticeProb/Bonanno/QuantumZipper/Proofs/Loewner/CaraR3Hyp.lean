/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR3Hyp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraRZ
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoArcInterior
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley

/-!
# EXT-CA nodes R2/R3: the bounded model of `revMap W T` for a simple hull

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R2** (bounded model part) and the
set-up of node **R3**. For a simple arc `γ` (continuous and injective on `[0,1]`, `γ 0` real,
`γ (0,1] ⊆ ℍ`) with `revHull W T = γ '' Ioc 0 1`:

* `carHyp_model`: `ψ = cayley ∘ revMap W T` satisfies the standing hypotheses `(Hψ)` of the
  C nodes (`CA.Car.CarHyp`) with `D = cayley '' (ℍ \ K)` and
  `E = sphere 0 1 ∪ cayley '' γ [0,1]` (circle plus attached arc);
* `ulc_modelE`: `E` is uniformly locally connected (T7: `ULC.sphere`, `ULC.image_Icc`,
  `ULC.union_of_isCompact_of_isClosed`);
* `cayley_mem_frontier`: every point of `ℝ ∪ γ [0,1]` is (after `cayley`) a frontier point of
  `D` (an arc has empty interior, `interior_arc_eq_empty`);
* `isPreconnected_modelE_diff_real`, `isPreconnected_modelE_diff_tip`: `E \ {q}` is connected
  for `q` the image of a real point other than the base `γ 0`, and for the tip `γ 1` (the input
  of C6).

These are elementary plane-topology facts (own elementary proofs).
-/

noncomputable section

open Set Metric Filter Topology Complex

namespace QuantumZipper

namespace CaraR

open CA CA.Topo CA.Car

variable {γ : ℝ → ℂ}

/-- The bounded model domain `cayley '' (ℍ \ γ (0,1])`. -/
def modelD (γ : ℝ → ℂ) : Set ℂ := cayley '' (H \ γ '' Ioc 0 1)

/-- The boundary set of the bounded model: the unit circle plus the image of the closed arc. -/
def modelE (γ : ℝ → ℂ) : Set ℂ := sphere 0 1 ∪ cayley '' (γ '' Icc 0 1)

theorem ne_neg_I_of_Hbar {z : ℂ} (hz : z ∈ Hbar) : z ∈ {w : ℂ | w ≠ -I} :=
  ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg hz)

theorem arc_subset_Hbar (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) :
    γ '' Icc 0 1 ⊆ Hbar := by
  rintro _ ⟨s, hs, rfl⟩
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h; show (0 : ℝ) ≤ (γ 0).im; rw [hγ0]
  · exact H_subset_Hbar (hγH s ⟨h, hs.2⟩)

theorem not_mem_H_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z ∉ H := by
  intro h; have : (0 : ℝ) < z.im := h; linarith

theorem H_diff_Ioc (hγ0 : (γ 0).im = 0) : H \ γ '' Ioc 0 1 = H \ γ '' Icc 0 1 := by
  ext z; constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; exact not_mem_H_of_im_eq_zero hγ0 hz
    · exact hn ⟨s, ⟨h, hs.2⟩, rfl⟩
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h => hn (image_mono Ioc_subset_Icc_self h)⟩

theorem continuousOn_cayley_arc (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0)
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) : ContinuousOn (cayley ∘ γ) (Icc 0 1) :=
  continuousOn_cayley.comp hγc fun s hs =>
    ne_neg_I_of_Hbar (arc_subset_Hbar hγ0 hγH ⟨s, hs, rfl⟩)

theorem isCompact_cayley_arc (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0)
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) : IsCompact (cayley '' (γ '' Icc 0 1)) := by
  rw [← image_comp]
  exact isCompact_Icc.image_of_continuousOn (continuousOn_cayley_arc hγc hγ0 hγH)

theorem modelD_eq (hγ0 : (γ 0).im = 0) :
    modelD γ = ball 0 1 ∩ cayleyInv ⁻¹' (H \ γ '' Icc 0 1) := by
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩
    rw [H_diff_Ioc hγ0] at hz
    have hzI := add_I_ne_zero_of_im_nonneg (le_of_lt (show (0 : ℝ) < z.im from hz.1))
    refine ⟨cayley_mem_ball hz.1, ?_⟩
    show cayleyInv (cayley z) ∈ H \ γ '' Icc 0 1
    rwa [cayleyInv_cayley hzI]
  · rintro ⟨hw, hz⟩
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw
    refine ⟨cayleyInv w, ?_, cayley_cayleyInv hw1⟩
    rw [H_diff_Ioc hγ0]; exact hz

theorem isOpen_modelD (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0) :
    IsOpen (modelD γ) := by
  rw [modelD_eq hγ0]
  refine (continuousOn_cayleyInv.mono fun w hw => ?_).isOpen_inter_preimage isOpen_ball
    (isOpen_H.sdiff (isCompact_Icc.image_of_continuousOn hγc).isClosed)
  rintro rfl; simp at hw

theorem modelD_subset_ball : modelD γ ⊆ ball 0 1 := by
  rintro _ ⟨z, hz, rfl⟩; exact cayley_mem_ball hz.1

theorem cayley_ofReal_mem_sphere (x : ℝ) : cayley (x : ℂ) ∈ sphere (0 : ℂ) 1 := by
  have hI := add_I_ne_zero_of_im_nonneg (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
  have h := one_sub_sq_norm_cayley (x : ℂ) hI
  rw [ofReal_im, mul_zero, zero_div] at h
  rw [mem_sphere_zero_iff_norm]
  have h2 : ‖cayley (x : ℂ)‖ ^ 2 = 1 ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2

theorem im_cayleyInv_of_mem_sphere {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    (cayleyInv w).im = 0 := by
  rw [im_cayleyInv, mem_sphere_zero_iff_norm.1 hw]; simp

theorem frontier_modelD_subset (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0) :
    frontier (modelD γ) ⊆ modelE γ := by
  intro w hw
  rw [(isOpen_modelD hγc hγ0).frontier_eq] at hw
  obtain ⟨hcl, hnot⟩ := hw
  have hcl' : w ∈ closedBall (0 : ℂ) 1 := by
    have := closure_mono (modelD_subset_ball (γ := γ)) hcl
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  rcases (mem_closedBall.1 hcl').lt_or_eq with hlt | heq
  · right
    have hw1 : w ≠ 1 := by rintro rfl; simp at hlt
    have hzH : cayleyInv w ∈ H := cayleyInv_mem_H (mem_ball.2 hlt)
    by_cases hzA : cayleyInv w ∈ γ '' Icc 0 1
    · exact ⟨cayleyInv w, hzA, cayley_cayleyInv hw1⟩
    · exact absurd (by rw [modelD_eq hγ0]; exact ⟨mem_ball.2 hlt, hzH, hzA⟩) hnot
  · left; exact mem_sphere.2 heq

theorem modelE_subset_compl (hγ0 : (γ 0).im = 0) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) :
    modelE γ ⊆ (modelD γ)ᶜ := by
  rintro w hwE ⟨z, hz, rfl⟩
  rcases hwE with hs | ⟨p, hp, hpz⟩
  · have h1 := cayley_mem_ball hz.1
    rw [mem_sphere] at hs; rw [mem_ball] at h1; linarith
  · have hpH := arc_subset_Hbar hγ0 hγH hp
    have := bijOn_cayley_Hbar.injOn hpH (H_subset_Hbar hz.1) hpz
    rw [H_diff_Ioc hγ0] at hz
    exact hz.2 (this ▸ hp)

/-- **R2 (bounded model).** `cayley ∘ revMap W T` satisfies the standing hypotheses `(Hψ)`. -/
theorem carHyp_model {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0)
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) (hK : revHull W T = γ '' Ioc 0 1) :
    CarHyp (cayley ∘ revMap W T) (modelD γ) (modelE γ) 2 where
  holo := differentiableOn_cayley_Hbar.comp (differentiableOn_revMap W hW hT.le)
    fun z hz => H_subset_Hbar ((bijOn_revMap_revHull hW hT.le).mapsTo hz).1
  bij := by
    have h1 := bijOn_revMap_revHull hW hT.le
    rw [hK] at h1
    refine (InjOn.bijOn_image ?_).comp h1
    exact bijOn_cayley_Hbar.injOn.mono fun z hz => H_subset_Hbar hz.1
  isOpen := isOpen_modelD hγc hγ0
  bdd := fun w hw => by
    have := modelD_subset_ball hw
    rw [mem_ball] at this ⊢; linarith
  isClosed := isClosed_sphere.union (isCompact_cayley_arc hγc hγ0 hγH).isClosed
  frontier_sub := frontier_modelD_subset hγc hγ0
  sub_compl := modelE_subset_compl hγ0 hγH
  E_bdd := by
    rintro w (hs | ⟨p, hp, rfl⟩)
    · rw [mem_sphere] at hs; rw [mem_closedBall]; linarith
    · have := cayley_mem_closedBall (arc_subset_Hbar hγ0 hγH hp)
      rw [mem_closedBall] at this ⊢; linarith

/-- **T7 for the bounded model.** The circle plus an attached arc is ULC. -/
theorem ulc_modelE (hγc : ContinuousOn γ (Icc 0 1)) (hγ0 : (γ 0).im = 0)
    (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) : ULC (modelE γ) := by
  have hc := continuousOn_cayley_arc hγc hγ0 hγH
  have := ULC.union_of_isCompact_of_isClosed (isCompact_sphere (0 : ℂ) 1)
    (isCompact_Icc.image_of_continuousOn hc).isClosed (ULC.sphere 0 1) (ULC.image_Icc hc)
  rwa [image_comp] at this

/-- Points of `ℍ̄` outside `ℍ \ γ [0,1]` are sent by `cayley` to frontier points of `D`. -/
theorem cayley_mem_frontier (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγ0 : (γ 0).im = 0) {p : ℂ} (hp : p ∈ Hbar) (hpD : p ∉ H \ γ '' Icc 0 1) :
    cayley p ∈ frontier (modelD γ) := by
  rw [(isOpen_modelD hγc hγ0).frontier_eq]
  refine ⟨?_, ?_⟩
  · have hcl : p ∈ closure (H \ γ '' Icc 0 1) := by
      by_contra hcl
      rw [Metric.mem_closure_iff] at hcl
      push Not at hcl
      obtain ⟨ε, hε, hball⟩ := hcl
      have hp0 : (0 : ℝ) ≤ p.im := hp
      set q : ℂ := p + ((ε / 2 : ℝ) : ℂ) * I with hq
      have hqim : q.im = p.im + ε / 2 := by simp [hq]
      have hsub : ball q (ε / 4) ⊆ γ '' Icc 0 1 := by
        intro z hz
        by_contra hzA
        have hzq : ‖z - q‖ < ε / 4 := by rw [← dist_eq_norm]; exact hz
        have him : |(z - q).im| ≤ ‖z - q‖ := abs_im_le_norm _
        have hzH : z ∈ H := by
          show (0 : ℝ) < z.im
          have : (z - q).im = z.im - q.im := sub_im z q
          rw [this] at him
          have := neg_abs_le (z.im - q.im)
          linarith
        have h1 := hball z ⟨hzH, hzA⟩
        have hpq : dist p q = ε / 2 := by
          rw [dist_eq_norm, hq, sub_add_cancel_left, norm_neg, norm_mul, norm_I, mul_one,
            norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have := dist_triangle p q z
        rw [dist_comm q z] at this
        have hzq' : dist z q < ε / 4 := hz
        linarith
      have hmem : q ∈ interior (γ '' Icc 0 1) :=
        mem_interior.2 ⟨ball q (ε / 4), hsub, isOpen_ball, mem_ball_self (by positivity)⟩
      rw [interior_arc_eq_empty ⟨γ, hγc, hγi, rfl⟩] at hmem
      exact hmem
    have hca : ContinuousAt cayley p :=
      continuousOn_cayley.continuousAt ((isOpen_ne.mem_nhds (ne_neg_I_of_Hbar hp)))
    have := mem_closure_image hca hcl
    rwa [modelD, H_diff_Ioc hγ0]
  · rintro ⟨z, hz, hzp⟩
    have := bijOn_cayley_Hbar.injOn (H_subset_Hbar hz.1) hp hzp
    rw [H_diff_Ioc hγ0] at hz
    exact hpD (this ▸ hz)

end CaraR

end QuantumZipper
