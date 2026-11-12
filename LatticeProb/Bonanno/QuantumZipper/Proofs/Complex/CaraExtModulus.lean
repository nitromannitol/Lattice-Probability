/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraExtModulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExtSep
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExtCurve
import Mathlib.Analysis.Complex.Schwarz

/-!
# EXT-CA C3, quantitative step: small half-disks have small images

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C3. Pommerenke, *Boundary Behaviour of Conformal
Maps* (1992), Thm 2.1, proof of (iv) ⇒ (i), printed pp. 21–22 (PDF pp. 29–30), and Prop. 2.3
(p. 22: the modulus depends only on the ULC modulus and the radii), in the half-plane form:

* C2 (`exists_short_semicircle_finite`, Wolff's lemma) gives a semicircle of radius
  `r ∈ (ρ², ρ)` around `x₀` whose image has length `< λ`;
* the image curve extends continuously to its end points (`exists_extend_Icc_of_lintegral`),
  which lie in `frontier D ⊆ E` (C1, `frontier_mem_of_tendsto`);
* ULC of `E` at scale `(ε, λ)` joins them by a preconnected `β ⊆ E` of diameter `≤ ε`;
* the Janiszewski step `norm_sub_le_of_mem_halfDisk` (reference point `I`) gives
  `ψ(H ∩ ball x₀ ρ²) ⊆ closedBall a (λ + ε)`.

`ULCAt E ε δ` is the ULC condition of `Topo.ULC` at one pair of scales, so that the modulus
obtained in `exists_modulus` visibly depends only on `R₀`, `η` (a lower bound for
`infDist (ψ I) E`), `ε` and the ULC modulus `δU` of `E` at scale `min (ε/8) (η/4)`.
-/

noncomputable section

open Set Metric Filter Topology Complex MeasureTheory
open scoped Real ENNReal

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

/-- `E` is uniformly locally connected at the pair of scales `(ε, δ)`. `Topo.ULC E` is
`∀ ε > 0, ∃ δ > 0, ULCAt E ε δ`. -/
def ULCAt (E : Set ℂ) (ε δ : ℝ) : Prop := ∀ a ∈ E, ∀ b ∈ E, dist a b < δ →
  ∃ β ⊆ E, IsPreconnected β ∧ a ∈ β ∧ b ∈ β ∧ Metric.diam β ≤ ε

private theorem semicircle_end_mem_frontier {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {x₀ r : ℝ} (hr : 0 < r) {cb : ℝ → ℂ}
    (hcb : ContinuousOn cb (Icc 0 π))
    (hcbψ : ∀ θ ∈ Ioo 0 π, cb θ = ψ ((x₀ : ℂ) + r * exp (θ * I)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc 0 π) (him : ((x₀ : ℂ) + r * exp (θ₀ * I)).im = 0)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Ioo 0 π) (hut : Tendsto u atTop (𝓝 θ₀)) :
    cb θ₀ ∈ frontier D := by
  set γ : ℝ → ℂ := fun θ => (x₀ : ℂ) + r * exp (θ * I) with hγ
  have hγc : Continuous γ := by fun_prop
  have hreal : γ θ₀ = (((γ θ₀).re : ℝ) : ℂ) := Complex.ext (by simp) (by rw [ofReal_im]; exact him)
  have hz : Tendsto (γ ∘ u) atTop (𝓝 (((γ θ₀).re : ℝ) : ℂ)) := by
    rw [← hreal]; exact (hγc.tendsto θ₀).comp hut
  have hcl : Tendsto (cb ∘ u) atTop (𝓝 (cb θ₀)) :=
    (hcb θ₀ hθ₀).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hut, Eventually.of_forall fun n => Ioo_subset_Icc_self (hu n)⟩)
  have heq : cb ∘ u = ψ ∘ (γ ∘ u) := funext fun n => hcbψ (u n) (hu n)
  rw [heq] at hcl
  exact frontier_mem_of_tendsto h (fun n => semicircle_mem_H x₀ hr (hu n)) hz hcl.mapClusterPt

/-- **C3, one half-disk.** With `λ` controlling the Wolff length (`2π²R₀²/log(1/ρ) < λ²`) and
`E` ULC at scales `(ε, λ)`, the image of `H ∩ ball x₀ ρ²` lies in a closed ball of radius
`λ + ε`, provided `λ + ε < η ≤ infDist (ψ I) E`. -/
theorem exists_center_halfDisk {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    {ε lam η ρ : ℝ} (hU : ULCAt E ε lam) (hη : η ≤ infDist (ψ I) E) (hlam : 0 < lam)
    (hlη : lam + ε < η) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρl : 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ρ) < lam ^ 2) (x₀ : ℝ) :
    ∃ a : ℂ, ∀ z ∈ H, ‖z - x₀‖ < ρ ^ 2 → ‖ψ z - a‖ ≤ lam + ε := by
  have hR : ψ '' H ⊆ ball 0 R₀ := h.bij.image_eq ▸ h.bdd
  obtain ⟨r, ⟨hr1, hr2⟩, hfin, hsq⟩ := exists_short_semicircle_finite isOpen_H h.holo
    h.bij.injOn hR (x₀ := x₀) hρ0 hρ1 (fun z hz => hz.1)
  have hr : 0 < r := (pow_pos hρ0 2).trans hr1
  set γ : ℝ → ℂ := fun θ => (x₀ : ℂ) + r * exp (θ * I) with hγ
  set ℓ : ℝ≥0∞ := ∫⁻ θ in Ioo 0 π, ‖deriv ψ (x₀ + r * exp (θ * I))‖ₑ * ENNReal.ofReal r
    with hℓ
  have hc : ContinuousOn (fun θ : ℝ => ψ (γ θ)) (Ioo 0 π) :=
    h.holo.continuousOn.comp (by fun_prop : Continuous γ).continuousOn
      fun θ hθ => semicircle_mem_H x₀ hr hθ
  obtain ⟨cb, hcb, hcbeq, hcbℓ⟩ := exists_extend_Icc_of_lintegral Real.pi_pos hc
    (enorm_sub_le_lintegral_semicircle h.holo x₀ hr) hfin
  have hcbψ : ∀ θ ∈ Ioo 0 π, cb θ = ψ ((x₀ : ℂ) + r * exp (θ * I)) := fun θ hθ => hcbeq hθ
  -- the length is `< λ`
  have hlog : 0 < Real.log (1 / ρ) := Real.log_pos ((one_lt_div hρ0).2 hρ1)
  have hℓl : ℓ < ENNReal.ofReal lam := by
    by_contra hle
    push Not at hle
    have h1 : ENNReal.ofReal (lam ^ 2) ≤ ℓ ^ 2 := by
      rw [ENNReal.ofReal_pow hlam.le]; exact pow_le_pow_left₀ bot_le hle 2
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans hsq)
    linarith
  have hcbl : ∀ s ∈ Icc 0 π, ∀ t ∈ Icc 0 π, ‖cb t - cb s‖ < lam := by
    intro s hs t ht
    have := (hcbℓ s hs t ht).trans_lt hℓl
    rwa [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hlam] at this
  -- the end points are in `frontier D ⊆ E`
  have h0 : cb 0 ∈ E := h.frontier_sub <| semicircle_end_mem_frontier h hr hcb hcbψ
    ⟨le_rfl, Real.pi_pos.le⟩ (by simp)
    (u := fun n => π / 2 * (1 / ((n : ℝ) + 1))) (fun n => by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      constructor <;> nlinarith [Real.pi_pos])
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (π / 2))
  have hπ : cb π ∈ E := h.frontier_sub <| semicircle_end_mem_frontier h hr hcb hcbψ
    ⟨Real.pi_pos.le, le_rfl⟩ (by simp [exp_mul_I])
    (u := fun n => π - π / 2 * (1 / ((n : ℝ) + 1))) (fun n => by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      constructor <;> nlinarith [Real.pi_pos])
    (by simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (π / 2)).const_sub π)
  -- a small preconnected `β ⊆ E` joining the end points
  obtain ⟨β, hβE, hβ, haβ, hbβ, hβd⟩ := hU _ h0 _ hπ (by
    rw [dist_comm, dist_eq_norm]; exact hcbl 0 ⟨le_rfl, Real.pi_pos.le⟩ π ⟨Real.pi_pos.le, le_rfl⟩)
  have hβb : Bornology.IsBounded (closure β) :=
    (isBounded_closedBall (x := (0 : ℂ)) (r := R₀)).subset
      ((closure_minimal hβE h.isClosed).trans h.E_bdd)
  have hJ : cb '' Icc 0 π ∪ closure β ⊆ ball (cb 0) (lam + ε) := by
    have hε : 0 ≤ ε := diam_nonneg.trans hβd
    rintro w (⟨θ, hθ, rfl⟩ | hw)
    · rw [mem_ball, dist_eq_norm]
      linarith [hcbl 0 ⟨le_rfl, Real.pi_pos.le⟩ θ hθ]
    · rw [mem_ball]
      have := dist_le_diam_of_mem hβb hw (subset_closure haβ)
      rw [diam_closure] at this
      linarith
  refine ⟨cb 0, fun z hz hzx => ?_⟩
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  have hIr : r < ‖I - x₀‖ := by
    have := abs_im_le_norm (I - x₀)
    simp only [sub_im, I_im, ofReal_im, sub_zero, abs_one] at this
    linarith
  have hq : lam + ε < ‖ψ I - cb 0‖ := by
    rw [← dist_eq_norm]; linarith [infDist_le_dist_of_mem (x := ψ I) h0]
  exact norm_sub_le_of_mem_halfDisk h hr hcb hcbψ h0 hπ hβE hβ haβ hbβ hJ hIH hIr hq hz
    (hzx.trans hr1)

theorem ULCAt.mono {E : Set ℂ} {ε δ δ' : ℝ} (h : ULCAt E ε δ) (hδ : δ' ≤ δ) : ULCAt E ε δ' :=
  fun a ha b hb hab => h a ha b hb (hab.trans_le hδ)

/-- The standing hypotheses are invariant under the automorphism `z ↦ -1/z` of `H`. -/
theorem CarHyp.comp_neg_inv {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀) :
    CarHyp (fun z => ψ (-z⁻¹)) D E R₀ := by
  have hmaps : MapsTo (fun z : ℂ => -z⁻¹) H H := by
    intro z hz
    have hz0 : 0 < z.im := hz
    have hne : z ≠ 0 := fun h0 => by simp [h0] at hz0
    show 0 < (-z⁻¹).im
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hz0 (normSq_pos.2 hne)
  have hne : ∀ z ∈ H, z ≠ 0 := fun z hz h0 => by
    have : 0 < z.im := hz
    simp [h0] at this
  have hinv : InvOn (fun z : ℂ => -z⁻¹) (fun z : ℂ => -z⁻¹) H H :=
    ⟨fun z _ => by simp, fun z _ => by simp⟩
  refine ⟨fun z hz => ?_, h.bij.comp (hinv.bijOn hmaps hmaps), h.isOpen, h.bdd, h.isClosed,
    h.frontier_sub, h.sub_compl, h.E_bdd⟩
  exact (((h.holo _ (hmaps hz)).differentiableAt (isOpen_H.mem_nhds (hmaps hz))).comp z
    (differentiableAt_inv (hne z hz)).neg).differentiableWithinAt

private theorem exists_params (R₀ η ε δU : ℝ) (hη : 0 < η) (hε : 0 < ε) (hδU : 0 < δU) :
    ∃ lam ρ : ℝ, 0 < lam ∧ lam ≤ δU ∧ lam + min (ε / 8) (η / 4) < η ∧
      2 * (lam + min (ε / 8) (η / 4)) ≤ ε ∧ 0 < ρ ∧ ρ < 1 ∧
      2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ρ) < lam ^ 2 := by
  set lam := min (min (ε / 8) (η / 4)) δU with hlam
  have hl0 : 0 < lam := lt_min (lt_min (by positivity) (by positivity)) hδU
  have hl1 : lam ≤ min (ε / 8) (η / 4) := min_le_left _ _
  have hm1 : min (ε / 8) (η / 4) ≤ ε / 8 := min_le_left _ _
  have hm2 : min (ε / 8) (η / 4) ≤ η / 4 := min_le_right _ _
  set K := 2 * π ^ 2 * R₀ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨lam, Real.exp (-(K / lam ^ 2 + 1)), hl0, min_le_right _ _, by linarith, by linarith,
    Real.exp_pos _, Real.exp_lt_one_iff.2 (by have : 0 ≤ K / lam ^ 2 := (by positivity); linarith),
    ?_⟩
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg, div_lt_iff₀ (by positivity)]
  have hl2 : 0 < lam ^ 2 := by positivity
  rw [mul_add, mul_div_cancel₀ _ hl2.ne', mul_one]
  linarith

/-- **C3, quantitative modulus** (Pommerenke 1992, Prop. 2.3, p. 22, half-plane form). The
modulus `δ` depends only on `R₀`, `η`, `ε` and the ULC modulus `δU` of `E` at scale
`min (ε/8) (η/4)`: it is uniform over all `(ψ, D, E)` satisfying the standing hypotheses with
`η ≤ infDist (ψ I) E`. -/
theorem exists_modulus (R₀ η ε δU : ℝ) (hη : 0 < η) (hε : 0 < ε) (hδU : 0 < δU) :
    ∃ δ > 0, ∀ (ψ : ℂ → ℂ) (D E : Set ℂ), CarHyp ψ D E R₀ →
      ULCAt E (min (ε / 8) (η / 4)) δU → η ≤ infDist (ψ I) E →
      ∀ z ∈ H, ∀ w ∈ H, dist z w < δ → dist (ψ z) (ψ w) ≤ ε := by
  obtain ⟨lam, ρ, hl0, hlδ, hlη, hlε, hρ0, hρ1, hρl⟩ := exists_params R₀ η ε δU hη hε hδU
  set C := |R₀| + 1 with hC
  have hC0 : 0 < C := by positivity
  have hρ2 : 0 < ρ ^ 2 := by positivity
  refine ⟨min (ρ ^ 2 / 2) (ε * ρ ^ 2 / (8 * C)), lt_min (by positivity) (by positivity),
    fun ψ D E h hU hη' z hz w hw hzw => ?_⟩
  have hδ1 := min_le_left (ρ ^ 2 / 2) (ε * ρ ^ 2 / (8 * C))
  have hδ2 := min_le_right (ρ ^ 2 / 2) (ε * ρ ^ 2 / (8 * C))
  have hz0 : 0 < z.im := hz
  by_cases hzi : z.im < ρ ^ 2 / 2
  · obtain ⟨a, ha⟩ := exists_center_halfDisk h (hU.mono hlδ) hη' hl0 hlη hρ0 hρ1 hρl z.re
    have hzre : ‖z - (z.re : ℂ)‖ = z.im := by
      rw [show z - (z.re : ℂ) = (z.im : ℂ) * I from Complex.ext (by simp) (by simp)]
      rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hz0]
    have h1 := ha z hz (by rw [hzre]; linarith)
    have h2 := ha w hw (by
      calc ‖w - (z.re : ℂ)‖ = ‖(w - z) + (z - (z.re : ℂ))‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - (z.re : ℂ)‖ := norm_add_le _ _
        _ < ρ ^ 2 := by rw [hzre, ← dist_eq_norm, dist_comm]; linarith)
    calc dist (ψ z) (ψ w) ≤ dist (ψ z) a + dist a (ψ w) := dist_triangle _ _ _
      _ ≤ (lam + min (ε / 8) (η / 4)) + (lam + min (ε / 8) (η / 4)) := by
        rw [dist_eq_norm, dist_comm, dist_eq_norm]; exact add_le_add h1 h2
      _ ≤ ε := by linarith
  · push Not at hzi
    set t := ρ ^ 2 / 2 with ht
    have ht0 : 0 < t := by positivity
    have hball : ball z t ⊆ H := by
      intro y hy
      have h1 : |y.im - z.im| ≤ ‖y - z‖ := by simpa using abs_im_le_norm (y - z)
      have h2 : ‖y - z‖ < t := by simpa [dist_eq_norm] using hy
      show 0 < y.im
      linarith [(abs_lt.1 (h1.trans_lt h2)).1]
    have hmaps : MapsTo ψ (ball z t) (closedBall (ψ z) (2 * C)) := by
      intro y hy
      have hy1 := h.bdd (h.bij.mapsTo (hball hy))
      have hz1 := h.bdd (h.bij.mapsTo hz)
      rw [mem_ball_zero_iff] at hy1 hz1
      rw [mem_closedBall, dist_eq_norm]
      have : |R₀| ≥ R₀ := le_abs_self R₀
      linarith [norm_sub_le (ψ y) (ψ z)]
    have hwb : w ∈ ball z t := by rw [mem_ball, dist_comm]; linarith
    have key := dist_le_div_mul_dist_of_mapsTo_ball (h.holo.mono hball) hmaps hwb
    rw [dist_comm (ψ z)]
    calc dist (ψ w) (ψ z) ≤ 2 * C / t * dist w z := key
      _ ≤ 2 * C / t * (ε * ρ ^ 2 / (8 * C)) := by
        gcongr; rw [dist_comm]; linarith
      _ = ε / 2 := by rw [ht]; field_simp; ring
      _ ≤ ε := by linarith

/-- **C3 at `∞`, quantitative.** Same dependence as `exists_modulus`: far out in `H`, `ψ`
oscillates by at most `ε` (via `z ↦ -1/z`, `CarHyp.comp_neg_inv`, which fixes `I`). -/
theorem exists_radius_infty (R₀ η ε δU : ℝ) (hη : 0 < η) (hε : 0 < ε) (hδU : 0 < δU) :
    ∃ Rb > 0, ∀ (ψ : ℂ → ℂ) (D E : Set ℂ), CarHyp ψ D E R₀ →
      ULCAt E (min (ε / 8) (η / 4)) δU → η ≤ infDist (ψ I) E →
      ∀ z ∈ H, ∀ w ∈ H, Rb < ‖z‖ → Rb < ‖w‖ → dist (ψ z) (ψ w) ≤ ε := by
  obtain ⟨lam, ρ, hl0, hlδ, hlη, hlε, hρ0, hρ1, hρl⟩ := exists_params R₀ η ε δU hη hε hδU
  have hρ2 : 0 < ρ ^ 2 := by positivity
  refine ⟨1 / ρ ^ 2, by positivity, fun ψ D E h hU hη' z hz w hw hzR hwR => ?_⟩
  obtain ⟨a, ha⟩ := exists_center_halfDisk h.comp_neg_inv (hU.mono hlδ) (by simpa using hη') hl0 hlη
    hρ0 hρ1 hρl 0
  have hH : ∀ y ∈ H, -y⁻¹ ∈ H := fun y hy => by
    have hy0 : 0 < y.im := hy
    have hne : y ≠ 0 := fun h0 => by simp [h0] at hy0
    show 0 < (-y⁻¹).im
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hy0 (normSq_pos.2 hne)
  have hfar : ∀ y ∈ H, 1 / ρ ^ 2 < ‖y‖ → ‖ψ y - a‖ ≤ lam + min (ε / 8) (η / 4) := by
    intro y hy hyR
    have hy0 : 0 < ‖y‖ := (by positivity : (0:ℝ) < 1 / ρ ^ 2).trans hyR
    have := ha (-y⁻¹) (hH y hy) (by
      rw [ofReal_zero, sub_zero, norm_neg, norm_inv]
      rw [one_div, inv_lt_comm₀ hρ2 hy0] at hyR
      exact hyR)
    simpa using this
  calc dist (ψ z) (ψ w) ≤ dist (ψ z) a + dist a (ψ w) := dist_triangle _ _ _
    _ ≤ (lam + min (ε / 8) (η / 4)) + (lam + min (ε / 8) (η / 4)) := by
      rw [dist_eq_norm, dist_comm, dist_eq_norm]; exact add_le_add (hfar z hz hzR) (hfar w hw hwR)
    _ ≤ ε := by linarith

end QuantumZipper.CA.Car
