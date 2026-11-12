/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M9
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# CONF Lemma 3.3, Step 3: condition 1 of `E^U` is an event of `h|_{ℂ∖U}` (`CONFEUOutside1`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:1238. Condition 1 of `E^U_r(z)` (C:1135) is
`D_h(∂B_{2r}(z), ∂B_{3r}(z)) ≥ c 𝔠_r e^{ξ h_r(z)}`. Written for `recField = h − h_ρ(w)` (Axiom III
with constants), the distance across the closed annulus `K = cl 𝔸_{2r,3r}(z) ⊆ ℂ ∖ U` is the
infimum of the internal distances in every neighbourhood `B_η(K)` (`GM.setDist_spheres_eq_internal`,
GM l. 1348), which is a.s. a measurable function of `recField|_{B_η(K)}` (Axiom II, over countable
dense subsets of the circles by continuity of internal metrics). The `liminf` over `η = 1/(n+1)`
of these events is `σ(recField|_{B_ε(ℂ∖U)})`-measurable for every `ε > 0`, i.e.
`recSigma`-measurable, and a.s. equal to condition 1. Own elementary argument following CONF's
sentence (the `liminf` device replaces CONF's "depends only on").

* **`confEUOutside1_of`**: `CONFEUOutside1 γ D c p`;
* **`confFKGFrozenEUc_of_link'`**: `CONFFKGFrozenEUc` from `CONFLem2_10` and `CONFHarmPartLink`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- the infimum of a function continuous on `V × V` over `A × B ⊆ V × V` equals its infimum over
dense subsets -/
lemma iInf₂_eq_of_dense_m10 {f : ℂ × ℂ → ℝ≥0∞} {V A B A₀ B₀ : Set ℂ}
    (hf : ContinuousOn f (V ×ˢ V)) (hAV : A ⊆ V) (hBV : B ⊆ V) (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B)
    (hAd : A ⊆ closure A₀) (hBd : B ⊆ closure B₀) :
    ⨅ x ∈ A₀, ⨅ y ∈ B₀, f (x, y) = ⨅ x ∈ A, ⨅ y ∈ B, f (x, y) := by
  refine le_antisymm (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
    (le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le_of_le x (hA₀ hx) (iInf₂_le y (hB₀ hy)))
  have hcl : (x, y) ∈ closure (A₀ ×ˢ B₀) := by rw [closure_prod_eq]; exact ⟨hAd hx, hBd hy⟩
  have hcw : ContinuousWithinAt f (A₀ ×ˢ B₀) (x, y) :=
    (hf (x, y) ⟨hAV hx, hBV hy⟩).mono (prod_mono (hA₀.trans hAV) (hB₀.trans hBV))
  exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const hcw fun q hq =>
    iInf₂_le_of_le q.1 hq.1 (iInf₂_le q.2 hq.2)

/-- **Condition 1 of `E^U` is an event of `h|_{ℂ∖U}`** (CONF C:1238) -/
theorem confEUOutside1_of {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {p : CONFParams} : CONFEUOutside1 γ D c p := by
  intro Ω mΩ P _ h hh z r hr T hT ρ w hρ hUw
  have hg := isWholePlaneGFF_recField hh ρ w
  have hpc := GM.isGFFPlusCont_of_isWholePlaneGFF hg
  set K : Set ℂ := {x | 2 * r ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 * r} with hK
  have hKU : K ⊆ (confU r p.δ z T)ᶜ := fun x hx hxU => by
    have h1 : 3 * r < ‖x - z‖ := hxU.1.1
    linarith [hx.2]
  set η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hη
  have hηp : ∀ n, 0 < η n := fun n => by positivity
  set Wn : ℕ → Opens ℂ := fun n => nbhdO (η n) K with hWn
  have hKW : ∀ n x, 2 * r ≤ ‖x - z‖ → ‖x - z‖ ≤ 3 * r → x ∈ (Wn n : Set ℂ) := fun n x h1 h2 =>
    self_subset_thickening (hηp n) K ⟨h1, h2⟩
  have hS2 : ∀ n, sphere z (2 * r) ⊆ (Wn n : Set ℂ) := fun n x hx => by
    rw [mem_sphere, dist_eq_norm] at hx; exact hKW n x hx.ge (by linarith)
  have hS3 : ∀ n, sphere z (3 * r) ⊆ (Wn n : Set ℂ) := fun n x hx => by
    rw [mem_sphere, dist_eq_norm] at hx; exact hKW n x (by linarith) hx.le
  obtain ⟨Q2, hQ2S, hQ2c, hQ2d⟩ :=
    (IsSeparable.of_separableSpace (sphere z (2 * r))).exists_countable_dense_subset
  obtain ⟨Q3, hQ3S, hQ3c, hQ3d⟩ :=
    (IsSeparable.of_separableSpace (sphere z (3 * r))).exists_countable_dense_subset
  choose F hFm hF using fun n => hD.locality P (recField h ρ w) hpc (Wn n)
  set θ : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (p.c * c r * Real.exp (xiGamma γ * circleAvg (recField h ρ w ω) r z)) with hθ
  set Φ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ⨅ x ∈ Q2, ⨅ y ∈ Q3, F n (restrictTo (Wn n) (recField h ρ w ω)) x y with hΦ
  set E : ℕ → Set Ω := fun n => {ω | θ ω ≤ Φ n ω} with hE
  refine ⟨⋃ N, ⋂ n ≥ N, E n, ?_, ?_⟩
  · -- measurability with respect to `σ(recField|_{B_ε(ℂ∖U)})` for every `ε`
    have hca : Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ]
        fun ω => circleAvg (recField h ρ w ω) r z :=
      GM.measurable_circleAvg_fieldSigmaClosed (recField h ρ w) r z
        (sphere_subset_compl_confU hr p.δ z T)
    show MeasurableSet[⨅ (ε : ℝ) (_ : 0 < ε),
      fieldSigma (recField h ρ w) (nbhdO ε (confU r p.δ z T)ᶜ)] _
    refine MeasurableSpace.measurableSet_iInf.2 fun ε => MeasurableSpace.measurableSet_iInf.2
      fun hε => ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε
    have e : (⋃ N, ⋂ n ≥ N, E n) = ⋃ N, ⋂ n ≥ N + N₀, E n := by
      ext ω
      simp only [mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨N, hN⟩; exact ⟨N, fun n hn => hN n (by omega)⟩
      · rintro ⟨N, hN⟩; exact ⟨N + N₀, hN⟩
    rw [e]
    refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter
      fun hn => ?_
    have hle : fieldSigma (recField h ρ w) (Wn n) ≤
        fieldSigma (recField h ρ w) (nbhdO ε (confU r p.δ z T)ᶜ) := by
      refine GM.fieldSigma_mono _ fun x hx => ?_
      have hηn : η n ≤ ε := by
        have : η n ≤ η N₀ := by
          simp only [hη]
          gcongr
          exact_mod_cast (show N₀ ≤ n by omega)
        exact this.trans hN₀.le
      exact thickening_mono hηn _ (thickening_subset_of_subset _ hKU hx)
    have hΦm : Measurable[fieldSigma (recField h ρ w) (Wn n)] (Φ n) := by
      refine Measurable.biInf _ hQ2c fun x _ => Measurable.biInf _ hQ3c fun y _ => ?_
      exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp ((hFm n).comp
        (comap_measurable _)))
    have hθm : Measurable[fieldSigma (recField h ρ w) (nbhdO ε (confU r p.δ z T)ᶜ)] θ :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (hca.mono (iInf₂_le ε hε) le_rfl))))
    exact measurableSet_le hθm (hΦm.mono hle le_rfl)
  · -- a.s. every `E n` is condition 1
    have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E n ↔ ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))) := by
      filter_upwards [ae_all_iff.2 hF, hD.weyl P _ hpc, hD.length P _ hpc,
        CircleAvg.ae_circleAvg_addConst hh z hr] with ω hFω hw hl hca n
      set a := circleAvg (h ω) ρ w with ha
      have hcz : circleAvg (h ω) r z = circleAvg (recField h ρ w ω) r z + a := by
        rw [recField, hca]; ring
      have hk : addConst (recField h ρ w ω) a = h ω := p2_addConst_addConst_neg (h ω) a
      have hdist : ∀ x y : ℂ, ENNReal.ofReal ((D (h ω)).1 (x, y)) =
          ENNReal.ofReal (Real.exp (xiGamma γ * a)) *
            ENNReal.ofReal ((D (recField h ρ w ω)).1 (x, y)) := fun x y => by
        rw [← hk, dist_addConst_of_weyl hl hw a, ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hthr : ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) =
          ENNReal.ofReal (Real.exp (xiGamma γ * a)) * θ ω := by
        rw [hθ, ← ENNReal.ofReal_mul (Real.exp_pos _).le, scaleFac, hcz]
        congr 1; rw [mul_add, Real.exp_add]; ring
      have hE0 : ENNReal.ofReal (Real.exp (xiGamma γ * a)) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      -- `Φ n ω` is the distance across the annulus for `D_{recField}`
      have hΦω : Φ n ω = setDist (D (recField h ρ w ω)) (sphere z (2 * r)) (sphere z (3 * r)) := by
        rw [GM.setDist_spheres_eq_internal _ hl (by linarith : 2 * r < 3 * r)
          (V := (Wn n : Set ℂ)) (fun x h1 h2 => hKW n x h1 h2)]
        have e1 : Φ n ω = ⨅ x ∈ Q2, ⨅ y ∈ Q3, (D (recField h ρ w ω)).internal (Wn n) x y := by
          refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr
            fun hy => ?_
          exact (hFω n x (hS2 n (hQ2S hx)) y (hS3 n (hQ3S hy))).symm
        rw [e1]
        exact iInf₂_eq_of_dense_m10 (f := fun q => (D (recField h ρ w ω)).internal (Wn n) q.1 q.2)
          ((D _).continuousOn_internal hl (Wn n).isOpen) (hS2 n) (hS3 n) hQ2S hQ3S hQ2d hQ3d
      show θ ω ≤ Φ n ω ↔ _
      rw [hΦω, hthr, GM.setDist_eq_iInf, GM.setDist_eq_iInf]
      simp only [le_iInf₂_iff, hdist]
      exact forall₂_congr fun x _ => forall₂_congr fun y _ =>
        (ENNReal.mul_le_mul_iff_right hE0 ENNReal.ofReal_ne_top).symm
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hall] with ω hω
    simp only [mem_iUnion, mem_iInter]
    constructor
    · intro h1; exact ⟨0, fun n _ => (hω n).2 h1⟩
    · rintro ⟨N, hN⟩; exact (hω N).1 (hN N le_rfl)

end LQGMetric.CONF
