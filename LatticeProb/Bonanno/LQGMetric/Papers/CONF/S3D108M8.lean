/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M7

/-!
# CONF Lemma 3.3, Step 3: `CONFEUSContLaw` (S-cont-law for condition 2 of `E^U`, frozen)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:667–669 and C:1240–1241; the argument is
described in the docstring of S3D108M7. Steps:

1. unconditional, for `g = h − h_r(z)`: `ae_internalDiam_ne_of_normalized` at the constant level
   `(c/100) 𝔠_r`, with a test function `= 1` on `𝔸_{2r,5r}(z)` vanishing on `∂B_r(z)`;
2. constants: `recField h ρ w = g + (h_r(z) − h_ρ(w))`, and both the diameter (Axiom III) and the
   threshold `euThr` scale by `e^{ξ(h_r(z) − h_ρ(w))}`;
3. Fubini: the measurable chain version of the event has `law(v) ⊗ law(X)`-measure equal to its
   `P`-measure along `(toSig ω, X ω)` (independence), which is `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **S-cont-law for condition 2 of `E^U` under the conditional law given `h|_{ℂ∖U}`** (CONF
C:667–669, C:1240–1241) -/
theorem confEUSContLaw_of {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {p : CONFParams} (hpc : 0 < p.c) : CONFEUSContLaw γ D c p := by
  intro Ω _ P _ h hh z r hr T hT ρ w hρ hUw X G hX hGm hXG hZB k hk
  have hannO : IsOpen (annulus z (2 * r) (5 * r) : Set ℂ) := (annulus z (2 * r) (5 * r)).isOpen
  obtain ⟨A₀, -, hA₀c, hA₀⟩ := exists_countable_internalDiam_eq (confSq (p.δ * r) z k) hannO
  -- step 1: the field normalized on `∂B_r(z)`
  have hg := isWholePlaneGFF_recField hh r z
  have hn : ∀ᵐ ω ∂P, circleAvg (recField h r z ω) r z = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh z hr] with ω hω
    simp only [recField, hω, add_neg_cancel]
  have hnorm : Continuous fun x : ℂ => ‖x - z‖ := (continuous_id.sub continuous_const).norm
  have hcl : closure (annulus z (2 * r) (5 * r) : Set ℂ) ⊆ {x | 3 / 2 * r < ‖x - z‖} := by
    refine (closure_mono (fun x (hx : 2 * r < ‖x - z‖ ∧ ‖x - z‖ < 5 * r) =>
      (show x ∈ {x : ℂ | 2 * r ≤ ‖x - z‖} from hx.1.le))).trans ?_
    rw [(isClosed_le continuous_const hnorm).closure_eq]
    intro x hx
    show 3 / 2 * r < ‖x - z‖
    have : 2 * r ≤ ‖x - z‖ := hx
    linarith
  obtain ⟨φ, hφ1, hφU⟩ := exists_testC_bump (isOpen_lt continuous_const hnorm)
    (isBounded_annulus_m6 z _ _) hcl
  have hφ0 : ∀ x ∈ sphere z |r|, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxt => by
      have h1 : 3 / 2 * r < ‖x - z‖ := hφU hxt
      rw [mem_sphere, Complex.dist_eq, abs_of_pos hr] at hx
      linarith
  have hcr : 0 < c r := hD.tightness.1 r hr
  have hT0 : ENNReal.ofReal (p.c / 100 * c r) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hU0 := ae_internalDiam_ne_of_normalized hγ hD hg hr z hn hA₀c hannO φ hφ1 hφ0 hT0
    ENNReal.ofReal_ne_top
  -- step 2: back to `recField h ρ w`
  have hP1 : ∀ᵐ ω ∂P, internalDiam (D (recField h ρ w ω)) A₀ (annulus z (2 * r) (5 * r)) ≠
      euThr (xiGamma γ) c p h ρ w r z ω := by
    filter_upwards [hU0, hD.weyl P _ (GM.isGFFPlusCont_of_isWholePlaneGFF hg),
      CircleAvg.ae_circleAvg_addConst hg z hr, hn] with ω h1 hw hca hnω
    set C := circleAvg (h ω) r z - circleAvg (h ω) ρ w with hC
    have eR : recField h ρ w ω = addConst (recField h r z ω) C := by
      simp only [recField, addConst, addFun, add_assoc, ← ofCont_add_m1]
      congr 2
      ext x; simp [hC]; ring
    have hl := isLength_of_weylAt0 hw
    have e3 : D (recField h ρ w ω) =
        (D (recField h r z ω)).smulPos (Real.exp (xiGamma γ * C)) (Real.exp_pos _) := by
      apply Subtype.ext
      ext q
      show (D (recField h ρ w ω)).1 (q.1, q.2) = _
      rw [eR, dist_addConst_of_weyl hl hw C]; rfl
    have hE0 : ENNReal.ofReal (Real.exp (xiGamma γ * C)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hthr : euThr (xiGamma γ) c p h ρ w r z ω =
        ENNReal.ofReal (Real.exp (xiGamma γ * C)) * ENNReal.ofReal (p.c / 100 * c r) := by
      rw [euThr, eR, hca, hnω, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [zero_add]; congr 1; ring
    rw [e3, internalDiam_smulPos_m5, hthr]
    intro heq
    exact h1 (le_antisymm ((ENNReal.mul_le_mul_iff_right hE0 ENNReal.ofReal_ne_top).1 heq.le)
      ((ENNReal.mul_le_mul_iff_right hE0 ENNReal.ofReal_ne_top).1 heq.ge))
  -- step 3: Fubini on the frozen product law
  have hle := recSigma_le hh ρ w (confU r p.δ z T)ᶜ
  have hWm := measurable_toSig hle
  have hval : @Measurable (SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ)) Ω _
      (recSigma h ρ w (confU r p.δ z T)ᶜ) SigOmega.val := comap_measurable _
  have hG₂m : Measurable fun v : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) => G v.val :=
    hGm.comp hval
  have hca : Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ]
      fun ω => circleAvg (recField h ρ w ω) r z :=
    GM.measurable_circleAvg_fieldSigmaClosed (recField h ρ w) r z
      (sphere_subset_compl_confU hr p.δ z T)
  have hTm : Measurable fun v : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) =>
      euThr (xiGamma γ) c p h ρ w r z v.val :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (hca.comp hval))))
  have hDG : Measurable fun q : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) × DistC =>
      D (G q.1.val + q.2) := hD.measurable.comp (measurable_add_frozen hG₂m)
  set E : Set (SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) × DistC) :=
    {q | chainDiam (D (G q.1.val + q.2)) A₀ (annulus z (2 * r) (5 * r)) =
      euThr (xiGamma γ) c p h ρ w r z q.1.val} with hE
  have hEm : MeasurableSet E := by
    refine measurableSet_eq_fun ?_ (hTm.comp measurable_fst)
    exact Measurable.biSup _ hA₀c fun u _ => Measurable.biSup _ hA₀c fun v _ =>
      (ContMetric.measurable_chainInf _).comp
        (hDG.prodMk (measurable_const (a := ((u, v) : ℂ × ℂ))))
  have hrec := isWholePlaneGFF_recField hh ρ w
  have hωE : ∀ᵐ ω ∂P, (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω, X ω) ∈ Eᶜ := by
    filter_upwards [hP1, hD.weyl P _ (GM.isGFFPlusCont_of_isWholePlaneGFF hrec)] with ω h1 hw
    intro hmem
    have eGX : G ω + X ω = recField h ρ w ω := by rw [hXG ω]; abel
    apply h1
    have h2 : chainDiam (D (G ω + X ω)) A₀ (annulus z (2 * r) (5 * r)) =
        euThr (xiGamma γ) c p h ρ w r z ω := hmem
    rwa [eGX, chainDiam_eq_internalDiam (isLength_of_weylAt0 hw) _ hannO] at h2
  have hmap : P.map (fun ω => (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω, X ω)) =
      (P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hX.1.aemeasurable).1 hX.2.1
  have hQp : ∀ᵐ q ∂((P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))).prod (P.map X)),
      q ∈ Eᶜ := by
    rw [← hmap]
    exact (ae_map_iff (hWm.prodMk hX.1).aemeasurable hEm.compl).2 hωE
  have hwe₂ := ae_ae_weylAt hD hWm hX.1 hX.2.1 hG₂m (by
    have e : (fun ω => G (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω).val + X ω) =
        recField h ρ w := funext fun ω => by simp only [toSig, hXG ω, add_sub_cancel]
    rw [e]; exact hrec)
  filter_upwards [Measure.ae_ae_of_ae_prod hQp, hwe₂] with v hv1 hv2
  filter_upwards [hv1, hv2] with x hx1 hx2
  have hl := isLength_of_weylAt0 hx2
  rw [hA₀ _ hl, ← chainDiam_eq_internalDiam hl _ hannO]
  exact hx1

end LQGMetric.CONF
