/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_21Proof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.21, step 1: locality of `D_h(B_ρ(z), ∂B_{2ρ}(z))`

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.21,
T:2345–2357: "The proof is similar to that of Lemma 3.19" — the first step of that proof
(T:2275–2281) is the independence of the coarse increment `h_{ρ'}(z) − h_𝕣(z)` from the
locally determined quantity, normalized by `e^{−ξ h_{ρ'}(z)}` (Axioms II and III).

* `setDistIn_le_setDist`: for a length metric, the distance from `A ⊆ B_ρ(z)` to `∂B_ρ(z)` equals
  the one computed with the internal metric of any `V ⊇ B̄_ρ(z)`: a near-geodesic stays in
  `B̄_ρ(z)` until its first hit of `∂B_ρ(z)` (the first-hit argument of
  `GM.setDist_spheres_eq_internal`, own elementary argument).
* `setDistIn_eq_iInf_dense`: `setDistIn` is a countable infimum (as `L32M.setDist_eq_iInf_dense`).
* `indepFun_setDistIn`: `indepFun_internalDiamU` for `setDistIn`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry GM

namespace L321

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- a near-geodesic from `A ⊆ B_ρ(z)` to `∂B_ρ(z)` stays in `B̄_ρ(z)` until its first hit of
`∂B_ρ(z)` (as in `GM.setDist_spheres_eq_internal`) -/
theorem setDistIn_le_setDist (D : ContMetric) (hD : D.IsLength) {V A : Set ℂ} {z : ℂ} {ρ : ℝ}
    (hA : A ⊆ ball z ρ) (hsub : ∀ w : ℂ, ‖w - z‖ ≤ ρ → w ∈ V) :
    setDistIn D A (sphere z ρ) V ≤ setDist D A (sphere z ρ) := by
  rw [GM.setDist_eq_iInf]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hab, hPc, hPa, hPb, hlen⟩ :=
    isLengthSpace_iff_curves.1 hD (D.pt x) (D.pt y) ε (by exact_mod_cast hε)
  set f : ℝ → ℝ := fun t => ‖D.unpt (P t) - z‖ with hf
  have hfc : ContinuousOn f (Icc a b) :=
    (continuous_norm.comp (D.continuous_unpt.sub continuous_const)).comp_continuousOn hPc
  have hfa : f a < ρ := by simp only [hf, hPa]; exact mem_ball_iff_norm.1 (hA hx)
  have hfb : f b = ρ := by simp only [hf, hPb]; exact mem_sphere_iff_norm.1 hy
  obtain ⟨t₂, ht₂, hft₂, hbef⟩ := exists_first_hit (P := f) hfc (isClosed_Ici (a := ρ))
    ⟨b, ⟨hab, le_rfl⟩, by rw [hfb]; exact mem_Ici.2 le_rfl⟩
  have hft₂' : ρ ≤ f t₂ := hft₂
  have hat₂ : a < t₂ := by
    rcases ht₂.1.eq_or_lt with h | h
    · rw [← h] at hft₂'; linarith
    · exact h
  have hf2 : f t₂ = ρ := by
    refine le_antisymm ?_ hft₂'
    have hne : (𝓝[Ico a t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot hat₂
    have hcw : ContinuousWithinAt f (Ico a t₂) t₂ :=
      (hfc t₂ ht₂).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₂.2))
    exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht =>
      (not_le.1 fun h => hbef t ht (mem_Ici.2 h)).le)
  have hsub2 : Icc a t₂ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₂.2
  have hmaps : MapsTo P (Icc a t₂) (D.pt '' V) := fun t ht => by
    refine ⟨D.unpt (P t), hsub _ ?_, rfl⟩
    rcases ht.2.eq_or_lt with h | h
    · rw [h]; exact hf2.le
    · exact (not_le.1 fun hc => hbef t ⟨ht.1, h⟩ (mem_Ici.2 hc)).le
  have hy' : D.unpt (P t₂) ∈ sphere z ρ := mem_sphere_iff_norm.2 hf2
  have hx' : D.unpt (P a) = x := by rw [hPa]; rfl
  calc setDistIn D A (sphere z ρ) V ≤ D.internal V (D.unpt (P a)) (D.unpt (P t₂)) := by
        unfold setDistIn
        exact iInf₂_le_of_le _ (hx' ▸ hx) (iInf₂_le _ hy')
    _ ≤ curveLength P a t₂ := internalEDist_le_curveLength hat₂.le (hPc.mono hsub2) hmaps
    _ ≤ curveLength P a b := eVariationOn.mono _ hsub2
    _ ≤ edist (D.pt x) (D.pt y) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (D.1 (x, y)) + ε := by
        rw [ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal]

theorem setDist_eq_setDistIn (D : ContMetric) (hD : D.IsLength) {V A : Set ℂ} {z : ℂ} {ρ : ℝ}
    (hA : A ⊆ ball z ρ) (hsub : ∀ w : ℂ, ‖w - z‖ ≤ ρ → w ∈ V) :
    setDist D A (sphere z ρ) = setDistIn D A (sphere z ρ) V := by
  refine le_antisymm ?_ (setDistIn_le_setDist D hD hA hsub)
  rw [GM.setDist_eq_iInf]
  unfold setDistIn
  refine iInf₂_mono fun x _ => iInf₂_mono fun y _ => ?_
  rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _

/-- `setDistIn` is a countable infimum over dense sequences (length metrics) -/
lemma setDistIn_eq_iInf_dense (d : ContMetric) (hd : d.IsLength) {V A B : Set ℂ} (hV : IsOpen V)
    (hAV : A ⊆ V) (hBV : B ⊆ V) {a b : ℕ → ℂ} (haA : ∀ n, a n ∈ A) (hbB : ∀ n, b n ∈ B)
    (hA : A ⊆ closure (range a)) (hB : B ⊆ closure (range b)) :
    setDistIn d A B V = ⨅ p : ℕ × ℕ, d.internal V (a p.1) (b p.2) := by
  unfold setDistIn
  refine le_antisymm (le_iInf fun p => iInf₂_le_of_le (a p.1) (haA p.1)
    (iInf₂_le_of_le (b p.2) (hbB p.2) le_rfl)) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  exact L32M.mem_of_dense (f := fun p : ℂ × ℂ => d.internal V p.1 p.2)
    (d.continuousOn_internal hd hV) (fun n => hAV (haA n)) (fun n => hBV (hbB n)) hA hB
    isClosed_Ici (fun i j => iInf_le (fun p : ℕ × ℕ => d.internal V (a p.1) (b p.2)) (i, j))
    hx hy (hAV hx) (hBV hy)

lemma setDistIn_of_scale {D₁ D₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (A B V : Set ℂ) :
    setDistIn D₂ A B V = ENNReal.ofReal e * setDistIn D₁ A B V := by
  have h0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  simp only [setDistIn, GM.internal_of_scale he h]
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]

/-- **T:2275–2281** for `setDistIn` in an open set `U ⊆ B̄_ρ(z)`. -/
theorem indepFun_setDistIn (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (U : Opens ℂ) (hU : (U : Set ℂ) ⊆ closedBall z ρ)
    {A B : Set ℂ} (hA : A ⊆ U) (hB : B ⊆ U) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧
      IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P ∧
      ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ * circleAvg (h ω) ρ z))) *
        setDistIn (D (h ω)) A B U := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) ρ z) with hg_def
  have hm : Measurable fun ω => -circleAvg (h ω) ρ z :=
    ((measurable_circleAvg_left ρ z).comp hh.measurable).neg
  have hg : IsWholePlaneGFF g P := hh.addConst hm
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g (GM.Tight.isGFFPlusCont_of_wp hg) U
  obtain ⟨a, haA, haD⟩ := L32M.exists_denseSeq hAne
  obtain ⟨b, hbB, hbD⟩ := L32M.exists_denseSeq hBne
  set G : DistOn U → ℝ≥0∞ := fun T => ⨅ p : ℕ × ℕ, Φ T (a p.1) (b p.2)
  have hG : Measurable G := Measurable.iInf fun p =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
  have hR : Measurable fun ω => restrictTo U (g ω) := (measurable_restrictTo U).comp hg.measurable
  refine ⟨fun ω => G (restrictTo U (g ω)), hG.comp hR, ?_, ?_⟩
  · have hI := CircleAvgIndep.indepFun_circleAvg_restrict hh z hρ hρr U hU
    exact hI.comp measurable_id hG
  · filter_upwards [hΦae, hD.length P g (GM.Tight.isGFFPlusCont_of_wp hg),
      hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh)] with ω h1 hl hsc
    have e1 : G (restrictTo U (g ω)) = setDistIn (D (g ω)) A B U := by
      rw [setDistIn_eq_iInf_dense (D (g ω)) hl U.isOpen hA hB haA hbB haD hbD]
      exact iInf_congr fun p => (h1 _ (hA (haA _)) _ (hB (hbB _))).symm
    rw [e1]
    rw [show -(xiGamma γ * circleAvg (h ω) ρ z) = xiGamma γ * (-circleAvg (h ω) ρ z) by ring]
    exact setDistIn_of_scale (Real.exp_pos _) (hsc (-circleAvg (h ω) ρ z)) _ _ _

end L321
end LQGMetric.DFGPS
