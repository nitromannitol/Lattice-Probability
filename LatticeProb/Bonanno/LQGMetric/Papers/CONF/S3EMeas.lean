/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3EMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jEDet
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L34

/-!
# CONF C:1150–1154, 1270: `E_r(z)` is determined by `(h − h_r(z))` on an annulus

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), `literature/src/1905.00381/confluence-final.tex`, C:1150–1154: "The occurrence
of `E^U_r(z)` or `E_r(z)` is unaffected by adding a constant to the field. By this and the locality
of `D_h` (Axiom II), these events are determined by `h|_{𝔸_{2r,5r}(z)}`, viewed modulo additive
constant", used at C:1270 as "each `E_r(z)` is determined by `(h − h_r(z))|_{𝔸_{2r,5r}(z)}`".

`confE_aeEventIn_norm`: `E_r(z)` is a.s. an event of `σ(g|_W)`, `g = h − h_r(z)`,
`W = 𝔸_{3r/2,5r}(z)`, given the locality of the harmonic part for the normalized field
(`CONFHarmLocN`, open). Conditions 1 and 2 are proved as in `GM.p412j_cond1`, `GM.p412j_cond2_sq`
(Axiom II for `g`, dense sequences), with Weyl scaling by the constant `h_r(z)`
(`IsWeakLQGMetric.ae_dist_addConst`): `D_h = e^{ξh_r(z)} D_g`, `𝔠_r e^{ξh_r(z)}` is the threshold.

Departure (proposed DV-CONF-EMeas): the annulus is `𝔸_{3r/2,5r}(z)` instead of `𝔸_{2r,5r}(z)`,
because `∂B_{2r}(z)` (condition 1) is not inside the open annulus `𝔸_{2r,5r}(z)` (same as
`DFGPS.aeEventIn_annEvent`). CONF L2.12 is then applied with `S₁ = 3/2` instead of `2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM

/-- **Locality of the harmonic part, normalized form** (CONF C:1150, condition 3; open): for an
open bounded `U` with `cl U ⊆ W` and `u ∈ U`, `𝔥^U(u) − h_ρ(w)` is a.s. a measurable function of
`(h − h_ρ(w))|_W`. (Compare `GM.P412jHarmLoc`, where the circle `∂B_ρ(w)` lies in `W` and the
σ-algebra is `σ(h|_W)`.) -/
def CONFHarmLocN : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (U : Set ℂ) (W : Opens ℂ), IsOpen U → Bornology.IsBounded U →
    closure U ⊆ W → ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → ∀ u ∈ U, ∃ G : Ω → ℝ,
      Measurable[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w)) W] G ∧
      (fun ω => harmPart P h U ω u - circleAvg (h ω) ρ w) =ᵐ[P] G

section Conditions
variable {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
  (hD : IsWeakLQGMetric γ D c₀) (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
  (hh : IsWholePlaneGFF h P) (cc : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ)
include hD hh hr

/-- `D_h = e^{ξ h_r(z)} D_{h − h_r(z)}` a.s. -/
theorem ae_dist_norm :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = Real.exp (xiGamma γ * circleAvg (h ω) r z) *
      (D (addConst (h ω) (-circleAvg (h ω) r z))).1 (u, v) := by
  have hm : Measurable fun ω => -circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.measurable).neg
  have hg := Tight.isGFFPlusCont_of_wp (hh.addConst hm)
  filter_upwards [hD.ae_dist_addConst hg] with ω hω u v
  have e : addConst (addConst (h ω) (-circleAvg (h ω) r z)) (circleAvg (h ω) r z) = h ω := by
    rw [GFFLaw.addConst_addConst, neg_add_cancel]
    exact DFunLike.ext _ _ fun φ => by simp [GFFInv.addConst_apply]
  have := hω (circleAvg (h ω) r z) u v
  rwa [e] at this

/-- condition 1 of `E^U_r(z)` (C:1134), normalized -/
theorem cond1_norm (c : ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
      (annulus z (3 / 2 * r) (5 * r))) {ω | ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z) with hg_def
  set W := annulus z (3 / 2 * r) (5 * r) with hW
  have hm : Measurable fun ω => -circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.measurable).neg
  have hgp := Tight.isGFFPlusCont_of_wp (hh.addConst hm)
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g hgp W
  obtain ⟨a, haS, haD⟩ := DFGPS.L32M.exists_denseSeq (S := sphere z (2 * r))
    (NormedSpace.sphere_nonempty.2 (by linarith))
  obtain ⟨b, hbS, hbD⟩ := DFGPS.L32M.exists_denseSeq (S := sphere z (3 * r))
    (NormedSpace.sphere_nonempty.2 (by linarith))
  have hsub : ∀ w : ℂ, 2 * r ≤ ‖w - z‖ → ‖w - z‖ ≤ 3 * r → w ∈ (W : Set ℂ) := fun w h1 h2 =>
    show 3 / 2 * r < ‖w - z‖ ∧ ‖w - z‖ < 5 * r from ⟨by linarith, by linarith⟩
  have hS2 : ∀ n, a n ∈ (W : Set ℂ) := fun n => hsub _ (mem_sphere_iff_norm.1 (haS n)).ge
    (by rw [mem_sphere_iff_norm.1 (haS n)]; linarith)
  have hS3 : ∀ n, b n ∈ (W : Set ℂ) := fun n => hsub _
    (by rw [mem_sphere_iff_norm.1 (hbS n)]; linarith) (mem_sphere_iff_norm.1 (hbS n)).le
  set V : Ω → (ℕ × ℕ → ℝ≥0∞) := fun ω q => Φ (restrictTo W (g ω)) (a q.1) (b q.2)
  have hV : Measurable[fieldSigma g W] V := by
    have hG : Measurable fun x : DistOn W => fun q : ℕ × ℕ => Φ x (a q.1) (b q.2) :=
      measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
    exact hG.comp (Measurable.of_comap_le le_rfl)
  set S : Set (ℕ × ℕ → ℝ≥0∞) := {x | ENNReal.ofReal (c * cc r) ≤ ⨅ q, x q}
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const (Measurable.iInf fun q => measurable_pi_apply q)
  refine ⟨V ⁻¹' S, hV hSm, ?_⟩
  filter_upwards [hΦae, hD.length P g hgp, ae_dist_norm hD P h hh hr z] with ω h1 hl hsc
  have he := Real.exp_pos (xiGamma γ * circleAvg (h ω) r z)
  have e : setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r)) =
      ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
        ⨅ q : ℕ × ℕ, Φ (restrictTo W (g ω)) (a q.1) (b q.2) := by
    rw [GM.setDist_of_scale he hsc,
      DFGPS.L32M.setDist_eq_iInf_dense (D (g ω)) hl W.isOpen (by linarith) hsub haS hbS haD hbD]
    congr 1
    exact iInf_congr fun q => h1 _ (hS2 _) _ (hS3 _)
  have hl' : ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z) =
      ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) * ENNReal.ofReal (c * cc r) := by
    rw [← ENNReal.ofReal_mul he.le, scaleFac]; congr 1; ring
  change (ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z) ≤
    setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))) = (V ω ∈ S)
  rw [e, hl', ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top]
  rfl

/-- condition 2 of `E^U_r(z)` (C:1135–1137), one square, normalized -/
theorem cond2_sq_norm (c δ : ℝ) (k : ℤ × ℤ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
      (annulus z (3 / 2 * r) (5 * r))) {ω |
      internalDiam (D (h ω)) (confSq (δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
        ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z)} := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) r z) with hg_def
  set Q := confSq (δ * r) z k
  set A := annulus z (2 * r) (5 * r)
  by_cases hQ : Q.Nonempty ∧ Q ⊆ (A : Set ℂ)
  · have hm : Measurable fun ω => -circleAvg (h ω) r z :=
      ((measurable_circleAvg_left r z).comp hh.measurable).neg
    have hgp := Tight.isGFFPlusCont_of_wp (hh.addConst hm)
    have hAW : A ≤ annulus z (3 / 2 * r) (5 * r) := fun w hw =>
      show 3 / 2 * r < ‖w - z‖ ∧ ‖w - z‖ < 5 * r from ⟨by linarith [hw.1], hw.2⟩
    obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g hgp A
    obtain ⟨a, haS, haD⟩ := DFGPS.L32M.exists_denseSeq hQ.1
    set V : Ω → (ℕ × ℕ → ℝ≥0∞) := fun ω q => Φ (restrictTo A (g ω)) (a q.1) (a q.2)
    have hV : Measurable[fieldSigma g (annulus z (3 / 2 * r) (5 * r))] V := by
      have hG : Measurable fun x : DistOn A => fun q : ℕ × ℕ => Φ x (a q.1) (a q.2) :=
        measurable_pi_iff.2 fun q =>
          (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
      exact (hG.comp (Measurable.of_comap_le le_rfl)).mono (fieldSigma_mono g hAW) le_rfl
    set S : Set (ℕ × ℕ → ℝ≥0∞) := {x | ⨆ q, x q ≤ ENNReal.ofReal (c * cc r)}
    have hSm : MeasurableSet S :=
      measurableSet_le (Measurable.iSup fun q => measurable_pi_apply q) measurable_const
    refine ⟨V ⁻¹' S, hV hSm, ?_⟩
    filter_upwards [hΦae, hD.length P g hgp, ae_dist_norm hD P h hh hr z] with ω h1 hl hsc
    have he := Real.exp_pos (xiGamma γ * circleAvg (h ω) r z)
    have e : internalDiam (D (h ω)) Q A =
        ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
          ⨆ q : ℕ × ℕ, Φ (restrictTo A (g ω)) (a q.1) (a q.2) := by
      rw [DFGPS.L32M.internalDiam_of_scale he hsc,
        DFGPS.L32M.internalDiam_eq_iSup (D (g ω)) hl A.isOpen hQ.2 haS haD]
      congr 1
      exact iSup_congr fun q => h1 _ (hQ.2 (haS _)) _ (hQ.2 (haS _))
    have hl' : ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z) =
        ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
          ENNReal.ofReal (c * cc r) := by
      rw [← ENNReal.ofReal_mul he.le, scaleFac]; congr 1; ring
    change (internalDiam (D (h ω)) Q A ≤ ENNReal.ofReal (c * scaleFac (xiGamma γ) cc (h ω) r z)) =
      (V ω ∈ S)
    rw [e, hl', ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top]
    rfl
  · rcases not_and_or.1 hQ with hQ | hQ
    · have : ∀ ω, internalDiam (D (h ω)) Q A = 0 := fun ω => by
        rw [not_nonempty_iff_eq_empty.1 hQ]; simp [internalDiam]
      simp only [this, zero_le]
      exact p412j_aeEventIn_const True
    · obtain ⟨u, huQ, huA⟩ := not_subset.1 hQ
      have htop : ∀ ω, internalDiam (D (h ω)) Q A = ⊤ := fun ω => by
        refine top_le_iff.1 (le_trans ?_ (le_iSup₂_of_le u huQ (le_iSup₂ (f := fun v _ =>
          (D (h ω)).internal A u v) u huQ)))
        unfold ContMetric.internal MetricGeometry.internalEDist
        have : IsEmpty {γ' : Path ((D (h ω)).pt u) ((D (h ω)).pt u) //
            ∀ t, γ' t ∈ (D (h ω)).pt '' (A : Set ℂ)} := ⟨fun γ' => huA (by
          obtain ⟨w, hw, hwu⟩ := γ'.2 0
          rw [Path.source] at hwu
          exact (show w = u from hwu) ▸ hw)⟩
        rw [iInf_of_empty]
      simp only [htop, top_le_iff, ENNReal.ofReal_ne_top]
      exact p412j_aeEventIn_const False

end Conditions

/-- condition 3 of `E^U_r(z)` (C:1138–1141), normalized, from `CONFHarmLocN` (template
`GM.p412j_cond3`) -/
theorem cond3_norm (hHL : CONFHarmLocN) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {U : Set ℂ}
    (W : Opens ℂ) (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUW : closure U ⊆ W)
    {ρ : ℝ} {w : ℂ} (hρ : 0 < ρ) (ε A : ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w)) W)
      {ω | ∀ u ∈ innerPart U ε, |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} := by
  by_cases hne : (innerPart U ε).Nonempty
  swap
  · have e : {ω | ∀ u ∈ innerPart U ε, |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} =
        {_ω | True} := by
      ext ω
      simp only [not_nonempty_iff_eq_empty.1 hne, mem_empty_iff_false, IsEmpty.forall_iff,
        forall_const, mem_ofPred_eq, implies_true]
    rw [e]; exact p412j_aeEventIn_const True
  obtain ⟨q, hqS, hqD⟩ := DFGPS.L32M.exists_denseSeq hne
  have hq : ∀ n, q n ∈ U := fun n => (hqS n).1
  choose G hG hGe using fun n => hHL P h hh U W hUo hUb hUW ρ w hρ (q n) (hq n)
  have key : {ω | ∀ u ∈ innerPart U ε, |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} =
      ⋂ n, {ω | |harmPart P h U ω (q n) - circleAvg (h ω) ρ w| ≤ A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    refine ⟨fun H n => H _ (hqS n), fun H u hu => ?_⟩
    by_contra hlt
    have hc : ContinuousAt (fun v => |harmPart P h U ω v - circleAvg (h ω) ρ w|) u :=
      ((p412j_harmPart_contAt P h U ω hu.1).sub continuousAt_const).abs
    have hnb := hc.preimage_mem_nhds (Ioi_mem_nhds (not_le.1 hlt))
    obtain ⟨_, hv, n, rfl⟩ := mem_closure_iff_nhds.1 (hqD hu) _ hnb
    exact absurd (H n) (not_le.2 hv)
  rw [key]
  refine gm_aeEventIn_iInter fun n => ⟨(fun ω => |G n ω|) ⁻¹' Iic A,
    (continuous_abs.measurable.comp (hG n)) measurableSet_Iic, ?_⟩
  filter_upwards [hGe n] with ω hω
  have hω' : harmPart P h U ω (q n) - circleAvg (h ω) ρ w = G n ω := hω
  change (|harmPart P h U ω (q n) - circleAvg (h ω) ρ w| ≤ A) = (|G n ω| ≤ A)
  rw [hω']

/-- **CONF C:1150, 1270**: `E_r(z)` is a.s. an event of `σ((h − h_r(z))|_{𝔸_{3r/2,5r}(z)})`, given
`CONFHarmLocN`. -/
theorem confEMeas_of (hHL : CONFHarmLocN) {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) : CONFEMeas γ D c := by
  intro p _ Ω _ P _ h hh z r hr
  set W := annulus z (3 / 2 * r) (5 * r)
  have hUW : ∀ T : Finset (ℤ × ℤ), closure (confU r p.δ z T) ⊆ (W : Set ℂ) := by
    intro T
    have hcl : IsClosed {w : ℂ | 3 * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 4 * r} :=
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
    refine (closure_minimal (fun w hw => ?_) hcl).trans (fun w hw => ?_)
    · have := hw.1; exact ⟨this.1.le, this.2.le⟩
    · show 3 / 2 * r < ‖w - z‖ ∧ ‖w - z‖ < 5 * r
      exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hEU : ∀ T : Finset (ℤ × ℤ), AEEventIn P (fieldSigma (fun ω => addConst (h ω)
      (-circleAvg (h ω) r z)) W) (confEU (xiGamma γ) c D P h p r z T) := by
    intro T
    have e : confEU (xiGamma γ) c D P h p r z T =
        {ω | ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
          setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} ∩
        ((⋂ k : confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)), {ω |
          internalDiam (D (h ω)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
            ENNReal.ofReal (p.c / 100 * scaleFac (xiGamma γ) c (h ω) r z)}) ∩
        {ω | ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
          |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A}) := by
      ext ω
      simp only [confEU, mem_ofPred_eq, mem_inter_iff, mem_iInter, Subtype.forall]
    rw [e]
    exact p412j_aeEventIn_inter (cond1_norm hD P h hh c hr z p.c)
      (p412j_aeEventIn_inter (gm_aeEventIn_iInter fun k =>
        cond2_sq_norm hD P h hh c hr z (p.c / 100) p.δ k)
      (cond3_norm hHL P h hh W (p412j_isOpen_confU r p.δ z T)
        (isBounded_closedBall.subset (p412j_confU_subset r p.δ z T)) (hUW T) hr _ _))
  have e : confE (xiGamma γ) c D P h p r z = ⋂ T : {T : Finset (ℤ × ℤ) //
      ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))},
      confEU (xiGamma γ) c D P h p r z T.1 := by
    ext ω
    simp only [confE, mem_iInter, Subtype.forall]
  obtain ⟨F, hF, hEF⟩ := gm_aeEventIn_iInter fun T : {T : Finset (ℤ × ℤ) //
      ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))} => hEU T.1
  exact ⟨F, hF, by rw [e]; exact hEF.symm⟩

end LQGMetric.CONF
