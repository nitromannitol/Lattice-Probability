/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma38Inputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma38

/-!
# GMS [18] Lemma 3.8 from the inputs of Proposition 2.10 and Lemma 2.7

Source: GMS [18] Lemma 3.8, with the square-based correction. This file discharges the two deterministic
quantities of `lemma38_core` from the probabilistic inputs:

* Step 1 ([18] (3.24)): `Energy(f^ε; G(V(A))) ≤ lemma34Bound ι r δ w A η` on `A = {ι < |u − z| < r}`
  (`energy_logRadAnnulus_le`; Lemma 3.3 with the logarithmic function, Proposition 2.10 for
  `(A, |∇f|²)`, `(A, 1)`, `(B_{R₁}(z), g)`);
* (3.19): `∑_{V(D')} diam² deg ≤ lemma38K ι w A η` on `D' = {ι/2 < |u − z| < 9ι}` (`cellSum_D'_le`;
  Lemma 3.1 with `f = 1`, Proposition 2.10 for `(D', 1)` and `(B_r(z), g')`);
* `lemma38` (**[18] Lemma 3.8 with squares**, deterministic single-scale form): under CAL, the event of
  Lemma 2.7 and the five Proposition 2.10 inputs, for every `κ > 0` and every vertex `x` whose cell meets
  `B_{5ι}(z)` ([18] has `B_{4sr}`; `5ι` also covers its grid step `[s, 4s] ⊂ [s', 5s']`),
  `P_x[X hits V(∂B_ι(z)) before V(∂B_r(z))] ≥ 1 − (6 √K √E / ι + 2κ)` with
  `E = lemma34Bound ι r δ w A η`, `K = lemma38K ι w A η`. For `ι = sr`, `δ = ε^q`, `w = ε^{β'}`, `η = ε^α`
  the right side is `1 − O(A/√log(1/s)) − O(ε^{positive})`, the form (3.23) of [18].
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic HarmonicInfinity Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- The boundary layer of the annulus between the radii `a` and `b` about `z`, at width `w`. -/
def annLayer (z : ℂ) (a b w : ℝ) (u : ℂ) : ℝ := max (radialBump z a w u) (radialBump z b w u)

theorem lintegral_annLayer_le (z : ℂ) {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 < w) :
    ∫⁻ u, ENNReal.ofReal (annLayer z a b w u) ≤
      ENNReal.ofReal (8 * π * w * (a + 2 * w) + 8 * π * w * (b + 2 * w)) := by
  calc ∫⁻ u, ENNReal.ofReal (annLayer z a b w u)
      ≤ ∫⁻ u, (ENNReal.ofReal (radialBump z a w u) + ENNReal.ofReal (radialBump z b w u)) := by
        refine lintegral_mono fun u => ?_
        unfold annLayer
        rcases le_total (radialBump z a w u) (radialBump z b w u) with h | h
        · rw [max_eq_right h]; exact le_add_self
        · rw [max_eq_left h]; exact le_self_add
    _ = (∫⁻ u, ENNReal.ofReal (radialBump z a w u)) + ∫⁻ u, ENNReal.ofReal (radialBump z b w u) :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp
          (continuous_radialBump z a hw).measurable) _
    _ ≤ ENNReal.ofReal (8 * π * w * (a + 2 * w)) + ENNReal.ofReal (8 * π * w * (b + 2 * w)) :=
        add_le_add (lintegral_radialBump_le z ha hw) (lintegral_radialBump_le z hb hw)
    _ = ENNReal.ofReal (8 * π * w * (a + 2 * w) + 8 * π * w * (b + 2 * w)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- Boundary cells of the annulus `{a < |u − z| < b}` lie in the layer `{annLayer ≥ 1}` and in
`B_{b + δ}(z)`. -/
theorem boundary_cell_annLayer {z : ℂ} {a b δ w : ℝ} (hw : 0 < w) (hδw : δ ≤ w) {x : V}
    (hdx : cellDiam H x ≤ δ) (hfr : (H.cell x ∩ frontier (annulusSet z a b)).Nonempty)
    (hab : a ≤ b) :
    (∀ u ∈ H.cell x, ‖u - z‖ ≤ b + δ) ∧ ∀ u ∈ H.cell x, 1 ≤ annLayer z a b w u := by
  obtain ⟨c, hcx, hcfr⟩ := hfr
  have hc := frontier_annulusSet_subset z a b hcfr
  have hdiam : diam (H.cell x) ≤ δ := hdx
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hd := (dist_le_cellDiam H hu hcx).trans hdx
    rw [dist_eq_norm] at hd
    have : ‖u - z‖ - ‖c - z‖ ≤ ‖u - c‖ := by
      have := norm_sub_norm_le (u - z) (c - z)
      rwa [sub_sub_sub_cancel_right] at this
    have hc' : ‖c - z‖ ≤ b := by
      rcases hc with h | h
      · have h' : ‖c - z‖ = a := h
        linarith
      · have h' : ‖c - z‖ = b := h
        linarith
    linarith
  · unfold annLayer
    rcases hc with h | h
    · have := abs_norm_sub_le_of_diam (H.isCompact_cell x).isBounded hdiam hcx h hu
      rw [radialBump_eq_one hw (this.trans hδw)]
      exact le_max_left _ _
    · have := abs_norm_sub_le_of_diam (H.isCompact_cell x).isBounded hdiam hcx h hu
      rw [radialBump_eq_one hw (this.trans hδw)]
      exact le_max_right _ _

/-- **Step 1 of [18] Lemma 3.8** ((3.24)): Lemma 3.3 for the logarithmic function of the annulus
`A = {ι < |u − z| < r}` (`0` inside, `1` outside), from the Lemma 2.7 bound and three Proposition 2.10
inputs. -/
theorem energy_logRadAnnulus_le {z : ℂ} {ι r R₁ δ w A η : ℝ} (hι : 0 < ι) (hιr : ι < r)
    (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ ι) (hR₁ : r + δ < R₁) (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A)
    (hη : 0 ≤ η) (hdiam : ∀ x ∈ vFin H (annulusSet z ι r), cellDiam H x ≤ δ)
    (hF : Prop210Bound H (annulusSet z ι r) (fun u => ‖fderiv ℝ (logRad z ι r) u‖ ^ 2) A η)
    (h1 : Prop210Bound H (annulusSet z ι r) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball z R₁) (annLayer z ι r w) A η) :
    energy G (vFin H (annulusSet z ι r)) (logRad z ι r ∘ annRef H z ι r) ≤
      lemma34Bound ι r δ w A η := by
  have hr : 0 < r := hι.trans hιr
  set D := annulusSet z ι r with hDdef
  have hDb := isBounded_annulusSet z ι r
  have hDo := isOpen_annulusSet z ι r
  set ℓ := Real.log (r / ι) with hℓ
  have hℓpos : 0 < ℓ := Real.log_pos ((one_lt_div hι).mpr hιr)
  have habs : |Real.log (r / ι)| = ℓ := abs_of_pos hℓpos
  have hpfar : ∀ x ∈ vFin H D, ι - δ < ‖annRef H z ι r x - z‖ := by
    intro x hx
    obtain ⟨u, hu, huD⟩ := (mem_vFin H hDb).mp hx
    have hd := (dist_le_cellDiam H hu (annRef_mem H z ι r x)).trans (hdiam x hx)
    rw [dist_eq_norm] at hd
    have h1 : ‖u - z‖ - ‖annRef H z ι r x - z‖ ≤ ‖u - annRef H z ι r x‖ := by
      have := norm_sub_norm_le (u - z) (annRef H z ι r x - z)
      rwa [sub_sub_sub_cancel_right] at this
    linarith [huD.1]
  set O : Set ℂ := {u | ι / 2 < ‖u - z‖} with hOdef
  have hO : IsOpen O := isOpen_norm_sub_gt z (ι / 2)
  have hdf : DifferentiableOn ℝ (logRad z ι r) O := differentiableOn_logRad z ι r (by positivity)
  set Λ := (ℓ * (ι / 2) ^ 2)⁻¹ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ (logRad z ι r) u - fderiv ℝ (logRad z ι r) v‖ ≤
      Λ * ‖u - v‖ := by
    intro u hu v hv
    have := norm_fderiv_logRad_sub_le (z := z) (a := ι) (b := r) (c := ι / 2) (by positivity)
      (le_of_lt hu) (le_of_lt hv)
    rwa [habs] at this
  have hseg : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y →
      segment ℝ (annRef H z ι r x) (annRef H z ι r y) ⊆ O := by
    intro x hx y hy hadj u hu
    have h1 := norm_sub_le_of_mem_segment hu
    have h2 : ‖annRef H z ι r y - annRef H z ι r x‖ ≤ 2 * δ := by
      rw [← dist_eq_norm, dist_comm]
      refine (dist_le_cellDiam_add_of_adj H hadj (annRef_mem H z ι r x)
        (annRef_mem H z ι r y)).trans ?_
      linarith [hdiam x hx, hdiam y hy]
    have h3 : ‖annRef H z ι r x - z‖ - ‖u - z‖ ≤ ‖u - annRef H z ι r x‖ := by
      have := norm_sub_norm_le (annRef H z ι r x - z) (u - z)
      rwa [sub_sub_sub_cancel_right, norm_sub_rev (annRef H z ι r x) u] at this
    show ι / 2 < ‖u - z‖
    linarith [hpfar x hx]
  set LF := 2 * (ℓ ^ 2 * ι ^ 3)⁻¹ with hLFdef
  have hLF0 : 0 ≤ LF := by positivity
  have hLipF : ∀ u ∈ D, ∀ v ∈ D, ‖fderiv ℝ (logRad z ι r) u‖ ^ 2 ≤
      ‖fderiv ℝ (logRad z ι r) v‖ ^ 2 + LF * dist u v := fun u hu v hv =>
    sqGrad_le_add (z := z) (a := ι) (b := r) (c := ι) hι hu.1.le hv.1.le
  set MF := (ℓ ^ 2 * (ι / 2) ^ 2)⁻¹ with hMFdef
  have hMF : ∀ x ∈ vFin H D, ‖fderiv ℝ (logRad z ι r) (annRef H z ι r x)‖ ^ 2 ≤ MF := fun x hx =>
    sqGrad_le (z := z) (a := ι) (b := r) (c := ι / 2) (by positivity) (by linarith [hpfar x hx])
  have hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ ball z R₁ ∧ ∀ u ∈ H.cell x, 1 ≤ annLayer z ι r w u := by
    intro x hx hfr
    obtain ⟨h1, h2⟩ := boundary_cell_annLayer H hw hδw (hdiam x hx) hfr hιr.le
    refine ⟨fun u hu => ?_, h2⟩
    rw [mem_ball, dist_eq_norm]
    linarith [h1 u hu]
  have h33 := lemma33 H hDo hDb hO hdf hΛ0 hLip (annRef H z ι r) (annRef_mem H z ι r) hseg hLF0
    hLipF hMF hdiam hbd hF h1 hg
  have hE : eucEnergy (logRad z ι r) D = ENNReal.ofReal (2 * π / ℓ) :=
    (eucEnergy_logRad_annulus (z := z) hι hιr).1
  have hvol : volume D ≤ ENNReal.ofReal (π * r ^ 2) := volume_annulusSet_le z ι r
  have hgint : (∫⁻ u in ball z R₁, ENNReal.ofReal (annLayer z ι r w u)) ≤
      ENNReal.ofReal (8 * π * w * (ι + 2 * w) + 8 * π * w * (r + 2 * w)) :=
    (setLIntegral_le_lintegral _ _).trans (lintegral_annLayer_le z hι.le hr.le hw)
  rw [← ENNReal.ofReal_le_ofReal_iff (lemma34Bound_nonneg hι hιr hδ0 hw.le hA hη)]
  refine h33.trans ?_
  rw [hE]
  unfold lemma34Bound
  have hℓpos' : 0 < Real.log (r / ι) := hℓpos
  have hP : ENNReal.ofReal A * ENNReal.ofReal (2 * π / ℓ) + ENNReal.ofReal η ≤
      ENNReal.ofReal (A * (2 * π / ℓ) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl le_rfl) le_rfl
  have hT : ENNReal.ofReal A * volume D + ENNReal.ofReal η ≤ ENNReal.ofReal (A * (π * r ^ 2) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl hvol) le_rfl
  have hU : ENNReal.ofReal A * (∫⁻ u in ball z R₁, ENNReal.ofReal (annLayer z ι r w u)) +
      ENNReal.ofReal η ≤
      ENNReal.ofReal (A * (8 * π * w * (ι + 2 * w) + 8 * π * w * (r + 2 * w)) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl hgint) le_rfl
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
  rw [h3]
  refine ennreal_add_le_ofReal (by positivity) (by positivity)
    (ennreal_mul_le_ofReal (by norm_num) le_rfl ?_)
    (ennreal_mul_le_ofReal (by positivity) le_rfl (ennreal_add_le_ofReal (by positivity)
      (by positivity) hT hU))
  refine ennreal_add_le_ofReal (by positivity) (by positivity)
    (ennreal_add_le_ofReal (by positivity) (by positivity) hP ?_) ?_
  · exact ennreal_mul_le_ofReal (by positivity) le_rfl hT
  · exact ennreal_mul_le_ofReal (by positivity) le_rfl hU

/-- The bound (3.19) for `D' = {ι/2 < |u − z| < 9ι}`: `A π (9ι)² + η + A V' + η`. -/
def lemma38K (ι w A η : ℝ) : ℝ :=
  A * (π * (9 * ι) ^ 2) + η + (A * (8 * π * w * (ι / 2 + 2 * w) + 8 * π * w * (9 * ι + 2 * w)) + η)

/-- **(3.19) on `D'`**: from Lemma 3.1 with `f = 1` and Proposition 2.10 for `(D', 1)` and
`(B_r(z), g')`. -/
theorem cellSum_D'_le {z : ℂ} {ι r δ w A η : ℝ} (hι : 0 < ι) (h10 : 10 * ι ≤ r) (h6 : 6 * δ ≤ ι)
    (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hdiam : ∀ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), cellDiam H x ≤ δ)
    (h1 : Prop210Bound H (annulusSet z (ι / 2) (9 * ι)) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball z r) (annLayer z (ι / 2) (9 * ι) w) A η) :
    ∑ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), cellDiam H x ^ 2 * G.deg x ≤
      lemma38K ι w A η := by
  set D' := annulusSet z (ι / 2) (9 * ι)
  have hbd : ∀ x ∈ vFin H D', (H.cell x ∩ frontier D').Nonempty →
      H.cell x ⊆ ball z r ∧ ∀ u ∈ H.cell x, 1 ≤ annLayer z (ι / 2) (9 * ι) w u := by
    intro x hx hfr
    obtain ⟨h1, h2⟩ := boundary_cell_annLayer H hw hδw (hdiam x hx) hfr (by linarith)
    refine ⟨fun u hu => ?_, h2⟩
    rw [mem_ball, dist_eq_norm]
    linarith [h1 u hu]
  have hsum := cellSum_one_le H (isOpen_annulusSet z _ _) (isBounded_annulusSet z _ _) hbd
  have h1' : (∫⁻ u in D', uDens H u) ≤ ENNReal.ofReal (A * (π * (9 * ι) ^ 2) + η) := by
    have := h1
    unfold Prop210Bound at this
    simp only [ENNReal.ofReal_one, one_mul, setLIntegral_const] at this
    refine this.trans (ennreal_add_le_ofReal (by positivity) hη
      (ennreal_mul_le_ofReal hA le_rfl (volume_annulusSet_le z _ _)) le_rfl)
  have hg' : (∫⁻ u in ball z r, ENNReal.ofReal (annLayer z (ι / 2) (9 * ι) w u) * uDens H u) ≤
      ENNReal.ofReal (A * (8 * π * w * (ι / 2 + 2 * w) + 8 * π * w * (9 * ι + 2 * w)) + η) :=
    hg.trans (ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl
      ((setLIntegral_le_lintegral _ _).trans (lintegral_annLayer_le z (by positivity)
        (by positivity) hw))) le_rfl)
  have hfin := hsum.trans (add_le_add h1' hg')
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_sum_of_nonneg fun x _ => by have := cellDiam_nonneg H x; positivity,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  unfold lemma38K
  linarith

/-- **[18] Lemma 3.8 with squares**, deterministic single-scale form: let `G` be connected with CAL,
`ι > 0`, `10ι ≤ r`, `δ ≤ ι/6`, `δ ≤ w`, `r + δ < R₁`, `B̄_{R₁}(z) ⊆ B_{ρ₁}(0)`; on the event of Lemma 2.7
(`CellDiamBound H ρ₁ δ`) and the five Proposition 2.10 inputs, for every `κ > 0` and every vertex `x` whose
cell meets `B_{5ι}(z)` ([18] has `B_{4sr}`; `5ι` also covers its grid step),
`P_x[X hits V(∂B_ι(z)) before V(∂B_r(z))] ≥ 1 − (6 √K √E / ι + 2κ)` with `K = lemma38K ι w A η`,
`E = lemma34Bound ι r δ w A η`. -/
theorem lemma38 (hconn : G.adj.Connected) (hcal : ConnectedAlongLines H) {z : ℂ}
    {ι r R₁ ρ₁ δ w A η κ : ℝ} (hι : 0 < ι) (h10 : 10 * ι ≤ r) (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ ι)
    (hR₁ : r + δ < R₁) (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hball : closedBall z R₁ ⊆ ball 0 ρ₁) (h27 : CellDiamBound H ρ₁ δ)
    (hF : Prop210Bound H (annulusSet z ι r) (fun u => ‖fderiv ℝ (logRad z ι r) u‖ ^ 2) A η)
    (h1 : Prop210Bound H (annulusSet z ι r) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball z R₁) (annLayer z ι r w) A η)
    (h1' : Prop210Bound H (annulusSet z (ι / 2) (9 * ι)) (fun _ => 1) A η)
    (hg' : Prop210Bound H (ball z r) (annLayer z (ι / 2) (9 * ι) w) A η)
    {x : V} (hx : (H.cell x ∩ ball z (5 * ι)).Nonempty) :
    1 - (6 * Real.sqrt (lemma38K ι w A η) * Real.sqrt (lemma34Bound ι r δ w A η) / ι + 2 * κ) ≤
      (hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z ι)).toReal := by
  have hR : r < R₁ := by linarith
  have hdiamB : ∀ x, (H.cell x ∩ closedBall z r).Nonempty → cellDiam H x ≤ δ := by
    intro x ⟨u, hu, huB⟩
    exact h27 x ⟨u, hu, hball (closedBall_subset_closedBall hR.le huB)⟩
  have hS : Lemma38Setup H z ι r δ :=
    { ι_pos := hι, ten_le := h10, δ_nonneg := hδ0, six_le := h6, diam_le := hdiamB }
  have hsubA : ∀ x ∈ vFin H (annulusSet z ι r), cellDiam H x ≤ δ := by
    intro x hx
    obtain ⟨u, hu, huA⟩ := (mem_vFin H (isBounded_annulusSet z _ _)).mp hx
    exact hdiamB x ⟨u, hu, by rw [mem_closedBall, dist_eq_norm]; exact huA.2.le⟩
  have hsubD : ∀ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), cellDiam H x ≤ δ := by
    intro x hx
    obtain ⟨u, hu, huA⟩ := (mem_vFin H (isBounded_annulusSet z _ _)).mp hx
    exact hdiamB x ⟨u, hu, by rw [mem_closedBall, dist_eq_norm]; linarith [huA.2]⟩
  exact lemma38_core hconn hcal hS
    (energy_logRadAnnulus_le H hι (by linarith) hδ0 h6 hR₁ hw hδw hA hη hsubA hF h1 hg)
    (cellSum_D'_le H hι h10 h6 hw hδw hA hη hsubD h1' hg') hκ hx

/-! ### Moving the inner radius (the grid step of [18]) -/

/-- **Monotonicity in the inner radius**: for `ι' ≤ ι`, hitting `V(∂B_{ι'}(z))` before `V(∂B_r(z))`
forces hitting `V(∂B_ι(z))` before `V(∂B_r(z))`. With `lemma38` at the grid radius `ι'` this gives the
bound at every `ι ∈ [ι', 5ι'/4]` (`[s, 4s] ⊂ [s', 5s']`, [18]). -/
theorem hitDist_in_mono (hconn : G.adj.Connected) {z : ℂ} {ι' ι r δ : ℝ}
    (hS' : Lemma38Setup H z ι' r δ) (hS : Lemma38Setup H z ι r δ) (hιι : ι' ≤ ι) {x : V}
    (hx : (H.cell x ∩ closedBall z r).Nonempty) :
    (hitDist G (vCircle H z ι' ∪ vCircle H z r) x (vCircle H z ι')).toReal ≤
      (hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z ι)).toReal := by
  by_cases hin : ∀ u ∈ H.cell x, ‖u - z‖ ≤ ι
  · rw [toReal_hitDist_in_eq hS hconn hx, annHit_eq_zero_of_inside hconn hS hin, sub_zero]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact hitDist_le_one G _ _ x)
  push Not at hin
  obtain ⟨u₀, hu₀, hu₀'⟩ := hin
  refine ENNReal.toReal_mono (hitDist_ne_top G _ _ x) ?_
  rw [hitDist_eq_hitLaw, hitDist_eq_hitLaw]
  unfold hitLaw
  refine measure_mono_ae ?_
  filter_upwards [ae_isStepPath G hconn x] with ω ⟨h0, hstep⟩ hω
  obtain ⟨hT, hmem⟩ := hω
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hT
  have hfirst := hitTime_eq_coe_iff.mp hn.symm
  rw [stopState_eq_of_eq hn.symm] at hmem
  -- the last vertex meets `∂B_{ι'}`, hence has a point with `|· − z| ≤ ι`
  obtain ⟨v, hv, hv'⟩ := hmem
  have hv'' : ‖v - z‖ = ι' := hv'
  obtain ⟨j, hj, hjm⟩ := exists_crossing_of_walk H
    ((continuous_norm_sub_const z).neg) (t := -ι) n (G.vertexPath ω) (hstep n)
    ⟨u₀, by rw [show G.vertexPath ω 0 = x from h0]; exact hu₀, by
      show -‖u₀ - z‖ ≤ -ι; linarith⟩
    ⟨v, hv, by show -ι ≤ -‖v - z‖; linarith⟩
  have hjIn : G.vertexPath ω j ∈ vCircle H z ι := by
    obtain ⟨c, hc, hct⟩ := hjm
    have hct' : -‖c - z‖ = -ι := hct
    exact ⟨c, hc, neg_inj.mp hct'⟩
  have hTI : hitTime (G.stateVertex ⁻¹' (vCircle H z ι ∪ vCircle H z r)) ω ≤ j :=
    hitTime_le_of_mem (Set.mem_union_left _ hjIn)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top j) hTI)
  have hmj : m ≤ j := by exact_mod_cast hm ▸ hTI
  have hmfirst := hitTime_eq_coe_iff.mp hm.symm
  refine ⟨by rw [← hm]; exact ENat.natCast_ne_top m, ?_⟩
  rw [stopState_eq_of_eq hm.symm]
  rcases hmfirst.1 with hmin | hmout
  · exact hmin
  · exfalso
    rcases Nat.lt_or_ge m n with hlt | hge
    · exact hfirst.2 m hlt (Set.mem_union_right _ hmout)
    · have hmn : m = n := by omega
      rw [hmn] at hmout
      exact Set.disjoint_left.mp (vCircle_disjoint hS') ⟨v, hv, hv'⟩ hmout

end MatedCRTHarmonic.GMS3
