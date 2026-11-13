/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13Layer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13EdgeGrad

/-!
# The boundary layer and the Theorem 3.2 bound on the good event

Source: [18] Lemma 3.1 with a boundary layer obtained from
Proposition 2.10 applied to a smoothed indicator `g` of a neighbourhood of `∂D`, with
`ρ′ = (1+ρ)/2` and `D′ = B_{ρ′}(0)`;
Lemma 3.3, Theorem 3.2, and Theorem 1.3 with the boundary condition `area(B_r(∂D)) ≤ C r`.

* `t13Layer D w` — the layer `clamp(2 − dist(·, ∂D)/w)`: `= 1` on the `w`-neighbourhood of `∂D`, `= 0` off the
  `2w`-neighbourhood, `w⁻¹`-Lipschitz; `t13_lintegral_layer_le` bounds its integral by `area(B_{2w}(∂D))`;
* `t13_isConnected_of_boundedConvexity` — a nonempty domain of bounded convexity is connected;
* **`t13_energy_le_on_event_R`** — on the event of Lemma 2.7 on `B_{ρ₁}(0)` (diameters `≤ δ ≤ w`) and of
  Proposition 2.10 for `(D, |∇f|²)`, `(D, 1)` and `(B_{ρ₁}(0), t13Layer D w)` (threshold `A`, tolerance `η`):
  `Energy(f_ε; G(D)) ≤ 3C² (A Energy(f; D) + η + 2GΛδ(4A + η) + G²(A I_w + η))
     + 24 C² (Λ(1+C))² δ² ((4A + η) + (A I_w + η))`,
  with `|∇f| ≤ G` on `D` and `I_w ≥ ∫_{B_{ρ₁}} t13Layer D w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal Classical

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3 LFMultigraph Harmonic

/-- The boundary layer of width `w`: `1` within distance `w` of `∂D`, `0` beyond `2w`, linear in between. -/
def t13Layer (D : Set ℂ) (w : ℝ) (z : ℂ) : ℝ := max (min 1 (2 - infDist z (frontier D) / w)) 0

theorem t13Layer_nonneg (D : Set ℂ) (w : ℝ) (z : ℂ) : 0 ≤ t13Layer D w z := le_max_right _ _

theorem t13Layer_le_one (D : Set ℂ) (w : ℝ) (z : ℂ) : t13Layer D w z ≤ 1 :=
  max_le (min_le_left _ _) zero_le_one

theorem t13Layer_eq_one {D : Set ℂ} {w : ℝ} (hw : 0 < w) {z : ℂ} (h : infDist z (frontier D) ≤ w) :
    t13Layer D w z = 1 := by
  have h1 : 1 ≤ 2 - infDist z (frontier D) / w := by
    have : infDist z (frontier D) / w ≤ 1 := (div_le_one hw).2 h
    linarith
  unfold t13Layer
  rw [min_eq_left h1, max_eq_left zero_le_one]

theorem t13Layer_eq_zero {D : Set ℂ} {w : ℝ} (hw : 0 < w) {z : ℂ} (h : 2 * w ≤ infDist z (frontier D)) :
    t13Layer D w z = 0 := by
  have h1 : 2 - infDist z (frontier D) / w ≤ 0 := by
    have : 2 ≤ infDist z (frontier D) / w := (le_div_iff₀ hw).2 (by linarith)
    linarith
  unfold t13Layer
  exact max_eq_right ((min_le_right _ _).trans h1)

theorem t13Layer_lipschitz (D : Set ℂ) {w : ℝ} (hw : 0 < w) (z u : ℂ) :
    |t13Layer D w z - t13Layer D w u| ≤ w⁻¹ * dist z u := by
  unfold t13Layer
  calc |max (min 1 (2 - infDist z (frontier D) / w)) 0 - max (min 1 (2 - infDist u (frontier D) / w)) 0|
      ≤ |min 1 (2 - infDist z (frontier D) / w) - min 1 (2 - infDist u (frontier D) / w)| :=
        abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |(2 - infDist z (frontier D) / w) - (2 - infDist u (frontier D) / w)| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |infDist z (frontier D) - infDist u (frontier D)| * w⁻¹ := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _),
          show (2 - infDist z (frontier D) / w) - (2 - infDist u (frontier D) / w) =
            -((infDist z (frontier D) - infDist u (frontier D)) * w⁻¹) by ring, abs_neg, abs_mul,
          abs_of_pos (inv_pos.2 hw)]
    _ ≤ dist z u * w⁻¹ := by
        gcongr
        have := (lipschitz_infDist_pt (frontier D)).dist_le_mul z u
        rw [Real.dist_eq, NNReal.coe_one, one_mul] at this
        exact this
    _ = w⁻¹ * dist z u := mul_comm _ _

/-- The integral of the layer is at most the area of the `2w`-neighbourhood of `∂D`. -/
theorem t13_lintegral_layer_le {D : Set ℂ} {w : ℝ} (hw : 0 < w) (hne : (frontier D).Nonempty) (Ω : Set ℂ) :
    ∫⁻ z in Ω, ENNReal.ofReal (t13Layer D w z) ≤ volume (thickening (2 * w) (frontier D)) := by
  refine (setLIntegral_le_lintegral _ _).trans ?_
  calc ∫⁻ z, ENNReal.ofReal (t13Layer D w z)
      ≤ ∫⁻ z, (thickening (2 * w) (frontier D)).indicator (fun _ => (1 : ℝ≥0∞)) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ thickening (2 * w) (frontier D)
        · rw [indicator_of_mem hz]
          exact ENNReal.ofReal_le_one.2 (t13Layer_le_one D w z)
        · rw [indicator_of_notMem hz, t13Layer_eq_zero hw
            (not_lt.1 fun h => hz ((mem_thickening_iff_infDist_lt hne).2 h)), ENNReal.ofReal_zero]
    _ = volume (thickening (2 * w) (frontier D)) :=
        lintegral_indicator_one isOpen_thickening.measurableSet

/-- A nonempty domain of bounded convexity is connected. -/
theorem t13_isConnected_of_boundedConvexity {D : Set ℂ} {C : ℝ} (hne : D.Nonempty)
    (hbc : BoundedConvexityWith C D) : IsConnected D := by
  obtain ⟨z₀, hz₀⟩ := hne
  refine IsPathConnected.isConnected ⟨z₀, hz₀, fun {w} hw => ?_⟩
  obtain ⟨p, hpc, hp0, hp1, hpD, -⟩ := hbc z₀ hz₀ w hw
  let γ : Path z₀ w :=
    { toFun := fun t : unitInterval => p t
      continuous_toFun := hpc.comp_continuous continuous_subtype_val fun t => t.2
      source' := by simp [hp0]
      target' := by simp [hp1] }
  exact ⟨γ, fun t => hpD t.2⟩

/-- `ofReal` of the combination appearing in Lemma 3.1. -/
theorem t13_ofReal_combo {a e η l v m i : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hη : 0 ≤ η) (hl : 0 ≤ l)
    (hv : 0 ≤ v) (hm : 0 ≤ m) (hi : 0 ≤ i) :
    ENNReal.ofReal ((a * e + η) + l * (a * v + η) + m * (a * i + η)) =
      (ENNReal.ofReal a * ENNReal.ofReal e + ENNReal.ofReal η) +
        ENNReal.ofReal l * (ENNReal.ofReal a * ENNReal.ofReal v + ENNReal.ofReal η) +
        ENNReal.ofReal m * (ENNReal.ofReal a * ENNReal.ofReal i + ENNReal.ofReal η) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) hη, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hl,
    ENNReal.ofReal_add (by positivity) hη, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hm,
    ENNReal.ofReal_add (by positivity) hη, ENNReal.ofReal_mul ha]

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **The Theorem 3.2 bound on the good event** (deterministic). -/
theorem t13_energy_le_on_event_R {D : Set ℂ} (hDo : IsOpen D) {ρ ρ₁ : ℝ} (hDsub : D ⊆ ball (0 : ℂ) ρ)
    {C : ℝ} (hC0 : 0 ≤ C) (hbc : BoundedConvexityWith C D) {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f D)
    {Λ : ℝ≥0} (hΛ : LipschitzOnWith Λ (fderiv ℝ f) D) (hfc : ContinuousOn f (closure D))
    {Gb : ℝ} (hGb0 : 0 ≤ Gb) (hG : ∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ Gb)
    {δ w A η Iw : ℝ} (hρδ : ρ + δ ≤ ρ₁) (hρ₁ : ρ₁ ≤ 1) (hδ0 : 0 ≤ δ) (hδw : δ ≤ w) (hw : 0 < w)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hIw0 : 0 ≤ Iw)
    (hIw : ∫⁻ z in ball (0 : ℂ) ρ₁, ENNReal.ofReal (t13Layer D w z) ≤ ENNReal.ofReal Iw)
    (h27 : CellDiamBound H ρ₁ δ)
    (hF : Prop210Bound H D (fun z => ‖fderiv ℝ f z‖ ^ 2) A η)
    (h1 : Prop210Bound H D (fun _ => 1) A η)
    (hg : Prop210Bound H (ball (0 : ℂ) ρ₁) (t13Layer D w) A η)
    {fε : V → ℝ} (hsol : IsGMSDirichletSolution H D f fε) :
    energy G (vFin H D) fε ≤
      3 * C ^ 2 * ((A * (eucEnergy f D).toReal + η) + 2 * Gb * Λ * δ * (A * 4 + η) +
        Gb ^ 2 * (A * Iw + η)) +
      24 * C ^ 2 * ((Λ : ℝ) * (1 + C)) ^ 2 * δ ^ 2 * ((A * 4 + η) + (A * Iw + η)) := by
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDsub
  have hρρ₁ : ρ ≤ ρ₁ := by linarith
  -- cells of `V(D)`: diameters and location
  have hdiam : ∀ x ∈ vFin H D, cellDiam H x ≤ δ := by
    intro x hx
    obtain ⟨z, hzx, hzD⟩ := (mem_vFin H hDb).1 hx
    exact h27 x ⟨z, hzx, ball_subset_ball hρρ₁ (hDsub hzD)⟩
  have hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ ball (0 : ℂ) ρ₁ ∧ ∀ z ∈ H.cell x, 1 ≤ t13Layer D w z := by
    intro x hx hb
    obtain ⟨b, hbx, hbF⟩ := hb
    obtain ⟨u, hux, huD⟩ := (mem_vFin H hDb).1 hx
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have hu := hDsub huD
      have hzu := (dist_le_cellDiam H hz hux).trans (hdiam x hx)
      rw [mem_ball, dist_zero_right] at hu ⊢
      calc ‖z‖ ≤ ‖z - u‖ + ‖u‖ := norm_le_norm_sub_add z u
        _ < δ + ρ := by rw [← dist_eq_norm]; linarith
        _ ≤ ρ₁ := by linarith
    · rw [t13Layer_eq_one hw ((infDist_le_dist_of_mem hbF).trans
        (((dist_le_cellDiam H hz hbx).trans (hdiam x hx)).trans hδw))]
  -- reference points `z_x ∈ H_x ∩ D`
  let zr : V → ℂ := fun x =>
    if h : (H.cell x ∩ D).Nonempty then h.choose else (cell_nonempty H x).choose
  have hzr : ∀ x, zr x ∈ H.cell x := by
    intro x
    by_cases h : (H.cell x ∩ D).Nonempty
    · simp only [zr, dite_eq_left h]
      exact h.choose_spec.1
    · simp only [zr, dite_eq_right h]
      exact (cell_nonempty H x).choose_spec
  have hzrD : ∀ x ∈ vFin H D, zr x ∈ H.cell x ∩ D := by
    intro x hx
    have h := (mem_vFin H hDb).1 hx
    simp only [zr, dite_eq_left h]
    exact h.choose_spec
  -- the energy bound of (3.14)
  have hE := t13_energy_le_grad H hDo hDb hC0 hbc hf hΛ hfc zr hzrD hsol
  set K : ℝ := (Λ : ℝ) * (1 + C) with hK
  set S1 : ℝ := ∑ x ∈ vFin H D, ‖fderiv ℝ f (zr x)‖ ^ 2 * (cellDiam H x ^ 2 * G.deg x) with hS1
  set S2 : ℝ := ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x with hS2
  have hsplit : ∑ x ∈ vFin H D, (G.deg x : ℝ) *
      (3 * C ^ 2 * cellDiam H x ^ 2 * ‖fderiv ℝ f (zr x)‖ ^ 2 + 24 * C ^ 2 * K ^ 2 * cellDiam H x ^ 4) ≤
      3 * C ^ 2 * S1 + 24 * C ^ 2 * K ^ 2 * δ ^ 2 * S2 := by
    rw [hS1, hS2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    have hd0 := cellDiam_nonneg H x
    have hd2 : cellDiam H x ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hd0 (hdiam x hx) 2
    have hdeg : (0 : ℝ) ≤ G.deg x := Nat.cast_nonneg _
    have h24 : 0 ≤ 24 * C ^ 2 * K ^ 2 := by positivity
    have : cellDiam H x ^ 4 = cellDiam H x ^ 2 * cellDiam H x ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hd2 (mul_nonneg h24 (mul_nonneg hdeg (sq_nonneg (cellDiam H x))))]
  -- the gradient sum: Lemma 3.1
  have hLip : ∀ z ∈ D, ∀ u ∈ D, ‖fderiv ℝ f z‖ ^ 2 ≤ ‖fderiv ℝ f u‖ ^ 2 + 2 * Gb * Λ * dist z u := by
    intro z hz u hu
    have hd : ‖fderiv ℝ f z‖ - ‖fderiv ℝ f u‖ ≤ Λ * dist z u := by
      have := hΛ.dist_le_mul z hz u hu
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f u)]
    have hz' := hG z hz
    have hu' := hG u hu
    have hn1 := norm_nonneg (fderiv ℝ f z)
    have hn2 := norm_nonneg (fderiv ℝ f u)
    have hΛd : 0 ≤ (Λ : ℝ) * dist z u := by positivity
    have h1 : (‖fderiv ℝ f z‖ - ‖fderiv ℝ f u‖) * (‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖) ≤
        Λ * dist z u * (‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    have h2 : (Λ : ℝ) * dist z u * (‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖) ≤ Λ * dist z u * (2 * Gb) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛd
    nlinarith [h1, h2]
  have hL0 : 0 ≤ 2 * Gb * Λ := by positivity
  have h31 := lemma31 H hDo hDb zr hzr hLip hL0 hdiam
    (fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hG _ (hzrD x hx).2) 2) hbd hF h1 hg
  have hEfin : eucEnergy f D ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Gb ^ 2) * volume D) ?_ ?_
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDb.measure_lt_top).ne
    · calc eucEnergy f D ≤ ∫⁻ _z in D, ENNReal.ofReal (Gb ^ 2) := by
            refine setLIntegral_mono' hDo.measurableSet fun z hz => ENNReal.ofReal_le_ofReal ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hG z hz) 2
        _ = ENNReal.ofReal (Gb ^ 2) * volume D := by rw [setLIntegral_const]
  have hvol : volume D ≤ ENNReal.ofReal 4 := by
    refine (measure_mono (hDsub.trans (ball_subset_ball (show ρ ≤ 1 by linarith)))).trans ?_
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.pi_lt_d2
    nlinarith
  have hR1 : ∑ x ∈ vFin H D, ENNReal.ofReal (‖fderiv ℝ f (zr x)‖ ^ 2 * (cellDiam H x ^ 2 * G.deg x)) ≤
      ENNReal.ofReal ((A * (eucEnergy f D).toReal + η) + 2 * Gb * Λ * δ * (A * 4 + η) +
        Gb ^ 2 * (A * Iw + η)) := by
    refine h31.trans ?_
    rw [t13_ofReal_combo hA ENNReal.toReal_nonneg hη (by positivity) (by norm_num) (sq_nonneg Gb) hIw0,
      ENNReal.ofReal_toReal hEfin]
    have hlw : ENNReal.ofReal (Gb ^ 2) = ENNReal.ofReal (Gb ^ 2) := rfl
    gcongr
    · exact le_of_eq (by rw [eucEnergy])
  have hS1le : S1 ≤ (A * (eucEnergy f D).toReal + η) + 2 * Gb * Λ * δ * (A * 4 + η) + Gb ^ 2 * (A * Iw + η) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => by
      have := cellDiam_nonneg H x
      positivity] at hR1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hR1
  -- the sum of `diam² deg`
  have hS2E := cellSum_one_le H hDo hDb hbd
  have h1' : (∫⁻ z in D, uDens H z) ≤ ENNReal.ofReal A * volume D + ENNReal.ofReal η := by
    have := h1
    unfold Prop210Bound at this
    simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_const, Measure.restrict_apply_univ]
      using this
  have hR2 : ∑ x ∈ vFin H D, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) ≤
      ENNReal.ofReal ((A * 4 + η) + (A * Iw + η)) := by
    refine hS2E.trans ((add_le_add h1' hg).trans ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) hη,
      ENNReal.ofReal_add (by positivity) hη, ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hA]
    gcongr
  have hS2le : S2 ≤ (A * 4 + η) + (A * Iw + η) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => by
      have := cellDiam_nonneg H x
      positivity] at hR2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hR2
  calc energy G (vFin H D) fε ≤ _ := hE
    _ ≤ 3 * C ^ 2 * S1 + 24 * C ^ 2 * K ^ 2 * δ ^ 2 * S2 := hsplit
    _ ≤ _ := by
        gcongr

end MatedCRTHarmonic.GMSMain
