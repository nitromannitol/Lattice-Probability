/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.Lipschitz at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Translate
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# Recentring the test pair: the Lipschitz comparison of [18] (4.43)–(4.44)

Source: [18], Case 4 of the proof of Proposition 4.10. After
recentring at the marked point `z₀`, a deterministic test pair `(D, f)` becomes the pair `(D − z₀, f(· + z₀))`, which
depends on `z₀`. For `‖z₀‖ < κ` the integrand `f(u)` on `D` is compared with the recentred one: if `u + z₀ ∈ D` then
`f(u) ≤ f(u + z₀) + Lκ` (Lipschitz bound), and otherwise `u + z₀` lies within `κ` of `∂D` and `f(u) ≤ M`. Hence
(`setLIntegral_le_recentred`), for every a.e.-measurable density `U ≥ 0`,

  `∫⁻_D f U ≤ ∫⁻_{D−z₀} f(· + z₀) U + Lκ ∫⁻_{D−z₀} U + M ∫⁻_{B_κ(∂D) − z₀} U`,

and (`globalGood_of_three`) the three good events for the recentred pairs `(D − z₀, f(· + z₀))`, `(D − z₀, 1)`,
`(B_κ(∂D) − z₀, 1)` imply the good event for `(D, f)` with the tolerance
`tol₁ + Lκ (A vol D + tol₂) + M (A vol B_κ(∂D) + tol₃)` ([18] (4.44)). The three recentred pairs become deterministic
in the recentred coordinates (`GMS4FO/Translate.lean`). [18] performs the same comparison in its Case 4 coordinates
`f(2(w ± z))`; here the recentring is a pure translation (`GMS4FO/Chain.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

/-- A point `w ∉ D` with `w − z₀ ∈ D` (`D` open) lies within `‖z₀‖` of the frontier of `D`. -/
theorem exists_frontier_near {D : Set ℂ} (hD : IsOpen D) {w z₀ : ℂ} (hin : w - z₀ ∈ D)
    (hout : w ∉ D) : ∃ x ∈ frontier D, dist w x ≤ ‖z₀‖ := by
  let g : Icc (0 : ℝ) 1 → ℂ := fun t => w - (1 - (t : ℝ)) • z₀
  have hg : Continuous g := by fun_prop
  let S : Set (Icc (0 : ℝ) 1) := g ⁻¹' D
  have hSo : IsOpen S := hD.preimage hg
  have h0 : (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ∈ S := by
    change w - (1 - (0 : ℝ)) • z₀ ∈ D
    simpa using hin
  have h1 : (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) ∉ S := by
    change w - (1 - (1 : ℝ)) • z₀ ∉ D
    simpa using hout
  have hne : (frontier S).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨_, h0⟩, fun h => h1 (h ▸ mem_univ _)⟩
  obtain ⟨t, ht⟩ := hne
  have htS : t ∉ S := fun h => (hSo.inter_frontier_eq.subset ⟨h, ht⟩ : _)
  have htcl : g t ∈ closure D := by
    have : t ∈ closure S := frontier_subset_closure ht
    exact closure_mono (image_preimage_subset g D) (mem_closure_image hg.continuousAt this)
  refine ⟨g t, ?_, ?_⟩
  · rw [hD.frontier_eq]
    exact ⟨htcl, htS⟩
  · have ht1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
    have ht2 : 1 - (t : ℝ) ≤ 1 := by linarith [t.2.1]
    rw [dist_eq_norm]
    change ‖w - (w - (1 - (t : ℝ)) • z₀)‖ ≤ ‖z₀‖
    rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1]
    calc (1 - (t : ℝ)) * ‖z₀‖ ≤ 1 * ‖z₀‖ := mul_le_mul_of_nonneg_right ht2 (norm_nonneg _)
      _ = ‖z₀‖ := one_mul _

/-- The translate of an open set is open. -/
theorem isOpen_image_sub {D : Set ℂ} (hD : IsOpen D) (z₀ : ℂ) :
    IsOpen ((fun z => z - z₀) '' D) :=
  (Homeomorph.subRight z₀).isOpenMap _ hD

theorem mem_image_sub_iff (D : Set ℂ) (z₀ u : ℂ) :
    u ∈ (fun z => z - z₀) '' D ↔ u + z₀ ∈ D := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨u + z₀, h, by ring⟩

/-- **The recentring comparison** [18] (4.43), for an a.e.-measurable density `U`. -/
theorem setLIntegral_le_recentred {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} {L M κ : ℝ}
    (hL : 0 ≤ L) (hfM : ∀ z ∈ D, f z ≤ M)
    (hlip : ∀ z ∈ D, ∀ w ∈ D, |f z - f w| ≤ L * dist z w) {z₀ : ℂ} (hz₀ : ‖z₀‖ < κ)
    {U : ℂ → ℝ≥0∞} (hU : AEMeasurable U volume) :
    (∫⁻ u in D, ENNReal.ofReal (f u) * U u) ≤
      (∫⁻ u in (fun z => z - z₀) '' D, ENNReal.ofReal (f (u + z₀)) * U u) +
        ENNReal.ofReal (L * κ) * (∫⁻ u in (fun z => z - z₀) '' D, U u) +
          ENNReal.ofReal M *
            (∫⁻ u in (fun z => z - z₀) '' thickening κ (frontier D), U u) := by
  set D' := (fun z => z - z₀) '' D with hD'def
  set T' := (fun z => z - z₀) '' thickening κ (frontier D) with hT'def
  have hD'o : IsOpen D' := isOpen_image_sub hD z₀
  have hT'o : IsOpen T' := isOpen_image_sub isOpen_thickening z₀
  -- continuity of the recentred test on `D'`
  have hcont : ContinuousOn (fun u => f (u + z₀)) D' := by
    have hfc : ContinuousOn f D := by
      refine Metric.continuousOn_iff.2 fun z hz e he => ?_
      refine ⟨e / (L + 1), by positivity, fun w hw hwz => ?_⟩
      have h1 := hlip w hw z hz
      have hL1 : 0 < L + 1 := by linarith
      calc dist (f w) (f z) = |f w - f z| := Real.dist_eq _ _
        _ ≤ L * dist w z := h1
        _ ≤ (L + 1) * dist w z := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < (L + 1) * (e / (L + 1)) := mul_lt_mul_of_pos_left hwz hL1
        _ = e := by field_simp
    refine hfc.comp (continuous_id.add continuous_const).continuousOn fun u hu => ?_
    exact (mem_image_sub_iff D z₀ u).1 hu
  have hm1 : AEMeasurable (D'.indicator fun u => ENNReal.ofReal (f (u + z₀)) * U u) volume := by
    refine (aemeasurable_indicator_iff hD'o.measurableSet).2 ?_
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcont.aemeasurable hD'o.measurableSet)).mul hU.restrict
  have hm2 : AEMeasurable (fun u => ENNReal.ofReal (L * κ) * D'.indicator U u) volume :=
    ((aemeasurable_indicator_iff hD'o.measurableSet).2 hU.restrict).const_mul _
  have hm12 : AEMeasurable (fun u => D'.indicator (fun u => ENNReal.ofReal (f (u + z₀)) * U u) u +
      ENNReal.ofReal (L * κ) * D'.indicator U u) volume := hm1.add hm2
  rw [← lintegral_indicator hD.measurableSet]
  refine (lintegral_mono (g := fun u => (D'.indicator (fun u => ENNReal.ofReal (f (u + z₀)) * U u) u +
      ENNReal.ofReal (L * κ) * D'.indicator U u) + ENNReal.ofReal M * T'.indicator U u) ?_).trans ?_
  rotate_left
  · rw [lintegral_add_left' hm12, lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hD'o.measurableSet,
      lintegral_indicator hD'o.measurableSet, lintegral_indicator hT'o.measurableSet]
  intro u
  by_cases hu : u ∈ D
  · rw [indicator_of_mem hu]
    have hfu := hfM u hu
    by_cases hu' : u + z₀ ∈ D
    · have hmem : u ∈ D' := (mem_image_sub_iff D z₀ u).2 hu'
      simp only [indicator_of_mem hmem]
      have hbound : ENNReal.ofReal (f u) ≤ ENNReal.ofReal (f (u + z₀)) + ENNReal.ofReal (L * κ) := by
        refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
        have h1 := hlip u hu (u + z₀) hu'
        have h2 : dist u (u + z₀) = ‖z₀‖ := by
          rw [dist_eq_norm, show u - (u + z₀) = -z₀ by ring, norm_neg]
        have h3 : L * ‖z₀‖ ≤ L * κ := mul_le_mul_of_nonneg_left hz₀.le hL
        rw [h2] at h1
        linarith [abs_le.1 h1]
      calc ENNReal.ofReal (f u) * U u
          ≤ (ENNReal.ofReal (f (u + z₀)) + ENNReal.ofReal (L * κ)) * U u := by gcongr
        _ = ENNReal.ofReal (f (u + z₀)) * U u + ENNReal.ofReal (L * κ) * U u := add_mul _ _ _
        _ ≤ _ := le_self_add
    · obtain ⟨x, hx, hdx⟩ := exists_frontier_near hD (w := u + z₀) (z₀ := z₀)
        (by simpa using hu) hu'
      have hT : u ∈ T' := by
        refine (mem_image_sub_iff _ z₀ u).2 ?_
        exact mem_thickening_iff.2 ⟨x, hx, lt_of_le_of_lt hdx hz₀⟩
      simp only [indicator_of_mem hT]
      calc ENNReal.ofReal (f u) * U u ≤ ENNReal.ofReal M * U u := by
            gcongr
        _ ≤ _ := le_add_self
  · rw [indicator_of_notMem hu]
    exact bot_le

theorem image_sub_eq_preimage_add (S : Set ℂ) (z₀ : ℂ) :
    (fun z => z - z₀) '' S = (fun z => z + z₀) ⁻¹' S := by
  ext u
  rw [mem_image_sub_iff, mem_preimage]

/-- The tolerance arithmetic of (4.44), in `ℝ≥0∞`. -/
theorem tol_combine_le {L M κ A VD VT tol₁ tol₂ tol₃ tol : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hVD : 0 ≤ VD) (hVT : 0 ≤ VT) (h₁ : 0 ≤ tol₁) (h₂ : 0 ≤ tol₂)
    (h₃ : 0 ≤ tol₃) (htol : tol₁ + L * κ * (A * VD + tol₂) + M * (A * VT + tol₃) ≤ tol) :
    ENNReal.ofReal tol₁ +
        (ENNReal.ofReal (L * κ) * (ENNReal.ofReal A * ENNReal.ofReal VD + ENNReal.ofReal tol₂) +
          ENNReal.ofReal M * (ENNReal.ofReal A * ENNReal.ofReal VT + ENNReal.ofReal tol₃)) ≤
      ENNReal.ofReal tol := by
  rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) h₂,
    ← ENNReal.ofReal_add (by positivity) h₃, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add h₁ (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

/-- **The three recentred good events give the good event** ([18] (4.43)–(4.44)). -/
theorem globalGood_of_three {η : ℝ → ℂ} {ε : ℝ} {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    {L M κ A tol₁ tol₂ tol₃ tol VD VT : ℝ} {R₁ R₂ R₃ R : Set ℂ} {r : ℝ}
    (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hVD0 : 0 ≤ VD) (hVT0 : 0 ≤ VT)
    (htol₁ : 0 ≤ tol₁) (htol₂ : 0 ≤ tol₂) (htol₃ : 0 ≤ tol₃)
    (hfM : ∀ z ∈ D, f z ≤ M) (hlip : ∀ z ∈ D, ∀ w ∈ D, |f z - f w| ≤ L * dist z w)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < κ) (hU : AEMeasurable (fun u => GMS4b.uStar ε η u) volume)
    (hVD : volume D ≤ ENNReal.ofReal VD) (hVT : volume (thickening κ (frontier D)) ≤ ENNReal.ofReal VT)
    (htol : tol₁ + L * κ * (A * VD + tol₂) + M * (A * VT + tol₃) ≤ tol)
    (hR : R ⊆ R₁)
    (h₁ : GlobalGood η ε ((fun z => z - z₀) '' D) (fun u => f (u + z₀)) A tol₁ R₁ r)
    (h₂ : GlobalGood η ε ((fun z => z - z₀) '' D) (fun _ => 1) A tol₂ R₂ r)
    (h₃ : GlobalGood η ε ((fun z => z - z₀) '' thickening κ (frontier D)) (fun _ => 1) A tol₃ R₃ r) :
    GlobalGood η ε D f A tol R r := by
  refine ⟨fun z hz => h₁.1 z (hR hz), ?_⟩
  have hsplit := setLIntegral_le_recentred hD hL hfM hlip hz₀ hU
  -- the deterministic integrals
  have hone : ∀ S : Set ℂ, (∫⁻ u in S, ENNReal.ofReal ((fun _ : ℂ => (1 : ℝ)) u)) = volume S := by
    intro S
    simp
  have hvolD : volume ((fun z => z - z₀) '' D) = volume D := by
    rw [image_sub_eq_preimage_add, measure_preimage_add_right]
  have hvolT : volume ((fun z => z - z₀) '' thickening κ (frontier D)) =
      volume (thickening κ (frontier D)) := by
    rw [image_sub_eq_preimage_add, measure_preimage_add_right]
  have hfD : (∫⁻ u in (fun z => z - z₀) '' D, ENNReal.ofReal (f (u + z₀))) =
      ∫⁻ u in D, ENNReal.ofReal (f u) := by
    have h := setLIntegral_translate (-z₀) D (fun z => ENNReal.ofReal (f z))
    have e1 : (fun z : ℂ => z + -z₀) = fun z => z - z₀ := by funext z; ring
    have e2 : (fun w : ℂ => ENNReal.ofReal (f (w - -z₀))) = fun w => ENNReal.ofReal (f (w + z₀)) := by
      funext w; congr 2; ring
    rw [e1] at h
    simp only [sub_neg_eq_add] at h
    exact h.symm
  have g₁ := h₁.2
  have g₂ := h₂.2
  have g₃ := h₃.2
  simp only [ENNReal.ofReal_one, one_mul, setLIntegral_one] at g₂ g₃
  rw [hvolD] at g₂
  rw [hvolT] at g₃
  rw [hfD] at g₁
  calc (∫⁻ u in D, ENNReal.ofReal (f u) * GMS4b.uStar ε η u)
      ≤ _ := hsplit
    _ ≤ (ENNReal.ofReal A * (∫⁻ u in D, ENNReal.ofReal (f u)) + ENNReal.ofReal tol₁) +
          ENNReal.ofReal (L * κ) * (ENNReal.ofReal A * ENNReal.ofReal VD + ENNReal.ofReal tol₂) +
          ENNReal.ofReal M * (ENNReal.ofReal A * ENNReal.ofReal VT + ENNReal.ofReal tol₃) := by
        gcongr
        · exact g₂.trans (add_le_add (mul_le_mul' le_rfl hVD) le_rfl)
        · exact g₃.trans (add_le_add (mul_le_mul' le_rfl hVT) le_rfl)
    _ ≤ ENNReal.ofReal A * (∫⁻ u in D, ENNReal.ofReal (f u)) + ENNReal.ofReal tol := by
        rw [add_assoc, add_assoc]
        gcongr
        exact tol_combine_le hL hκ hM hA hVD0 hVT0 htol₁ htol₂ htol₃ htol

end MatedCRTHarmonic.GMS4FO
