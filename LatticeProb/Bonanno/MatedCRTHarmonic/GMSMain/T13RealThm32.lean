/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13RealThm32 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13RealEnergy

/-!
# [18] Theorem 3.2 at every real mesh, from named inputs

Source: [18] Theorem 3.2 ((i)): there are `α, β > 0`
(depending only on `γ`) such that for each `C ≥ 1` there is `A = A(C, ρ, γ)` with, for each `ε ∈ (0, 1)` and each
`(D, f) ∈ 𝒞_C(ε^β)`, `P[Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + ε^α] ≥ 1 − O_ε(ε^α)` "at a rate depending only on
`C, ρ, γ`". The class `𝒞_C(δ)`: `D ⊂ B_ρ(0)` open, `area(B_r(∂D)) ≤ C r` for `r ∈ (0, 1)`,
`C`-bounded convexity; `f` differentiable on `D` with `∇f` `δ⁻¹`-Lipschitz and `‖f‖_∞, ‖∇f‖_∞ ≤ δ⁻¹` (and, for the
boundary data (1.6), continuous on `D̄`).

Proof ([18] Lemma 3.3 with the boundary-layer correction): on the event of Lemma 2.7 and of Proposition 2.10 for the
three tests, `t13_energy_le_on_event_R` with `G = Λ = M := ε^{-β}` gives `Energy(f_ε) ≤ 3C²A₂ Energy(f; D) + err`,
`err ≤ K M² ε^m ≤ K ε^{m/2} ≤ ε^{α_t}` (`t13r_err_le`; `m = min(α, q, β′)`, `4β ≤ m`, `α_t ≤ m/4`) for all small `ε`
UNIFORMLY over the class; the tests are admissible for every `(D, f)` in the class once `2β ≤ β₂`, `C_b ≥ 2`.

* **`t13r_theorem32_of_inputs`** — from the named inputs (real-mesh Lemma 2.7 and Proposition 2.10).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-- The energy over the empty domain vanishes. -/
theorem t13r_energy_vFin_empty {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (g : V → ℝ) : energy G (vFin H ∅) g = 0 := by
  have hempty : vFin H (∅ : Set ℂ) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨z, hz⟩ := (mem_vFin H Bornology.isBounded_empty).1 hx
    exact hz.2
  unfold energy
  rw [hempty]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [mem_edgesIn] at he
  exact absurd he.1 (Finset.notMem_empty _)

/-- **One mesh and one pair `(D, f) ∈ 𝒞_C(ε^β)` of Theorem 3.2** (the per-mesh step of
`t13r_theorem32_of_inputs`, with the small-mesh conditions as hypotheses). -/
theorem t13r_theorem32_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    {ρ ρ₁ q β₂ α A₂ CP C27 Cb C β αt β' m K ε : ℝ}
    (hρ0 : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁1 : ρ₁ < 1) (hq : 0 < q) (hβ₂ : 0 < β₂) (hα : 0 < α)
    (hA₂ : 0 ≤ A₂) (hCP : 0 ≤ CP) (hC27 : 0 ≤ C27) (hC1 : 1 ≤ C) (hCCb : C ≤ Cb) (hCb : 16 * π ≤ Cb)
    (hβ : 0 < β) (h2β : 2 * β ≤ β₂) (h4β : 4 * β ≤ m) (hαtm : αt ≤ m / 4)
    (hβ'def : β' = min q β₂) (hmdef : m = min α (min q β₂))
    (hK : K = 3 * C ^ 2 * (2 + 2 * (A₂ * 4 + 1) + 2 * A₂ * C) +
      24 * C ^ 2 * (1 + C) ^ 2 * (A₂ * 4 + 2 + 2 * A₂ * C))
    (h27 : ∀ ε ∈ Ioo (0 : ℝ) 1, P (EpsALemma27Bad bm η ε q ρ₁) ≤ ENNReal.ofReal (C27 * ε ^ α))
    (h210 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible ε ρ₁ Cb β₂ V g →
      P (EpsAProp210Bad bm η ε V g A₂ (ε ^ α)) ≤ ENNReal.ofReal (CP * ε ^ α))
    (hε0 : 0 < ε) (hεI : ε ∈ Ioo (0 : ℝ) 1) (hδρ : ε ^ q < ρ₁ - ρ) (hw2 : ε ^ β' < 1 / 2)
    (hKsmall : K * ε ^ (m / 4) ≤ 1)
    {D : Set ℂ} {f : ℂ → ℝ} (hDo : IsOpen D) (hDsub : D ⊆ ball (0 : ℂ) ρ)
    (hbdry : ∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r))
    (hbc : BoundedConvexityWith C D) (hf : DifferentiableOn ℝ f D)
    (hLipf : ∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w)
    (hGf : ∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) (hfc : ContinuousOn f (closure D)) :
    P {ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) D f (3 * C ^ 2 * A₂) (ε ^ αt)} ≤
      ENNReal.ofReal ((C27 + 3 * CP) * ε ^ α) := by
  have hρ₁0 : 0 < ρ₁ := hρ0.trans hρρ₁
  have hCb1 : 1 < Cb := by nlinarith [Real.pi_gt_three]
  have hCb2 : 2 ≤ Cb := by nlinarith [Real.pi_gt_three]
  have hC0 : 0 ≤ C := by linarith
  have hβ'0 : 0 < β' := by rw [hβ'def]; exact lt_min hq hβ₂
  have hm0 : 0 < m := by rw [hmdef]; exact lt_min hα (lt_min hq hβ₂)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hε : (0 : ℝ) < ε := hε0
  have hε1 : ε < 1 := hεI.2
  have hεI' : ε ∈ Ioo (0 : ℝ) 1 := hεI
  have hm : 0 ≤ ε ^ α := Real.rpow_nonneg hε.le α
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDsub
  set B27 := EpsALemma27Bad bm η ε q ρ₁
  -- the empty domain
  rcases D.eq_empty_or_nonempty with hDe | hne
  · subst hDe
    refine (measure_mono ?_).trans ((h27 ε hεI').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) hm)))
    intro ω hω h27ω
    apply hω
    refine ⟨h27ω.1, fun hlf H _ fε _ => ?_⟩
    rw [t13r_energy_vFin_empty H fε, ENNReal.ofReal_zero]
    exact bot_le
  -- a nonempty domain
  have hfr : (frontier D).Nonempty := by
    refine nonempty_frontier_iff.2 ⟨hne, fun h => ?_⟩
    have : (2 : ℂ) ∈ ball (0 : ℂ) ρ := hDsub (h ▸ mem_univ _)
    rw [mem_ball, dist_zero_right] at this
    norm_num at this
    linarith
  have hconn : IsConnected D := t13_isConnected_of_boundedConvexity hne hbc
  set M : ℝ := ε ^ (-β) with hMdef
  have hM0 : 0 < M := Real.rpow_pos_of_pos hε _
  have hM1 : 1 ≤ M := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)
  set Λ : ℝ≥0 := M.toNNReal with hΛdef
  have hΛM : (Λ : ℝ) = M := Real.coe_toNNReal _ hM0.le
  have hΛ : LipschitzOnWith Λ (fderiv ℝ f) D := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [hΛM, dist_eq_norm]
    exact hLipf z hz w hw
  -- `M² ≤ C_b ε^{-β₂}` and `2M² ≤ C_b ε^{-β₂}`
  have hMsq : M ^ 2 = ε ^ (-(2 * β)) := by
    rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have hM2le : M ^ 2 ≤ ε ^ (-β₂) := by
    rw [hMsq]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)
  have hβ₂pos : 0 < ε ^ (-β₂) := Real.rpow_pos_of_pos hε _
  have hGb2 : M ^ 2 ≤ Cb * ε ^ (-β₂) := hM2le.trans (le_mul_of_one_le_left hβ₂pos.le hCb1.le)
  have hGbΛ : 2 * M * M ≤ Cb * ε ^ (-β₂) :=
    calc 2 * M * M = 2 * M ^ 2 := by ring
      _ ≤ 2 * ε ^ (-β₂) := by linarith [hM2le]
      _ ≤ Cb * ε ^ (-β₂) := mul_le_mul_of_nonneg_right hCb2 hβ₂pos.le
  have hFLip : ∀ z ∈ D, ∀ u ∈ D, |‖fderiv ℝ f z‖ ^ 2 - ‖fderiv ℝ f u‖ ^ 2| ≤ 2 * M * M * dist z u := by
    intro z hz u hu
    have hd : |‖fderiv ℝ f z‖ - ‖fderiv ℝ f u‖| ≤ M * dist z u :=
      (abs_norm_sub_norm_le _ _).trans (hLipf z hz u hu)
    have hsum : ‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖ ≤ 2 * M := by linarith [hGf z hz, hGf u hu]
    rw [show ‖fderiv ℝ f z‖ ^ 2 - ‖fderiv ℝ f u‖ ^ 2 =
      (‖fderiv ℝ f z‖ - ‖fderiv ℝ f u‖) * (‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖)]
    calc |‖fderiv ℝ f z‖ - ‖fderiv ℝ f u‖| * (‖fderiv ℝ f z‖ + ‖fderiv ℝ f u‖)
        ≤ M * dist z u * (2 * M) := mul_le_mul hd hsum (by positivity) (by positivity)
      _ = 2 * M * M * dist z u := by ring
  set δ := ε ^ q with hδdef
  set w := ε ^ β' with hwdef
  set ηt := ε ^ α with hηdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hε.le q
  have hw0 : 0 < w := Real.rpow_pos_of_pos hε β'
  have hδw : δ ≤ w := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by rw [hβ'def]; exact min_le_left _ _)
  have hpowpos : 0 < ε ^ (-β₂) := hβ₂pos
  have hwinv : w⁻¹ ≤ Cb * ε ^ (-β₂) := by
    rw [hwdef, ← Real.rpow_neg hε.le]
    exact (Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by rw [hβ'def]; linarith [min_le_right q β₂])).trans
      (le_mul_of_one_le_left hpowpos.le hCb1.le)
  have hone : (1 : ℝ) ≤ Cb * ε ^ (-β₂) :=
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)).trans
      (le_mul_of_one_le_left hpowpos.le hCb1.le)
  -- the three tests
  have hadmF : GMS4.Prop210Admissible ε ρ₁ Cb β₂ D (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    ⟨hε, hε1, hρ₁0, hρ₁1, hCb1, hβ₂, hDo, hconn, hDsub.trans (ball_subset_ball hρρ₁.le),
      fun r hr => (hbdry r hr).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCCb hr.1.le)),
      fun z hz => ⟨sq_nonneg _, (pow_le_pow_left₀ (norm_nonneg _) (hGf z hz) 2).trans hGb2⟩,
      fun z hz u hu => (hFLip z hz u hu).trans (mul_le_mul_of_nonneg_right hGbΛ dist_nonneg)⟩
  have hadm1 : GMS4.Prop210Admissible ε ρ₁ Cb β₂ D (fun _ => 1) :=
    ⟨hε, hε1, hρ₁0, hρ₁1, hCb1, hβ₂, hDo, hconn, hDsub.trans (ball_subset_ball hρρ₁.le),
      fun r hr => (hbdry r hr).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCCb hr.1.le)),
      fun z _ => ⟨zero_le_one, hone⟩, fun z _ u _ => by simp only [sub_self, abs_zero]; positivity⟩
  have hlayer := MesoModel.recBallLayer_admissible (s := 1) (ρ := 1) (w := 1) hε hε1 hρ₁0 le_rfl hρ₁1 hCb hβ₂
    one_pos hone (by simpa using hone)
  have hadmg : GMS4.Prop210Admissible ε ρ₁ Cb β₂ (ball (0 : ℂ) ρ₁) (t13Layer D w) :=
    ⟨hε, hε1, hρ₁0, hρ₁1, hCb1, hβ₂, isOpen_ball, isConnected_ball hρ₁0, le_rfl,
      hlayer.2.2.2.2.2.2.2.2.2.1, fun z _ => ⟨t13Layer_nonneg D w z, (t13Layer_le_one D w z).trans hone⟩,
      fun z _ u _ => (t13Layer_lipschitz D hw0 z u).trans (mul_le_mul_of_nonneg_right hwinv dist_nonneg)⟩
  have hIw : ∫⁻ z in ball (0 : ℂ) ρ₁, ENNReal.ofReal (t13Layer D w z) ≤ ENNReal.ofReal (C * (2 * w)) :=
    (t13_lintegral_layer_le hw0 hfr _).trans (hbdry _ ⟨by positivity, by linarith⟩)
  -- the error term is at most `ε^{α_t}`
  have hs1 : ε ^ m ≤ 1 := Real.rpow_le_one hε.le hε1.le hm0.le
  have hηs : ηt ≤ ε ^ m := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by rw [hmdef]; exact min_le_left _ _)
  have hδs : δ ≤ ε ^ m := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
    (by rw [hmdef]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hws : w ≤ ε ^ m := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
    (by rw [hmdef, hβ'def]; exact min_le_right _ _)
  have herr := t13r_err_le hC1 hA₂ hM1 hm hηs hδ0 hδs hw0.le hws hs1
  have hMs : M ^ 2 * ε ^ m ≤ ε ^ (m / 4) * ε ^ (m / 4) := by
    rw [hMsq, ← Real.rpow_add hε, ← Real.rpow_add hε]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)
  have hKs : K * (M ^ 2 * ε ^ m) ≤ ε ^ αt := by
    have hq4 : 0 ≤ ε ^ (m / 4) := Real.rpow_nonneg hε.le _
    have h1 : K * (ε ^ (m / 4) * ε ^ (m / 4)) ≤ ε ^ (m / 4) :=
      calc K * (ε ^ (m / 4) * ε ^ (m / 4)) = K * ε ^ (m / 4) * ε ^ (m / 4) := by ring
        _ ≤ 1 * ε ^ (m / 4) := mul_le_mul_of_nonneg_right hKsmall hq4
        _ = ε ^ (m / 4) := one_mul _
    have h2 : ε ^ (m / 4) ≤ ε ^ αt := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hαtm
    calc K * (M ^ 2 * ε ^ m) ≤ K * (ε ^ (m / 4) * ε ^ (m / 4)) := mul_le_mul_of_nonneg_left hMs hK0
      _ ≤ ε ^ αt := h1.trans h2
  set BF := EpsAProp210Bad bm η ε D (fun z => ‖fderiv ℝ f z‖ ^ 2) A₂ ηt
  set B1 := EpsAProp210Bad bm η ε D (fun _ => 1) A₂ ηt
  set Bg := EpsAProp210Bad bm η ε (ball (0 : ℂ) ρ₁) (t13Layer D w) A₂ ηt
  have hsub : {ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) D f (3 * C ^ 2 * A₂) (ε ^ αt)} ⊆ B27 ∪ BF ∪ B1 ∪ Bg := by
    intro ω hω
    by_contra hcon
    have h27ω : ω ∉ B27 := fun h => hcon (Or.inl (Or.inl (Or.inl h)))
    have hFω : ω ∉ BF := fun h => hcon (Or.inl (Or.inl (Or.inr h)))
    have h1ω : ω ∉ B1 := fun h => hcon (Or.inl (Or.inr h))
    have hgω : ω ∉ Bg := fun h => hcon (Or.inr h)
    have h27' : _ := not_not.1 h27ω
    apply hω
    refine ⟨h27'.1, fun hlf H hcell fε hsol => ?_⟩
    have hen := t13_energy_le_on_event_R H hDo hDsub hC0 hbc hf hΛ hfc hM0.le hGf
      (by linarith) hρ₁1.le hδ0 hδw hw0 hA₂ hm (by positivity) hIw (h27'.2 hlf H hcell)
      (epsA_prop210Bound_of_not_mem_bad hFω hlf H hcell) (epsA_prop210Bound_of_not_mem_bad h1ω hlf H hcell)
      (epsA_prop210Bound_of_not_mem_bad hgω hlf H hcell) hsol
    rw [hΛM] at hen
    have hEfin : eucEnergy f D ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal (M ^ 2) * volume D) ?_ ?_
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDb.measure_lt_top).ne
      · calc eucEnergy f D ≤ ∫⁻ _z in D, ENNReal.ofReal (M ^ 2) := by
              refine setLIntegral_mono' hDo.measurableSet fun z hz => ENNReal.ofReal_le_ofReal ?_
              exact pow_le_pow_left₀ (norm_nonneg _) (hGf z hz) 2
          _ = ENNReal.ofReal (M ^ 2) * volume D := by rw [setLIntegral_const]
    set e := (eucEnergy f D).toReal with hedef
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    have hbound : energy (MatedCRT.graph ε (bm ω) hlf) (vFin H D) fε ≤
        3 * C ^ 2 * A₂ * e + ε ^ αt := by
      have hsplit : 3 * C ^ 2 * ((A₂ * e + ηt) + 2 * M * M * δ * (A₂ * 4 + ηt) +
          M ^ 2 * (A₂ * (C * (2 * w)) + ηt)) +
          24 * C ^ 2 * (M * (1 + C)) ^ 2 * δ ^ 2 * ((A₂ * 4 + ηt) + (A₂ * (C * (2 * w)) + ηt)) =
          3 * C ^ 2 * A₂ * e + (3 * C ^ 2 * (ηt + 2 * M * M * δ * (A₂ * 4 + ηt) +
            M ^ 2 * (A₂ * (C * (2 * w)) + ηt)) +
          24 * C ^ 2 * (M * (1 + C)) ^ 2 * δ ^ 2 * ((A₂ * 4 + ηt) + (A₂ * (C * (2 * w)) + ηt))) := by ring
      calc energy (MatedCRT.graph ε (bm ω) hlf) (vFin H D) fε ≤ _ := hen
        _ = _ := hsplit
        _ ≤ 3 * C ^ 2 * A₂ * e + K * (M ^ 2 * ε ^ m) := by rw [hK]; linarith [herr]
        _ ≤ 3 * C ^ 2 * A₂ * e + ε ^ αt := by linarith [hKs]
    calc ENNReal.ofReal (energy (MatedCRT.graph ε (bm ω) hlf) (vFin H D) fε)
        ≤ ENNReal.ofReal (3 * C ^ 2 * A₂ * e + ε ^ αt) := ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (3 * C ^ 2 * A₂) * eucEnergy f D + ENNReal.ofReal (ε ^ αt) := by
          rw [ENNReal.ofReal_add (by positivity) (Real.rpow_nonneg hε.le _),
            ENNReal.ofReal_mul (by positivity), hedef, ENNReal.ofReal_toReal hEfin]
  calc P ({ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) D f (3 * C ^ 2 * A₂) (ε ^ αt)}) ≤ P (B27 ∪ BF ∪ B1 ∪ Bg) := measure_mono hsub
    _ ≤ ((P B27 + P BF) + P B1) + P Bg :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ((ENNReal.ofReal (C27 * ηt) + ENNReal.ofReal (CP * ηt)) + ENNReal.ofReal (CP * ηt)) +
          ENNReal.ofReal (CP * ηt) :=
        add_le_add (add_le_add (add_le_add (h27 ε hεI') (h210 ε hεI' _ _ hadmF)) (h210 ε hεI' _ _ hadm1))
          (h210 ε hεI' _ _ hadmg)
    _ = ENNReal.ofReal ((C27 + 3 * CP) * ηt) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **[18] Theorem 3.2 at every real mesh from the two named real-mesh inputs**: Lemma 2.7 on `B_{ρ₁}(0)` and
Proposition 2.10 at `(ρ₁, C_b, β₂)` (threshold `A₂`, tolerance and rate exponent `α`) in their stated forms,
`ρ < ρ₁ < 1`, `1 ≤ C ≤ C_b`, `16π ≤ C_b`; class exponent `β` with `2β ≤ β₂`, `4β ≤ m := min(α, q, β₂)`, tolerance
exponent `α_t ≤ m/4`. Then `A = 3C²A₂` and the rate `C_r` is uniform over `ε ∈ (0, 1)` and `(D, f) ∈ 𝒞_C(ε^β)`. -/
theorem t13r_theorem32_of_inputs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    {ρ ρ₁ q β₂ α A₂ CP C27 Cb C β αt : ℝ}
    (hρ0 : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁1 : ρ₁ < 1) (hq : 0 < q) (hβ₂ : 0 < β₂) (hα : 0 < α)
    (hA₂ : 0 ≤ A₂) (hCP : 0 ≤ CP) (hC27 : 0 ≤ C27) (hC1 : 1 ≤ C) (hCCb : C ≤ Cb) (hCb : 16 * π ≤ Cb)
    (hβ : 0 < β) (h2β : 2 * β ≤ β₂) (h4β : 4 * β ≤ min α (min q β₂))
    (hαtm : αt ≤ min α (min q β₂) / 4)
    (h27 : ∀ ε ∈ Ioo (0 : ℝ) 1, P (EpsALemma27Bad bm η ε q ρ₁) ≤ ENNReal.ofReal (C27 * ε ^ α))
    (h210 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible ε ρ₁ Cb β₂ V g →
      P (EpsAProp210Bad bm η ε V g A₂ (ε ^ α)) ≤ ENNReal.ofReal (CP * ε ^ α)) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (D : Set ℂ) (f : ℂ → ℝ), IsOpen D → D ⊆ ball (0 : ℂ) ρ →
      (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
      BoundedConvexityWith C D → DifferentiableOn ℝ f D →
      (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
      (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
      ContinuousOn f (closure D) →
        P {ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) D f (3 * C ^ 2 * A₂) (ε ^ αt)} ≤
          ENNReal.ofReal (Cr * ε ^ α) := by
  set β' : ℝ := min q β₂ with hβ'def
  have hβ'0 : 0 < β' := lt_min hq hβ₂
  set m : ℝ := min α (min q β₂) with hmdef
  have hm0 : 0 < m := lt_min hα (lt_min hq hβ₂)
  set K : ℝ := 3 * C ^ 2 * (2 + 2 * (A₂ * 4 + 1) + 2 * A₂ * C) +
    24 * C ^ 2 * (1 + C) ^ 2 * (A₂ * 4 + 2 + 2 * A₂ * C) with hK
  let Q : ℝ → Set ℂ × (ℂ → ℝ) → Prop := fun ε i =>
    IsOpen i.1 ∧ i.1 ⊆ ball (0 : ℂ) ρ ∧
      (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier i.1)) ≤ ENNReal.ofReal (C * r)) ∧
      BoundedConvexityWith C i.1 ∧ DifferentiableOn ℝ i.2 i.1 ∧
      (∀ z ∈ i.1, ∀ w ∈ i.1, ‖fderiv ℝ i.2 z - fderiv ℝ i.2 w‖ ≤ ε ^ (-β) * dist z w) ∧
      (∀ z ∈ i.1, ‖fderiv ℝ i.2 z‖ ≤ ε ^ (-β)) ∧ ContinuousOn i.2 (closure i.1)
  let Bad : ℝ → Set ℂ × (ℂ → ℝ) → Set Ω := fun ε i =>
    {ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) i.1 i.2 (3 * C ^ 2 * A₂) (ε ^ αt)}
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, Q ε i → P (Bad ε i) ≤ ENNReal.ofReal ((C27 + 3 * CP) * ε ^ α) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
      (t13r_tendsto_rpow hq).eventually (gt_mem_nhds (show (0 : ℝ) < ρ₁ - ρ by linarith)),
      (t13r_tendsto_rpow hβ'0).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      ((t13r_tendsto_rpow (show 0 < m / 4 by positivity)).const_mul K).eventually
        (ge_mem_nhds (show K * 0 < 1 by simp))]
      with ε hε0 hεI hδρ hw2 hKsmall
    rintro ⟨D, f⟩ ⟨hDo, hDsub, hbdry, hbc, hf, hLipf, hGf, hfc⟩
    exact t13r_theorem32_step P bm η hρ0 hρρ₁ hρ₁1 hq hβ₂ hα hA₂ hCP hC27 hC1 hCCb hCb hβ h2β h4β hαtm
      hβ'def hmdef hK h27 h210 hε0 hεI hδρ hw2 hKsmall hDo hDsub hbdry hbc hf hLipf hGf hfc
  obtain ⟨Cr, hCr, hrate⟩ := t13r_rate_of_eventually hα (by positivity) hev
  refine ⟨Cr, hCr, fun ε hε D f hDo hDsub hbdry hbc hf hLipf _ hGf hfc => ?_⟩
  exact hrate ε hε (D, f) ⟨hDo, hDsub, hbdry, hbc, hf, hLipf, hGf, hfc⟩

end MatedCRTHarmonic.GMSMain
