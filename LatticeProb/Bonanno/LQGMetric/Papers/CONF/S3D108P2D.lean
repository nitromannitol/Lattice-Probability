/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P2D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2C
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7L1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightBlueprint

/-!
# CONF Lemma 3.3, Step 2: the bound (3.12) from tightness and the harmonic part (D108 P2)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, (3.12) (C:1219–1223): "By Axioms IV′ and V …
we can find a constant `C > 0`, depending only on `δ`, such that … `P[max_V sup D_{h̊^U}(u,v;·)
≤ C𝔠_r] ≥ 1/2`." CONF leaves the argument implicit; the proof goes through `D_h` (Axiom V) and a
lower bound for the harmonic part, since `D_{h̊^U} = e^{−ξ𝔥^U}·D_{h|_U}` (C:1197):

* `zb_312_of` : with `Y = (h − h_ρ(w)) − f_n` the field of Remark 1.2 (`exists_zbField`,
  `f_n = 𝔥^U` on `V`), on the events
  `{diam(K; D_h(·,·;W)) ≤ S 𝔠_r e^{ξ h_r(z)}}` (tightness, e.g. `blueprint_GMS2_4c`) and
  `{𝔥^U ≥ (h − h_ρ(w))_r(z) − A′ on W}` (harmonic part), one has
  `diam(K; D_Y(·,·;W)) ≤ S e^{ξA′} 𝔠_r`; hence the failure probabilities add.

Own routine argument (the paper's "by Axioms IV′ and V"): Weyl scaling (Axiom III) by the
constant `h_ρ(w)` and by `max(f_n, m)`, `m = (h − h_ρ(w))_r(z) − A′`, which equals `f_n` on `W`
(locality of Weyl scaling), and the comparison of internal metrics `LM.t17_internal_le_of_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **(3.12) from tightness of `D_h` and a lower bound for the harmonic part** (C:1219–1223,
C:1197). -/
theorem zb_312_of {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {ρ : ℝ} {w : ℂ} {U : Set ℂ} {hU : IsOpen U} {X : Ω → DistC}
    {V : Set ℂ} {Y : Ω → DistC} {fn : Ω → C(ℂ, ℝ)}
    (hYdef : ∀ ω, Y ω = addFun (recField h ρ w ω) (-(fn ω)))
    (hfnb : ∀ ω, ∃ M, ∀ x, |fn ω x| ≤ M)
    (hfnV : ∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      EqOn ⇑(fn ω) 𝔥 V)
    {W : Set ℂ} (hWo : IsOpen W) (hWV : W ⊆ V) (K : Set ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ)
    {S A' : ℝ} (hS : 0 ≤ S) {β₁ β₂ : ℝ≥0∞}
    (h1 : P {ω | internalDiam (D (h ω)) K W ≤
      ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤ β₁)
    (h2 : P {ω | ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U ∧
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) ∧
      ∀ u ∈ W, circleAvg (recField h ρ w ω) r z - A' ≤ 𝔥 u}ᶜ ≤ β₂) :
    P {ω | internalDiam (D (Y ω)) K W ≤
      ENNReal.ofReal (S * Real.exp (xiGamma γ * A') * c r)}ᶜ ≤ β₁ + β₂ := by
  set ξ := xiGamma γ
  have hξ : 0 ≤ ξ := (GM.xiGamma_pos hγ).le
  set g' : Ω → DistC := recField h ρ w with hg'
  have hg'G : IsWholePlaneGFF g' P := isWholePlaneGFF_recField hh ρ w
  have hgood : ∀ᵐ ω ∂P, (D (g' ω)).IsLength ∧
      (∀ (f : C(ℂ, ℝ)) (u v : ℂ),
        weylScale ξ f (D (g' ω)) u v = ENNReal.ofReal ((D (addFun (g' ω) f)).1 (u, v))) ∧
      (∀ (c' : ℝ) (u v : ℂ),
        (D (addConst (h ω) c')).1 (u, v) = Real.exp (ξ * c') * (D (h ω)).1 (u, v)) ∧
      ∀ c', circleAvg (addConst (h ω) c') r z = circleAvg (h ω) r z + c' := by
    filter_upwards [hD.length P g' (GM.Tight.isGFFPlusCont_of_wp hg'G),
      hD.weyl P g' (GM.Tight.isGFFPlusCont_of_wp hg'G),
      hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh),
      CircleAvg.ae_circleAvg_addConst hh z hr] with ω a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  set E1 := {ω | internalDiam (D (h ω)) K W ≤
      ENNReal.ofReal (S * scaleFac ξ c (h ω) r z)} with hE1
  set E2 := {ω | ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U ∧
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) ∧
      ∀ u ∈ W, circleAvg (recField h ρ w ω) r z - A' ≤ 𝔥 u} with hE2
  have hsub : {ω | internalDiam (D (Y ω)) K W ≤
      ENNReal.ofReal (S * Real.exp (ξ * A') * c r)}ᶜ ≤ᵐ[P] (E1ᶜ ∪ E2ᶜ : Set Ω) := by
    filter_upwards [hgood] with ω hg hω
    obtain ⟨hl, hw, hc, hca⟩ := hg
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hω1, 𝔥, h𝔥, hT, hlow⟩ := hcon
    apply hω
    show internalDiam (D (Y ω)) K W ≤ ENNReal.ofReal (S * Real.exp (ξ * A') * c r)
    set hρ := circleAvg (h ω) ρ w
    set m := circleAvg (g' ω) r z - A' with hm
    have hgm : circleAvg (g' ω) r z = circleAvg (h ω) r z - hρ := by
      rw [hg', recField, hca]; ring
    have hfV := hfnV ω 𝔥 h𝔥 hT
    obtain ⟨M, hM⟩ := hfnb ω
    set ft : C(ℂ, ℝ) := fn ω ⊔ ContinuousMap.const ℂ m with hft
    have hftW : ∀ x ∈ W, ξ * (-(fn ω)) x = ξ * (-ft) x := by
      intro x hx
      have : m ≤ fn ω x := by rw [hfV (hWV hx)]; exact hlow x hx
      simp [hft, ContinuousMap.sup_apply, max_eq_left this]
    -- `D_Y(·,·;W) = D_{g' − ft}(·,·;W) ≤ e^{−ξm} D_{g'}(·,·;W) = e^{−ξm − ξh_ρ} D_h(·,·;W)`
    have hcmp : ∀ u v : ℂ, (D (Y ω)).internal W u v ≤
        ENNReal.ofReal (Real.exp (-(ξ * m)) * Real.exp (-(ξ * hρ))) *
          (D (h ω)).internal W u v := by
      intro u v
      have e1 : (D (Y ω)).internal W u v = (D (addFun (g' ω) (-ft))).internal W u v := by
        rw [hYdef ω]
        exact internal_weyl_eq_of_internal_eq hWo (fun a b => (hw _ a b).symm)
          (fun a b => (hw _ a b).symm) (fun _ _ _ _ => rfl) hftW u v
      have hb2 : ∀ x, ξ * (-ft) x ≤ -(ξ * m) := by
        intro x
        have : m ≤ ft x := by simp [hft, ContinuousMap.sup_apply]
        simp only [ContinuousMap.neg_apply]; nlinarith
      have ha2 : ∀ x, -(ξ * max M m) ≤ ξ * (-ft) x := by
        intro x
        have h1 : fn ω x ≤ M := (le_abs_self _).trans (hM x)
        have : ft x ≤ max M m := by
          simp only [hft, ContinuousMap.sup_apply, ContinuousMap.const_apply]
          exact max_le_max h1 le_rfl
        simp only [ContinuousMap.neg_apply]; nlinarith
      have e2 : (D (addFun (g' ω) (-ft))).internal W u v ≤
          ENNReal.ofReal (Real.exp (-(ξ * m))) * (D (g' ω)).internal W u v :=
        LM.t17_internal_le_of_le (Real.exp_pos _)
          (fun x y => (dist_addFun_mem_Icc_of_weyl hl hw ha2 hb2 x y).2) W u v
      have e3 : D (g' ω) = (D (h ω)).smulPos (Real.exp (ξ * -hρ)) (Real.exp_pos _) := by
        apply Subtype.ext
        ext p
        show (D (addConst (h ω) (-hρ))).1 (p.1, p.2) = _
        rw [hc]; rfl
      rw [e1]
      refine e2.trans ?_
      rw [e3, ContMetric.internal_smulPos, ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_neg]
    have hk : Real.exp (-(ξ * m)) * Real.exp (-(ξ * hρ)) *
        (S * (c r * Real.exp (ξ * circleAvg (h ω) r z))) = S * Real.exp (ξ * A') * c r := by
      have e : -(ξ * m) + -(ξ * hρ) + ξ * circleAvg (h ω) r z = ξ * A' := by
        rw [hm, hgm]; ring
      calc _ = S * c r * (Real.exp (-(ξ * m)) * Real.exp (-(ξ * hρ)) *
            Real.exp (ξ * circleAvg (h ω) r z)) := by ring
        _ = S * c r * Real.exp (ξ * A') := by rw [← Real.exp_add, ← Real.exp_add, e]
        _ = _ := by ring
    calc internalDiam (D (Y ω)) K W
        ≤ ENNReal.ofReal (Real.exp (-(ξ * m)) * Real.exp (-(ξ * hρ))) *
            internalDiam (D (h ω)) K W := by
          unfold internalDiam
          refine iSup₂_le fun u hu => iSup₂_le fun v hv => (hcmp u v).trans ?_
          gcongr
          exact le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)
      _ ≤ ENNReal.ofReal (Real.exp (-(ξ * m)) * Real.exp (-(ξ * hρ))) *
            ENNReal.ofReal (S * scaleFac ξ c (h ω) r z) := by gcongr; exact hω1
      _ = ENNReal.ofReal (S * Real.exp (ξ * A') * c r) := by
          rw [← ENNReal.ofReal_mul (by positivity), scaleFac, hk]
  calc P {ω | internalDiam (D (Y ω)) K W ≤
        ENNReal.ofReal (S * Real.exp (ξ * A') * c r)}ᶜ
      ≤ P (E1ᶜ ∪ E2ᶜ) := measure_mono_ae hsub
    _ ≤ P E1ᶜ + P E2ᶜ := measure_union_le _ _
    _ ≤ β₁ + β₂ := add_le_add h1 h2

/-- **CONF Lemma 3.3, Step 2** (C:1217–1234), assembled: from the tightness of `D_h`-internal
diameters at every scale (`HT`, e.g. `blueprint_GMS2_4c` for connected `W₀ i`) and a lower bound
in probability for the harmonic part on `rV₀ + z` (`HH`, open input), there is `𝔭 > 0`,
depending only on the unit-scale configuration, with `P[∀ i, diam(rK₀ i + z; D_{h̊}(·,·;rW₀ i + z))
≤ s 𝔠_r] ≥ 𝔭` for every scale, centre and version of `h̊^{rU₀+z}`. -/
theorem zb_step2_of_tight {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {U₀ V₀ : Opens ℂ} (hU₀b : Bornology.IsBounded (U₀ : Set ℂ))
    (hU₀ne : (U₀ : Set ℂ).Nonempty) (hV₀U₀ : closure (V₀ : Set ℂ) ⊆ U₀) {ι : Type} [Fintype ι]
    {W₀ : ι → Opens ℂ} (hW₀V₀ : ∀ i, W₀ i ≤ V₀) {K₀ : ι → Set ℂ} (hK₀W₀ : ∀ i, K₀ i ⊆ W₀ i)
    {a₀ : ι → ℕ → ℂ} (ha₀ : ∀ i n, a₀ i n ∈ K₀ i) (hKa₀ : ∀ i, K₀ i ⊆ closure (range (a₀ i)))
    {S A' s : ℝ} (hS : 0 < S) (hs : 0 < s) (hc : ∀ r, 0 < r → 0 < c r)
    (HT : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (r : ℝ), 0 < r → ∀ (z : ℂ) (i : ι),
      P {ω | internalDiam (D (h ω)) (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤
        ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤
        ENNReal.ofReal (1 / (4 * (Fintype.card ι + 1))))
    (HH : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (r : ℝ), 0 < r → ∀ (z : ℂ)
      (X : Ω → DistC), IsL33ZBPart P h ρ w (affOpens r z U₀) (affOpens r z U₀).isOpen X →
      P {ω | ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) ∧
        (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
          restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
            (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) ∧
        ∀ u ∈ (affOpens r z V₀ : Set ℂ), circleAvg (recField h ρ w ω) r z - A' ≤ 𝔥 u}ᶜ ≤
        ENNReal.ofReal (1 / (4 * (Fintype.card ι + 1)))) :
    ∃ 𝔭 : ℝ, 0 < 𝔭 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ) (r : ℝ), 0 < r → ∀ (z : ℂ) (X : Ω → DistC),
        IsL33ZBPart P h ρ w (affOpens r z U₀) (affOpens r z U₀).isOpen X →
        ∃ Y : Ω → DistC, IsGFFPlusCont Y P ∧
          (∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) →
            (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
              restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
                (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
            ∀ W' : Set ℂ, IsOpen W' → W' ⊆ affOpens r z V₀ → ∀ f' : C(ℂ, ℝ), EqOn ⇑f' 𝔥 W' →
            ∀ u v : ℂ, (D (addFun (recField h ρ w ω) (-f'))).internal W' u v =
              (D (Y ω)).internal W' u v) ∧
          ENNReal.ofReal 𝔭 ≤ P {ω | ∀ i, internalDiam (D (Y ω))
              (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤ ENNReal.ofReal (s * c r)} := by
  set ξ := xiGamma γ
  have hC : 0 < S * Real.exp (ξ * A') := by positivity
  obtain ⟨𝔭, h𝔭, H𝔭⟩ := zb_step2_uniform hγ hD hU₀b hU₀ne hV₀U₀ hW₀V₀ hK₀W₀ ha₀ hKa₀ hC hs
  refine ⟨𝔭, h𝔭, ?_⟩
  intro Ω _ P _ h hh ρ w r hr z X hX
  obtain ⟨Y, fn, hYd, hfb, hfV, hYc, hW, Hℓ⟩ := H𝔭 P h hh ρ w r hr z X hX
  refine ⟨Y, hYc, hW, Hℓ (c r) (hc r hr) ?_⟩
  set n : ℕ := Fintype.card ι
  set β : ℝ := 1 / (4 * (n + 1)) with hβ
  have hβ0 : 0 ≤ β := by positivity
  set E := {ω | ∀ i, internalDiam (D (Y ω)) (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤
    ENNReal.ofReal (S * Real.exp (ξ * A') * c r)} with hE
  have hi : ∀ i, P {ω | internalDiam (D (Y ω)) (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤
      ENNReal.ofReal (S * Real.exp (ξ * A') * c r)}ᶜ ≤ ENNReal.ofReal (2 * β) := by
    intro i
    have h2 := HH P h hh ρ w r hr z X hX
    have h2' : P {ω | ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (affOpens r z U₀) ∧
        (∀ φ : TestOn (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen),
          restrictTo (toOpens (affOpens r z U₀) (affOpens r z U₀).isOpen)
            (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) ∧
        ∀ u ∈ (affOpens r z (W₀ i) : Set ℂ), circleAvg (recField h ρ w ω) r z - A' ≤ 𝔥 u}ᶜ ≤
        ENNReal.ofReal β := by
      refine le_trans (measure_mono ?_) h2
      intro ω hω hω'
      apply hω
      obtain ⟨𝔥, a1, a2, a3⟩ := hω'
      exact ⟨𝔥, a1, a2, fun u hu => a3 u (hW₀V₀ i hu)⟩
    have key := zb_312_of hγ hD hh hYd hfb hfV (affOpens r z (W₀ i)).isOpen
      (fun x hx => hW₀V₀ i hx) (affFwd r z '' K₀ i) hr z hS.le
      (HT P h hh r hr z i) h2'
    refine key.trans ?_
    rw [← ENNReal.ofReal_add hβ0 hβ0]; apply ENNReal.ofReal_le_ofReal; linarith
  have hEc : P Eᶜ ≤ ENNReal.ofReal (1 / 2) := by
    have e : Eᶜ = ⋃ i, {ω | internalDiam (D (Y ω)) (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤
        ENNReal.ofReal (S * Real.exp (ξ * A') * c r)}ᶜ := by
      ext ω; simp [hE, not_forall]
    rw [e]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hβ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [show (n : ℝ) * (2 * (1 / (4 * (n + 1)))) = n / (2 * (n + 1)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h1 : (1 : ℝ≥0∞) ≤ P E + P Eᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self E]
    exact measure_union_le _ _
  have h3 : (1 : ℝ≥0∞) ≤ P E + ENNReal.ofReal (1 / 2) := h1.trans (add_le_add le_rfl hEc)
  have h4 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2) ≤ P E := by
    rw [tsub_le_iff_right]; exact h3
  have h5 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  rw [h5] at h4
  exact h4

/-- **The tightness input `HT` of `zb_step2_of_tight`** from `blueprint_GMS2_4c` (GM Axiom V,
internal diameters; D14), uniformly over a finite family of connected bounded `W₀ i ⊇ K₀ i`. -/
theorem exists_tight_family {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {ι : Type} [Fintype ι] {W₀ : ι → Opens ℂ}
    (hWb : ∀ i, Bornology.IsBounded (W₀ i : Set ℂ)) (hWc : ∀ i, IsPreconnected (W₀ i : Set ℂ))
    {K₀ : ι → Set ℂ} (hKc : ∀ i, IsCompact (K₀ i)) (hK₀W₀ : ∀ i, K₀ i ⊆ W₀ i) {β : ℝ}
    (hβ : 0 < β) :
    ∃ S : ℝ, 0 < S ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (r : ℝ), 0 < r → ∀ (z : ℂ) (i : ι),
      P {ω | internalDiam (D (h ω)) (affFwd r z '' K₀ i) (affOpens r z (W₀ i)) ≤
        ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤ ENNReal.ofReal β := by
  have H := fun i => GM.Tight.blueprint_GMS2_4c γ hγ hγ2 D c hD (W₀ i) (K₀ i) (W₀ i).isOpen (hWb i)
    (hWc i) (hKc i) (hK₀W₀ i) (1 - β) (by linarith)
  choose S hS HS using H
  have hsum : 0 ≤ ∑ i, S i := Finset.sum_nonneg fun j _ => (hS j).le
  refine ⟨∑ i, S i + 1, by linarith, ?_⟩
  intro Ω _ P _ h hh r hr z i
  have hSi : S i ≤ ∑ j, S j + 1 := by
    have := Finset.single_le_sum (f := S) (fun j _ => (hS j).le) (Finset.mem_univ i)
    linarith
  have hsf : ∀ ω, 0 ≤ scaleFac (xiGamma γ) c (h ω) r z := fun ω =>
    mul_nonneg (hD.tightness.1 r hr).le (Real.exp_pos _).le
  have hr0 : r ≠ 0 := hr.ne'
  have eK : scaleSet r z (K₀ i) = affFwd r z '' K₀ i := by rw [scaleSet, affFwd_eq]
  have eW : scaleSet r z (W₀ i) = (affOpens r z (W₀ i) : Set ℂ) := by
    rw [scaleSet, ← affFwd_eq, image_affFwd_eq hr0]; rfl
  have key := HS i P h hh z r hr
  rw [eK, eW, sub_sub_cancel] at key
  refine le_trans (measure_mono ?_) key
  intro ω hω hω'
  apply hω
  exact hω'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hSi (hsf ω)))

end LQGMetric.CONF
