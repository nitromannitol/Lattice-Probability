/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412jEDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iCond
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3GeoA

/-!
# CONF l. 1260: `E_r(z)` is determined by the field near `cl B_{5r}(z)` (`P412iEDet`)

Source: CONF (arXiv:1905.00381, `confluence-final.tex`) l. 1133–1145 (the events `E^U_r(z)`,
`E_r(z)`) and l. 1260 ("Since `E_r(z)` is determined by `h|_{A_{2r,5r}(z)}`"), read as in
`P412iEDet` (DV-EDet): a.s. an event of `σ(h|_V)` for every open `V ⊇ cl B_{5r}(z)`.

* condition 1 (`p412j_cond1`): `D_h(∂B_{2r}, ∂B_{3r})` is a countable infimum of `D_h(·,·;V)` at
  dense pairs (`L32M.setDist_eq_iInf_dense`), a function of `h|_V` (Axiom II), and `h_r(z)` is
  `σ(h|_V)`-measurable (`measurable_circleAvg_fieldSigma`) — the method of DFGPS L3.2
  (`L32M.aeEventIn_annEvent`);
* condition 2 (`p412j_cond2`): the internal diameters in `A_{2r,5r}(z)` are countable suprema
  (`L32M.internalDiam_eq_iSup`), or identically `∞` when the square leaves the annulus;
* condition 3 (`p412j_cond3`): `harmPart` is continuous on `U` for every `ω` (harmonic, or the junk
  `0`), so the condition is a countable intersection over a dense sequence of `U_{δr/4}`; each
  `𝔥^U(u) − h_r(z)` is a.s. a `σ(h|_V)`-measurable variable by the **locality of the harmonic
  part** `P412jHarmLoc` (hypothesis, see below);
* `p412j_EDet`, `p412j_EDetAll`: `P412iEDet`, `P412iEDetAll` from `P412jHarmLoc`.

`P412jHarmLoc` (not proved here, reported): for a whole-plane GFF `h` (any additive constant), an
open bounded `U` and an open `V ⊇ cl U`, `𝔥^U(u) − h_ρ(w)` (`∂B_ρ(w) ⊆ V`) is a.s. equal to a
`σ(h|_V)`-measurable variable. This is the Markov property in its "harmonic extension of the
boundary values" form (Sheffield, *Gaussian free fields for mathematicians*, §2.6; Berestycki–Powell
arXiv:2404.16642, Thm 1.52): `𝔥^U` is the harmonic extension of `h|_{∂U}`, determined by `h` on
any neighbourhood of `∂U`; `IsHarmPart` conditions on all of `h|_{ℂ∖U}`, and the project's LM
Lemma 2.1 (`lmLem2_1`, `markov_normAt`) gives only `σ(h|_{ℂ∖U})`-determinedness, not the
localisation to `V ∖ U`, and only for normalized fields (here the additive constant is arbitrary,
which is why the difference with `h_ρ(w)` is taken).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **Locality of the harmonic part** (missing GFF input, see the module docstring): for an open
bounded `U`, an open `V ⊇ cl U`, a circle `∂B_ρ(w) ⊆ V` and `u ∈ U`, `𝔥^U(u) − h_ρ(w)` is a.s. a
`σ(h|_V)`-measurable variable. -/
def P412jHarmLoc : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (U V : Set ℂ) (hV : IsOpen V), IsOpen U → Bornology.IsBounded U →
    closure U ⊆ V → ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → sphere w ρ ⊆ V → ∀ u ∈ U,
    ∃ G : Ω → ℝ, Measurable[fieldSigma h (toOpens V hV)] G ∧
      (fun ω => harmPart P h U ω u - circleAvg (h ω) ρ w) =ᵐ[P] G

theorem p412j_aeEventIn_inter {Ω : Type} {m0 m : MeasurableSpace Ω} {P : @Measure Ω m0}
    {E₁ E₂ : Set Ω} (h₁ : @AEEventIn Ω m0 P m E₁) (h₂ : @AEEventIn Ω m0 P m E₂) :
    @AEEventIn Ω m0 P m (E₁ ∩ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∩ F₂, MeasurableSet.inter (m := m) hF₁ hF₂, he₁.inter he₂⟩

theorem p412j_aeEventIn_const {Ω : Type} {m0 m : MeasurableSpace Ω} {P : @Measure Ω m0}
    (q : Prop) : @AEEventIn Ω m0 P m {_ω : Ω | q} := by
  by_cases hq : q
  · exact ⟨univ, @MeasurableSet.univ Ω m, by simp [hq]⟩
  · exact ⟨∅, @MeasurableSet.empty Ω m, by simp [hq]⟩

variable {Ω : Type} [MeasurableSpace Ω]

/-- the harmonic part is continuous on `U` for every `ω` -/
theorem p412j_harmPart_contAt (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) (ω : Ω) {u : ℂ}
    (hu : u ∈ U) : ContinuousAt (harmPart P h U ω) u := by
  unfold harmPart
  split_ifs with hH
  · exact (hH.choose_spec.1 ω u hu).1.continuousAt
  · exact continuousAt_const

theorem p412j_isClosed_confSq (ε : ℝ) (z : ℂ) (k : ℤ × ℤ) : IsClosed (confSq ε z k) := by
  have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have e : confSq ε z k = ({w : ℂ | z.re + k.1 * ε ≤ w.re} ∩ {w : ℂ | w.re ≤ z.re + (k.1 + 1) * ε})
      ∩ ({w : ℂ | z.im + k.2 * ε ≤ w.im} ∩ {w : ℂ | w.im ≤ z.im + (k.2 + 1) * ε}) := by
    ext w; simp only [confSq, mem_inter_iff, mem_setOf_eq, and_assoc]
  rw [e]
  exact ((isClosed_le continuous_const hre).inter (isClosed_le hre continuous_const)).inter
    ((isClosed_le continuous_const him).inter (isClosed_le him continuous_const))

theorem p412j_isOpen_confU (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : IsOpen (confU r δ z T) :=
  (annulus z (3 * r) (4 * r)).isOpen.sdiff
    (T.finite_toSet.isClosed_biUnion fun k _ => p412j_isClosed_confSq _ _ _)

theorem p412j_confU_subset (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confU r δ z T ⊆ closedBall z (4 * r) := fun w hw => by
  have := hw.1.2
  rw [mem_closedBall, dist_eq_norm]; exact this.le

section Conditions
variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c₀)
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
  (ξ : ℝ) (cc : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (V : Set ℂ) (hV : IsOpen V)
  (hBV : closedBall z (5 * r) ⊆ V)
include hD hh hr hBV

/-- `h_r(z)` is `σ(h|_V)`-measurable -/
theorem p412j_meas_circleAvg :
    Measurable[fieldSigma h (toOpens V hV)] fun ω => circleAvg (h ω) r z := by
  refine (measurable_circleAvg_fieldSigma h r z (show (0 : ℝ) < r by linarith)).mono
    (fieldSigma_mono h ?_) le_rfl
  intro w hw
  obtain ⟨y, hy, hwy⟩ := mem_thickening_iff.1 hw
  have hyz : dist y z = r := by rw [mem_sphere.1 hy, abs_of_pos hr]
  refine hBV (mem_closedBall.2 ?_)
  linarith [dist_triangle w y z]

/-- condition 1 of `E^U_r(z)` (CONF l. 1134) -/
theorem p412j_cond1 (c : ℝ) :
    AEEventIn P (fieldSigma h (toOpens V hV)) {ω | ENNReal.ofReal (c * scaleFac ξ cc (h ω) r z) ≤
      setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} := by
  have hgp := Tight.isGFFPlusCont_of_wp hh
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp (toOpens V hV)
  obtain ⟨a, haS, haD⟩ := DFGPS.L32M.exists_denseSeq (S := sphere z (2 * r))
    (NormedSpace.sphere_nonempty.2 (by linarith))
  obtain ⟨b, hbS, hbD⟩ := DFGPS.L32M.exists_denseSeq (S := sphere z (3 * r))
    (NormedSpace.sphere_nonempty.2 (by linarith))
  have hsub : ∀ w : ℂ, 2 * r ≤ ‖w - z‖ → ‖w - z‖ ≤ 3 * r → w ∈ V := fun w _ h2 =>
    hBV (by rw [mem_closedBall, dist_eq_norm]; linarith)
  have hS : ∀ {ρ : ℝ}, ρ ≤ 5 * r → sphere z ρ ⊆ V := fun hρ w hw =>
    hBV (mem_closedBall.2 ((mem_sphere.1 hw).le.trans hρ))
  set W : Ω → (ℕ × ℕ → ℝ≥0∞) × ℝ := fun ω =>
    (fun q => Φ (restrictTo (toOpens V hV) (h ω)) (a q.1) (b q.2), circleAvg (h ω) r z)
  have hW : Measurable[fieldSigma h (toOpens V hV)] W := by
    refine Measurable.prodMk ?_ (p412j_meas_circleAvg hD P h hh hr z V hV hBV)
    have hG : Measurable fun x : DistOn (toOpens V hV) => fun q : ℕ × ℕ => Φ x (a q.1) (b q.2) :=
      measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
    exact hG.comp (Measurable.of_comap_le le_rfl)
  set S : Set ((ℕ × ℕ → ℝ≥0∞) × ℝ) :=
    {x | ENNReal.ofReal (c * (cc r * Real.exp (ξ * x.2))) ≤ ⨅ q, x.1 q}
  have hSm : MeasurableSet S := by
    have h1 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × ℝ =>
        ENNReal.ofReal (c * (cc r * Real.exp (ξ * x.2))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_snd))))
    have h2 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × ℝ => ⨅ q, x.1 q :=
      Measurable.iInf fun q => (measurable_pi_apply q).comp measurable_fst
    exact measurableSet_le h1 h2
  refine ⟨W ⁻¹' S, hW hSm, ?_⟩
  filter_upwards [hΦae, hD.length P h hgp] with ω h1 hl
  have e : setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r)) =
      ⨅ q : ℕ × ℕ, Φ (restrictTo (toOpens V hV) (h ω)) (a q.1) (b q.2) := by
    rw [DFGPS.L32M.setDist_eq_iInf_dense (D (h ω)) hl hV (by linarith) hsub haS hbS haD hbD]
    exact iInf_congr fun q => h1 _ (hS (by linarith) (haS _)) _ (hS (by linarith) (hbS _))
  change (ENNReal.ofReal (c * scaleFac ξ cc (h ω) r z) ≤
    setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))) = (W ω ∈ S)
  rw [e]; rfl

/-- condition 2 of `E^U_r(z)` (CONF l. 1135–1137), one square -/
theorem p412j_cond2_sq (c δ : ℝ) (k : ℤ × ℤ) :
    AEEventIn P (fieldSigma h (toOpens V hV)) {ω |
      internalDiam (D (h ω)) (confSq (δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
        ENNReal.ofReal (c * scaleFac ξ cc (h ω) r z)} := by
  set Q := confSq (δ * r) z k
  set A := annulus z (2 * r) (5 * r)
  by_cases hQ : Q.Nonempty ∧ Q ⊆ (A : Set ℂ)
  · have hgp := Tight.isGFFPlusCont_of_wp hh
    have hAV : A ≤ toOpens V hV := fun w hw => hBV (mem_closedBall.2 (by
      rw [dist_eq_norm]; exact hw.2.le))
    obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp A
    obtain ⟨a, haS, haD⟩ := DFGPS.L32M.exists_denseSeq hQ.1
    set W : Ω → (ℕ × ℕ → ℝ≥0∞) × ℝ := fun ω =>
      (fun q => Φ (restrictTo A (h ω)) (a q.1) (a q.2), circleAvg (h ω) r z)
    have hW : Measurable[fieldSigma h (toOpens V hV)] W := by
      refine Measurable.prodMk ?_ (p412j_meas_circleAvg hD P h hh hr z V hV hBV)
      have hG : Measurable fun x : DistOn A => fun q : ℕ × ℕ => Φ x (a q.1) (a q.2) :=
        measurable_pi_iff.2 fun q =>
          (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
      exact (hG.comp (Measurable.of_comap_le le_rfl)).mono (fieldSigma_mono h hAV) le_rfl
    set S : Set ((ℕ × ℕ → ℝ≥0∞) × ℝ) :=
      {x | ⨆ q, x.1 q ≤ ENNReal.ofReal (c * (cc r * Real.exp (ξ * x.2)))}
    have hSm : MeasurableSet S := by
      have h1 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × ℝ =>
          ENNReal.ofReal (c * (cc r * Real.exp (ξ * x.2))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.mul
          (Real.measurable_exp.comp (measurable_const.mul measurable_snd))))
      have h2 : Measurable fun x : (ℕ × ℕ → ℝ≥0∞) × ℝ => ⨆ q, x.1 q :=
        Measurable.iSup fun q => (measurable_pi_apply q).comp measurable_fst
      exact measurableSet_le h2 h1
    refine ⟨W ⁻¹' S, hW hSm, ?_⟩
    filter_upwards [hΦae, hD.length P h hgp] with ω h1 hl
    have e : internalDiam (D (h ω)) Q A =
        ⨆ q : ℕ × ℕ, Φ (restrictTo A (h ω)) (a q.1) (a q.2) := by
      rw [DFGPS.L32M.internalDiam_eq_iSup (D (h ω)) hl A.isOpen hQ.2 haS haD]
      exact iSup_congr fun q => h1 _ (hQ.2 (haS _)) _ (hQ.2 (haS _))
    change (internalDiam (D (h ω)) Q A ≤ ENNReal.ofReal (c * scaleFac ξ cc (h ω) r z)) =
      (W ω ∈ S)
    rw [e]; rfl
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

/-- condition 3 of `E^U_r(z)` (CONF l. 1138–1141), from the locality of the harmonic part -/
theorem p412j_cond3 (hHL : P412jHarmLoc) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {U V : Set ℂ} (hV : IsOpen V) (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUV : closure U ⊆ V) {ρ : ℝ} {w : ℂ} (hρ : 0 < ρ)
    (hS : sphere w ρ ⊆ V) (ε A : ℝ) :
    AEEventIn P (fieldSigma h (toOpens V hV)) {ω | ∀ u ∈ innerPart U ε,
      |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} := by
  by_cases hne : (innerPart U ε).Nonempty
  swap
  · have e : {ω | ∀ u ∈ innerPart U ε, |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} =
        {_ω | True} := by
      ext ω
      simp only [not_nonempty_iff_eq_empty.1 hne, mem_empty_iff_false, IsEmpty.forall_iff,
        forall_const, mem_setOf_eq, implies_true]
    rw [e]; exact p412j_aeEventIn_const True
  obtain ⟨q, hqS, hqD⟩ := DFGPS.L32M.exists_denseSeq hne
  have hq : ∀ n, q n ∈ U := fun n => (hqS n).1
  choose G hG hGe using fun n => hHL P h hh U V hV hUo hUb hUV ρ w hρ hS (q n) (hq n)
  have key : {ω | ∀ u ∈ innerPart U ε, |harmPart P h U ω u - circleAvg (h ω) ρ w| ≤ A} =
      ⋂ n, {ω | |harmPart P h U ω (q n) - circleAvg (h ω) ρ w| ≤ A} := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter]
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

/-- `E^U_r(z)` is a.s. an event of `σ(h|_V)`, `V ⊇ cl B_{5r}(z)` -/
theorem p412j_confEU (hHL : P412jHarmLoc) {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ) (p : CONFParams) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (V : Set ℂ) (hV : IsOpen V) (hBV : closedBall z (5 * r) ⊆ V)
    (T : Finset (ℤ × ℤ)) :
    AEEventIn P (fieldSigma h (toOpens V hV)) (confEU ξ cc D P h p r z T) := by
  have e : confEU ξ cc D P h p r z T =
      {ω | ENNReal.ofReal (p.c * scaleFac ξ cc (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))} ∩
      ((⋂ k : confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)), {ω |
        internalDiam (D (h ω)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
          ENNReal.ofReal (p.c / 100 * scaleFac ξ cc (h ω) r z)}) ∩
      {ω | ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
        |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A}) := by
    ext ω
    simp only [confEU, mem_setOf_eq, mem_inter_iff, mem_iInter, Subtype.forall]
  rw [e]
  have h4 : closedBall z (4 * r) ⊆ V := (closedBall_subset_closedBall (by linarith)).trans hBV
  refine p412j_aeEventIn_inter (p412j_cond1 hD P h hh ξ cc hr z V hV hBV p.c)
    (p412j_aeEventIn_inter (gm_aeEventIn_iInter fun k =>
      p412j_cond2_sq hD P h hh ξ cc hr z V hV hBV (p.c / 100) p.δ k)
    (p412j_cond3 hHL P h hh hV (p412j_isOpen_confU r p.δ z T)
      (isBounded_closedBall.subset (p412j_confU_subset r p.δ z T))
      ((closure_minimal (p412j_confU_subset r p.δ z T) isClosed_closedBall).trans h4) hr
      ((sphere_subset_closedBall).trans ((closedBall_subset_closedBall (by linarith)).trans h4))
      _ _))

/-- `E_r(z)` is a.s. an event of `σ(h|_V)`, `V ⊇ cl B_{5r}(z)` -/
theorem p412j_confE (hHL : P412jHarmLoc) {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ) (p : CONFParams) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (V : Set ℂ) (hV : IsOpen V) (hBV : closedBall z (5 * r) ⊆ V) :
    AEEventIn P (fieldSigma h (toOpens V hV)) (confE ξ cc D P h p r z) := by
  have e : confE ξ cc D P h p r z = ⋂ T : {T : Finset (ℤ × ℤ) //
      ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))},
      confEU ξ cc D P h p r z T.1 := by
    ext ω
    simp only [confE, mem_iInter, Subtype.forall]
  rw [e]
  exact gm_aeEventIn_iInter fun T => p412j_confEU hHL hD P h hh ξ cc p hr z V hV hBV T.1

/-- **CONF l. 1260** (`P412iEDet`) from the locality of the harmonic part -/
theorem p412j_EDet (hHL : P412jHarmLoc) {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ) (p : CONFParams) :
    P412iEDet ξ cc D P h p := fun _ hr z V hV hBV =>
  p412j_confE hHL hD P h hh ξ cc p hr z V hV hBV

/-- **CONF l. 1260** on every probability space (`P412iEDetAll`) from the locality of the
harmonic part -/
theorem p412j_EDetAll (hHL : P412jHarmLoc) {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (p : CONFParams) : P412iEDetAll γ D c₀ p :=
  fun P _ h hh => p412j_EDet hHL hD P h hh _ _ p

end LQGMetric.GM
