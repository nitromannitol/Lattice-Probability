/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L33CM
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.StrongWeak
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas

/-!
# CONF Lemma 3.3, Step 2: the bump shift (D108 packet P2)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, proof of Lemma 3.3, Step 2 (C:1226–1231):
"Let `f := ξ⁻¹(log C − log(c e^{−ξA}/100)) g`. By Axiom III, if the event in (3.12) occurs, then
`G^U` occurs with `h̊^U − f` in place of `h̊^U`. By a standard calculation for the GFF, the laws of
`h̊^U` and `h̊^U − f` are mutually absolutely continuous and the law of the Radon–Nikodym derivative
depends only on the Dirichlet energy of `f` … It follows that `P[G^U]` is bounded below by a
constant depending only on [the Dirichlet energy]."

To make "`G^U` occurs with `h̊^U − f` in place of `h̊^U`" formal one needs a *single* measurable
functional `F` of the field on `W` which computes the internal metric both for the field and for
the shifted field (Axiom II gives a functional per field). We obtain it by applying Axiom II once
to the field `Y + β b` on `Ω × Bool` (`β` a fair coin; own routine device): `locality_pair`.
Then:

* `internal_addFun_eq_of_eqOn` : Weyl scaling by a continuous `b = L` on `W` multiplies
  `D(·,·;W)` by `e^{ξL}` (Axiom III + locality of Weyl scaling, `internal_weyl_eq_of_internal_eq`);
* `zb_step2_shift` : **the bump step of C:1226–1231**: for `Y` a GFF plus continuous function
  whose restriction to `W` is a.s. the zero-boundary GFF `X` of `U ⊇ W`, `f ∈ C_c^∞(U)` with
  `f = L` on `W`, and `K ⊆ W`,
  `P[diam(K; D_Y(·,·;W)) ≤ e^{−ξL} t]² · e^{−(f,f)_∇} ≤ P[diam(K; D_Y(·,·;W)) ≤ t]`
  (with `zb_lower_of_shift`, the Cameron–Martin bound of S3L33CM).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

lemma p2_ofCont_add (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

lemma p2_addFun_zero (g : DistC) : addFun g 0 = g := by
  have : ofCont 0 = 0 := by ext φ; simp [ofCont]
  simp [addFun, this]

/-- **Axiom II with a common functional for `Y` and `Y + b`** (own routine device: Axiom II for
the field `Y + β b` on `Ω × Bool`, `β` a fair coin). -/
theorem locality_pair {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → DistC}
    (hY : IsGFFPlusCont Y P) (b : C(ℂ, ℝ)) (V : Opens ℂ) :
    ∃ F : DistOn V → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧ ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ y ∈ V,
      (D (Y ω)).internal V z y = F (restrictTo V (Y ω)) z y ∧
      (D (addFun (Y ω) b)).internal V z y = F (restrictTo V (addFun (Y ω) b)) z y := by
  obtain ⟨hYm, f₀, hf₀, hw⟩ := hY
  set sel : Bool → C(ℂ, ℝ) := fun β => cond β b 0 with hsel
  have hmf : ∀ β : Bool, Measurable fun ω : Ω => (ω, β) :=
    fun β => measurable_id.prodMk measurable_const
  set P' : Measure (Ω × Bool) :=
    (2 : ℝ≥0∞)⁻¹ • (P.map (fun ω => (ω, false)) + P.map (fun ω => (ω, true))) with hP'
  have hhalf : ∀ a : ℝ≥0∞, (2 : ℝ≥0∞)⁻¹ * (a + a) = a := fun a => by
    rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hfst : P'.map Prod.fst = P := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs, hP', Measure.smul_apply, Measure.add_apply,
      Measure.map_apply (hmf false) (measurable_fst hs),
      Measure.map_apply (hmf true) (measurable_fst hs)]
    simp only [preimage_preimage, preimage_id', smul_eq_mul]
    exact hhalf _
  have : IsProbabilityMeasure P' := by
    constructor
    have h1 : P' univ = (P'.map Prod.fst) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    rw [h1, hfst, measure_univ]
  have hae : ∀ {p : Ω × Bool → Prop}, (∀ᵐ q ∂P', p q) → ∀ β, ∀ᵐ ω ∂P, p (ω, β) := by
    intro p hp β
    rw [hP', Measure.ae_ennreal_smul_measure_iff (by norm_num), ae_add_measure_iff] at hp
    cases β
    · exact ae_of_ae_map (hmf false).aemeasurable hp.1
    · exact ae_of_ae_map (hmf true).aemeasurable hp.2
  set Y' : Ω × Bool → DistC := fun q => addFun (Y q.1) (sel q.2) with hY'
  have hselm : Measurable fun q : Ω × Bool => sel q.2 :=
    (measurable_of_countable sel).comp measurable_snd
  have hY'c : IsGFFPlusCont Y' P' := by
    refine ⟨measurable_addFun.comp ((hYm.comp measurable_fst).prodMk hselm),
      fun q => f₀ q.1 + sel q.2, ?_, ?_⟩
    · exact ContinuousMap.measurable_iff_eval.2 fun x =>
        ((ContinuousMap.measurable_iff_eval.1 hf₀ x).comp measurable_fst).add
          ((ContinuousMap.measurable_iff_eval.1 hselm x))
    · have e : (fun q => Y' q - ofCont (f₀ q.1 + sel q.2)) =
          (fun ω => Y ω - ofCont (f₀ ω)) ∘ Prod.fst := by
        funext q
        simp only [hY', addFun, p2_ofCont_add, Function.comp_apply]
        abel
      rw [e]
      refine DFGPS.L217.isWholePlaneGFF_of_map_eq (hw.measurable.comp measurable_fst) hw ?_
      rw [← Measure.map_map hw.measurable measurable_fst, hfst]
  obtain ⟨F, hFm, hF⟩ := hD.locality P' Y' hY'c V
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hae hF false, hae hF true] with ω h0 h1 z hz y hy
  have e0 : Y' (ω, false) = Y ω := p2_addFun_zero _
  have e1 : Y' (ω, true) = addFun (Y ω) b := rfl
  refine ⟨?_, ?_⟩
  · have := h0 z hz y hy; rwa [e0] at this
  · have := h1 z hz y hy; rwa [e1] at this

/-- **Weyl scaling by a function constant on `W`**: if `b = L` on the open set `W`, then
`D_{k+b}(·,·;W) = e^{ξL} D_k(·,·;W)` (Axiom III and the locality of Weyl scaling). -/
theorem internal_addFun_eq_of_eqOn {ξ : ℝ} {D : DistC → ContMetric} {k : DistC}
    (hl : (D k).IsLength)
    (hw : ∀ (f : C(ℂ, ℝ)) (z w : ℂ),
      weylScale ξ f (D k) z w = ENNReal.ofReal ((D (addFun k f)).1 (z, w)))
    {W : Set ℂ} (hW : IsOpen W) {b : C(ℂ, ℝ)} {L : ℝ} (hb : ∀ x ∈ W, b x = L) (u v : ℂ) :
    (D (addFun k b)).internal W u v = ENNReal.ofReal (Real.exp (ξ * L)) * (D k).internal W u v := by
  have e1 := internal_weyl_eq_of_internal_eq (ξ := ξ) hW (fun x y => (hw b x y).symm)
    (fun x y => (hw (ContinuousMap.const ℂ L) x y).symm) (fun _ _ _ _ => rfl)
    (fun x hx => by rw [hb x hx]; rfl) u v
  have hc := dist_addConst_of_weyl hl hw L
  have e2 : D (addConst k L) = (D k).smulPos (Real.exp (ξ * L)) (Real.exp_pos _) := by
    apply Subtype.ext
    ext p
    show (D (addConst k L)).1 (p.1, p.2) = _
    rw [hc]; rfl
  rw [e1, show addFun k (ContinuousMap.const ℂ L) = addConst k L from rfl, e2,
    ContMetric.internal_smulPos]

/-- restriction `𝒟'(U) → 𝒟'(W)` for `W ⊆ U` -/
def resUW (U W : Opens ℂ) (x : DistOn U) : DistOn W :=
  x.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := U))

lemma measurable_resUW (U W : Opens ℂ) : Measurable (resUW U W) :=
  measurable_distOn_iff.2 fun _ => measurable_distOn_apply _

lemma resUW_restrictTo {U W : Opens ℂ} (hWU : W ≤ U) (k : DistC) :
    resUW U W (restrictTo U k) = restrictTo W k := by
  ext φ
  show k _ = k _
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, hWU]

lemma restrictTo_add' (W : Opens ℂ) (k k' : DistC) :
    restrictTo W (k + k') = restrictTo W k + restrictTo W k' := rfl

/-- **The bump step of CONF Lemma 3.3, Step 2** (C:1226–1231), for a countable family of
pairs `K i ⊆ W i ⊆ U` (the components in the event `G^U`). `Y` is a GFF plus a continuous
function whose restriction to each `W i` is a.s. that of `X`, `X|_U` a zero-boundary GFF on `U`;
`f ∈ C_c^∞(U)` equals the constant `L` on every `W i`. Then
`P[∀ i, diam(K i; D_Y(·,·;W i)) ≤ e^{−ξL} t]² · e^{−(f,f)_∇} ≤ P[∀ i, diam(K i; D_Y(·,·;W i)) ≤ t]`. -/
theorem zb_step2_shift {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → DistC}
    (hY : IsGFFPlusCont Y P) {U : Opens ℂ} (hUb : Bornology.IsBounded (U : Set ℂ))
    (hne : (U : Set ℂ).Nonempty) {X : Ω → DistC}
    (hzb : IsZeroBoundaryGFF U (fun ω => restrictTo U (X ω)) P) {ι : Type} [Countable ι]
    {W : ι → Opens ℂ} (hWU : ∀ i, W i ≤ U)
    (hres : ∀ᵐ ω ∂P, ∀ i, restrictTo (W i) (Y ω) = restrictTo (W i) (X ω))
    (f : MarkovZB.zsSub (U : Set ℂ)) {L : ℝ} (hfL : ∀ i, ∀ x ∈ (W i : Set ℂ), f.1 x = L)
    {K : ι → Set ℂ} (hKW : ∀ i, K i ⊆ W i) {a : ι → ℕ → ℂ} (haK : ∀ i n, a i n ∈ K i)
    (hKa : ∀ i, K i ⊆ closure (range (a i))) (t : ℝ≥0∞) :
    P {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤
        ENNReal.ofReal (Real.exp (-(xiGamma γ * L))) * t} ^ 2 *
        ENNReal.ofReal (Real.exp (-QuantumZipper.dirichletEnergyOn (U : Set ℂ) f.1)) ≤
      P {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤ t} := by
  set ξ := xiGamma γ
  have hf2 : f.1 ∈ QuantumZipper.zeroSpace (U : Set ℂ) := f.2
  set b : C(ℂ, ℝ) := ⟨f.1, hf2.1.continuous⟩ with hb
  set G : DistOn U := restrictTo U (ofCont b) with hGdef
  have hG : ∀ φ : TestOn U, G φ = ∫ x, f.1 x * φ x := by
    intro φ
    show ofCont b _ = _
    rw [ofCont_apply]
    congr 1; funext x
    simp [TestFunction.monoCLM_apply, hb, mul_comm]
  choose F hFm hF using fun i => locality_pair hD hY b (W i)
  set A : Set (DistOn U) :=
    {x | ∀ i, ∀ p : ℕ × ℕ, F i (resUW U (W i) x) (a i p.1) (a i p.2) ≤ t} with hAdef
  have hA : MeasurableSet A := by
    rw [hAdef, Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun p => measurableSet_le ?_ measurable_const
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((hFm i).comp (measurable_resUW U (W i))))
  have key := zb_lower_of_shift hUb hne hzb f hG hA
  have hgood : ∀ᵐ ω ∂P, (D (Y ω)).IsLength ∧
      (∀ (g : C(ℂ, ℝ)) (z w : ℂ),
        weylScale ξ g (D (Y ω)) z w = ENNReal.ofReal ((D (addFun (Y ω) g)).1 (z, w))) ∧
      (∀ i, ∀ z ∈ W i, ∀ y ∈ W i, (D (Y ω)).internal (W i) z y = F i (restrictTo (W i) (Y ω)) z y ∧
        (D (addFun (Y ω) b)).internal (W i) z y =
          F i (restrictTo (W i) (addFun (Y ω) b)) z y) ∧
      ∀ i, restrictTo (W i) (Y ω) = restrictTo (W i) (X ω) := by
    filter_upwards [hD.length P Y hY, hD.weyl P Y hY, ae_all_iff.2 hF, hres] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- the unshifted event
  have hR : (fun ω => restrictTo U (X ω)) ⁻¹' A ≤ᵐ[P]
      {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤ t} := by
    filter_upwards [hgood] with ω hg hω i
    obtain ⟨hl, -, hloc, hrs⟩ := hg
    rw [DFGPS.L32M.internalDiam_eq_iSup (D (Y ω)) hl (W i).isOpen (hKW i) (haK i) (hKa i)]
    refine iSup_le fun p => ?_
    have := hω i p
    simp only [resUW_restrictTo (hWU i)] at this
    rw [(hloc i _ (hKW i (haK i p.1)) _ (hKW i (haK i p.2))).1, hrs i]
    exact this
  -- the shifted event
  have hL : {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤
        ENNReal.ofReal (Real.exp (-(ξ * L))) * t}
      ≤ᵐ[P] {ω | restrictTo U (X ω) + G ∈ A} := by
    filter_upwards [hgood] with ω hg hω i p
    obtain ⟨hl, hw, hloc, hrs⟩ := hg
    have hω' : internalDiam (D (Y ω)) (K i) (W i) ≤
        ENNReal.ofReal (Real.exp (-(ξ * L))) * t := hω i
    have e1 : resUW U (W i) (restrictTo U (X ω) + G) = restrictTo (W i) (addFun (Y ω) b) := by
      rw [hGdef, show restrictTo U (X ω) + restrictTo U (ofCont b) =
        restrictTo U (X ω + ofCont b) from rfl, resUW_restrictTo (hWU i), addFun,
        restrictTo_add', restrictTo_add', hrs i]
    rw [e1, ← (hloc i _ (hKW i (haK i p.1)) _ (hKW i (haK i p.2))).2,
      internal_addFun_eq_of_eqOn hl hw (W i).isOpen (fun x hx => hfL i x hx)]
    have hle : (D (Y ω)).internal (W i) (a i p.1) (a i p.2) ≤
        internalDiam (D (Y ω)) (K i) (W i) :=
      le_iSup₂_of_le (a i p.1) (haK i p.1) (le_iSup₂_of_le (a i p.2) (haK i p.2) le_rfl)
    calc ENNReal.ofReal (Real.exp (ξ * L)) * (D (Y ω)).internal (W i) (a i p.1) (a i p.2)
        ≤ ENNReal.ofReal (Real.exp (ξ * L)) *
            (ENNReal.ofReal (Real.exp (-(ξ * L))) * t) := by gcongr; exact hle.trans hω'
      _ = t := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  calc P {ω | ∀ i, internalDiam (D (Y ω)) (K i) (W i) ≤
          ENNReal.ofReal (Real.exp (-(ξ * L))) * t} ^ 2 *
        ENNReal.ofReal (Real.exp (-QuantumZipper.dirichletEnergyOn (U : Set ℂ) f.1))
      ≤ P {ω | restrictTo U (X ω) + G ∈ A} ^ 2 *
        ENNReal.ofReal (Real.exp (-QuantumZipper.dirichletEnergyOn (U : Set ℂ) f.1)) := by
        exact mul_le_mul_left (pow_le_pow_left₀ (zero_le) (measure_mono_ae hL) 2) _
    _ ≤ P {ω | restrictTo U (X ω) ∈ A} := key
    _ ≤ _ := measure_mono_ae hR

end LQGMetric.CONF
