/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_19 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19CI
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46Meas
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Definition 2.15 (form (3)) and Lemma 2.19 (`lem-inside-circle`)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T").

* `LocalAt P h' I V` — the condition of DFGPS Def 2.15 (T:1136–1139) for one open set `V`:
  `I(·,·;V)` is conditionally independent from `(h', I(·,·;ℂ ∖ cl V))` given `h'|_{cl V}`.
* `normField h z r = h − h_r(z)` and `normFam ξ h D z r` = the internal metrics of
  `e^{−ξ h_r(z)} D` (the objects of `Blueprint.IsXiAdditive2`, T:1150–1155).
* `lem2_19` — **DFGPS Lemma 2.19** (T:1182–1206): "It suffices to prove Lemma 2.17 in the case
  when `B_r(z) ⊂ V`." Formally: if for all `z, r, V` with `B_r(z) ⊆ V` the pair
  `(h − h_r(z), e^{−ξh_r(z)} D)` satisfies `LocalAt` at `V`, then it does for all `z, r, V`.
  The paper's proof is followed: `h_r(z) = −h̃_{r₀}(z₀)` is `σ(h̃|_{cl V})`-measurable
  (T:1194–1195), so the conditioning can be enlarged (weak union, `L219.condIndepEv_transfer`), and
  `D_{h̃}(·,·;V)`, `D_{h̃}(·,·;ℂ∖cl V)`, `h̃` are functions of the old objects and `h̃|_{cl V}`
  (T:1200–1204). All the relations hold almost surely (circle averages of `h + c`), whence the
  null-event bookkeeping; the empty `V` (which the paper skips) is trivial.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Bilip

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- `h − h_r(z)` -/
def normField (h : Ω → DistC) (z : ℂ) (r : ℝ) : Ω → DistC :=
  fun ω => addConst (h ω) (-circleAvg (h ω) r z)

/-- the internal metrics of `e^{−ξ h_r(z)} D` -/
def normFam (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (z : ℂ) (r : ℝ) :
    Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r z)) * (D ω).internal V u v

/-- **DFGPS Definition 2.15**, the condition for one open set `V` (T:1136–1139): the internal
metric `I(·,·;V)` is conditionally independent from `(h', I(·,·;ℂ∖cl V))` given `h'|_{cl V}`. -/
def LocalAt (P : Measure Ω) (h' : Ω → DistC) (I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞) (V : Set ℂ) :
    Prop :=
  CondIndepEv (fieldSigmaClosed h' (closure V)) (famSigma I V)
    (MeasurableSpace.comap h' inferInstance ⊔ famSigma I (closure V)ᶜ) P

namespace L219

variable {P : Measure Ω}

omit mΩ in
lemma measurable_addConst_of {M : MeasurableSpace Ω} {Ψ : Ω → DistC} {x : Ω → ℝ}
    (hΨ : Measurable[M] Ψ) (hx : Measurable[M] x) :
    Measurable[M] fun ω => addConst (Ψ ω) (x ω) := by
  refine (GFFInv.measurable_distC_iff (mα := M)).2 fun φ => ?_
  simp only [GFFInv.addConst_apply]
  exact ((GFFInv.measurable_distC_iff (mα := M)).1 hΨ φ).add (hx.const_mul _)

omit mΩ in
lemma measurable_restrictTo_addConst {M : MeasurableSpace Ω} (O : TopologicalSpace.Opens ℂ)
    {Ψ : Ω → DistC} {x : Ω → ℝ} (hΨ : Measurable[M] fun ω => restrictTo O (Ψ ω))
    (hx : Measurable[M] x) : Measurable[M] fun ω => restrictTo O (addConst (Ψ ω) (x ω)) := by
  refine (measurable_distOn_iff (α := Ω)).2 fun φ => ?_
  have e : ∀ ω, restrictTo O (addConst (Ψ ω) (x ω)) φ = restrictTo O (Ψ ω) φ +
      (∫ y, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ) y) * x ω :=
    fun ω => GFFInv.addConst_apply _ _ _
  simp_rw [e]
  exact ((measurable_distOn_apply φ).comp hΨ).add (hx.const_mul _)

lemma comap_le_aeClosure_of_ae_eq {β : Type*} [MeasurableSpace β] {M : MeasurableSpace Ω}
    {X Y : Ω → β} (hY : Measurable[M] Y) (h : X =ᵐ[P] Y) :
    MeasurableSpace.comap X inferInstance ≤ aeClosure P M := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨Y ⁻¹' S, hY hS, ?_⟩
  filter_upwards [h] with ω hω
  change (X ω ∈ S) = (Y ω ∈ S)
  rw [hω]

omit mΩ in
lemma fieldSigmaClosed_le_comap (g : Ω → DistC) (K : Set ℂ) :
    fieldSigmaClosed g K ≤ MeasurableSpace.comap g inferInstance :=
  (iInf₂_le (1 : ℝ) one_pos).trans
    (Measurable.comap_le ((measurable_restrictTo _).comp (comap_measurable g)))

omit mΩ in
lemma measurable_scale {M : MeasurableSpace Ω} {x : Ω → ℝ} {Y : Ω → ℂ → ℂ → ℝ≥0∞} (ξ : ℝ)
    (hx : Measurable[M] x) (hY : Measurable[M] Y) :
    Measurable[M] fun ω u v => ENNReal.ofReal (Real.exp (ξ * x ω)) * Y ω u v := by
  refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
  exact (ENNReal.measurable_ofReal.comp (hx.const_mul ξ).exp).mul
    ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp hY))

omit mΩ in
lemma ofReal_exp_mul_ofReal_exp (x y : ℝ) (t : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp x) * (ENNReal.ofReal (Real.exp y) * t) =
      ENNReal.ofReal (Real.exp (x + y)) * t := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos x).le, ← Real.exp_add]

lemma measurable_scaleF {D : Ω → ContMetric} (hD : Measurable D) {F : ContMetric × ℂ × ℂ → ℝ≥0∞}
    (hF : Measurable F) (ξ : ℝ) {x : Ω → ℝ} (hx : Measurable x) :
    Measurable fun ω u v => ENNReal.ofReal (Real.exp (-ξ * x ω)) * F (D ω, u, v) :=
  measurable_scale (-ξ) hx (measurable_pi_iff.2 fun _u => measurable_pi_iff.2 fun _v =>
    hF.comp (hD.prodMk measurable_const))

omit mΩ in
lemma internal_empty (D : ContMetric) (u v : ℂ) : D.internal ∅ u v = ⊤ := by
  unfold ContMetric.internal MetricGeometry.internalEDist
  rw [image_empty]
  have : IsEmpty {γ : Path (D.pt u) (D.pt v) // ∀ t, γ t ∈ (∅ : Set D.Space)} :=
    ⟨fun γ => γ.2 0⟩
  exact iInf_of_empty _

end L219

open L219

/-- **DFGPS Lemma 2.19** (`lem-inside-circle`, T:1182–1206): "It suffices to prove
Lemma 2.17 in the case when `B_r(z) ⊂ V`." If, for every `z₀`, `r₀ > 0` and open `V ⊇ B_{r₀}(z₀)`,
the internal metric of `e^{−ξh_{r₀}(z₀)} D` on `V` is conditionally independent from
`(h − h_{r₀}(z₀), e^{−ξh_{r₀}(z₀)} D(·,·;ℂ∖cl V))` given `(h − h_{r₀}(z₀))|_{cl V}`, then the same
holds for every `z`, `r > 0` and open `V`. -/
theorem lem2_19 {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} {D : Ω → ContMetric}
    (ξ : ℝ) (hh : IsWholePlaneGFF h P) (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (H : ∀ (z₀ : ℂ) (r₀ : ℝ) (V : TopologicalSpace.Opens ℂ), 0 < r₀ →
      Metric.ball z₀ r₀ ⊆ V → LocalAt P (normField h z₀ r₀) (normFam ξ h D z₀ r₀) V)
    (z : ℂ) (r : ℝ) (V : TopologicalSpace.Opens ℂ) (hr : 0 < r) :
    LocalAt P (normField h z r) (normFam ξ h D z r) V := by
  obtain ⟨FV, hFV, hFVe⟩ := measurable_internal V.isOpen
  obtain ⟨FC, hFC, hFCe⟩ := measurable_internal (isClosed_closure (s := (V : Set ℂ))).isOpen_compl
  set c : Ω → ℝ := fun ω => circleAvg (h ω) r z with hcdef
  have hc : Measurable c := (measurable_circleAvg_left r z).comp hh.measurable
  set h₁ := normField h z r with hh₁
  have hm₁ : Measurable h₁ := measurable_addConst_of hh.measurable hc.neg
  -- the measurable version of `e^{−ξ h_r(z)} D(·,·;ℂ∖cl V)`
  set Y₁c := fun ω u v => ENNReal.ofReal (Real.exp (-ξ * c ω)) * FC (D ω, u, v) with hY₁c
  have hY₁cm : Measurable Y₁c := measurable_scaleF hD hFC ξ hc
  have hI₁c : ∀ᵐ ω ∂P, normFam ξ h D z r ω (closure (V : Set ℂ))ᶜ = Y₁c ω := by
    filter_upwards [hlen] with ω hl
    funext u v
    change ENNReal.ofReal _ * (D ω).internal _ u v = ENNReal.ofReal _ * _
    rw [hFCe _ hl]
  rcases (V : Set ℂ).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · -- `V = ∅`: `I(·,·;∅) ≡ ∞`, so `σ(I(·,·;V))` is trivial
    have hconst : (fun ω => normFam ξ h D z r ω V) = fun _ _ _ => ⊤ := by
      funext ω u v
      simp only [normFam, hV, internal_empty]
      exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    refine condIndepEv_of_le_aeClosure (fieldSigmaClosed_le hm₁ _) ?_ ?_
    · rintro s ⟨S, hS, rfl⟩
      refine ⟨_, ?_, EventuallyEq.rfl⟩
      rw [hconst]
      exact measurable_const hS
    · exact sup_le (hm₁.comap_le.trans (le_aeClosure _))
        (famSigma_le_aeClosure_of_measurable hY₁cm hI₁c)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 V.isOpen z₀ hz₀
  have hsph : Metric.sphere z₀ |r₀| ⊆ closure (V : Set ℂ) := by
    rw [abs_of_pos hr₀]
    exact Metric.sphere_subset_closedBall.trans
      ((closure_ball z₀ hr₀.ne').symm ▸ closure_mono hball)
  set c₀ : Ω → ℝ := fun ω => circleAvg (h ω) r₀ z₀ with hc₀def
  have hc₀ : Measurable c₀ := (measurable_circleAvg_left r₀ z₀).comp hh.measurable
  set h₀ := normField h z₀ r₀ with hh₀
  have hm₀ : Measurable h₀ := measurable_addConst_of hh.measurable hc₀.neg
  -- `h̃ = h₀ + (h_{r₀}(z₀) − h_r(z))` and `h₀ = h̃ + (h_r(z) − h_{r₀}(z₀))`, literally
  have e₁ : ∀ ω, h₁ ω = addConst (h₀ ω) (c₀ ω - c ω) := fun ω => by
    simp only [hh₁, hh₀, normField, GFFLaw.addConst_addConst]
    congr 1; ring
  -- `a' = h̃_{r₀}(z₀)`, `b' = h₀_r(z)`
  set a' : Ω → ℝ := fun ω => circleAvg (h₁ ω) r₀ z₀ with ha'def
  set b' : Ω → ℝ := fun ω => circleAvg (h₀ ω) r z with hb'def
  have ha' : ∀ᵐ ω ∂P, a' ω = c₀ ω - c ω := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh z₀ hr₀] with ω hω
    simp only [ha'def, hh₁, normField, hω, hc₀def, hcdef]; ring
  have hb' : ∀ᵐ ω ∂P, b' ω = c ω - c₀ ω := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh z hr] with ω hω
    simp only [hb'def, hh₀, normField, hω, hc₀def, hcdef]; ring
  have ha'm : Measurable[fieldSigmaClosed h₁ (closure (V : Set ℂ))] a' :=
    GM.measurable_circleAvg_fieldSigmaClosed h₁ r₀ z₀ hsph
  -- measurable versions of the old internal metrics
  set Y₀v := fun ω u v => ENNReal.ofReal (Real.exp (-ξ * c₀ ω)) * FV (D ω, u, v) with hY₀v
  set Y₀c := fun ω u v => ENNReal.ofReal (Real.exp (-ξ * c₀ ω)) * FC (D ω, u, v) with hY₀c
  have hY₀vm : Measurable Y₀v := measurable_scaleF hD hFV ξ hc₀
  have hY₀cm : Measurable Y₀c := measurable_scaleF hD hFC ξ hc₀
  have hI₀v : ∀ᵐ ω ∂P, normFam ξ h D z₀ r₀ ω V = Y₀v ω := by
    filter_upwards [hlen] with ω hl
    funext u v
    change ENNReal.ofReal _ * (D ω).internal _ u v = ENNReal.ofReal _ * _
    rw [hFVe _ hl]
  have hI₀c : ∀ᵐ ω ∂P, normFam ξ h D z₀ r₀ ω (closure (V : Set ℂ))ᶜ = Y₀c ω := by
    filter_upwards [hlen] with ω hl
    funext u v
    change ENNReal.ofReal _ * (D ω).internal _ u v = ENNReal.ofReal _ * _
    rw [hFCe _ hl]
  -- the new internal metrics are `e^{ξ a'}` times the old ones, a.s.
  have hscale : ∀ (W : Set ℂ) (F : ContMetric × ℂ × ℂ → ℝ≥0∞),
      (∀ D' : ContMetric, D'.IsLength → ∀ u v, D'.internal W u v = F (D', u, v)) →
      ∀ᵐ ω ∂P, normFam ξ h D z r ω W = fun u v => ENNReal.ofReal (Real.exp (ξ * a' ω)) *
        (ENNReal.ofReal (Real.exp (-ξ * c₀ ω)) * F (D ω, u, v)) := by
    intro W F hF
    filter_upwards [hlen, ha'] with ω hl hω
    funext u v
    rw [ofReal_exp_mul_ofReal_exp, hω, ← hF _ hl]
    simp only [normFam, hcdef]
    congr 3; ring
  have H₀ := H z₀ r₀ V hr₀ hball
  unfold LocalAt at H₀ ⊢
  refine condIndepEv_transfer (G := fieldSigmaClosed h₀ (closure (V : Set ℂ))) (A := MeasurableSpace.comap Y₀v inferInstance)
    (B := MeasurableSpace.comap h₀ inferInstance ⊔ MeasurableSpace.comap Y₀c inferInstance)
    (fieldSigmaClosed_le hm₀ _) hY₀vm.comap_le (sup_le hm₀.comap_le hY₀cm.comap_le)
    (fieldSigmaClosed_le hm₁ _) ?_ ?_ ?_ ?_ ?_
  · -- the hypothesis at `(z₀, r₀)`, with the measurable versions
    refine GM.Bilip.CondIndepEv.of_le_aeClosure H₀
      (comap_le_aeClosure_of_ae_eq (comap_measurable _) (hI₀v.mono fun ω hω => hω.symm)) ?_
    exact sup_le (le_sup_left.trans (le_aeClosure _))
      ((comap_le_aeClosure_of_ae_eq (comap_measurable _) (hI₀c.mono fun ω hω => hω.symm)).trans
        (aeClosure_mono le_sup_right))
  · -- `σ(h₀|_{cl V}) ≤ σ(h̃|_{cl V})` up to null events (T:1195: `h|_{cl V} = h̃|_{cl V} + h_r(z)`)
    intro s hs
    refine GM.gm_aeEventIn_fieldSigmaClosed h₁ _ fun n => ?_
    set ε : ℝ := 1 / ((n : ℝ) + 1)
    have hε : 0 < ε := by positivity
    have hs' : MeasurableSet[fieldSigma h₀ (nbhdO ε (closure (V : Set ℂ)))] s := by
      have := hs
      unfold fieldSigmaClosed at this
      rw [MeasurableSpace.measurableSet_iInf] at this
      have := this ε
      rw [MeasurableSpace.measurableSet_iInf] at this
      exact this hε
    obtain ⟨S, hS, rfl⟩ := hs'
    have ha'O : Measurable[fieldSigma h₁ (nbhdO ε (closure (V : Set ℂ)))] a' :=
      (GM.measurable_circleAvg_fieldSigma h₁ r₀ z₀ hε).mono
        (GM.fieldSigma_mono h₁ (Metric.thickening_subset_of_subset ε hsph)) le_rfl
    refine ⟨(fun ω => restrictTo (nbhdO ε (closure (V : Set ℂ)))
      (addConst (h₁ ω) (-a' ω))) ⁻¹' S,
      measurable_restrictTo_addConst _ (comap_measurable _) ha'O.neg hS, ?_⟩
    filter_upwards [ha'] with ω hω
    change (restrictTo _ (h₀ ω) ∈ S) = (restrictTo _ (addConst (h₁ ω) (-a' ω)) ∈ S)
    rw [hω, e₁ ω, GFFLaw.addConst_addConst, add_neg_cancel, GFFLaw.addConst_zero']
  · -- `σ(h̃|_{cl V}) ≤ σ(h₀)` up to null events (`h̃ = h₀ − h₀_r(z)`)
    refine (fieldSigmaClosed_le_comap h₁ _).trans ((comap_le_aeClosure_of_ae_eq
      (measurable_addConst_of (comap_measurable h₀)
        ((measurable_circleAvg_left r z).comp (comap_measurable h₀)).neg) ?_).trans
      (aeClosure_mono (le_sup_left.trans le_sup_left)))
    filter_upwards [hb'] with ω hω
    change h₁ ω = addConst (h₀ ω) (-b' ω)
    rw [e₁ ω, hω]; congr 1; ring
  · -- `D_{h̃}(·,·;V) = e^{ξ a'} D_h(·,·;V)` (T:1200)
    exact famSigma_le_aeClosure_of_measurable (measurable_scale ξ (ha'm.mono le_sup_right le_rfl)
      ((comap_measurable Y₀v).mono le_sup_left le_rfl)) (hscale _ FV hFVe)
  · -- `h̃ = h₀ + a'` and `D_{h̃}(·,·;ℂ∖cl V) = e^{ξ a'} D_h(·,·;ℂ∖cl V)` (T:1201–1202)
    refine sup_le (comap_le_aeClosure_of_ae_eq (measurable_addConst_of
      ((comap_measurable h₀).mono (le_sup_left.trans le_sup_left) le_rfl)
      (ha'm.mono le_sup_right le_rfl)) ?_) ?_
    · filter_upwards [ha'] with ω hω
      rw [e₁ ω, hω]
    · exact famSigma_le_aeClosure_of_measurable (measurable_scale ξ (ha'm.mono le_sup_right le_rfl)
        ((comap_measurable Y₀c).mono (le_sup_right.trans le_sup_left) le_rfl)) (hscale _ FC hFCe)

end LQGMetric.DFGPS
