/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B8
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# `CONFHarmTailN` and CONF Lemma 3.5 (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:1170–1172: for a fixed `U ∈ 𝒰_1(0;δ)`, `sup_{u∈U_{δ/4}} |𝔥^U(u)|` is a.s.
finite, and the bound is uniform by the invariance of the law of `h` modulo constants. We prove
the quantitative form (Ding–Gwynne Lemma 2.2, (2.4): a Gaussian tail; `dg_tail_unif`):

* normalize away from `U₁ = confU 1 δ 0 T`: `k = h − h(ψ₀)` (`ψ₀` a unit bump off `cl U₁`),
  `g = k − k_1(0)`; then `g = h + c` with `c = −h_1(0) = 0` a.s., `g_1(0) = 0` a.s., and the raw
  `σ(g|_{ℂ∖U₁})` is the mod-constant one (`HarmExist.fieldSigmaClosed_addConst_le`, D110);
* the Markov harmonic part of `g` (`markov_harmPart_dec`) is a harmonic part in the D110 sense and
  equals `𝔥^{U₁}_h` a.s. (`isHarmPart0_addConst_iff`, `isHarmPart_ae_eq'`);
* `dg_tail_unif` gives `P[sup_K |𝔥| > A] ≤ 4e^{−a₁A²}` with `a₁` depending only on `K`, `U₁`
  and `Var[g(ψ_c)]`, which is the same for every normalized whole-plane GFF
  (`GFFLaw.map_eq_of_normalized_ae`; a reference field from `GFFExist.exists_wholePlaneGFF`).

Main results: `confHarmTailN : CONFHarmTailN`, `confHarmExists : CONFHarmExists`
(= `HarmExist.exists_isHarmPart`), **`confLem3_5 : Blueprint.CONFLem3_5`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

theorem closure_innerPart_subset {U : Set ℂ} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    closure (innerPart U ε) ⊆ U := by
  intro x hx
  have h1 : closure (innerPart U ε) ⊆ closure U := closure_mono fun y hy => hy.1
  have h2 : closure (innerPart U ε) ⊆ {y | ε ≤ infDist y (frontier U)} :=
    closure_minimal (fun y hy => le_of_lt hy.2)
      (isClosed_le continuous_const (continuous_infDist_pt _))
  by_contra hxU
  have hfr : x ∈ frontier U := ⟨h1 hx, by rwa [hU.interior_eq]⟩
  have := h2 hx
  rw [mem_ofPred_eq, Metric.infDist_zero_of_mem hfr] at this
  linarith

/-- **the unit-scale harmonic-part bound** (CONF C:1170–1172, via DG Lemma 2.2) -/
theorem confHarmTailN : CONFHarmTailN := by
  intro δ hδ hδ1 T β hβ
  set U₁ := confU 1 δ 0 T
  have hU₁o : IsOpen U₁ := GM.p412j_isOpen_confU 1 δ 0 T
  have hU₁b : Bornology.IsBounded U₁ := isBounded_confU' 1 δ 0 T
  set K := closure (innerPart U₁ (δ / 4))
  have hKU : K ⊆ U₁ := closure_innerPart_subset hU₁o (by positivity)
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hU₁b.subset hKU)
  have hdisj : Disjoint U₁ (sphere (0 : ℂ) 1) := Set.disjoint_left.2 fun x hx hx1 => by
    have := hx.1.1
    rw [mem_sphere, dist_zero_right] at hx1
    rw [sub_zero, hx1] at this
    linarith
  have hsph : sphere (0 : ℂ) |1| ⊆ U₁ᶜ := fun x hx hxU => by
    rw [abs_one] at hx; exact Set.disjoint_left.1 hdisj hxU hx
  obtain ⟨ψc, hψc⟩ := dg_tail_unif (V := toOpens U₁ hU₁o) hKc hKU
  -- the reference normalized field and the common variance
  obtain ⟨Ω₀, m₀, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  obtain ⟨hg₀, hn₀⟩ := DFGPS.isNormalizedAt_recenter hh₀ one_pos 0
  set g₀ : Ω₀ → DistC := fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)
  obtain ⟨ρ₀, -, hρ₀⟩ := HarmLoc.exists_unit_test isOpen_univ univ_nonempty
  set v := Var[fun T : DistC => T ψc; P₀.map g₀]
  obtain ⟨a₁, ha₁, Ht⟩ := hψc v
  set A := max 1 (Real.log (4 / β) / a₁)
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨A, by linarith, ?_⟩
  intro Ω _ P _ h hh
  -- normalization away from `U₁`
  have hne : ((closure U₁)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact NormedSpace.unbounded_univ ℝ ℂ (hne ▸ hU₁b.closure)
  obtain ⟨ψ₀, hψ₀cl, hψ₀1⟩ := HarmLoc.exists_unit_test isClosed_closure.isOpen_compl hne
  have hψ₀U : tsupport (ψ₀ : ℂ → ℝ) ⊆ U₁ᶜ :=
    hψ₀cl.trans (compl_subset_compl.2 subset_closure)
  set k := normIn h ψ₀
  have hk : IsWholePlaneGFF k P := isWholePlaneGFF_normIn hh.1 ψ₀
  set F : Ω → ℝ := fun ω => -circleAvg (k ω) 1 0
  have hFm : Measurable[fieldSigmaClosed k U₁ᶜ] F :=
    (GM.measurable_circleAvg_fieldSigmaClosed k 1 0 hsph).neg
  set g : Ω → DistC := fun ω => addConst (k ω) (F ω)
  have hg : IsWholePlaneGFF g P :=
    hk.addConst ((measurable_circleAvg_left 1 0).comp hk.measurable).neg
  have hn : ∀ᵐ ω ∂P, circleAvg (g ω) 1 0 = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hk 0 one_pos] with ω hω
    simp only [g, F]; rw [hω]; ring
  have eσ : fieldSigmaClosed g U₁ᶜ = fieldSigmaClosed0 g U₁ᶜ := by
    refine le_antisymm ?_ (fieldSigmaClosed0_le_fieldSigmaClosed g _)
    refine (HarmExist.fieldSigmaClosed_addConst_le k F U₁ᶜ hFm).trans (le_of_eq ?_)
    rw [fieldSigmaClosed_normIn_eq h hψ₀1 hψ₀U]
    exact (fieldSigmaClosed0_addConst k F U₁ᶜ).trans
      (fieldSigmaClosed0_addConst h _ U₁ᶜ) |>.symm
  obtain ⟨Hf, G, hz, hraw, hGm, hdec, hind, hzb, hlink⟩ :=
    markov_harmPart_dec hg one_pos 0 hn hU₁o hdisj
  have hHf : IsHarmPart P g U₁ Hf := by
    unfold HarmLoc.IsHarmPartRaw at hraw
    rw [eσ] at hraw
    exact hraw
  -- `g = h + c`, `c = 0` a.s.
  set c : Ω → ℝ := fun ω => -(h ω ψ₀) + F ω
  have hgc : g = fun ω => addConst (h ω) (c ω) := by
    funext ω
    simp only [g, k, normIn, c, GFFLaw.addConst_addConst]
  have hc0 : ∀ᵐ ω ∂P, c ω = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh.1 0 one_pos, hh.2] with ω h1 h2
    simp only [c, F, k, normIn]
    rw [h1, h2]; ring
  have hHh : IsHarmPart P h U₁ (fun ω x => Hf ω x - c ω) := by
    refine (isHarmPart0_addConst_iff h c U₁ (fun ω x => Hf ω x - c ω)).1 ?_
    have e : (fun ω x => Hf ω x - c ω + c ω) = Hf := by funext ω x; ring
    show IsHarmPart P (fun ω => addConst (h ω) (c ω)) U₁ (fun ω x => Hf ω x - c ω + c ω)
    rw [e, ← hgc]; exact hHf
  have huniq := isHarmPart_ae_eq' hU₁o hU₁b (isHarmPart0_harmPart0 ⟨_, hHh⟩) hHh
  -- the variance of `g(ψ_c)` is the common one
  have hlaw : P.map g = P₀.map g₀ :=
    GFFLaw.map_eq_of_normalized_ae hρ₀ (measurable_circleAvg_left 1 0) hg hg₀
      (CircleAvg.ae_circleAvg_addConst hg 0 one_pos)
      (CircleAvg.ae_circleAvg_addConst hg₀ 0 one_pos) hn hn₀
  have hvar : Var[fun ω => g ω ψc; P] ≤ v := by
    refine le_of_eq ?_
    rw [show v = Var[fun T : DistC => T ψc; P.map g] by rw [hlaw], variance_map (GFFInv.measurable_pair ψc).aemeasurable hg.measurable.aemeasurable]
    rfl
  have htail := Ht ⟨hg, hn⟩ hGm hdec hind hzb hvar A (by linarith)
  refine le_trans (measure_mono_ae ?_) (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [huniq, hc0, hlink] with ω h1 h2 h3
    rintro ⟨x, hx, hlt⟩
    refine ⟨Hf ω, hHf.1 ω, h3, x, subset_closure hx, ?_⟩
    have e1 : harmPart P h U₁ ω x = Hf ω x - c ω := h1 x hx.1
    rw [e1, h2, sub_zero] at hlt
    exact hlt
  · have hlog : Real.log (4 / β) ≤ a₁ * A ^ 2 := by
      have h1 : Real.log (4 / β) / a₁ ≤ A := le_max_right _ _
      have h2 : Real.log (4 / β) ≤ a₁ * A := by rwa [div_le_iff₀ ha₁, mul_comm] at h1
      have h3 : a₁ * A ≤ a₁ * A ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) ha₁.le
      linarith
    have : Real.exp (-a₁ * A ^ 2) ≤ β / 4 := by
      calc Real.exp (-a₁ * A ^ 2) ≤ Real.exp (-Real.log (4 / β)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = β / 4 := by
            rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    linarith

/-- **existence of harmonic parts** (DEC-110 P3, `HarmExist.exists_isHarmPart`, P2-D110c) -/
theorem confHarmExists : CONFHarmExists := by
  intro Ω _ P _ h hh U hU hUb
  exact HarmExist.exists_isHarmPart hh hU hUb

/-- CONF L3.5's other leaves, unconditionally -/
theorem confHarmLocN : CONFHarmLocN := confHarmLocN_of_exists confHarmExists

theorem confHarmBound : CONFHarmBound :=
  confHarmBound_of_U (confHarmBoundU_of confHarmExists confHarmTailN)

end LQGMetric.CONF
