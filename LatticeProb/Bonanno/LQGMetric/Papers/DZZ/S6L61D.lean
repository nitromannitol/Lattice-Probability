/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61C

/-!
# DZZ Lemma 6.1, lower half: the segment bound by contradiction (P2-DZZ61L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 6.1, l. 2593–2608.
"Suppose the preceding statement fails for some `L_δ`. Let `v_{L_δ}` be an arbitrary point on
`L_δ`. … we can construct four short crossings … Consequently, the union of these short crossings
[and] the geodesic between `L_δ` and `∂𝕍̄_u` … contains a path between `v_{L_δ}` and `∂𝕍̄_u`.
Therefore, by the same argument as in Lemma 5.4, we get
`E log min_{y ∈ ∂𝕍̄_u} D(v_{L_δ}, y) ≤ (χ − ι) log δ⁻¹`. This contradicts
(eq-point-to-boundary-kappa)."

Inputs, stated as exact hypotheses (not available in the library):
* `DZZL61PtBdry P μ α χ u`: the lower half of DZZ (eq-point-to-boundary-kappa) (l. 2593–2596,
  "by Lemma 5.4 and a similar derivation to (eq-distance-point-to-boundary-bound)") at
  `κ = (1−α)/20`, for centres `v_δ ∈ ∂𝕍̄_{u,α}` (DZZ apply it at the moving point `v_{L_δ}`).
  Its derivation from `DZZLem54Exp` needs DZZ Lemma 3.? (lem-scaling-coupling, l. 611) and
  (eq-geodesic-range) (l. 2340); not formalized.
* `DZZL61Glue P μ α χ u ι`: the four RSW short crossings of DZZ Fig. glue, in the form used:
  w.p. → 1, `min_{∂𝕍̄_u} D(v_δ, ·) ≤ min_{L_δ × ∂𝕍̄_u} D + δ^{−χ+ι}` (DZZ l. 2562–2570: the
  crossings are unions of a bounded number of `D̃(x,y)`, `|x−y| ≤ 10|L_δ|`, each `≤ δ^{−χ+ι}`
  w.p. → 1, by (eq-delta_0) and the scaling argument of (eq-z-open)).
* `hfin`: a.s. `D_δ(x,y) < ∞` on `𝕍̄_u` (GMC regularity, as `hreg` in `S5Adapt`).

The step from these to the segment bound (concentration, Proposition 3.17, for the pairs
`(L_δ, ∂𝕍̄_u)` and `(v_δ, ∂𝕍_{v_δ,κ})`; the first exit from `𝕍_{v_δ,κ}`; the logarithm of the
glued bound) is proved here: `dzzL61SegBound_of_glue`; with `dzzLem61Lower_of_segBound` this
gives, in S6L61E with `DZZL61GlueK` (segment length `δ^{2ι/χ}`, DEC-117 §2(c)),
`dzzLem61Lower_of_glue`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The lower half of DZZ (eq-point-to-boundary-kappa) (l. 2593–2596) at `κ = (1−α)/20`, for
centres on `∂𝕍̄_{u,α}` (moving with `δ`). -/
def DZZL61PtBdry (P : Measure Ω) (μ : Ω → Measure ℂ) (α χ : ℝ) (u : ℂ) : Prop :=
  ∀ v : ℝ → ℂ, (∀ δ, v δ ∈ frontier (sqBox u (α / 20))) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (χ - ε) * Real.log δ⁻¹ ≤
      ∫ ω, logMinLGD (μ ω) δ {v δ} (frontier (sqBox (v δ) ((1 - α) / 20))) ∂P

lemma IsBdrySeg.nonempty {c : ℂ} {a ℓ : ℝ} {L : Set ℂ} (h : IsBdrySeg c a ℓ L) (hℓ : 0 ≤ ℓ) :
    L.Nonempty :=
  (h.isConnected hℓ).nonempty

lemma sqBox_subset_sqBox_of_mem {u v : ℂ} {α : ℝ} (hv : v ∈ sqBox u (α / 20)) :
    sqBox v ((1 - α) / 20) ⊆ sqBox u (1 / 20) := by
  intro z ⟨h1, h2⟩
  obtain ⟨h3, h4⟩ := hv
  constructor
  · have := abs_sub_le z.re v.re u.re; linarith
  · have := abs_sub_le z.im v.im u.im; linarith

lemma dist_ge_of_mem_frontier_sqBox {v z : ℂ} {l : ℝ} (hl : 0 < l)
    (hz : z ∈ frontier (sqBox v l)) : l / 2 ≤ dist v z := by
  rw [dist_comm, dist_eq_norm]
  rcases edge_of_mem_frontier_sqBox hl hz with h | h
  · have := Complex.abs_re_le_norm (z - v); rw [Complex.sub_re] at this; linarith
  · have := Complex.abs_im_le_norm (z - v); rw [Complex.sub_im] at this; linarith

/-- **The segment bound of DZZ Lemma 6.1** (l. 2601–2608), by contradiction from
(eq-point-to-boundary-kappa) (`DZZL61PtBdry`), the gluing of Fig. glue at segment length `δ^κ`
(`hglue` is `DZZL61GlueK P μ α χ u ι κ` of S5D117 unfolded; S5D117 imports this file) and DZZ
Proposition 3.17. Only `0 < κ < ξ` is used here; the consumer takes `κ = 2ι/χ`
(DEC-117 §2(c)). -/
theorem dzzL61SegBound_of_glue {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {α χ ξ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hξ : 0 < ξ) (hξα : ξ ≤ (1 - α) / 40)
    (h317 : DZZProp317 P μ ξ) {u : ℂ} (hu : u ∈ dzzVbar) {ι : ℝ} (hι : 0 < ι) (hι1 : ι < 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκξ : κ < ξ)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, ∀ x ∈ sqBox u (1 / 20), ∀ y ∈ sqBox u (1 / 20),
      lgdDZZ (μ ω) δ x y < ⊤)
    (hpt : DZZL61PtBdry P μ α χ u)
    (hglue : ∀ (L : ℝ → Set ℂ) (v : ℝ → ℂ),
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), IsBdrySeg u (α / 20) (δ ^ κ) (L δ) ∧ v δ ∈ L δ) →
      Tendsto (fun δ => P {ω | ¬ ((lgdMinSet (μ ω) δ {v δ} (frontier (sqBox u (1 / 20))) : ℝ≥0∞) ≤
        (lgdMinSet (μ ω) δ (L δ) (frontier (sqBox u (1 / 20))) : ℝ≥0∞) +
          ENNReal.ofReal (δ ^ (-(χ - ι))))}) (𝓝[>] 0) (𝓝 0)) :
    DZZL61SegBound P μ α χ u ι κ := by
  classical
  intro L hL
  have hLlog : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < Real.log δ⁻¹ := fun δ hδ =>
    Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ.2)
  by_cases hχ : χ ≤ 2 * ι
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    have := hLlog δ hδ
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) this.le).trans
      (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _)
  push_neg at hχ
  have hξ9 : ξ ≤ 9 / 20 := by linarith
  set a : ℝ := α / 20 with hadef
  have ha0 : 0 < a := by positivity
  set κb : ℝ := (1 - α) / 20 with hκbdef
  have hκb : 0 < κb := by rw [hκbdef]; linarith
  set F := frontier (sqBox u a) with hFdef
  set G := frontier (sqBox u (1 / 20)) with hGdef
  -- a point `v_δ ∈ L_δ` (a corner of `∂𝕍̄_{u,α}` when `L_δ ∩ ∂𝕍̄_{u,α} = ∅`)
  set c₀ : ℂ := ⟨u.re - a / 2, u.im - a / 2⟩
  have hc₀ : c₀ ∈ F := by
    rw [hFdef, frontier_sqBox ha0]
    exact Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr
      ⟨⟨le_rfl, by show u.re - a / 2 ≤ u.re + a / 2; linarith⟩, rfl⟩)))
  let v : ℝ → ℂ := fun δ => if h : (L δ ∩ F).Nonempty then h.some else c₀
  have hvF : ∀ δ, v δ ∈ F := fun δ => by
    simp only [v]; split_ifs with h
    · exact h.some_mem.2
    · exact hc₀
  have hvL : ∀ δ, IsBdrySeg u a (δ ^ κ) (L δ) → 0 < δ → v δ ∈ L δ := fun δ h hδ => by
    have hne : (L δ ∩ F).Nonempty := by
      obtain ⟨x, hx⟩ := h.nonempty (Real.rpow_pos_of_pos hδ _).le
      exact ⟨x, hx, h.1 hx⟩
    simp only [v, dif_pos hne]; exact hne.some_mem.1
  have hvbox : ∀ δ, v δ ∈ sqBox u a := fun δ => (isClosed_sqBox _ _).frontier_subset (hvF δ)
  -- the two fixed points completing the admissible families
  set a₀ : ℂ := u + ((α / 40 : ℝ) : ℂ)
  set b₀ : ℂ := u + ((1 / 40 : ℝ) : ℂ)
  have ha₀ : a₀ ∈ sqBox u (α / 20) := by
    constructor
    · show |(u + ((α / 40 : ℝ) : ℂ)).re - u.re| ≤ α / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_of_pos (by positivity)]
      linarith
    · show |(u + ((α / 40 : ℝ) : ℂ)).im - u.im| ≤ α / 20 / 2
      rw [Complex.add_im, Complex.ofReal_im, add_zero, sub_self, abs_zero]; positivity
  have hb₀G : b₀ ∈ G := by
    rw [hGdef, frontier_sqBox (by norm_num)]
    refine Or.inr (Complex.mem_reProdIm.mpr ⟨?_, ?_⟩)
    · show (u + ((1 / 40 : ℝ) : ℂ)).re = u.re + 1 / 20 / 2
      rw [Complex.add_re, Complex.ofReal_re]; ring
    · show (u + ((1 / 40 : ℝ) : ℂ)).im ∈ _
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact ⟨by linarith, by linarith⟩
  have hb₀ : b₀ ∈ sqBox u (1 / 20) := (isClosed_sqBox _ _).frontier_subset hb₀G
  have hXi : ∀ z ∈ sqBox u (1 / 20), z ∈ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_mem_sqBox hu hz le_rfl hξ.le hξ9
  have hXia : ∀ z ∈ sqBox u a, z ∈ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_mem_sqBox hu hz (by rw [hadef]; linarith) hξ.le hξ9
  have hdG : ∀ x ∈ sqBox u a, ∀ y ∈ G, ξ ≤ dist x y := fun x hx y hy => by
    have := edge_of_mem_frontier_sqBox (by norm_num : (0 : ℝ) < 1 / 20) hy
    norm_num at this
    exact hξα.trans (dist_ge_of_edge hx this)
  have hab : ξ ≤ dist a₀ b₀ := hdG a₀ ha₀ b₀ hb₀G
  have hGsub : G ⊆ sqBox u (1 / 20) := (isClosed_sqBox _ _).frontier_subset
  have hGadm : ∀ δ, δ ^ ξ ≤ 1 / 20 → IsXiAdmissibleSet ξ δ G := fun δ h =>
    Or.inr ⟨isConnected_frontier_sqBox u (by norm_num),
      h.trans (side_le_diam_frontier_sqBox u (by norm_num))⟩
  have hsmall := eventually_rpow_le hξ (lt_min hκb (by norm_num) : (0 : ℝ) < min κb (1 / 20))
  have hsmall2 := eventually_rpow_le (by linarith : 0 < ξ - κ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hξℓ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ ξ ≤ δ ^ κ / 2 := by
    filter_upwards [hsmall2, self_mem_nhdsWithin] with δ h hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have : δ ^ ξ = δ ^ (ξ - κ) * δ ^ κ := by
      rw [← Real.rpow_add hδ']; ring_nf
    rw [this]
    have := Real.rpow_pos_of_pos hδ' κ
    nlinarith
  set ι'' : ℝ := ι / 8 with hι''def
  have hι'' : ι'' ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [hι''def]; linarith⟩
  -- the concentration events
  have hE1 := conc_tendsto_of_eventually h317 (hXia a₀ ha₀) (hXi b₀ hb₀) hab
    (A := L) (B := fun _ => G) (by
      filter_upwards [hL, hsmall, hξℓ, self_mem_nhdsWithin] with δ h1 h2 h3 h4
      have hδ' : (0 : ℝ) < δ := h4
      have hℓ := (Real.rpow_pos_of_pos hδ' κ).le
      refine ⟨fun z hz => hXia z (h1.subset_sqBox hz), fun z hz => hXi z (hGsub hz),
        Or.inr ⟨h1.isConnected hℓ, h3.trans (h1.diam_ge ha0.le hℓ)⟩,
        hGadm δ (h2.trans (min_le_right _ _)), fun x hx y hy => hdG x (h1.subset_sqBox hx) y hy⟩)
    hι''
  have hE2 := conc_tendsto_of_eventually h317 (hXia a₀ ha₀) (hXi b₀ hb₀) hab
    (A := fun δ => {v δ}) (B := fun δ => frontier (sqBox (v δ) κb)) (by
      filter_upwards [hsmall] with δ h2
      have hsub : frontier (sqBox (v δ) κb) ⊆ sqBox u (1 / 20) :=
        ((isClosed_sqBox _ _).frontier_subset).trans (sqBox_subset_sqBox_of_mem (hvbox δ))
      refine ⟨singleton_subset_iff.mpr (hXia _ (hvbox δ)), fun z hz => hXi z (hsub hz),
        Or.inl ⟨v δ, rfl⟩, Or.inr ⟨isConnected_frontier_sqBox _ hκb,
          (h2.trans (min_le_left _ _)).trans (side_le_diam_frontier_sqBox _ hκb)⟩,
        fun x hx y hy => ?_⟩
      rw [mem_singleton_iff.mp hx]
      have := dist_ge_of_mem_frontier_sqBox hκb hy
      rw [hκbdef] at this; linarith)
    hι''
  have hE3 := hglue L v (by
    filter_upwards [hL, self_mem_nhdsWithin] with δ h1 h2 using ⟨h1, hvL δ h1 h2⟩)
  have hq : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) := ENNReal.ofReal_pos.mpr (by norm_num)
  have hlogbig : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Real.log 2 + 1 < ι / 2 * Real.log δ⁻¹ := by
    have h := (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop
      (by positivity : (0 : ℝ) < ι / 2)
    exact h.eventually_gt_atTop _
  by_contra hcon
  rw [not_eventually] at hcon
  have hev0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hall := hev0.and (hL.and ((hE1.eventually (gt_mem_nhds hq)).and
    ((hE2.eventually (gt_mem_nhds hq)).and ((hE3.eventually (gt_mem_nhds hq)).and
    (hfin.and ((hpt v hvF (ι / 4) (by positivity)).and hlogbig))))))
  obtain ⟨δ, hbad, hδ1, hL1, h1, h2, h3, h4, h5, h6⟩ := (hcon.and_eventually hall).exists
  have hδ0 : 0 < δ := hδ1.1
  have hLp := hLlog δ hδ1
  push_neg at hbad
  beta_reduce at h1 h2 h3 hbad
  have h4' := ae_iff.mp h4
  set E1 := (conc1Event μ P δ ι'' (L δ) G)ᶜ
  set E2 := (conc1Event μ P δ ι'' {v δ} (frontier (sqBox (v δ) κb)))ᶜ
  set E3 := {ω | ¬ ((lgdMinSet (μ ω) δ {v δ} G : ℝ≥0∞) ≤
      (lgdMinSet (μ ω) δ (L δ) G : ℝ≥0∞) + ENNReal.ofReal (δ ^ (-(χ - ι))))}
  set E4 := {ω | ¬ ∀ x ∈ sqBox u (1 / 20), ∀ y ∈ sqBox u (1 / 20), lgdDZZ (μ ω) δ x y < ⊤}
  have hU : P (E1 ∪ E2 ∪ E3 ∪ E4) < 1 := by
    calc P (E1 ∪ E2 ∪ E3 ∪ E4) ≤ P E1 + P E2 + P E3 + P E4 :=
          (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
            (add_le_add_left (measure_union_le _ _) _)) _)
      _ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + 0 := by
          rw [h4']; gcongr
      _ = ENNReal.ofReal (3 / 4) := by
          rw [add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
      _ < 1 := ENNReal.ofReal_lt_one.mpr (by norm_num)
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ E1 ∪ E2 ∪ E3 ∪ E4 := by
    by_contra hh
    push_neg at hh
    have : P univ ≤ P (E1 ∪ E2 ∪ E3 ∪ E4) := measure_mono fun ω _ => hh ω
    rw [measure_univ] at this
    exact absurd hU (not_lt.mpr this)
  simp only [E1, E2, E3, E4, mem_union, not_or, mem_compl_iff, not_not, mem_setOf_eq] at hω
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hω
  simp only [conc1Event, mem_setOf_eq] at c1 c2
  set mL := lgdMinSet (μ ω) δ (L δ) G with hmLdef
  set mv := lgdMinSet (μ ω) δ {v δ} G with hmvdef
  set mk := lgdMinSet (μ ω) δ {v δ} (frontier (sqBox (v δ) κb)) with hmkdef
  have hvL' := hvL δ hL1 hδ0
  have hv20 : v δ ∈ sqBox u (1 / 20) := by
    obtain ⟨e1, e2⟩ := hvbox δ
    exact ⟨e1.trans (by rw [hadef]; linarith), e2.trans (by rw [hadef]; linarith)⟩
  have hmv : mv < ⊤ := lt_of_le_of_lt (iInf₂_le_of_le (v δ) (mem_singleton _)
    (iInf₂_le b₀ hb₀G)) (c4 (v δ) hv20 b₀ hb₀)
  have hmLv : mL ≤ mv := biInf_mono fun x hx => by rw [mem_singleton_iff.mp hx]; exact hvL'
  have hmkv : mk ≤ mv := lgdMinSet_box_le_of_exit (μ ω) δ hα0 hα1 (hvbox δ)
  have hmL : mL ≠ ⊤ := (hmLv.trans_lt hmv).ne
  have hmk : mk ≠ ⊤ := (hmkv.trans_lt hmv).ne
  have eL : ((mL.toNat : ℕ) : ℕ∞) = mL := ENat.natCast_toNat hmL
  have ev : ((mv.toNat : ℕ) : ℕ∞) = mv := ENat.natCast_toNat hmv.ne
  have ek : ((mk.toNat : ℕ) : ℕ∞) = mk := ENat.natCast_toNat hmk
  have hnL1 : (1 : ℝ) ≤ mL.toNat := by
    have := one_le_lgdMinSet (μ ω) δ (L δ) G
    rw [← hmLdef, ← eL] at this; exact_mod_cast this
  have hnk1 : (1 : ℝ) ≤ mk.toNat := by
    have := one_le_lgdMinSet (μ ω) δ {v δ} (frontier (sqBox (v δ) κb))
    rw [← hmkdef, ← ek] at this; exact_mod_cast this
  have hnkv : (mk.toNat : ℝ) ≤ mv.toNat := by
    rw [← ek, ← ev] at hmkv; exact_mod_cast hmkv
  set r : ℝ := δ ^ (-(χ - ι)) with hrdef
  have hr : 0 < r := Real.rpow_pos_of_pos hδ0 _
  have hlogr : Real.log r = (χ - ι) * Real.log δ⁻¹ := by
    rw [hrdef, Real.log_rpow hδ0, Real.log_inv]; ring
  have hnv : (mv.toNat : ℝ) ≤ mL.toNat + r := by
    rw [← ev, ← eL, ENat.toENNReal_coe, ENat.toENNReal_coe] at c3
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,
      ENNReal.ofReal_ne_top⟩) c3
    rwa [ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hr.le] at this
  have hXL : Real.log (mL.toNat : ℝ) < Real.log r := by
    have e1 := (abs_le.mp c1).2
    have e2 : logMinLGD (μ ω) δ (L δ) G = Real.log (mL.toNat : ℝ) := rfl
    rw [hlogr]; rw [e2] at e1
    have : ι'' * Real.log δ⁻¹ ≤ ι * Real.log δ⁻¹ := mul_le_mul_of_nonneg_right
      (by rw [hι''def]; linarith) hLp.le
    nlinarith
  have hnLr : (mL.toNat : ℝ) < r := (Real.log_lt_log_iff (by linarith) hr).mp hXL
  have hlogv : Real.log (mv.toNat : ℝ) ≤ Real.log 2 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogk : Real.log (mk.toNat : ℝ) ≤ Real.log (mv.toNat : ℝ) :=
    Real.log_le_log (by linarith) hnkv
  have e3 := (abs_le.mp c2).1
  have e4 : logMinLGD (μ ω) δ {v δ} (frontier (sqBox (v δ) κb)) =
    Real.log (mk.toNat : ℝ) := rfl
  rw [e4] at e3
  rw [hlogr] at hlogv
  have h7 : ι / 2 * Real.log δ⁻¹ ≤ 5 * ι / 8 * Real.log δ⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hLp.le
  rw [hι''def] at e3
  nlinarith

end DZZ
end LQGMetric
