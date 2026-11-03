/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylLength at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylConcat

/-!
# Internal metrics of a Weyl-scaled metric (GM.S5.W)

Let `D, D'` be continuous metrics on `ℂ` with `D' = e^{ξ f}·D` (GM (1.6), `uniqueness-final.tex`
l. 300–302; for an LQG metric `D' = D_{h+f}` by Axiom III). Main result
(`weylScaleOn_eq_internal`): for every open `U`,

  `D'(z, w; U) = inf ∫_0^L e^{ξ f(P t)} dt` over `D`-length-parametrized paths `P ⊂ U`,

i.e. `(e^{ξ f}·D)(·,·;U) = weylScaleOn ξ f D U`. Consequences:

* `internal_eq_of_eq_const` (blueprint GM.S5.W, used at GM l. 3403–3550): if `ξ f ≡ c` on `U`
  then `D'(·,·;U) = e^c D(·,·;U)`, and two-sided bounds when `a ≤ ξ f ≤ b` on `U`;
* `isLength_of_eq_weylScale`: `D'` is a length metric (GM Axiom I is consistent with III).

Proof (own elementary argument; GM states these facts without proof):
`≤`: a `D`-length-parametrized `P ⊂ U` satisfies `D'(P s, P t) ≤ ∫_s^t e^{ξ f(P)}` for every
sub-path, so its `D'`-length is at most `∫_0^L e^{ξ f(P)}` (partition definition of length).
`≥`: for a path `γ ⊂ U` choose a bounded open `V`, `range γ ⊂ V ⊂ U`, with `ξ f ≥ a` on `V`, and
`ρ = min_{range γ} D(·, Vᶜ) > 0`. A `D`-path of Weyl cost `< e^a ρ` started on `range γ` cannot
leave `V` (its cost before the exit time is `≥ e^a ×` its `D`-length). Cutting `γ` into pieces of
`D'`-diameter `< e^a ρ` (uniform continuity) and concatenating near-optimal paths (the triangle
inequality `weylScaleOn_triangle`) gives `weylScaleOn U ≤ Σ D'(γ tᵢ, γ tᵢ₊₁) ≤ len(γ; D')`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

/-- the identity `D.Space → ℂ` -/
def weylToC (D : ContMetric) : D.Space → ℂ := id

/-- The identity `ℂ → D.Space` is continuous (as in `ContMetric.continuous_pt`, InternalC). -/
theorem continuous_weylPt (D : ContMetric) : Continuous D.pt := by
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  have hc : Continuous fun y : ℂ => D.1 (y, x) :=
    D.1.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h' := h y hy
  rw [D.2.self_eq_zero x, Real.dist_eq, sub_zero] at h'
  exact (le_abs_self _).trans_lt h'

/-- The identity `D.Space → ℂ` is continuous. -/
theorem continuous_weylToC (D : ContMetric) : Continuous (weylToC D) := by
  refine Metric.continuous_iff.2 fun b ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small b ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have ha' : D.1 (b, a) < δ := lt_of_eq_of_lt (D.2.symm b a) ha
  rw [Complex.dist_eq, norm_sub_rev]
  exact h a ha'

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric} {U : Set ℂ}

/-- A length-parametrized path leaving the open set `V` (on which `ξ f ≥ a`) has Weyl cost at
least `e^a D(P 0, Vᶜ)`. -/
theorem le_weylCost_of_exit {L : ℝ} {P : ℝ → ℂ} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    {V : Set ℂ} (hV : IsOpen V) {a : ℝ} (ha : ∀ x ∈ V, a ≤ ξ * f x)
    (hexit : ∃ t ∈ Icc 0 L, P t ∉ V) :
    ENNReal.ofReal (Real.exp a) * infEDist (D.pt (P 0)) (D.pt '' Vᶜ) ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  have hcP : ContinuousOn P (Icc 0 L) := (continuous_weylToC D).comp_continuousOn hc
  set S := Icc 0 L ∩ P ⁻¹' Vᶜ
  have hS : IsClosed S := hcP.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl
  obtain ⟨t, ht, htV⟩ := hexit
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmem := hS.csInf_mem ⟨t, ht, htV⟩ hbdd
  set s₀ := sInf S
  have hbefore : ∀ τ ∈ Ico 0 s₀, P τ ∈ V := fun τ hτ => by
    by_contra hτV
    exact absurd hτ.2 (not_lt.2 (csInf_le hbdd ⟨⟨hτ.1, hτ.2.le.trans hmem.1.2⟩, hτV⟩))
  calc ENNReal.ofReal (Real.exp a) * infEDist (D.pt (P 0)) (D.pt '' Vᶜ)
      ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal s₀ := by
        gcongr
        refine (infEDist_le_edist_of_mem (y := D.pt (P s₀))
          (⟨P s₀, hmem.2, rfl⟩ : D.pt (P s₀) ∈ D.pt '' Vᶜ)).trans ?_
        have := edist_le_curveLength (D.pt ∘ P) hmem.1.1
        rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ hmem.1, sub_zero] at this
        exact this
    _ = ∫⁻ _ in Ico 0 s₀, ENNReal.ofReal (Real.exp a) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero]
    _ ≤ ∫⁻ t in Ico 0 s₀, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        setLIntegral_mono' measurableSet_Ico fun τ hτ =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (ha _ (hbefore τ hτ)))
    _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        lintegral_mono_set (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hmem.1.2))

/-- Near-optimal paths of small cost started at `x` stay in `V ⊆ U`, so
`(e^{ξ f}·D)_U(x, y) ≤ (e^{ξ f}·D)(x, y)` when the latter is `< e^a D(x, Vᶜ)`. -/
theorem weylScaleOn_le_weylScale_of_lt {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {a : ℝ}
    (ha : ∀ x ∈ V, a ≤ ξ * f x) {x y : ℂ}
    (hlt : weylScale ξ f D x y < ENNReal.ofReal (Real.exp a) * infEDist (D.pt x) (D.pt '' Vᶜ)) :
    weylScaleOn ξ f D U x y ≤ weylScale ξ f D x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hlt' := lt_min hc hlt
  simp only [weylScale, iInf_lt_iff] at hlt'
  obtain ⟨L, P, hL, hcP, hu, h0, h1, hcost⟩ := hlt'
  have hin : ∀ t ∈ Icc 0 L, P t ∈ U := by
    intro t ht
    by_contra htU
    have := le_weylCost_of_exit hL hcP hu hV ha ⟨t, ht, fun h => htU (hVU h)⟩
    rw [h0] at this
    exact lt_irrefl _ (this.trans_lt (hcost.trans_le (min_le_right _ _)))
  exact (weylScaleOn_le hL hcP hu h0 h1 hin).trans (hcost.trans_le (min_le_left _ _)).le

variable (D' : ContMetric)
  (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
include hD'

/-- `≤`: the `D'`-internal metric is at most the Weyl cost of any admissible path in `U`. -/
theorem internal_le_weylScaleOn (z w : ℂ) : D'.internal U z w ≤ weylScaleOn ξ f D U z w := by
  refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
  have hcP : ContinuousOn P (Icc 0 L) := (continuous_weylToC D).comp_continuousOn hc
  have hc' : ContinuousOn (D'.pt ∘ P) (Icc 0 L) := (continuous_weylPt D').comp_continuousOn hcP
  have hlen : curveLength (D'.pt ∘ P) 0 L ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
    refine eVariationOn_le_lintegral fun s t hs hst ht => ?_
    rw [setLIntegral_congr Ioc_ae_eq_Icc]
    show edist (D'.pt (P s)) (D'.pt (P t)) ≤ _
    rw [edist_dist]
    refine le_of_eq_of_le (hD' (P s) (P t)) ?_
    rw [← weylScaleOn_univ]
    exact weylScaleOn_le_sub hu (fun _ _ => mem_univ _) hs hst ht
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hL hc'
  rw [← h0, ← h1]
  refine (internalEDist_le_pathLength γ fun t => ?_).trans (hγ.trans_le hlen)
  obtain ⟨s, hs, hst⟩ := hrange (mem_range_self t)
  exact ⟨P s, hU s hs, hst⟩

/-- `≥`: Weyl cost with paths in the open set `U` is at most the `D'`-internal metric on `U`. -/
theorem weylScaleOn_le_internal (hU : IsOpen U) (z w : ℂ) :
    weylScaleOn ξ f D U z w ≤ D'.internal U z w := by
  unfold ContMetric.internal internalEDist
  refine le_iInf fun γ' => ?_
  obtain ⟨γ, hγU⟩ := γ'
  by_cases hfin : pathLength γ = ∞
  · rw [hfin]; exact le_top
  -- the range of `γ` in `ℂ`, a compact subset of a bounded open `V ⊆ U`
  set g : unitInterval → ℂ := fun t => weylToC D' (γ t)
  have hg : Continuous g := (continuous_weylToC D').comp γ.continuous
  have hK : IsCompact (range g) := isCompact_range hg
  have hKU : range g ⊆ U := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨x, hx, hxt⟩ := hγU t
    have : x = g t := hxt
    exact this ▸ hx
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  set V := U ∩ ball (0 : ℂ) R
  have hV : IsOpen V := hU.inter isOpen_ball
  have hKV : range g ⊆ V := fun x hx => ⟨hKU hx, hR hx⟩
  obtain ⟨a, ha⟩ : ∃ a, ∀ x ∈ V, a ≤ ξ * f x := by
    obtain ⟨a, ha⟩ := (isCompact_closedBall (0 : ℂ) R).bddBelow_image
      (f := fun x => ξ * f x) (by fun_prop : Continuous fun x => ξ * f x).continuousOn
    exact ⟨a, fun x hx => ha ⟨x, ball_subset_closedBall hx.2, rfl⟩⟩
  -- `ρ = min_{range γ} D(·, Vᶜ) > 0`
  set Φ : ℂ → ℝ≥0∞ := fun x => infEDist (D.pt x) (D.pt '' Vᶜ)
  have hΦc : Continuous Φ := continuous_infEDist.comp (continuous_weylPt D)
  have hclosed : IsClosed (D.pt '' Vᶜ) := by
    have : D.pt '' Vᶜ = weylToC D ⁻¹' Vᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [this]; exact hV.isClosed_compl.preimage (continuous_weylToC D)
  have hΦpos : ∀ x ∈ V, 0 < Φ x := fun x hx => by
    refine infEDist_pos_iff_notMem_closure.2 ?_
    rw [hclosed.closure_eq]
    rintro ⟨y, hy, hyx⟩
    have : y = x := hyx
    exact hy (this ▸ hx)
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ∀ x ∈ range g, ρ ≤ Φ x := by
    obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn (range_nonempty g) hΦc.continuousOn
    exact ⟨Φ x0, hΦpos x0 (hKV hx0), fun x hx => hmin hx⟩
  set η := ENNReal.ofReal (Real.exp a) * ρ
  have hη : 0 < η := ENNReal.mul_pos (by simpa using Real.exp_pos a) hρpos.ne'
  -- uniform continuity of `γ` and a fine subdivision `u i = min (i / n) 1`
  have huc : UniformContinuousOn γ.extend (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous γ.continuous_extend.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := EMetric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set u : ℕ → ℝ := fun i => min ((i : ℝ) / n) 1
  have humono : Monotone u := fun i j hij =>
    min_le_min_right _ (div_le_div_of_nonneg_right (Nat.cast_le.2 hij) hnpos.le)
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (div_nonneg (Nat.cast_nonneg i) hnpos.le) zero_le_one, min_le_right _ _⟩
  have hu0 : u 0 = 0 := by simp [u]
  have hun : u n = 1 := by simp [u, div_self hnpos.ne']
  have hstep : ∀ i, edist (u i) (u (i + 1)) < δ := by
    intro i
    refine lt_of_le_of_lt ?_ hn
    rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnpos]
    refine ENNReal.ofReal_le_ofReal ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
    rw [sub_self, abs_zero, Nat.cast_succ, ← sub_div, sub_add_cancel_left, abs_div, abs_neg,
      abs_one, abs_of_pos hnpos, one_div]
    exact max_le le_rfl (inv_nonneg.2 hnpos.le)
  set q : ℕ → ℂ := fun i => weylToC D' (γ.extend (u i))
  have hq : ∀ i, q i ∈ range g := fun i => ⟨⟨u i, humem i⟩, by
    simp only [g, q, Path.extend_extends' γ ⟨u i, humem i⟩]⟩
  have hq0 : q 0 = z := by simp only [q, hu0, Path.extend_zero]; rfl
  have hqn : q n = w := by simp only [q, hun, Path.extend_one]; rfl
  have hDq : ∀ i, weylScale ξ f D (q i) (q (i + 1)) =
      edist (γ.extend (u (i + 1))) (γ.extend (u i)) := by
    intro i
    rw [← hD', edist_comm, edist_dist]
    rfl
  calc weylScaleOn ξ f D U z w = weylScaleOn ξ f D U (q 0) (q n) := by rw [hq0, hqn]
    _ ≤ ∑ i ∈ Finset.range n, weylScaleOn ξ f D U (q i) (q (i + 1)) :=
        weylScaleOn_le_sum q (hKU (hq 0)) n
    _ ≤ ∑ i ∈ Finset.range n, weylScale ξ f D (q i) (q (i + 1)) := by
        refine Finset.sum_le_sum fun i _ => weylScaleOn_le_weylScale_of_lt hV inter_subset_left
          ha ?_
        rw [hDq, edist_comm]
        refine (hδ' (humem i) (humem (i + 1)) (hstep i)).trans_le ?_
        show ENNReal.ofReal (Real.exp a) * ρ ≤ ENNReal.ofReal (Real.exp a) * Φ (q i)
        exact mul_le_mul' le_rfl (hρ _ (hq i))
    _ = ∑ i ∈ Finset.range n, edist (γ.extend (u (i + 1))) (γ.extend (u i)) :=
        Finset.sum_congr rfl fun i _ => hDq i
    _ ≤ eVariationOn γ.extend (Icc 0 1) := eVariationOn.sum_le humono humem
    _ = pathLength γ := rfl

/-- **Internal metrics of `e^{ξ f}·D`**: if the continuous metric `D'` equals `e^{ξ f}·D`, then
for every open `U`, `D'(·,·;U)` is the Weyl infimum over length-parametrized paths in `U`. -/
theorem weylScaleOn_eq_internal (hU : IsOpen U) (z w : ℂ) :
    weylScaleOn ξ f D U z w = D'.internal U z w :=
  le_antisymm (weylScaleOn_le_internal D' hD' hU z w) (internal_le_weylScaleOn D' hD' z w)

/-- **GM.S5.W**: if `D' = e^{ξ f}·D` and `ξ f ≡ c` on the open set `U`, then
`D'(·,·;U) = e^c D(·,·;U)`. -/
theorem internal_eq_of_eq_const (hU : IsOpen U) {c : ℝ} (hf : ∀ x ∈ U, ξ * f x = c)
    (z w : ℂ) :
    D'.internal U z w = ENNReal.ofReal (Real.exp c) * D.internal U z w := by
  rw [← weylScaleOn_eq_internal D' hD' hU, weylScaleOn_of_eq_const hf]

/-- Two-sided bound on internal metrics: `a ≤ ξ f ≤ b` on the open set `U` ⇒
`e^a D(·,·;U) ≤ D'(·,·;U) ≤ e^b D(·,·;U)`. -/
theorem internal_mem_Icc_of_le (hU : IsOpen U) {a b : ℝ} (ha : ∀ x ∈ U, a ≤ ξ * f x)
    (hb : ∀ x ∈ U, ξ * f x ≤ b) (z w : ℂ) :
    ENNReal.ofReal (Real.exp a) * D.internal U z w ≤ D'.internal U z w ∧
      D'.internal U z w ≤ ENNReal.ofReal (Real.exp b) * D.internal U z w := by
  rw [← weylScaleOn_eq_internal D' hD' hU]
  exact ⟨le_weylScaleOn_of_le ha, weylScaleOn_le_of_le hb⟩

/-- `e^{ξ f}·D` is a length metric whenever it is a continuous metric. -/
theorem isLength_of_eq_weylScale : D'.IsLength := by
  intro x y ε hε
  have h : ENNReal.ofReal (D'.1 (weylToC D' x, weylToC D' y)) =
      D'.internal univ (weylToC D' x) (weylToC D' y) := by
    rw [hD', ← weylScaleOn_univ]
    exact weylScaleOn_eq_internal D' hD' isOpen_univ _ _
  have hlt : D'.internal univ (weylToC D' x) (weylToC D' y) <
      edist x y + ENNReal.ofReal ε := by
    rw [← h, edist_dist]
    exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (by simpa using hε)
  unfold ContMetric.internal internalEDist at hlt
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  exact ⟨γ.1, hγ.le⟩

end LQGMetric
