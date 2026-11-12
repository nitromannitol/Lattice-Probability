/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The length measure of a curve (packet P-GRID, DEC-107 §5; decision D111)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.2 (l. 937–946) and (5.2) (l. 950–953) use `len(P ∩ S; D)`,
"`P ∩ S` is a countable union of excursions of `P`", and the proof of Lemma 5.2 "assume that `P`
is parametrized by `D`-length … the Lebesgue measure of `P⁻¹(ε𝒢_θ)` is zero". We formalize
`len(P ∩ A; D)` as the **length measure** of the curve evaluated at the time set `P⁻¹(A)`: the
Stieltjes measure of `t ↦ len(P|_{[a,t]})` (the curve extended constantly outside `[a,b]`). For a
`D`-length parametrization it is Lebesgue measure, as in LM's proof.

* `t17Ext g a b` — `g` extended by `g a`, `g b` outside `[a, b]`;
* `t17LenSF` — `t ↦ variationOnFromTo (t17Ext g a b) univ a t`, a continuous monotone (Stieltjes)
  function for a continuous curve of finite length;
* `t17LenMeas g a b` — its Stieltjes measure (`0` if `g` is not a continuous finite-length curve
  on `[a, b]`);
* `t17LenMeas_Icc` — sub-goal (i) of handoff/P2-LM17a.md: `μ_{g}([a,b]) = len(g; [a,b])`;
* `t17LenMeas_Icc_sub` — `μ_g([s,u]) = len(g; [s,u])` for `a ≤ s ≤ u ≤ b`, the form needed for
  sub-goal (ii) (`μ_g(g⁻¹ S) ≤ μ_g([s,u]) = len(g|_{[s,u]})` for the first/last hits `s, u`).

Own construction (standard: the variation measure of a continuous BV function, e.g. Folland,
*Real Analysis*, §3.5; mathlib `StieltjesFunction.measure`, `variationOnFromTo`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.LM

variable {M : Type*} [PseudoEMetricSpace M]

/-- the curve `g` on `[a, b]`, extended constantly to `ℝ` -/
def t17Ext (g : ℝ → M) (a b : ℝ) : ℝ → M := fun t => g (max a (min b t))

lemma t17_clamp_mono (a b : ℝ) : Monotone fun t : ℝ => max a (min b t) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

lemma t17_clamp_image {a b : ℝ} (hab : a ≤ b) : (fun t : ℝ => max a (min b t)) '' univ = Icc a b := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x, mem_univ _, by simp only [min_eq_right h2, max_eq_right h1]⟩

lemma t17_clamp_eqOn {a b : ℝ} : EqOn (fun t : ℝ => max a (min b t)) id (Icc a b) := by
  intro t ht
  simp [min_eq_right ht.2, max_eq_right ht.1]

lemma t17Ext_eVariationOn {g : ℝ → M} (a b : ℝ) (s : Set ℝ) :
    eVariationOn (t17Ext g a b) s = eVariationOn g ((fun t : ℝ => max a (min b t)) '' s) :=
  eVariationOn.comp_eq_of_monotoneOn g _ ((t17_clamp_mono a b).monotoneOn s)

lemma t17Ext_eVariationOn_univ {g : ℝ → M} {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (t17Ext g a b) univ = eVariationOn g (Icc a b) := by
  rw [t17Ext_eVariationOn, t17_clamp_image hab]

lemma t17Ext_eVariationOn_Icc {g : ℝ → M} {a b s u : ℝ} (has : a ≤ s) (_hsu : s ≤ u) (hub : u ≤ b) :
    eVariationOn (t17Ext g a b) (Icc s u) = eVariationOn g (Icc s u) := by
  rw [t17Ext_eVariationOn]
  congr 1
  rw [(t17_clamp_eqOn.mono (Icc_subset_Icc has hub)).image_eq, image_id]

lemma t17Ext_continuous {g : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn g (Icc a b)) :
    Continuous (t17Ext g a b) :=
  hc.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) fun _ =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- the hypotheses: `g` is a continuous curve of finite length on `[a, b]` -/
def T17Curve (g : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn g (Icc a b) ∧ eVariationOn g (Icc a b) ≠ ⊤

lemma T17Curve.bv {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) :
    BoundedVariationOn (t17Ext g a b) univ := by
  unfold BoundedVariationOn; rw [t17Ext_eVariationOn_univ h.1]; exact h.2.2

/-- `t ↦ len(g|_{[a,t]})` as a Stieltjes function -/
def t17LenSF {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) : StieltjesFunction ℝ where
  toFun := variationOnFromTo (t17Ext g a b) univ a
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn h.bv.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x :=
    (((h.bv.continuousAt_variationOnFromTo_iff a x).2
      ((t17Ext_continuous h.1 h.2.1).continuousAt)).continuousWithinAt)

lemma t17LenSF_continuous {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) :
    Continuous (t17LenSF h) :=
  continuous_iff_continuousAt.2 fun x =>
    (h.bv.continuousAt_variationOnFromTo_iff a x).2 ((t17Ext_continuous h.1 h.2.1).continuousAt)

open scoped Classical in
/-- **the length measure** `μ_{g}` of a curve on `[a, b]` (zero if `g` is not a continuous curve
of finite length there); `len(g ∩ A) := μ_g(g⁻¹ A)`. -/
def t17LenMeas (g : ℝ → M) (a b : ℝ) : Measure ℝ :=
  if h : T17Curve g a b then (t17LenSF h).measure else 0

lemma t17LenMeas_eq {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) :
    t17LenMeas g a b = (t17LenSF h).measure := by
  simp [t17LenMeas, h]

/-- `μ_g([s, u]) = len(g; [s, u])` for `[s, u] ⊆ [a, b]` -/
theorem t17LenMeas_Icc_sub {g : ℝ → M} {a b s u : ℝ} (h : T17Curve g a b) (has : a ≤ s)
    (hsu : s ≤ u) (hub : u ≤ b) : t17LenMeas g a b (Icc s u) = eVariationOn g (Icc s u) := by
  rw [t17LenMeas_eq h, StieltjesFunction.measure_Icc,
    ((t17LenSF_continuous h).continuousAt.continuousWithinAt).leftLim_eq]
  have hfin : eVariationOn g (Icc s u) ≠ ⊤ :=
    ne_top_of_le_ne_top h.2.2 (eVariationOn.mono g (Icc_subset_Icc has hub))
  have hloc := h.bv.locallyBoundedVariationOn
  show ENNReal.ofReal (variationOnFromTo (t17Ext g a b) univ a u -
      variationOnFromTo (t17Ext g a b) univ a s) = _
  rw [variationOnFromTo.sub_right hloc (mem_univ _) (mem_univ _) (mem_univ _),
    variationOnFromTo.eq_of_le _ _ hsu, univ_inter, t17Ext_eVariationOn_Icc has hsu hub,
    ENNReal.ofReal_toReal hfin]

/-- sub-goal (i): `μ_g([a, b]) = len(g; [a, b])` -/
theorem t17LenMeas_Icc {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) :
    t17LenMeas g a b (Icc a b) = eVariationOn g (Icc a b) :=
  t17LenMeas_Icc_sub h le_rfl h.1 le_rfl

/-- sub-goal (ii): a time set inside `[s, u] ⊆ [a, b]` (e.g. `P⁻¹ S` between the first and last
hits `s, u` of `cl S`) has length measure at most `len(g; [s, u])`. -/
theorem t17LenMeas_le_of_subset {g : ℝ → M} {a b s u : ℝ} (h : T17Curve g a b) (has : a ≤ s)
    (hsu : s ≤ u) (hub : u ≤ b) {A : Set ℝ} (hA : A ⊆ Icc s u) :
    t17LenMeas g a b A ≤ eVariationOn g (Icc s u) :=
  (measure_mono hA).trans_eq (t17LenMeas_Icc_sub h has hsu hub)

/-! ## Sub-goal (iv): comparison of length measures -/

lemma t17_eVariationOn_le_mul {M' : Type*} [PseudoEMetricSpace M'] {g : ℝ → M} {g' : ℝ → M'}
    {s : Set ℝ} {c : ℝ≥0∞} (hle : ∀ x ∈ s, ∀ y ∈ s, edist (g' x) (g' y) ≤ c * edist (g x) (g y)) :
    eVariationOn g' s ≤ c * eVariationOn g s := by
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1, edist (g' (p.2.1 (i + 1))) (g' (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, c * edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => hle _ (p.2.2.2 _) _ (p.2.2.2 _)
    _ = c * ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ c * eVariationOn g s := by
        gcongr; exact eVariationOn.sum_le p.2.2.1 p.2.2.2

lemma t17_varFromTo_eq {g : ℝ → M} {a b : ℝ} (h : T17Curve g a b) {x y : ℝ} (hxy : x ≤ y) :
    t17LenSF h y - t17LenSF h x = (eVariationOn (t17Ext g a b) (Icc x y)).toReal := by
  show variationOnFromTo (t17Ext g a b) univ a y - variationOnFromTo (t17Ext g a b) univ a x = _
  rw [variationOnFromTo.sub_right h.bv.locallyBoundedVariationOn (mem_univ _) (mem_univ _)
    (mem_univ _), variationOnFromTo.eq_of_le _ _ hxy, univ_inter]

/-- sub-goal (iv): if `g'` is pointwise `c`-Lipschitz relative to `g` on `[a, b]` (e.g. `D' ≤ c D`
along the same curve), then `μ_{g'} ≤ c μ_g`. -/
theorem t17LenMeas_le_smul {M' : Type*} [PseudoEMetricSpace M'] {g : ℝ → M} {g' : ℝ → M'}
    {a b : ℝ} (h : T17Curve g a b) (h' : T17Curve g' a b) (c : NNReal)
    (hle : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, edist (g' x) (g' y) ≤ c * edist (g x) (g y)) :
    t17LenMeas g' a b ≤ c • t17LenMeas g a b := by
  have hcl : ∀ t : ℝ, max a (min b t) ∈ Icc a b := fun _ =>
    ⟨le_max_left _ _, max_le h.1 (min_le_left _ _)⟩
  have hext : ∀ s : Set ℝ, eVariationOn (t17Ext g' a b) s ≤ c * eVariationOn (t17Ext g a b) s :=
    fun s => t17_eVariationOn_le_mul fun x _ y _ => hle _ (hcl x) _ (hcl y)
  have hfin : ∀ s : Set ℝ, eVariationOn (t17Ext g a b) s ≠ ⊤ := fun s =>
    ne_top_of_le_ne_top h.bv (eVariationOn.mono _ (subset_univ s))
  let W : StieltjesFunction ℝ :=
    { toFun := fun x => (c : ℝ) * t17LenSF h x - t17LenSF h' x
      mono' := by
        intro x y hxy
        have h1 := t17_varFromTo_eq h hxy
        have h2 := t17_varFromTo_eq h' hxy
        have h3 : (eVariationOn (t17Ext g' a b) (Icc x y)).toReal ≤
            (c : ℝ) * (eVariationOn (t17Ext g a b) (Icc x y)).toReal := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin _))
            (hext (Icc x y))
          rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
        show (c : ℝ) * t17LenSF h x - t17LenSF h' x ≤ (c : ℝ) * t17LenSF h y - t17LenSF h' y
        have h4 : (c : ℝ) * (t17LenSF h y - t17LenSF h x) =
            (c : ℝ) * (eVariationOn (t17Ext g a b) (Icc x y)).toReal := by rw [h1]
        linarith
      right_continuous' := fun x =>
        ((continuous_const.mul (t17LenSF_continuous h)).sub
          (t17LenSF_continuous h')).continuousAt.continuousWithinAt }
  have hsum : c • t17LenSF h = W + t17LenSF h' := by
    ext x
    show (c : ℝ) * t17LenSF h x = ((c : ℝ) * t17LenSF h x - t17LenSF h' x) + t17LenSF h' x
    ring
  rw [t17LenMeas_eq h, t17LenMeas_eq h', ← StieltjesFunction.measure_smul, hsum,
    StieltjesFunction.measure_add]
  exact Measure.le_add_left le_rfl

/-! ## Sub-goal (iii): locality of the length measure on open time sets -/

section Local

open scoped Classical

/-- every open set of `ℝ` is the union of the closed rational intervals it contains -/
lemma t17_open_eq_iUnion_Icc {W : Set ℝ} (hW : IsOpen W) :
    W = ⋃ p : ℚ × ℚ, (if Icc (p.1 : ℝ) p.2 ⊆ W then Icc (p.1 : ℝ) p.2 else ∅) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε / 2 < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + ε / 2 by linarith)
    have hsub : Icc (q : ℝ) r ⊆ W := fun t ht => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    exact ⟨(q, r), by simp only [hsub, if_true]; exact ⟨hq2.le, hr1.le⟩⟩
  · rintro ⟨p, hp⟩
    by_cases h : Icc (p.1 : ℝ) p.2 ⊆ W
    · simp only [h, if_true] at hp; exact h hp
    · simp only [h, if_false] at hp; exact hp.elim

/-- the π-system of closed intervals inside `O` and measurable sets outside `O` -/
def t17PiO (O : Set ℝ) : Set (Set ℝ) :=
  {s | MeasurableSet s ∧ (s ⊆ Oᶜ ∨ ∃ x y : ℝ, s = Icc x y ∧ Icc x y ⊆ O)}

lemma t17PiO_isPiSystem (O : Set ℝ) : IsPiSystem (t17PiO O) := by
  rintro s ⟨hs, hs'⟩ t ⟨ht, ht'⟩ -
  refine ⟨hs.inter ht, ?_⟩
  rcases hs' with hs' | ⟨x, y, rfl, hxy⟩
  · exact Or.inl (inter_subset_left.trans hs')
  · rcases ht' with ht' | ⟨x', y', rfl, -⟩
    · exact Or.inl (inter_subset_right.trans ht')
    · refine Or.inr ⟨max x x', min y y', Icc_inter_Icc, ?_⟩
      rw [← Icc_inter_Icc]; exact inter_subset_left.trans hxy

lemma t17PiO_generate {O : Set ℝ} (hO : IsOpen O) :
    (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom (t17PiO O) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun s hs => hs.1)
  rw [BorelSpace.measurable_eq (α := ℝ)]
  refine MeasurableSpace.generateFrom_le fun U hU0 => ?_
  have hU : IsOpen U := hU0
  have hsplit : U = (U \ O) ∪ (U ∩ O) := (diff_union_inter U O).symm
  rw [hsplit]
  have hmem : U \ O ∈ t17PiO O := ⟨hU.measurableSet.diff hO.measurableSet, Or.inl fun x hx => hx.2⟩
  refine MeasurableSet.union (MeasurableSpace.measurableSet_generateFrom hmem) ?_
  rw [t17_open_eq_iUnion_Icc (hU.inter hO)]
  refine MeasurableSet.iUnion fun p => ?_
  by_cases h : Icc (p.1 : ℝ) p.2 ⊆ U ∩ O
  · rw [if_pos h]
    have hmem : Icc (p.1 : ℝ) p.2 ∈ t17PiO O :=
      ⟨measurableSet_Icc, Or.inr ⟨_, _, rfl, h.trans inter_subset_right⟩⟩
    exact MeasurableSpace.measurableSet_generateFrom hmem
  · rw [if_neg h]; exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom (t17PiO O))

/-- sub-goal (iii): two curves whose lengths agree on every closed time interval inside the open
time set `O ⊆ (a, b)` have the same length measure on `O`. -/
theorem t17LenMeas_eq_on_open {M' : Type*} [PseudoEMetricSpace M'] {g : ℝ → M} {g' : ℝ → M'}
    {a b : ℝ} (h : T17Curve g a b) (h' : T17Curve g' a b) {O : Set ℝ} (hO : IsOpen O)
    (hOab : O ⊆ Ioo a b)
    (heq : ∀ x y, x ≤ y → Icc x y ⊆ O → eVariationOn g (Icc x y) = eVariationOn g' (Icc x y)) :
    t17LenMeas g a b O = t17LenMeas g' a b O := by
  set μ := t17LenMeas g a b
  set μ' := t17LenMeas g' a b
  -- agreement on the π-system
  have hC : ∀ s ∈ t17PiO O, μ.restrict O s = μ'.restrict O s := by
    rintro s ⟨hs, hs'⟩
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    rcases hs' with hs' | ⟨x, y, rfl, hxy⟩
    · have : s ∩ O = ∅ := eq_empty_of_forall_notMem fun z hz => hs' hz.1 hz.2
      rw [this, measure_empty, measure_empty]
    · rw [inter_eq_left.2 hxy]
      by_cases hle : x ≤ y
      · have hx : a ≤ x := (hOab (hxy ⟨le_rfl, hle⟩)).1.le
        have hy : y ≤ b := (hOab (hxy ⟨hle, le_rfl⟩)).2.le
        rw [t17LenMeas_Icc_sub h hx hle hy, t17LenMeas_Icc_sub h' hx hle hy, heq x y hle hxy]
      · rw [Icc_eq_empty hle, measure_empty, measure_empty]
  have hfinO : ∀ t, μ.restrict O t ≠ ⊤ := fun t => by
    refine ne_of_lt ?_
    calc μ.restrict O t ≤ μ.restrict O univ := measure_mono (subset_univ _)
      _ = μ O := Measure.restrict_apply_univ O
      _ ≤ μ (Icc a b) := measure_mono (hOab.trans Ioo_subset_Icc_self)
      _ = eVariationOn g (Icc a b) := t17LenMeas_Icc h
      _ < ⊤ := h.2.2.lt_top
  set T : Set (Set ℝ) := {Oᶜ} ∪
    range (fun p : ℚ × ℚ => if Icc (p.1 : ℝ) p.2 ⊆ O then Icc (p.1 : ℝ) p.2 else ∅)
  have hTC : T ⊆ t17PiO O := by
    rintro t (ht | ⟨p, rfl⟩)
    · rw [mem_singleton_iff.1 ht]
      exact ⟨hO.measurableSet.compl, Or.inl subset_rfl⟩
    · by_cases hp : Icc (p.1 : ℝ) p.2 ⊆ O
      · dsimp only; rw [if_pos hp]; exact ⟨measurableSet_Icc, Or.inr ⟨_, _, rfl, hp⟩⟩
      · dsimp only; rw [if_neg hp]; exact ⟨MeasurableSet.empty, Or.inl (empty_subset _)⟩
  have hTc : T.Countable := (countable_singleton _).union (countable_range _)
  have hU : ⋃₀ T = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ O
    · rw [t17_open_eq_iUnion_Icc hO, mem_iUnion] at hx
      obtain ⟨p, hp⟩ := hx
      exact ⟨_, Or.inr ⟨p, rfl⟩, hp⟩
    · exact ⟨Oᶜ, Or.inl rfl, hx⟩
  have hres : μ.restrict O = μ'.restrict O := by
    refine Measure.ext_of_generateFrom_of_cover (t17PiO_generate hO) hTc (t17PiO_isPiSystem O) hU
      (fun t _ => hfinO t) (fun t ht s hs => ?_) (fun t ht => hC t (hTC ht))
    by_cases hne : (s ∩ t).Nonempty
    · exact hC _ (t17PiO_isPiSystem O s hs t (hTC ht) hne)
    · rw [not_nonempty_iff_eq_empty.1 hne, measure_empty, measure_empty]
  have := congrArg (fun ν : Measure ℝ => ν univ) hres
  simpa only [Measure.restrict_apply_univ] using this

end Local

end LQGMetric.LM
