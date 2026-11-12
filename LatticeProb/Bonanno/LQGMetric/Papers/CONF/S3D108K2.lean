/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108K2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# CONF Proposition 2.8: monotonicity and continuity of internal-diameter events (Axiom III)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, proof of Proposition 2.8 (C:748–752): "By
Axiom III, it is a.s. the case that for each continuous function `f` one has
`D_{h+f} = e^{ξf}·D_h`. In particular, if `f` is non-negative then `D_{h+f} ≥ D_h`. Therefore
`g ↦ Φ(D_g)` … are non-decreasing and a.s. continuous at `h` in the sense of Lemma 2.10";
and C:664–669 (the functionals `𝟙{sup_{u ∈ A, v ∈ B} D(u,v) ≥ c}`: "obviously non-decreasing …
a.s. continuous at `D_h` since the probability that the supremum … is exactly equal to `c` is
zero").

Deterministic part, at a field `k` at which the Weyl identity of `IsWeakLQGMetric.weyl` holds for
every `f ∈ C(ℂ, ℝ)` (the a.s. event of Axiom III):

* `internal_addFun_eq_weylScaleOn`: `D_{k+f}(·,·;V) = (e^{ξf}·D_k)_V` (`weylScaleOn_eq_internal`);
* `internalDiam_addFun_mono`: `f ≤ g`, `ξ ≥ 0` ⇒ `diam(A; D_{k+f}(·,·;V)) ≤ diam(A; D_{k+g}(·,·;V))`;
* `internalDiam_addFun_mem`: `|f| ≤ ε` on `V` ⇒ the diameters differ by a factor `e^{±ξε}`;
* `eventually_le_iff_of_sandwich`: a quantity squeezed between `e^{∓ξε} a` (every `ε > 0`,
  eventually) is eventually on the same side of a threshold `T ≠ a` as `a`;
* **`diamEvent_weyl_mono`, `diamEvent_weyl_cont`**: the events
  `{∀ i ∈ I, diam(A i; D(·,·;V i)) ≤ T i}` (`I` finite, `V i` open bounded) — the form of
  `fatG` (S3D112A) and of condition 2 of `E^U_r(z)` — are non-increasing in `f` and, if no
  diameter equals its threshold at `k`, continuous along `fₙ → 0` in `C(ℂ, ℝ)`: exactly the
  hypotheses `hGm`/`hGc` of `confProp2_8_frozen` (S3D108K1) at the sample.

The remaining probabilistic input for continuity is CONF's "the probability that the supremum is
exactly equal to `c` is zero" (blueprint S-cont-law).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

section Weyl

variable {ξ : ℝ} {D : DistC → ContMetric} {k : DistC}

/-- the Weyl identity at the field `k`, for every continuous `f` (Axiom III, a.s. event) -/
def WeylAt (ξ : ℝ) (D : DistC → ContMetric) (k : DistC) : Prop :=
  ∀ (f : C(ℂ, ℝ)) (z w : ℂ), weylScale ξ f (D k) z w = ENNReal.ofReal ((D (addFun k f)).1 (z, w))

/-- `D_{k+f}(·,·;V) = (e^{ξ f}·D_k)_V` for open `V` -/
lemma internal_addFun_eq_weylScaleOn (hw : WeylAt ξ D k) (f : C(ℂ, ℝ)) {V : Set ℂ}
    (hV : IsOpen V) (u v : ℂ) :
    (D (addFun k f)).internal V u v = weylScaleOn ξ f (D k) V u v :=
  (weylScaleOn_eq_internal (D (addFun k f)) (fun x y => (hw f x y).symm) hV u v).symm

/-- monotonicity of internal diameters in the continuous perturbation -/
lemma internalDiam_addFun_mono (hξ : 0 ≤ ξ) (hw : WeylAt ξ D k) {f g : C(ℂ, ℝ)} (hfg : f ≤ g)
    (A : Set ℂ) {V : Set ℂ} (hV : IsOpen V) :
    internalDiam (D (addFun k f)) A V ≤ internalDiam (D (addFun k g)) A V := by
  refine iSup₂_mono fun u _ => iSup₂_mono fun v _ => ?_
  rw [internal_addFun_eq_weylScaleOn hw f hV, internal_addFun_eq_weylScaleOn hw g hV]
  exact weylScaleOn_mono fun x _ => mul_le_mul_of_nonneg_left (hfg x) hξ

/-- two-sided bound of internal diameters for a perturbation with `|f| ≤ ε` on `V` -/
lemma internalDiam_addFun_mem (hξ : 0 ≤ ξ) (hw : WeylAt ξ D k) {f : C(ℂ, ℝ)} {ε : ℝ}
    (A : Set ℂ) {V : Set ℂ} (hV : IsOpen V) (hf : ∀ x ∈ V, |f x| ≤ ε) :
    ENNReal.ofReal (Real.exp (-(ξ * ε))) * internalDiam (D k) A V ≤
        internalDiam (D (addFun k f)) A V ∧
      internalDiam (D (addFun k f)) A V ≤
        ENNReal.ofReal (Real.exp (ξ * ε)) * internalDiam (D k) A V := by
  have hb := fun u v => internal_mem_Icc_of_le (D (addFun k f)) (fun x y => (hw f x y).symm) hV
    (a := -(ξ * ε)) (b := ξ * ε)
    (fun x hx => by
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hf x hx)) hξ
      linarith)
    (fun x hx => mul_le_mul_of_nonneg_left (le_of_abs_le (hf x hx)) hξ) u v
  unfold internalDiam
  simp_rw [ENNReal.mul_iSup]
  exact ⟨iSup₂_mono fun u _ => iSup₂_mono fun v _ => (hb u v).1,
    iSup₂_mono fun u _ => iSup₂_mono fun v _ => (hb u v).2⟩

end Weyl

/-- a quantity squeezed between `e^{-ξε} a` and `e^{ξε} a` (for every `ε > 0`, eventually) is
eventually on the same side of a threshold `T ≠ a` as `a` -/
lemma eventually_le_iff_of_sandwich {ξ : ℝ} {a T : ℝ≥0∞} (hne : a ≠ T) {b : ℕ → ℝ≥0∞}
    (hb : ∀ ε > 0, ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp (-(ξ * ε))) * a ≤ b n ∧
      b n ≤ ENNReal.ofReal (Real.exp (ξ * ε)) * a) :
    ∀ᶠ n in atTop, (b n ≤ T ↔ a ≤ T) := by
  have ht : ∀ c : ℝ, Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (c * ε)) * a)
      (𝓝[>] 0) (𝓝 a) := fun c => by
    have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (c * ε))) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun ε : ℝ => ENNReal.ofReal (Real.exp (c * ε)) :=
        ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      simpa using hc.tendsto 0
    simpa using (ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)).mono_left nhdsWithin_le_nhds
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ε, hεT, hε⟩ :=
      (((ht ξ).eventually (gt_mem_nhds hlt)).and self_mem_nhdsWithin).exists
    filter_upwards [hb ε hε] with n hn
    exact ⟨fun _ => hlt.le, fun _ => hn.2.trans hεT.le⟩
  · obtain ⟨ε, hεT, hε⟩ :=
      (((ht (-ξ)).eventually (lt_mem_nhds hgt)).and self_mem_nhdsWithin).exists
    filter_upwards [hb ε hε] with n hn
    have hn' : T < b n := lt_of_lt_of_le (by simpa [neg_mul] using hεT) hn.1
    exact ⟨fun h => absurd h (not_le.2 hn'), fun h => absurd h (not_le.2 hgt)⟩

section Events

variable {ξ : ℝ} {D : DistC → ContMetric} {k : DistC} {ι : Type*}

/-- **the diameter events are non-increasing in the field** (CONF C:664–667, C:1236–1238) -/
theorem diamEvent_weyl_mono (hξ : 0 ≤ ξ) (hw : WeylAt ξ D k) (I : Set ι) (A V : ι → Set ℂ)
    (hV : ∀ i, IsOpen (V i)) (T : ι → ℝ≥0∞) {f g : C(ℂ, ℝ)} (hfg : f ≤ g)
    (hg : ∀ i ∈ I, internalDiam (D (addFun k g)) (A i) (V i) ≤ T i) :
    ∀ i ∈ I, internalDiam (D (addFun k f)) (A i) (V i) ≤ T i := fun i hi =>
  (internalDiam_addFun_mono hξ hw hfg (A i) (hV i)).trans (hg i hi)

/-- **the diameter events are continuous at `k`** along continuous perturbations `fₙ → 0`
(locally uniformly), provided no diameter equals its threshold (CONF C:667–669, C:1239–1241) -/
theorem diamEvent_weyl_cont (hξ : 0 ≤ ξ) (hw : WeylAt ξ D k) {I : Set ι} (hI : I.Finite)
    (A V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (hVb : ∀ i, Bornology.IsBounded (V i))
    (T : ι → ℝ≥0∞) (hne : ∀ i ∈ I, internalDiam (D k) (A i) (V i) ≠ T i)
    {fn : ℕ → C(ℂ, ℝ)} (hfn : Tendsto fn atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ((∀ i ∈ I, internalDiam (D (addFun k (fn n))) (A i) (V i) ≤ T i) ↔
      ∀ i ∈ I, internalDiam (D k) (A i) (V i) ≤ T i) := by
  have hall : ∀ i ∈ I, ∀ᶠ n in atTop,
      (internalDiam (D (addFun k (fn n))) (A i) (V i) ≤ T i ↔
        internalDiam (D k) (A i) (V i) ≤ T i) := by
    intro i hi
    refine eventually_le_iff_of_sandwich (ξ := ξ) (hne i hi) fun ε hε => ?_
    have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hfn)
      (closure (V i)) (hVb i).isCompact_closure
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu ε hε] with n hn
    refine internalDiam_addFun_mem hξ hw (A i) (hV i) fun x hx => ?_
    have := hn x (subset_closure hx)
    rw [ContinuousMap.zero_apply, dist_comm, Real.dist_eq, sub_zero] at this
    exact this.le
  filter_upwards [(eventually_all_finite hI).2 hall] with n hn
  exact ⟨fun h i hi => (hn i hi).1 (h i hi), fun h i hi => (hn i hi).2 (h i hi)⟩

end Events

end LQGMetric.CONF
