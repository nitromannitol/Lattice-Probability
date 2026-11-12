/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas3
import LatticeProb.Bonanno.LQGMetric.Meas.CR
import LatticeProb.Bonanno.LQGMetric.Meas.Internal

/-!
# GM Lemma 3.7: conditions 2 and 3 of `𝖤_r(z)` are universally measurable (task P2-LOCMEAS)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
conditions 2 and 3 of `𝖤_r(z)` (l. 1328–1329). Decision D30: events quantified over continua or
paths are universally measurable (Lusin). Here paths `P : [a, b] → ℂ` are replaced by
`η ∈ C([0,1], ℂ)` (affine reparametrization, `exists_reparam`), and then

* `lowerSemicontinuous_lenPath`: `(d, η) ↦ len(η; d)` is lower semicontinuous (a supremum of
  continuous partition sums), hence Borel;
* `isOpen_setOf_not_disconnects`: "`range η` does not disconnect `E` from `F`" is open in `η`
  (a path avoiding the compact `range η` keeps avoiding it under uniform perturbation);
* `uMeasurableSet_gaLongB`: condition 2, with the internal metric replaced by its Borel version
  `chainInf` (equal on length metrics, `ContMetric.internal_eq_chainInf`), is coanalytic;
* `uMeasurableSet_gaAround`: condition 3 is analytic.

Own elementary arguments (no source needed beyond D30's Lusin theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-! ## Paths on `[a, b]` versus `C([0,1], ℂ)` -/

lemma image_affine_Icc {a b : ℝ} (hab : a ≤ b) :
    (fun t : ℝ => a + t * (b - a)) '' Icc 0 1 = Icc a b := by
  have h1 : (fun t : ℝ => a + t * (b - a)) = (fun x => a + x) ∘ (fun t => t * (b - a)) := rfl
  rw [h1, image_comp, image_mul_right_Icc zero_le_one (sub_nonneg.2 hab), image_const_add_Icc]
  congr 1 <;> ring

lemma pjPath_image (η : C(unitInterval, ℂ)) : (fun t => η (pj t)) '' Icc 0 1 = range η := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t, t.2, ?_⟩
    show η (pj t) = η t
    rw [show pj t = t from Subtype.ext (pj_coe_of_mem t.2)]

lemma pjPath_continuousOn (η : C(unitInterval, ℂ)) :
    ContinuousOn (fun t => η (pj t)) (Icc 0 1) :=
  (η.continuous.comp continuous_projIcc).continuousOn

lemma pjPath_zero (η : C(unitInterval, ℂ)) : η (pj 0) = η 0 := by
  rw [show pj 0 = 0 from Set.projIcc_left zero_le_one]

lemma pjPath_one (η : C(unitInterval, ℂ)) : η (pj 1) = η 1 := by
  rw [show pj 1 = 1 from Set.projIcc_right zero_le_one]

/-- **affine reparametrization**: a path continuous on `[a, b]` is a `C([0,1], ℂ)` path with the
same endpoints, range and length (for every continuous metric) -/
lemma exists_reparam {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    ∃ η : C(unitInterval, ℂ), η 0 = P a ∧ η 1 = P b ∧ range η = P '' Icc a b ∧
      ∀ d : ContMetric, d.len (fun t => η (pj t)) 0 1 = d.len P a b := by
  set φ : ℝ → ℝ := fun t => a + t * (b - a)
  have hφm : ∀ t : unitInterval, φ t ∈ Icc a b := fun t => by
    have := t.2.1; have := t.2.2
    exact ⟨by simp only [φ]; nlinarith, by simp only [φ]; nlinarith⟩
  let η : C(unitInterval, ℂ) := ⟨fun t => P (φ t), hP.comp_continuous (by fun_prop) hφm⟩
  refine ⟨η, by simp [η, φ], by simp [η, φ], ?_, fun d => ?_⟩
  · rw [← image_affine_Icc hab, image_image]
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  · unfold ContMetric.len curveLength
    have heq : EqOn (d.pt ∘ fun t => η (pj t)) ((d.pt ∘ P) ∘ φ) (Icc 0 1) := fun t ht => by
      simp only [Function.comp_apply, η, ContinuousMap.coe_mk, pj_coe_of_mem ht]
    rw [eVariationOn.eq_of_eqOn heq, eVariationOn.comp_eq_of_monotoneOn _ φ
      (fun s _ t _ hst => by simp only [φ]; nlinarith [sub_nonneg.2 hab]), image_affine_Icc hab]

/-- `∀` over paths on intervals `↔` `∀` over `C([0,1], ℂ)` -/
lemma forall_path_iff (d : ContMetric) (Q : ℂ → ℂ → Set ℂ → ℝ≥0∞ → Prop) :
    (∀ (a b : ℝ) (P : ℝ → ℂ), a ≤ b → ContinuousOn P (Icc a b) →
      Q (P a) (P b) (P '' Icc a b) (d.len P a b)) ↔
    ∀ η : C(unitInterval, ℂ), Q (η 0) (η 1) (range η) (d.len (fun t => η (pj t)) 0 1) := by
  constructor
  · intro H η
    have := H 0 1 (fun t => η (pj t)) zero_le_one (pjPath_continuousOn η)
    rwa [pjPath_zero, pjPath_one, pjPath_image] at this
  · intro H a b P hab hP
    obtain ⟨η, h0, h1, hr, hl⟩ := exists_reparam hab hP
    have := H η
    rwa [h0, h1, hr, hl] at this

/-- `∃` over paths on intervals `↔` `∃` over `C([0,1], ℂ)` -/
lemma exists_path_iff (d : ContMetric) (Q : Set ℂ → ℝ≥0∞ → Prop) :
    (∃ (a b : ℝ) (P : ℝ → ℂ), a ≤ b ∧ ContinuousOn P (Icc a b) ∧
      Q (P '' Icc a b) (d.len P a b)) ↔
    ∃ η : C(unitInterval, ℂ), Q (range η) (d.len (fun t => η (pj t)) 0 1) := by
  constructor
  · rintro ⟨a, b, P, hab, hP, hQ⟩
    obtain ⟨η, -, -, hr, hl⟩ := exists_reparam hab hP
    exact ⟨η, by rwa [hr, hl]⟩
  · rintro ⟨η, hQ⟩
    refine ⟨0, 1, fun t => η (pj t), zero_le_one, pjPath_continuousOn η, ?_⟩
    rwa [pjPath_image]

/-! ## Borel ingredients -/

/-- the `d`-length of `η` is lower semicontinuous in `(d, η)` -/
theorem lowerSemicontinuous_lenPath :
    LowerSemicontinuous fun p : ContMetric × C(unitInterval, ℂ) =>
      p.1.len (fun t => p.2 (pj t)) 0 1 := by
  have e : (fun p : ContMetric × C(unitInterval, ℂ) => p.1.len (fun t => p.2 (pj t)) 0 1) =
      fun p => ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1},
        ∑ i ∈ Finset.range q.1,
          ENNReal.ofReal (p.1.1 (p.2 (pj (q.2.1 (i + 1))), p.2 (pj (q.2.1 i)))) := by
    funext p
    unfold ContMetric.len curveLength eVariationOn
    simp only [Function.comp_apply, ContMetric.edist_pt]
  rw [e]
  refine lowerSemicontinuous_iSup fun q => Continuous.lowerSemicontinuous ?_
  refine continuous_finsetSum _ fun i _ => ENNReal.continuous_ofReal.comp ?_
  exact continuous_contMetric_apply.comp (continuous_fst.prodMk
    (((continuous_eval_const _).comp continuous_snd).prodMk
      ((continuous_eval_const _).comp continuous_snd)))

set_option maxHeartbeats 1000000 in
/-- `(g, η) ↦ len(η; D_g)` is Borel -/
theorem measurable_lenPath {D : DistC → ContMetric} (hD : Measurable D) :
    Measurable fun p : DistC × C(unitInterval, ℂ) => (D p.1).len (fun t => p.2 (pj t)) 0 1 := by
  have hm : Measurable fun p : ContMetric × C(unitInterval, ℂ) =>
      p.1.len (fun t => p.2 (pj t)) 0 1 := lowerSemicontinuous_lenPath.measurable
  exact hm.comp ((hD.comp measurable_fst).prodMk measurable_snd)

/-- "`range η` does not disconnect `E` from `F`" is open -/
theorem isOpen_setOf_not_disconnects (E F : Set ℂ) :
    IsOpen {η : C(unitInterval, ℂ) | ¬ Disconnects (range η) E F} := by
  have e : {η : C(unitInterval, ℂ) | ¬ Disconnects (range η) E F} =
      ⋃ (x : ℂ) (y : ℂ) (γ : Path x y) (_ : x ∈ E) (_ : y ∈ F),
        {η : C(unitInterval, ℂ) | MapsTo η univ (range γ)ᶜ} := by
    ext η
    simp only [Disconnects, not_forall, mem_ofPred_eq, mem_iUnion, exists_prop]
    refine exists₃_congr fun x y γ => ?_
    simp only [← exists_prop, not_nonempty_iff_eq_empty]
    refine exists_congr fun _ => exists_congr fun _ => ?_
    constructor
    · intro h t _ ht
      exact (eq_empty_iff_forall_notMem.1 h) (η t) ⟨ht, t, rfl⟩
    · intro h
      refine eq_empty_iff_forall_notMem.2 ?_
      rintro _ ⟨hγ, t, rfl⟩
      exact h (mem_univ t) hγ
  rw [e]
  exact isOpen_iUnion fun x => isOpen_iUnion fun y => isOpen_iUnion fun γ =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => ContinuousMap.isOpen_setOfPred_mapsTo
      isCompact_univ (isCompact_range γ.continuous).isClosed.isOpen_compl

theorem measurable_setDist_singleton (F : Set ℂ) :
    Measurable fun p : ContMetric × ℂ => setDist p.1 {p.2} F := by
  have e : (fun p : ContMetric × ℂ => setDist p.1 {p.2} F) =
      fun p => ⨅ y ∈ F, ENNReal.ofReal (p.1.1 (p.2, y)) := by
    funext p; rw [setDist_eq_iInf]; simp only [mem_singleton_iff, iInf_iInf_eq_left]
  rw [e]
  refine measurable_biInf_of_continuous (f := fun (p : ContMetric × ℂ) (y : ℂ) =>
    ENNReal.ofReal (p.1.1 (p.2, y))) (fun p => ?_) (fun y => ?_) F
  · exact ENNReal.continuous_ofReal.comp (p.1.1.continuous.comp
      (continuous_const.prodMk continuous_id))
  · exact (ENNReal.continuous_ofReal.comp (continuous_contMetric_apply.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))).measurable

theorem measurable_setDist (A B : Set ℂ) : Measurable fun d : ContMetric => setDist d A B := by
  have e : (fun d : ContMetric => setDist d A B) =
      fun d => ⨅ p ∈ A ×ˢ B, ENNReal.ofReal (d.1 p) := by
    funext d; rw [setDist_eq_iInf, biInf_prod]
  rw [e]
  refine measurable_biInf_of_continuous (f := fun (d : ContMetric) (p : ℂ × ℂ) =>
    ENNReal.ofReal (d.1 p)) (fun d => ENNReal.continuous_ofReal.comp d.1.continuous)
    (fun p => ?_) _
  exact (ENNReal.continuous_ofReal.comp (continuous_contMetric_apply.comp
    (continuous_id.prodMk continuous_const))).measurable

/-! ## Conditions 2 and 3 are universally measurable -/

lemma measurable_of_set {α : Type*} [MeasurableSpace α] {p : α → Prop}
    (h : MeasurableSet {a | p a}) : Measurable p := measurableSet_setOfPred.1 h

/-- condition 2 of `𝖤_r(z)` with the internal metric replaced by its Borel version `chainInf` -/
def gaLongB (D D' : DistC → ContMetric) (α r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r,
    (setDist (D g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
        ENNReal.ofReal ((D g).1 (u, v)) ∨
      setDist (D' g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
        ENNReal.ofReal ((D' g).1 (u, v))) →
    ∀ (a b : ℝ) (P : ℝ → ℂ), a ≤ b → ContinuousOn P (Icc a b) → P a = u → P b = v →
      P '' Icc a b ⊆ closure (annulus z (α * r) r : Set ℂ) →
      (D g).chainInf (annulus z (r / 2) (2 * r)) u v < (D g).len P a b}

lemma mem_gaLong_iff_gaLongB {D D' : DistC → ContMetric} {α r : ℝ} {z : ℂ} {g : DistC}
    (hL : (D g).IsLength) : g ∈ gaLong D D' α r z ↔ g ∈ gaLongB D D' α r z := by
  simp only [gaLong, gaLongB, mem_ofPred_eq,
    (D g).internal_eq_chainInf hL (annulus z (r / 2) (2 * r)).isOpen]

/-- the Borel relation behind condition 2 -/
def gaLongS (D D' : DistC → ContMetric) (α r : ℝ) (z : ℂ) :
    Set (DistC × ℂ × ℂ × C(unitInterval, ℂ)) :=
  {p | p.2.1 ∈ sphere z (α * r) → p.2.2.1 ∈ sphere z r →
      (setDist (D p.1) {p.2.1} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
          ENNReal.ofReal ((D p.1).1 (p.2.1, p.2.2.1)) ∨
        setDist (D' p.1) {p.2.1} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
          ENNReal.ofReal ((D' p.1).1 (p.2.1, p.2.2.1))) →
      p.2.2.2 0 = p.2.1 → p.2.2.2 1 = p.2.2.1 →
      (∀ t, p.2.2.2 t ∈ closure (annulus z (α * r) r : Set ℂ)) →
      (D p.1).chainInf (annulus z (r / 2) (2 * r)) p.2.1 p.2.2.1 <
        (D p.1).len (fun t => p.2.2.2 (pj t)) 0 1}

lemma measurable_setDist_lt {X : Type*} [MeasurableSpace X] {f : X → ContMetric} {u v : X → ℂ}
    (hf : Measurable f) (hu : Measurable u) (hv : Measurable v) (F : Set ℂ) :
    Measurable fun x => setDist (f x) {u x} F < ENNReal.ofReal ((f x).1 (u x, v x)) := by
  have b1 : Measurable fun x => setDist (f x) {u x} F :=
    Measurable.comp (g := fun p : ContMetric × ℂ => setDist p.1 {p.2} F)
      (f := fun x => (f x, u x)) (measurable_setDist_singleton F) (hf.prodMk hu)
  have c0 : Measurable fun q : ContMetric × ℂ × ℂ => ENNReal.ofReal (q.1.1 q.2) :=
    ENNReal.measurable_ofReal.comp continuous_contMetric_apply.measurable
  have b2 : Measurable fun x => ENNReal.ofReal ((f x).1 (u x, v x)) :=
    Measurable.comp (g := fun q : ContMetric × ℂ × ℂ => ENNReal.ofReal (q.1.1 q.2))
      (f := fun x => (f x, u x, v x)) c0 (hf.prodMk (hu.prodMk hv))
  exact measurable_of_set (measurableSet_lt b1 b2)

lemma measurable_chainInf_comp {X : Type*} [MeasurableSpace X] {f : X → ContMetric}
    {u v : X → ℂ} (hf : Measurable f) (hu : Measurable u) (hv : Measurable v) (V : Set ℂ) :
    Measurable fun x => (f x).chainInf V (u x) (v x) :=
  Measurable.comp (g := fun q : ContMetric × ℂ × ℂ => q.1.chainInf V q.2.1 q.2.2)
    (f := fun x => (f x, u x, v x)) (ContMetric.measurable_chainInf V) (hf.prodMk (hu.prodMk hv))

lemma measurable_lenPath_comp {X : Type*} [MeasurableSpace X] {f : X → ContMetric}
    {η : X → C(unitInterval, ℂ)} (hf : Measurable f) (hη : Measurable η) :
    Measurable fun x => (f x).len (fun t => η x (pj t)) 0 1 := by
  have hm : Measurable fun p : ContMetric × C(unitInterval, ℂ) =>
      p.1.len (fun t => p.2 (pj t)) 0 1 := lowerSemicontinuous_lenPath.measurable
  exact Measurable.comp (g := fun p : ContMetric × C(unitInterval, ℂ) =>
      p.1.len (fun t => p.2 (pj t)) 0 1) (f := fun x => (f x, η x)) hm (hf.prodMk hη)

set_option maxHeartbeats 1000000 in
lemma measurableSet_gaLongS {D D' : DistC → ContMetric} (hD : Measurable D)
    (hD' : Measurable D') (α r : ℝ) (z : ℂ) : MeasurableSet (gaLongS D D' α r z) := by
  set K := closure (annulus z (α * r) r : Set ℂ)
  set V : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ)
  have mu : Measurable fun p : DistC × ℂ × ℂ × C(unitInterval, ℂ) => p.2.1 := measurable_snd.fst
  have mv : Measurable fun p : DistC × ℂ × ℂ × C(unitInterval, ℂ) => p.2.2.1 :=
    measurable_snd.snd.fst
  have mη : Measurable fun p : DistC × ℂ × ℂ × C(unitInterval, ℂ) => p.2.2.2 :=
    measurable_snd.snd.snd
  have hKc : IsClosed {η : C(unitInterval, ℂ) | ∀ t, η t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_closure.preimage (continuous_eval_const t)
  have m1 := measurable_of_set ((isClosed_sphere (x := z) (ε := α * r)).measurableSet.preimage mu)
  have m2 := measurable_of_set ((isClosed_sphere (x := z) (ε := r)).measurableSet.preimage mv)
  have m4 := measurable_of_set
    (measurableSet_eq_fun ((continuous_eval_const (0 : unitInterval)).measurable.comp mη) mu)
  have m5 := measurable_of_set
    (measurableSet_eq_fun ((continuous_eval_const (1 : unitInterval)).measurable.comp mη) mv)
  have m6 := measurable_of_set (hKc.measurableSet.preimage mη)
  have m7 := measurable_of_set (measurableSet_lt
    (measurable_chainInf_comp (hD.comp measurable_fst) mu mv V)
    (measurable_lenPath_comp (hD.comp measurable_fst) mη))
  exact measurableSet_setOfPred.2 (m1.imp (m2.imp
    (((measurable_setDist_lt (hD.comp measurable_fst) mu mv _).or
    (measurable_setDist_lt (hD'.comp measurable_fst) mu mv _)).imp (m4.imp (m5.imp (m6.imp m7))))))

/-- **condition 2 is universally measurable** (Borel form, coanalytic) -/
theorem uMeasurableSet_gaLongB {D D' : DistC → ContMetric} (hD : Measurable D)
    (hD' : Measurable D') (α r : ℝ) (z : ℂ) : UMeasurableSet (gaLongB D D' α r z) := by
  set K := closure (annulus z (α * r) r : Set ℂ)
  set V : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ)
  convert UMeasurableSet.setOf_forall (measurableSet_gaLongS hD hD' α r z) using 1
  ext g
  constructor
  · rintro H ⟨u, v, η⟩ hu hv hc h0 h1 hK
    exact (forall_path_iff (D g) (fun x y I l => x = u → y = v → I ⊆ K →
      (D g).chainInf V u v < l)).1 (fun a b P hab hP => H u hu v hv hc a b P hab hP) η h0 h1
      (range_subset_iff.2 hK)
  · intro H u hu v hv hc
    exact (forall_path_iff (D g) (fun x y I l => x = u → y = v → I ⊆ K →
      (D g).chainInf V u v < l)).2 (fun η h0 h1 hK => H (u, v, η) hu hv hc h0 h1
      (range_subset_iff.1 hK))

set_option maxHeartbeats 1000000 in
/-- **condition 3 is universally measurable** (analytic) -/
theorem uMeasurableSet_gaAround {D : DistC → ContMetric} (hD : Measurable D) (α A r : ℝ)
    (z : ℂ) : UMeasurableSet (gaAround D α A r z) := by
  set V : Set ℂ := (annulus z (α * r) r : Set ℂ)
  have hm1 : MeasurableSet {p : DistC × C(unitInterval, ℂ) | range p.2 ⊆ V} := by
    have : {η : C(unitInterval, ℂ) | range η ⊆ V} = {η : C(unitInterval, ℂ) | MapsTo η univ V} := by
      ext η; simp only [mem_ofPred_eq, mapsTo_univ_iff, range_subset_iff]
    have ho := ContinuousMap.isOpen_setOfPred_mapsTo (X := unitInterval) (Y := ℂ) isCompact_univ
      (annulus z (α * r) r).isOpen
    rw [← this] at ho
    exact ho.measurableSet.preimage measurable_snd
  have hm2 : MeasurableSet {p : DistC × C(unitInterval, ℂ) |
      Disconnects (range p.2) (sphere z (α * r)) (sphere z r)} := by
    have := (isOpen_setOf_not_disconnects (sphere z (α * r)) (sphere z r)).measurableSet.compl
    have e : {η : C(unitInterval, ℂ) | ¬ Disconnects (range η) (sphere z (α * r)) (sphere z r)}ᶜ
        = {η : C(unitInterval, ℂ) | Disconnects (range η) (sphere z (α * r)) (sphere z r)} := by
      ext η; simp only [mem_compl_iff, mem_ofPred_eq, not_not]
    rw [e] at this
    exact this.preimage measurable_snd
  have hm3 : MeasurableSet {p : DistC × C(unitInterval, ℂ) |
      (D p.1).len (fun t => p.2 (pj t)) 0 1 ≤
        ENNReal.ofReal A * setDist (D p.1) (sphere z (α * r)) (sphere z r)} :=
    measurableSet_le (measurable_lenPath_comp (hD.comp measurable_fst) measurable_snd)
      (measurable_const.mul ((measurable_setDist _ _).comp (hD.comp measurable_fst)))
  convert UMeasurableSet.setOf_exists (hm1.inter (hm2.inter hm3)) using 1
  ext g
  exact exists_path_iff (D g) (fun I l => I ⊆ V ∧ Disconnects I (sphere z (α * r)) (sphere z r) ∧
    l ≤ ENNReal.ofReal A * setDist (D g) (sphere z (α * r)) (sphere z r))

end LQGMetric.GM
