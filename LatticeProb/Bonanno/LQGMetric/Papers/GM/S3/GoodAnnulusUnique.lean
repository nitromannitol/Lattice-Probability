/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusUnique at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Meas.CR
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Rat

/-!
# Uniqueness of geodesics as a Borel condition (task P2-M2E, decisions D43, D48)

For GM Lemma 3.7 (`uniqueness-final.tex` l. 1340–1360) the event `𝖤_r(z)` quantifies over pairs
`(u, v)` whose `D_h`-geodesic is unique. "The geodesic from `u` to `v` is unique" is coanalytic for
fixed `(u, v)` (`uMeasurableSet_geodUnique`), which does not survive the quantifier over `(u, v)`.
Decision D48: on boundedly compact length metrics it is a Borel condition on `(D, u, v)`.

We prove this through midpoints (own elementary argument, replacing D43/D48's upper-semicontinuity
route by a shorter one with the same conclusion): for `t ∈ [0,1]` let
`M_t = {x | D(u,x) = t D(u,v), D(x,v) = (1−t) D(u,v)}`.
* `geodUnique_of_midUnique`: if every `M_t`, `t` rational, has at most one point, the geodesic is
  unique (two geodesics agree at rational times, hence everywhere) — for every metric;
* `midUnique_of_geodUnique`: conversely, if geodesics exist between all pairs (boundedly compact
  length metrics, `exists_isGeod01_of_bcpt`), uniqueness of the geodesic from `u` to `v` forces
  every `M_t` to be a singleton (a point of `M_t` lies on the concatenation of geodesics
  `u → x → v`, `exists_geod_through`);
* `measurableSet_midUnique`: `{(D,u,v) | MidUnique D u v}` is Borel (CR2,
  `measurableSet_exists_le_of_isClosed`, over the closed sets `{‖x − y‖ ≥ 1/(n+1)}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric.GM

/-- `t ↦ projIcc 0 1 t ∈ [0,1]` -/
def pj (t : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one t

lemma pj_coe_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (pj t : ℝ) = t := by
  simp [pj, Set.projIcc_of_mem _ ht]

/-- `x ∈ M_t`: `D(u,x) = t D(u,v)` and `D(x,v) = (1 − t) D(u,v)` -/
def midPt (D : ContMetric) (u v : ℂ) (t : ℝ) (x : ℂ) : Prop :=
  D.1 (u, x) = t * D.1 (u, v) ∧ D.1 (x, v) = (1 - t) * D.1 (u, v)

/-- every `M_t`, `t ∈ ℚ ∩ [0,1]`, has at most one point -/
def MidUnique (D : ContMetric) (u v : ℂ) : Prop :=
  ∀ q : ℚ, ∀ x y : ℂ, midPt D u v (pj q) x → midPt D u v (pj q) y → x = y

lemma midPt_of_isGeod01 {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)}
    (h : D.IsGeod01 u v η) (t : unitInterval) : midPt D u v t (η t) := by
  obtain ⟨h0, h1, hd⟩ := h
  refine ⟨?_, ?_⟩
  · have := hd 0 t
    rw [h0] at this
    rw [this]; simp [abs_of_nonneg t.2.1]
  · have := hd t 1
    rw [h1] at this
    rw [this]; simp [abs_of_nonneg (sub_nonneg.2 t.2.2)]

lemma denseRange_pj_rat : DenseRange fun q : ℚ => pj q :=
  (Set.projIcc_surjective zero_le_one).denseRange.comp Rat.denseRange_cast continuous_projIcc

/-- `MidUnique` ⇒ the geodesic is unique (any metric) -/
theorem geodUnique_of_midUnique {D : ContMetric} {u v : ℂ} (h : MidUnique D u v) :
    D.GeodUnique u v := by
  intro η η' hη hη'
  have : (η : unitInterval → ℂ) = η' :=
    denseRange_pj_rat.equalizer η.continuous η'.continuous (funext fun q =>
      h q _ _ (midPt_of_isGeod01 hη _) (midPt_of_isGeod01 hη' _))
  exact ContinuousMap.ext (congrFun this)

lemma dist_symm' (D : ContMetric) (a b : ℂ) : D.1 (a, b) = D.1 (b, a) := D.2.symm a b

/-- a point `x ∈ M_t`, `0 < t < 1`, lies on a geodesic: the concatenation of geodesics
`u → x → v` -/
theorem exists_geod_through {D : ContMetric} {u v x : ℂ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {η₁ η₂ : C(unitInterval, ℂ)} (h1 : D.IsGeod01 u x η₁) (h2 : D.IsGeod01 x v η₂)
    (hx : midPt D u v t x) : ∃ η : C(unitInterval, ℂ), D.IsGeod01 u v η ∧ η (pj t) = x := by
  set L := D.1 (u, v) with hL
  have ht1' : 0 < 1 - t := by linarith
  have e0 : pj 0 = 0 := Subtype.ext (pj_coe_of_mem ⟨le_rfl, zero_le_one⟩)
  have e1 : pj 1 = 1 := Subtype.ext (pj_coe_of_mem ⟨zero_le_one, le_rfl⟩)
  let F : unitInterval → ℂ := fun s =>
    if (s : ℝ) ≤ t then η₁ (pj ((s : ℝ) / t)) else η₂ (pj (((s : ℝ) - t) / (1 - t)))
  have hFc : Continuous F := by
    refine Continuous.if_le (η₁.continuous.comp (continuous_projIcc.comp
      (continuous_subtype_val.div_const t))) (η₂.continuous.comp (continuous_projIcc.comp
      ((continuous_subtype_val.sub continuous_const).div_const _))) continuous_subtype_val
      continuous_const fun s hs => ?_
    show η₁ (pj ((s : ℝ) / t)) = η₂ (pj (((s : ℝ) - t) / (1 - t)))
    rw [hs, div_self ht0.ne', sub_self, zero_div, e1, e0, h1.2.1, h2.1]
  have hux : D.1 (u, x) = t * L := hx.1
  have hxv : D.1 (x, v) = (1 - t) * L := hx.2
  -- the two pieces
  have hp1 : ∀ s : unitInterval, (s : ℝ) ≤ t → ((pj ((s : ℝ) / t) : unitInterval) : ℝ) = s / t :=
    fun s hs => pj_coe_of_mem ⟨div_nonneg s.2.1 ht0.le, (div_le_one ht0).2 hs⟩
  have hp2 : ∀ s : unitInterval, ¬ (s : ℝ) ≤ t →
      ((pj (((s : ℝ) - t) / (1 - t)) : unitInterval) : ℝ) = (s - t) / (1 - t) := fun s hs =>
    pj_coe_of_mem ⟨div_nonneg (by linarith [not_le.1 hs]) ht1'.le,
      (div_le_one ht1').2 (by linarith [s.2.2])⟩
  have d1 : ∀ a b : unitInterval, D.1 (η₁ a, η₁ b) = |(b : ℝ) - a| * (t * L) := fun a b => by
    rw [h1.2.2 a b, hux]
  have d2 : ∀ a b : unitInterval, D.1 (η₂ a, η₂ b) = |(b : ℝ) - a| * ((1 - t) * L) := fun a b => by
    rw [h2.2.2 a b, hxv]
  have hL0 : 0 ≤ L := by
    have := D.2.triangle u v u
    rw [D.2.self_eq_zero, dist_symm' D v u] at this; linarith
  -- distances to the endpoints and to `x`
  have hend : ∀ s : unitInterval, D.1 (u, F s) = s * L ∧ D.1 (F s, v) = (1 - s) * L ∧
      D.1 (F s, x) = |(s : ℝ) - t| * L := by
    intro s
    by_cases hs : (s : ℝ) ≤ t
    · have hF : F s = η₁ (pj ((s : ℝ) / t)) := if_pos hs
      have a1 : D.1 (u, F s) = s * L := by
        rw [hF, ← h1.1, d1, hp1 s hs, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero,
          abs_of_nonneg (div_nonneg s.2.1 ht0.le)]
        field_simp
      have a3 : D.1 (F s, x) = |(s : ℝ) - t| * L := by
        rw [hF, ← h1.2.1, d1, hp1 s hs, show ((1 : unitInterval) : ℝ) = 1 from rfl,
          abs_of_nonneg (by rw [sub_nonneg, div_le_one ht0]; exact hs),
          abs_of_nonpos (by linarith)]
        field_simp; ring
      refine ⟨a1, le_antisymm ?_ ?_, a3⟩
      · have := D.2.triangle (F s) x v
        rw [a3, hxv, abs_of_nonpos (by linarith)] at this; linarith
      · have := D.2.triangle u (F s) v
        rw [a1] at this; linarith
    · have hF : F s = η₂ (pj (((s : ℝ) - t) / (1 - t))) := if_neg hs
      have hst : t < s := not_le.1 hs
      have a2 : D.1 (F s, v) = (1 - s) * L := by
        rw [hF, ← h2.2.1, d2, hp2 s hs, show ((1 : unitInterval) : ℝ) = 1 from rfl,
          abs_of_nonneg (by rw [sub_nonneg, div_le_one ht1']; linarith [s.2.2])]
        field_simp; ring
      have a3 : D.1 (F s, x) = |(s : ℝ) - t| * L := by
        rw [dist_symm', hF, ← h2.1, d2, hp2 s hs, show ((0 : unitInterval) : ℝ) = 0 from rfl,
          sub_zero, abs_of_nonneg (div_nonneg (by linarith) ht1'.le), abs_of_nonneg (by linarith)]
        field_simp
      refine ⟨le_antisymm ?_ ?_, a2, a3⟩
      · have := D.2.triangle u x (F s)
        rw [hux, dist_symm' D x (F s), a3, abs_of_nonneg (by linarith)] at this; linarith
      · have := D.2.triangle u (F s) v
        rw [a2] at this; linarith
  -- upper bound on increments
  have hup : ∀ a b : unitInterval, (a : ℝ) ≤ b → D.1 (F a, F b) ≤ ((b : ℝ) - a) * L := by
    intro a b hab
    by_cases ha : (a : ℝ) ≤ t
    · by_cases hb : (b : ℝ) ≤ t
      · have hFa : F a = η₁ (pj ((a : ℝ) / t)) := if_pos ha
        have hFb : F b = η₁ (pj ((b : ℝ) / t)) := if_pos hb
        rw [hFa, hFb, d1, hp1 a ha, hp1 b hb, ← sub_div, abs_of_nonneg (div_nonneg
          (by linarith) ht0.le)]
        field_simp; rfl
      · have := D.2.triangle (F a) x (F b)
        rw [(hend a).2.2, dist_symm' D x (F b), (hend b).2.2, abs_of_nonpos (by linarith),
          abs_of_nonneg (by linarith [not_le.1 hb])] at this
        linarith
    · have hb : ¬ (b : ℝ) ≤ t := fun hb => ha (hab.trans hb)
      have hFa : F a = η₂ (pj (((a : ℝ) - t) / (1 - t))) := if_neg ha
      have hFb : F b = η₂ (pj (((b : ℝ) - t) / (1 - t))) := if_neg hb
      rw [hFa, hFb, d2, hp2 a ha, hp2 b hb, ← sub_div, abs_of_nonneg (div_nonneg
        (by linarith) ht1'.le)]
      field_simp; ring_nf; rfl
  have hinc : ∀ a b : unitInterval, (a : ℝ) ≤ b → D.1 (F a, F b) = ((b : ℝ) - a) * L := by
    intro a b hab
    refine le_antisymm (hup a b hab) ?_
    have h₁ := D.2.triangle u (F a) v
    have h₂ := D.2.triangle (F a) (F b) v
    rw [(hend a).1, (hend b).2.1] at *
    linarith [(hend a).2.1]
  refine ⟨⟨F, hFc⟩, ⟨?_, ?_, fun a b => ?_⟩, ?_⟩
  · show F 0 = u
    have : F 0 = η₁ (pj (((0 : unitInterval) : ℝ) / t)) := if_pos (by simp [ht0.le])
    rw [this, show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_div, e0, h1.1]
  · show F 1 = v
    have : F 1 = η₂ (pj ((((1 : unitInterval) : ℝ) - t) / (1 - t))) :=
      if_neg (by simp; linarith)
    rw [this, show ((1 : unitInterval) : ℝ) = 1 from rfl, div_self ht1'.ne', e1, h2.2.1]
  · show D.1 (F a, F b) = |(b : ℝ) - a| * L
    rcases le_total (a : ℝ) b with hab | hab
    · rw [hinc a b hab, abs_of_nonneg (by linarith)]
    · rw [dist_symm', hinc b a hab, abs_of_nonpos (by linarith)]; ring
  · show F (pj t) = x
    have hpt : ((pj t : unitInterval) : ℝ) = t := pj_coe_of_mem ⟨ht0.le, ht1.le⟩
    have : F (pj t) = η₁ (pj (((pj t : unitInterval) : ℝ) / t)) := if_pos hpt.le
    rw [this, hpt, div_self ht0.ne', e1, h1.2.1]

/-- uniqueness of the geodesic ⇒ `MidUnique`, when geodesics exist between all pairs -/
theorem midUnique_of_geodUnique {D : ContMetric}
    (hex : ∀ a b : ℂ, ∃ η, D.IsGeod01 a b η) {u v : ℂ} (h : D.GeodUnique u v) :
    MidUnique D u v := by
  intro q x y hx hy
  set t : ℝ := ((pj q : unitInterval) : ℝ) with ht
  have ht01 : 0 ≤ t ∧ t ≤ 1 := ⟨(pj q).2.1, (pj q).2.2⟩
  rcases eq_or_lt_of_le ht01.1 with h0 | h0
  · have e1 : D.1 (u, x) = 0 := by rw [hx.1, ← h0, zero_mul]
    have e2 : D.1 (u, y) = 0 := by rw [hy.1, ← h0, zero_mul]
    exact (D.2.eq_of_eq_zero _ _ e1).symm.trans (D.2.eq_of_eq_zero _ _ e2)
  rcases eq_or_lt_of_le ht01.2 with h1 | h1
  · have e1 : D.1 (x, v) = 0 := by rw [hx.2, h1, sub_self, zero_mul]
    have e2 : D.1 (y, v) = 0 := by rw [hy.2, h1, sub_self, zero_mul]
    exact (D.2.eq_of_eq_zero _ _ e1).trans (D.2.eq_of_eq_zero _ _ e2).symm
  obtain ⟨ηx1, hx1⟩ := hex u x
  obtain ⟨ηx2, hx2⟩ := hex x v
  obtain ⟨ηy1, hy1⟩ := hex u y
  obtain ⟨ηy2, hy2⟩ := hex y v
  obtain ⟨ηx, hηx, hηxt⟩ := exists_geod_through h0 h1 hx1 hx2 hx
  obtain ⟨ηy, hηy, hηyt⟩ := exists_geod_through h0 h1 hy1 hy2 hy
  rw [← hηxt, ← hηyt, h ηx ηy hηx hηy]

/-- the defect `|D(u,x) − tD(u,v)| + |D(x,v) − (1−t)D(u,v)|` -/
def midDefect (D : ContMetric) (u v : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  |D.1 (u, x) - t * D.1 (u, v)| + |D.1 (x, v) - (1 - t) * D.1 (u, v)|

lemma midDefect_nonneg (D : ContMetric) (u v : ℂ) (t : ℝ) (x : ℂ) : 0 ≤ midDefect D u v t x :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma midPt_iff_defect {D : ContMetric} {u v : ℂ} {t : ℝ} {x : ℂ} :
    midPt D u v t x ↔ midDefect D u v t x ≤ 0 := by
  unfold midPt midDefect
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]; simp
  · intro h
    have a := abs_nonneg (D.1 (u, x) - t * D.1 (u, v))
    have b := abs_nonneg (D.1 (x, v) - (1 - t) * D.1 (u, v))
    exact ⟨sub_eq_zero.1 (abs_eq_zero.1 (by linarith)), sub_eq_zero.1 (abs_eq_zero.1 (by linarith))⟩

lemma continuous_midDefect (t : ℝ) :
    Continuous fun p : (ContMetric × ℂ × ℂ) × (ℂ × ℂ) => midDefect p.1.1 p.1.2.1 p.1.2.2 t p.2.1 := by
  unfold midDefect
  have hev := continuous_contMetric_apply
  have f1 : Continuous fun p : (ContMetric × ℂ × ℂ) × (ℂ × ℂ) => p.1.1.1 (p.1.2.1, p.2.1) :=
    hev.comp (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd.fst))
  have f2 : Continuous fun p : (ContMetric × ℂ × ℂ) × (ℂ × ℂ) => p.1.1.1 (p.1.2.1, p.1.2.2) :=
    hev.comp (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_fst.snd.snd))
  have f3 : Continuous fun p : (ContMetric × ℂ × ℂ) × (ℂ × ℂ) => p.1.1.1 (p.2.1, p.1.2.2) :=
    hev.comp (continuous_fst.fst.prodMk (continuous_snd.fst.prodMk continuous_fst.snd.snd))
  exact ((f1.sub (continuous_const.mul f2)).abs).add ((f3.sub (continuous_const.mul f2)).abs)

/-- **`MidUnique` is a Borel condition on `(D, u, v)`** -/
theorem measurableSet_midUnique :
    MeasurableSet {p : ContMetric × ℂ × ℂ | MidUnique p.1 p.2.1 p.2.2} := by
  have key : ∀ (q : ℚ) (n : ℕ), MeasurableSet {p : ContMetric × ℂ × ℂ | ∃ xy ∈
      {xy : ℂ × ℂ | 1 / ((n : ℝ) + 1) ≤ ‖xy.1 - xy.2‖},
      midDefect p.1 p.2.1 p.2.2 (pj q) xy.1 + midDefect p.1 p.2.1 p.2.2 (pj q) xy.2 ≤ 0} := by
    intro q n
    refine measurableSet_exists_le_of_isClosed (f := fun (p : ContMetric × ℂ × ℂ) (xy : ℂ × ℂ) =>
      midDefect p.1 p.2.1 p.2.2 (pj q) xy.1 + midDefect p.1 p.2.1 p.2.2 (pj q) xy.2)
      (fun p => ?_) (fun xy => ?_) (isClosed_le continuous_const
        (continuous_fst.sub continuous_snd).norm) 0
    · have h := continuous_midDefect (pj q)
      exact (h.comp (continuous_const.prodMk continuous_id)).add
        (h.comp (continuous_const.prodMk (continuous_snd.prodMk continuous_fst)))
    · have h := continuous_midDefect (pj q)
      exact ((h.comp (continuous_id.prodMk continuous_const)).add
        (h.comp (continuous_id.prodMk (continuous_const : Continuous fun _ :
          ContMetric × ℂ × ℂ => (xy.2, xy.1))))).measurable
  have heq : {p : ContMetric × ℂ × ℂ | MidUnique p.1 p.2.1 p.2.2} =
      ⋂ (q : ℚ) (n : ℕ), {p : ContMetric × ℂ × ℂ | ∃ xy ∈
        {xy : ℂ × ℂ | 1 / ((n : ℝ) + 1) ≤ ‖xy.1 - xy.2‖},
        midDefect p.1 p.2.1 p.2.2 (pj q) xy.1 + midDefect p.1 p.2.1 p.2.2 (pj q) xy.2 ≤ 0}ᶜ := by
    ext p
    simp only [MidUnique, mem_ofPred_eq, mem_iInter, mem_compl_iff, not_exists, not_and]
    constructor
    · intro h q n xy hxy hle
      have a := midDefect_nonneg p.1 p.2.1 p.2.2 (pj q) xy.1
      have b := midDefect_nonneg p.1 p.2.1 p.2.2 (pj q) xy.2
      have e := h q xy.1 xy.2 (midPt_iff_defect.2 (by linarith)) (midPt_iff_defect.2 (by linarith))
      rw [e, sub_self, norm_zero] at hxy
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro h q x y hx hy
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 (sub_ne_zero.2 hne))
      exact h q n (x, y) hn.le (by linarith [midPt_iff_defect.1 hx, midPt_iff_defect.1 hy])
  rw [heq]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun n => (key q n).compl

end LQGMetric.GM
