/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.SetupArc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Setup

/-!
# GM Lemma 4.5, pathwise part: the arc containing `P(t_k)` determines `P(s_k)`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.5
(`lem-geo-sigma-algebra`, l. 1663–1675):

> "On the complementary event `{𝕨 ∉ 𝓑^•_{t_k}}`, we have `P(s_k) ∈ ∂𝓑^•_{s_k}` … Moreover,
> `P|_{[0,t_k]}` is a.s. the unique (hence also leftmost) `D_h`-geodesic from `𝕫` to `P(t_k)`,
> hence `P(s_k)` is one of the points of `Conf_k`. By the definition of `𝓘_k`, this point is
> determined by which arc of `𝓘_k` contains `P(t_k)`."

Formalized here (deterministic, then a.s.): if the `D`-geodesic from `𝕫` to `𝕨` is unique and
`𝕨 ∉ 𝓑^•_t`, `0 < s < t`, then `P(s) ∈ Conf(s,t)`, `P(t) ∈ arcOf (P s)`, and `P(s)` is the only
point `x ∈ Conf(s,t)` whose arc contains `P(t)` (`gm_L4_5_arc`, `gm_L4_5_arc_ae`).
"Unique hence leftmost": the leftmost geodesic to `P(t)` given by CONF Lemma 2.4 agrees with `P`
on `[0,t]`, because any geodesic to `P(t)` followed by `P|_{[t,|P|]}` is a geodesic to `𝕨`
(`gm_geodL_eqOn_of_unique`; the concatenation argument GM leaves implicit, own elementary proof).
The geodesic `P` is the unit-speed form `geodL` of a constant-speed geodesic `η` (decision D31).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Det
variable {D : ContMetric} {z w : ℂ}

theorem gm_D_nonneg (D : ContMetric) (x y : ℂ) : 0 ≤ D.1 (x, y) :=
  @dist_nonneg D.Space _ x y

/-- the unit-speed form `P(t) = η(t / D(z,w))` of a constant-speed geodesic `η` on `[0,1]` -/
def geodL (D : ContMetric) (z w : ℂ) (η : C(unitInterval, ℂ)) (t : ℝ) : ℂ :=
  η (projIcc 0 1 zero_le_one (t / D.1 (z, w)))

theorem gm_geodL_isGeodesicL {η : C(unitInterval, ℂ)} (hη : IsGeod01 D z w η) (hzw : z ≠ w) :
    IsGeodesicL D (geodL D z w η) (D.1 (z, w)) z w := by
  have hL : 0 < D.1 (z, w) :=
    lt_of_le_of_ne (gm_D_nonneg D z w) (fun h0 => hzw (D.2.eq_of_eq_zero z w h0.symm))
  refine ⟨hL.le, ?_, ?_, ?_⟩
  · simp only [geodL, zero_div]
    rw [← hη.1]
    congr 1
    exact projIcc_left _
  · simp only [geodL, div_self hL.ne']
    rw [← hη.2.1]
    congr 1
    exact projIcc_right _
  · intro a ha b hb
    simp only [geodL]
    rw [hη.2.2]
    have hA : a / D.1 (z, w) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ha.1 hL.le, (div_le_one hL).mpr ha.2⟩
    have hB : b / D.1 (z, w) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hb.1 hL.le, (div_le_one hL).mpr hb.2⟩
    rw [projIcc_of_mem _ hA, projIcc_of_mem _ hB]
    simp only
    rw [← sub_div, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']

/-- a unit-speed geodesic gives a constant-speed one: `η(x) = P(L x)` -/
theorem gm_exists_geod01 {P : ℝ → ℂ} {L : ℝ} (hP : IsGeodesicL D P L z w) :
    ∃ η : C(unitInterval, ℂ), IsGeod01 D z w η ∧ ∀ x : unitInterval, η x = P (L * x) := by
  have hc := gm_geodL_continuousOn hP
  have hmaps : ∀ x : unitInterval, L * (x : ℝ) ∈ Icc 0 L :=
    fun x => ⟨mul_nonneg hP.1 x.2.1, mul_le_of_le_one_right hP.1 x.2.2⟩
  refine ⟨⟨fun x => P (L * x), hc.comp_continuous
    (continuous_const.mul continuous_subtype_val) hmaps⟩, ⟨?_, ?_, ?_⟩, fun _ => rfl⟩
  · show P (L * ((0 : unitInterval) : ℝ)) = z
    simp only [Set.Icc.coe_zero, mul_zero]
    exact hP.2.1
  · show P (L * ((1 : unitInterval) : ℝ)) = w
    simp only [Set.Icc.coe_one, mul_one]
    exact hP.2.2.1
  · intro a b
    show D.1 (P (L * a), P (L * b)) = |(b : ℝ) - a| * D.1 (z, w)
    rw [hP.2.2.2 _ (hmaps a) _ (hmaps b)]
    have hLd : D.1 (z, w) = L := by
      have := hP.2.2.2 0 ⟨le_rfl, hP.1⟩ L ⟨hP.1, le_rfl⟩
      rwa [hP.2.1, hP.2.2.1, sub_zero, abs_of_nonneg hP.1] at this
    rw [hLd, ← mul_sub, abs_mul, abs_of_nonneg hP.1, mul_comm]

/-- the mixed case of the concatenation: `D(Q a, P b) = b − a` for `a ≤ t < b` -/
theorem gm_concat_dist {P Q : ℝ → ℂ} {L t : ℝ} (hP : IsGeodesicL D P L z w)
    (hQ : IsGeodesicL D Q t z (P t)) (ht : t ≤ L) {a b : ℝ} (ha : a ∈ Icc 0 t)
    (hb : b ∈ Icc 0 L) (hab : t < b) : D.1 (Q a, P b) = b - a := by
  have htI : t ∈ Icc 0 L := ⟨hQ.1, ht⟩
  have h1 : D.1 (Q a, Q t) = t - a := by
    rw [hQ.2.2.2 a ha t ⟨hQ.1, le_rfl⟩, abs_of_nonneg (by linarith [ha.2])]
  have h2 : D.1 (P t, P b) = b - t := by
    rw [hP.2.2.2 t htI b hb, abs_of_nonneg (by linarith)]
  have h3 : D.1 (z, Q a) = a := by
    have := hQ.2.2.2 0 ⟨le_rfl, hQ.1⟩ a ha
    rwa [hQ.2.1, sub_zero, abs_of_nonneg ha.1] at this
  have h4 : D.1 (z, P b) = b := gm_geodL_dist hP hb
  apply le_antisymm
  · have := D.2.triangle (Q a) (Q t) (P b)
    rw [hQ.2.2.1] at this h1
    linarith
  · have := D.2.triangle z (Q a) (P b)
    linarith

/-- **Unique hence leftmost** (GM l. 1673): if the `D`-geodesic from `z` to `w` is unique, every
unit-speed geodesic `Q` from `z` to `P(t)` agrees with `P` on `[0, t]`. -/
theorem gm_geodL_eqOn_of_unique (hU : UniqueGeod D z w) {P : ℝ → ℂ} {L : ℝ}
    (hP : IsGeodesicL D P L z w) {Q : ℝ → ℂ} {t : ℝ} (ht : t ≤ L)
    (hQ : IsGeodesicL D Q t z (P t)) : EqOn Q P (Icc 0 t) := by
  classical
  let R : ℝ → ℂ := fun u => if u ≤ t then Q u else P u
  have hR : IsGeodesicL D R L z w := by
    refine ⟨hP.1, ?_, ?_, ?_⟩
    · simp only [R, hQ.1, ↓reduceIte]
      exact hQ.2.1
    · by_cases hLt : L ≤ t
      · have hLe : L = t := le_antisymm hLt ht
        simp only [R, hLt, ↓reduceIte]
        rw [hLe, hQ.2.2.1, ← hLe]
        exact hP.2.2.1
      · simp only [R, hLt, ↓reduceIte]
        exact hP.2.2.1
    · intro a ha b hb
      by_cases hat : a ≤ t <;> by_cases hbt : b ≤ t <;> simp only [R, hat, hbt, ↓reduceIte]
      · exact hQ.2.2.2 a ⟨ha.1, hat⟩ b ⟨hb.1, hbt⟩
      · rw [gm_concat_dist hP hQ ht ⟨ha.1, hat⟩ hb (not_le.mp hbt),
          abs_of_nonneg (by linarith [not_le.mp hbt])]
      · rw [D.2.symm, gm_concat_dist hP hQ ht ⟨hb.1, hbt⟩ ha (not_le.mp hat),
          abs_of_nonpos (by linarith [not_le.mp hat])]
        ring
      · exact hP.2.2.2 a ha b hb
  obtain ⟨ηR, hηR, hRx⟩ := gm_exists_geod01 hR
  obtain ⟨ηP, hηP, hPx⟩ := gm_exists_geod01 hP
  have heq : ηR = ηP := hU.unique hηR hηP
  intro u hu
  rcases eq_or_lt_of_le hP.1 with hL0 | hL0
  · -- `L = 0`: then `t = 0 = u`
    have hu0 : u = 0 := le_antisymm (hu.2.trans (ht.trans hL0.symm.le)) hu.1
    rw [hu0, hQ.2.1, hP.2.1]
  · have hx : u / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hu.1 hL0.le, (div_le_one hL0).mpr (hu.2.trans ht)⟩
    have := congrArg (fun η : C(unitInterval, ℂ) => η ⟨u / L, hx⟩) heq
    simp only [hRx, hPx] at this
    rw [mul_div_cancel₀ _ hL0.ne'] at this
    simpa only [R, hu.2, ↓reduceIte] using this

/-- `P(u) ∈ cl 𝓑_u` for `0 < u ≤ L` (approach along the geodesic) -/
theorem gm_geod_mem_closure_ballM {P : ℝ → ℂ} {L u : ℝ} (hP : IsGeodesicL D P L z w)
    (hu : 0 < u) (huL : u ≤ L) : P u ∈ closure (ballM D z u) := by
  have hc := gm_geodL_continuousOn hP
  have hcw : ContinuousWithinAt P (Ico 0 u) u :=
    (hc u ⟨hu.le, huL⟩).mono (fun v hv => ⟨hv.1, hv.2.le.trans huL⟩)
  have hmem : u ∈ closure (Ico 0 u) := by rw [closure_Ico hu.ne]; exact ⟨hu.le, le_rfl⟩
  refine closure_mono ?_ (hcw.mem_closure_image hmem)
  rintro _ ⟨v, hv, rfl⟩
  show D.1 (z, P v) < u
  rw [gm_geodL_dist hP ⟨hv.1, hv.2.le.trans huL⟩]
  exact hv.2

/-- if `w ∉ 𝓑^•_t` (`t > 0`), the geodesic is longer than `t` -/
theorem gm_lt_length_of_not_mem {P : ℝ → ℂ} {L t : ℝ} (hP : IsGeodesicL D P L z w) (ht : 0 < t)
    (hw : w ∉ filledBall D z t) : t < L := by
  by_contra hle
  replace hle := not_lt.mp hle
  apply hw
  rcases eq_or_lt_of_le hP.1 with hL0 | hL0
  · have hwz : w = z := by rw [← hP.2.2.1, ← hL0, hP.2.1]
    refine Or.inl (subset_closure ?_)
    show D.1 (z, w) < t
    rw [hwz, D.2.self_eq_zero]
    exact ht
  · have := gm_geod_mem_closure_ballM hP hL0 le_rfl
    rw [hP.2.2.1] at this
    exact Or.inl (gm_closure_ballM_mono D z hle this)

/-- **GM Lemma 4.5, pathwise part** (l. 1669–1675), deterministic form. -/
theorem gm_L4_5_arc (hU : UniqueGeod D z w) {P : ℝ → ℂ} {L s t : ℝ}
    (hP : IsGeodesicL D P L z w) (hs : 0 < s) (hst : s < t) (hw : w ∉ filledBall D z t)
    (hleft : ∀ y ∈ frontier (filledBall D z t), ∃ Q, IsLeftmostGeod D z t y Q)
    (hdisj : (confPts D z s t).PairwiseDisjoint (arcOf D z t)) :
    P s ∈ confPts D z s t ∧ P t ∈ arcOf D z t (P s) ∧
      ∀ x ∈ confPts D z s t, P t ∈ arcOf D z t x → x = P s := by
  have ht : 0 < t := hs.trans hst
  have htL := gm_lt_length_of_not_mem hP ht hw
  have hfrt : P t ∈ frontier (filledBall D z t) := gm_geod_mem_frontier hP ht htL hw
  have hfrs : P s ∈ frontier (filledBall D z s) :=
    gm_geod_mem_frontier hP hs (hst.trans htL) (fun h' => hw (gm_filledBall_mono D z hst.le h'))
  obtain ⟨Q, hQ⟩ := hleft (P t) hfrt
  have hEq := gm_geodL_eqOn_of_unique hU hP htL.le hQ.2.1
  have hQs : Q s = P s := hEq ⟨hs.le, hst.le⟩
  have hconf : P s ∈ confPts D z s t := ⟨hfrs, P t, Q, hQ, s, ⟨hs.le, hst.le⟩, hQs⟩
  have harc : P t ∈ arcOf D z t (P s) := ⟨hfrt, Q, hQ, s, ⟨hs.le, hst.le⟩, hQs⟩
  refine ⟨hconf, harc, fun x hx hxa => ?_⟩
  by_contra hne
  exact (hdisj hx hconf hne).le_bot ⟨hxa, harc⟩

/-- **GM Lemma 4.5, pathwise part**, a.s. form: for a random constant-speed geodesic `η` from
`𝕫` to `𝕨` which is a.s. the unique one, a.s. for all `0 < s < t` with `𝕨 ∉ 𝓑^•_t`, the point
`P(s)` (`P` = unit-speed form of `η`) lies in `Conf(s,t)`, its arc contains `P(t)`, and it is the
only point of `Conf(s,t)` whose arc contains `P(t)`. -/
theorem gm_L4_5_arc_ae (hC24 : CONFLem2_4) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (𝕫 𝕨 : ℂ)
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) (η : Ω → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t → 𝕨 ∉ filledBall (D (h ω)) 𝕫 t →
      geodL (D (h ω)) 𝕫 𝕨 (η ω) s ∈ confPts (D (h ω)) 𝕫 s t ∧
      geodL (D (h ω)) 𝕫 𝕨 (η ω) t ∈ arcOf (D (h ω)) 𝕫 t (geodL (D (h ω)) 𝕫 𝕨 (η ω) s) ∧
      ∀ x ∈ confPts (D (h ω)) 𝕫 s t, geodL (D (h ω)) 𝕫 𝕨 (η ω) t ∈ arcOf (D (h ω)) 𝕫 t x →
        x = geodL (D (h ω)) 𝕫 𝕨 (η ω) s := by
  filter_upwards [hη, hC24 γ hγ hγ2 D c hD P h hh 𝕫,
    gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫] with ω hηω h24 h41 s t hs hst hw
  exact gm_L4_5_arc hηω.2 (gm_geodL_isGeodesicL hηω.1 h𝕫𝕨) hs hst hw
    (fun y hy => (h24 t (hs.trans hst) y hy true).1) (h41 s t hs hst).2.2.1

end Det

end LQGMetric.GM
