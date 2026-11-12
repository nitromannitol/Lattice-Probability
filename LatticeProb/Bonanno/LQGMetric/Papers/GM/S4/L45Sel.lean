/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Sel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det7
import Mathlib.Data.Rat.Denumerable
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics

/-!
# GM Lemma 4.5 without a geodesic selection: deterministic part (task P2-E2S)

GM, arXiv:1905.00383, `uniqueness-final.tex` Lemma 4.5, proof l. 1665–1675: "`P|_{[0,s_k]}` is
determined by `(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` and the arc of `𝓘_k` containing `P(t_k)`". Instead of
a measurable geodesic selection (`GMGeodSelDet`), each point `P(s_k u)` is decoded with the
decoder `gmXi` (as `GMConfPtSel` in `L45Det7`) from the field events

* `gmGeodWSet` (on `{𝕨 ∈ 𝓑^•_{t_k}}`): some geodesic from `𝕫` to `𝕨`, at time `s_k u`, lies in a
  rational half-plane;
* `gmGeodCEv` (on `{𝕨 ∉ 𝓑^•_{t_k}}`): some point of `Conf_k` with a prescribed finite hit prefix
  of its arc has a geodesic from `𝕫` whose constant-speed form at `u` lies in a rational
  half-plane.

This file: locality of these events (`gm_geodWSet_sat`, `gm_geodCEv_sat`, using
`GMLocData.isGeod01` and the equality of distances `gm_dist_eq_of_locData`), the decoding lemmas
`gm_conf_decode_pred`, `gm_gmXi_eq`, and `gm_geod01_eq_of_unique` (GM l. 1673, "unique hence the
restriction"). Own elementary arguments around GM's text; no new mathematics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the `𝕨`-events: `𝕨 ∈ 𝓑^•_{t}` and some geodesic from `𝕫` to `𝕨` is in the half-plane `j` at
time `s u` (`s = τ_R c₀`, `t = τ_R c`) -/
def gmGeodWSet (D : DistC → ContMetric) (𝕫 𝕨 : ℂ) (R c₀ c : ℝ) (u : unitInterval)
    (j : Bool × ℚ) : Set DistC :=
  {g | 𝕨 ∈ gmKt D 𝕫 R c g ∧ ∃ Q : C(unitInterval, ℂ), IsGeod01 (D g) 𝕫 𝕨 Q ∧
    geodL (D g) 𝕫 𝕨 Q (tauD (D g) 𝕫 R * c₀ * u) ∈ gmHalf j}

/-- the `Conf`-events: a point of `Conf(s,t)` whose arc has the hit prefix `(i.2.1, i.2.2)` and
which has a geodesic from `𝕫` lying at `u` in the half-plane `i.1` -/
def gmGeodCEv (V : ℕ → Set ℂ) (d : ContMetric) (𝕫 : ℂ) (s t : ℝ) (u : unitInterval)
    (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) : Prop :=
  ∃ x ∈ confPts d 𝕫 s t, (∀ n ∈ i.2.1, gmPat V d 𝕫 t x n) ∧
    (∀ n ∈ i.2.2, ¬ gmPat V d 𝕫 t x n) ∧
    ∃ Q : C(unitInterval, ℂ), IsGeod01 d 𝕫 x Q ∧ Q u ∈ gmHalf i.1

theorem gm_exists_geod01_of_lenSet {d : ContMetric} (hd : d ∈ LocalEvent.lenSet) (z w : ℂ) :
    ∃ η, IsGeod01 d z w η :=
  exists_isGeod01_of_bcpt d (LocalEvent.isLength_of_mem_lenSet hd)
    (LocalEvent.bcpt_of_mem_lenSet hd) z w

/-- one half of the locality of `d(𝕫, x)`, `x ∈ 𝓑^•_T` (as in `GMLocData.isGeod01`) -/
theorem gm_dist_le_of_locData {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {x : ℂ} (hx : x ∈ filledBall d₁ 𝕫 T)
    {η₂ : C(unitInterval, ℂ)} (hη₂ : IsGeod01 d₂ 𝕫 x η₂) : d₁.1 (𝕫, x) ≤ d₂.1 (𝕫, x) := by
  have hx₂ : x ∈ filledBall d₂ 𝕫 T := by rw [H.filledBall_eq le_rfl]; exact hx
  have hr₂ : range η₂ ⊆ U := (gm_range_geod_subset_filledBall hη₂ hx₂).trans
    (by rw [H.filledBall_eq le_rfl]; exact H.sub)
  have h1 := gm_internal_le_of_isGeod01' hη₂ hr₂
  have h2 : ENNReal.ofReal (d₁.1 (𝕫, x)) ≤ d₁.internal U 𝕫 x := by
    rw [← ContMetric.edist_pt]
    exact MetricGeometry.edist_le_internalEDist _ _ _
  rw [H.int] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (gm_D_nonneg d₂ 𝕫 x)).1 (h2.trans h1)

/-- **`d(𝕫, x)` is local** for `x ∈ 𝓑^•_T` (geodesics from `𝕫` to `x` stay in `𝓑^•_T ⊆ U`) -/
theorem gm_dist_eq_of_locData {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {x : ℂ} (hx : x ∈ filledBall d₁ 𝕫 T)
    {η₁ η₂ : C(unitInterval, ℂ)} (hη₁ : IsGeod01 d₁ 𝕫 x η₁) (hη₂ : IsGeod01 d₂ 𝕫 x η₂) :
    d₂.1 (𝕫, x) = d₁.1 (𝕫, x) := by
  have hx₂ : x ∈ filledBall d₂ 𝕫 T := by rw [H.filledBall_eq le_rfl]; exact hx
  exact le_antisymm (gm_dist_le_of_locData H.symm hx₂ hη₁) (gm_dist_le_of_locData H hx hη₂)

/-- geodesics from `𝕫` to points of `𝓑^•_T` are local, for a boundedly compact length `d₂` -/
theorem GMLocData.isGeod01_of_len {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) (hd₂ : d₂ ∈ LocalEvent.lenSet) {x : ℂ}
    (hx : x ∈ filledBall d₁ 𝕫 T) {η : C(unitInterval, ℂ)} (hη : IsGeod01 d₁ 𝕫 x η) :
    IsGeod01 d₂ 𝕫 x η := by
  obtain ⟨η₂, hη₂⟩ := gm_exists_geod01_of_lenSet hd₂ 𝕫 x
  exact H.isGeod01 hx hη₂ hη

/-- saturation of the `𝕨`-events -/
theorem gm_geodWSet_sat {D : DistC → ContMetric} {𝕫 𝕨 : ℂ} {R c₀ c : ℝ} (u : unitInterval)
    (j : Bool × ℚ) (g₁ g₂ : DistC) (U : Set ℂ) (_h1 : D g₁ ∈ LocalEvent.lenSet)
    (h2 : D g₂ ∈ LocalEvent.lenSet) (hτe : tauD (D g₂) 𝕫 R = tauD (D g₁) 𝕫 R)
    (H : GMLocData (D g₁) (D g₂) 𝕫 (tauD (D g₁) 𝕫 R * c) U)
    (hB : g₁ ∈ gmGeodWSet D 𝕫 𝕨 R c₀ c u j) : g₂ ∈ gmGeodWSet D 𝕫 𝕨 R c₀ c u j := by
  obtain ⟨hw, Q, hQ, hQu⟩ := hB
  have hw' : 𝕨 ∈ filledBall (D g₁) 𝕫 (tauD (D g₁) 𝕫 R * c) := hw
  obtain ⟨η₂, hη₂⟩ := gm_exists_geod01_of_lenSet h2 𝕫 𝕨
  have hd := gm_dist_eq_of_locData H hw' hQ hη₂
  refine ⟨?_, Q, H.isGeod01_of_len h2 hw' hQ, ?_⟩
  · show 𝕨 ∈ filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * c)
    rw [hτe, H.filledBall_eq le_rfl]
    exact hw
  · rw [hτe]
    unfold geodL at hQu ⊢
    rw [hd]
    exact hQu

/-- saturation of the `Conf`-events -/
theorem gm_geodCEv_sat {D : DistC → ContMetric} {V : ℕ → Set ℂ} {𝕫 : ℂ} {R c₀ c : ℝ}
    (hR : 0 < R) (hc₀ : c₀ ≤ c) (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (g₁ g₂ : DistC)
    (U : Set ℂ) (_h1 : D g₁ ∈ LocalEvent.lenSet) (h2 : D g₂ ∈ LocalEvent.lenSet)
    (hτe : tauD (D g₂) 𝕫 R = tauD (D g₁) 𝕫 R)
    (H : GMLocData (D g₁) (D g₂) 𝕫 (tauD (D g₁) 𝕫 R * c) U)
    (hB : g₁ ∈ {g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 R * c₀) (tauD (D g) 𝕫 R * c) u i}) :
    g₂ ∈ {g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 R * c₀) (tauD (D g) 𝕫 R * c) u i} := by
  have hle : tauD (D g₁) 𝕫 R * c₀ ≤ tauD (D g₁) 𝕫 R * c :=
    mul_le_mul_of_nonneg_left hc₀ (gm_tauD_pos _ 𝕫 hR).le
  obtain ⟨x, hx, hF, hG, Q, hQ, hQu⟩ := hB
  have hxB : x ∈ filledBall (D g₁) 𝕫 (tauD (D g₁) 𝕫 R * c) :=
    gm_filledBall_mono _ 𝕫 hle ((gm_filledBall_isClosed _ 𝕫 _).frontier_subset hx.1)
  show gmGeodCEv V (D g₂) 𝕫 _ _ u i
  rw [hτe]
  refine ⟨x, ?_, ?_, ?_, Q, H.isGeod01_of_len h2 hxB hQ, hQu⟩
  · rw [H.confPts_eq hle le_rfl]; exact hx
  · simpa only [gmPat, H.arcOf_eq le_rfl] using hF
  · simpa only [gmPat, H.arcOf_eq le_rfl] using hG

/-- **decoding** a property of `x ∈ Conf` from the prefix events -/
theorem gm_conf_decode_pred {V : ℕ → Set ℂ} {d : ContMetric} {𝕫 : ℂ} {s t : ℝ}
    (hfin : (confPts d 𝕫 s t).Finite) (hinj : InjOn (gmPat V d 𝕫 t) (confPts d 𝕫 s t))
    {x : ℂ} (hx : x ∈ confPts d 𝕫 s t) (Φ : ℂ → Prop) :
    Φ x ↔ ∃ L, ∀ L' ≥ L, ∃ x' ∈ confPts d 𝕫 s t,
      (∀ n ∈ gmPreF (gmPat V d 𝕫 t x) L', gmPat V d 𝕫 t x' n) ∧
      (∀ n ∈ gmPreG (gmPat V d 𝕫 t x) L', ¬ gmPat V d 𝕫 t x' n) ∧ Φ x' := by
  classical
  constructor
  · intro hj
    refine ⟨0, fun L' _ => ⟨x, hx, fun n hn => ?_, fun n hn => ?_, hj⟩⟩
    · simp only [gmPreF, Finset.mem_filter] at hn
      exact hn.2
    · simp only [gmPreG, Finset.mem_filter] at hn
      exact hn.2
  · rintro ⟨L, hL⟩
    obtain ⟨L₀, hL₀⟩ := gm_exists_prefix hfin hinj hx
    obtain ⟨x', hx', hF, hG, hj⟩ := hL (max L L₀) (le_max_left _ _)
    have : x' = x := hL₀ x' hx' fun n hn => by
      have hn' : n < max L L₀ := lt_of_lt_of_le hn (le_max_right _ _)
      by_cases hpx : gmPat V d 𝕫 t x n
      · exact ⟨fun _ => hpx, fun _ => hF n (by simp [gmPreF, hn', hpx])⟩
      · exact ⟨fun h => absurd h (hG n (by simp [gmPreG, hn', hpx])), fun h => absurd h hpx⟩
    rw [← this]
    exact hj

/-- the decoder recovers a point from its rational half-planes -/
theorem gm_gmXi_eq {Ω : Type} {Z : Ω → (Bool × ℚ) × Finset ℕ × Finset ℕ → Bool} {ω : Ω}
    {σ : ℕ → Prop} {y : ℂ} (hy : ∀ j, gmPre Z ω σ j ↔ y ∈ gmHalf j) : gmXi Z (ω, σ) = y := by
  classical
  unfold gmXi
  rw [gm_ereal_iSup_rat' (r := y.re) (fun a => by rw [hy]; simp [gmHalf]),
    gm_ereal_iSup_rat' (r := y.im) (fun a => by rw [hy]; simp [gmHalf]),
    EReal.toReal_coe, EReal.toReal_coe]
  exact Complex.re_add_im y

/-- **unique hence the restriction** (GM l. 1673): with a unique geodesic `P` from `𝕫` to `𝕨`,
every constant-speed geodesic `Q` from `𝕫` to `P(s)` is `u ↦ P(s u)` -/
theorem gm_geod01_eq_of_unique {d : ContMetric} {𝕫 𝕨 : ℂ} (hU : UniqueGeod d 𝕫 𝕨) {P : ℝ → ℂ}
    {L : ℝ} (hP : IsGeodesicL d P L 𝕫 𝕨) {s : ℝ} (hs : 0 < s) (hsL : s ≤ L)
    {Q : C(unitInterval, ℂ)} (hQ : IsGeod01 d 𝕫 (P s) Q) (u : unitInterval) : Q u = P (s * u) := by
  have hxd : d.1 (𝕫, P s) = s := gm_geodL_dist hP ⟨hs.le, hsL⟩
  have hx𝕫 : 𝕫 ≠ P s := by
    intro hzx
    rw [← hzx, d.2.self_eq_zero] at hxd
    exact hs.ne hxd
  have hQL := gm_geodL_isGeodesicL hQ hx𝕫
  rw [hxd] at hQL
  have hEq := gm_geodL_eqOn_of_unique hU hP hsL hQL
    ⟨mul_nonneg hs.le u.2.1, mul_le_of_le_one_right hs.le u.2.2⟩
  rw [← hEq]
  simp only [geodL, hxd]
  rw [mul_div_cancel_left₀ (u : ℝ) hs.ne', projIcc_val]

end LQGMetric.GM
