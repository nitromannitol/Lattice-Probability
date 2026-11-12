/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Chain

/-!
# GM Lemma 5.7, deterministic part: `F_r(z)` is determined by the internal metrics of `B_{3r}(z)`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.7, l. 3006–3017 (task P2-M2L2). For boundedly compact length metrics `D_g`, `D̃_g` with
`c_* D_g ≤ D̃_g ≤ C_* D_g`:

* "the set of `u, v` for which `D̃(u,v) ≤ (c_*/C_*)² D̃(u, ∂B_{2r}(z))` is determined by `h|_{B_{3r}}`"
  (`setDist_sphere_le_of_internal_eq`: `D̃(u, ∂B_{2r}(z))` is computed from `D̃(·,·;B_{3r}(z))`);
* "each `D̃_h`-geodesic from `u` to `v` is contained in `B_{2r}(z)`, so the set of `D̃_h`-geodesics
  is the same as the set of `D̃_h(·,·;B_{2r}(z))`-geodesics" (`isGeod01_iff_isGeodI`, P2-M2E,
  with the open set `B_{3r}(z)`);
* "`D(u,v) ≤ (c_*/C_*) D(u, ∂B_{2r}(z))`, so `D(u,v) = D(u,v;B_{2r}(z))`" (`dist_le_of_tube`);
* the internal metric of `V ⊆ B_{3r}(z)` is determined by that of `B_{3r}(z)`
  (`internal_eq_of_internal_eq`: lengths of paths in `V` are lengths for `D(·,·;B_{3r})`,
  `lenFun_internal`).

Main result: `tubeEvent_saturated`. Own elementary arguments for the metric facts GM uses
implicitly (first hitting of a sphere by a geodesic, attainment of `D̃(u, ∂B_{2r})`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- internal metrics of `V ⊆ U` are determined by the internal metric of `U` -/
lemma internal_le_of_internal_eq {d₁ d₂ : ContMetric} {U V : Set ℂ} (hVU : V ⊆ U)
    (he : ∀ x y, d₁.internal U x y = d₂.internal U x y) (x y : ℂ) :
    d₂.internal V x y ≤ d₁.internal V x y := by
  refine le_iInf fun γ => ?_
  set P : ℝ → ℂ := fun t => d₁.unpt (γ.1.extend t) with hP
  have hPc : ContinuousOn P (Icc 0 1) :=
    (d₁.continuous_unpt.comp γ.1.continuous_extend).continuousOn
  have hPV : MapsTo P (Icc 0 1) V := fun t ht => by
    have := γ.2 ⟨t, ht⟩
    rw [← Path.extend_apply γ.1 ht] at this
    exact (d₁.mem_image_pt (z := P t)).1 this
  have h0 : P 0 = x := by simp only [hP, Path.extend_zero]; rfl
  have h1 : P 1 = y := by simp only [hP, Path.extend_one]; rfl
  have hl : ∀ d : ContMetric, ∀ J : ℂ → ℂ → ℝ≥0∞, (∀ a b, J a b = d.internal U a b) →
      lenFun J P 0 1 = d.len P 0 1 := fun d J hJ => by
    rw [show J = d.internal U from funext fun a => funext fun b => hJ a b]
    exact lenFun_internal d hPc (hPV.mono_right hVU)
  calc d₂.internal V x y = d₂.internal V (P 0) (P 1) := by rw [h0, h1]
    _ ≤ d₂.len P 0 1 := DFGPS.internal_le_len_of_path d₂ hPc hPV (left_mem_Icc.2 zero_le_one)
        (right_mem_Icc.2 zero_le_one)
    _ = d₁.len P 0 1 := by
        rw [← hl d₂ (d₁.internal U) fun a b => he a b, hl d₁ (d₁.internal U) fun a b => rfl]
    _ = pathLength γ.1 := rfl

lemma internal_eq_of_internal_eq {d₁ d₂ : ContMetric} {U V : Set ℂ} (hVU : V ⊆ U)
    (he : d₁.internal U = d₂.internal U) : d₁.internal V = d₂.internal V := by
  funext x y
  exact le_antisymm (internal_le_of_internal_eq hVU (fun a b => (congrFun₂ he a b).symm) x y)
    (internal_le_of_internal_eq hVU (fun a b => congrFun₂ he a b) x y)

lemma setDist_singleton_le {d : ContMetric} {u w : ℂ} {S : Set ℂ} (hw : w ∈ S) :
    setDist d {u} S ≤ ENNReal.ofReal (d.1 (u, w)) := by
  rw [setDist_eq_iInf]
  exact iInf₂_le_of_le u rfl (iInf₂_le w hw)

lemma le_setDist_singleton {d : ContMetric} {u : ℂ} {S : Set ℂ} {a : ℝ≥0∞}
    (h : ∀ y ∈ S, a ≤ ENNReal.ofReal (d.1 (u, y))) : a ≤ setDist d {u} S := by
  rw [setDist_eq_iInf]
  refine le_iInf₂ fun x hx => ?_
  rw [mem_singleton_iff.1 hx]
  exact le_iInf₂ h

/-- a geodesic from inside `B_ρ(z)` to outside crosses `∂B_ρ(z)` -/
lemma setDist_sphere_le_of_geod {d : ContMetric} (hex : ∀ a b : ℂ, ∃ η, IsGeod01 d a b η)
    {z u y : ℂ} {ρ : ℝ} (hu : ‖u - z‖ < ρ) (hy : ρ ≤ ‖y - z‖) :
    setDist d {u} (sphere z ρ) ≤ ENNReal.ofReal (d.1 (u, y)) := by
  obtain ⟨η, hη⟩ := hex u y
  have hc : Continuous fun t : unitInterval => ‖η t - z‖ := (η.continuous.sub continuous_const).norm
  have hmem : ρ ∈ Icc ‖η 0 - z‖ ‖η 1 - z‖ := by
    rw [hη.1, hη.2.1]; exact ⟨hu.le, hy⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hc hmem
  have hw : η t ∈ sphere z ρ := by rw [mem_sphere_iff_norm]; exact ht
  refine (setDist_singleton_le hw).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [dist_geod_left hη t]
  have := d.nonneg u y
  nlinarith [t.2.2, t.2.1]

/-- `D(u, ∂B_ρ(z)) ≤ D(u, ∂B_R(z))` for `ρ < R` -/
lemma setDist_sphere_le_frontier {d : ContMetric} (hex : ∀ a b : ℂ, ∃ η, IsGeod01 d a b η)
    {z u : ℂ} {ρ R : ℝ} (hu : ‖u - z‖ < ρ) (hρR : ρ < R) :
    setDist d {u} (sphere z ρ) ≤ setDist d {u} (frontier (ball z R)) := by
  rw [frontier_ball z (by linarith [norm_nonneg (u - z)] : R ≠ 0)]
  refine le_setDist_singleton fun y hy => setDist_sphere_le_of_geod hex hu ?_
  rw [mem_sphere_iff_norm.1 hy]; exact hρR.le

lemma isLen_of_mem {d : ContMetric} (hd : d ∈ LocalEvent.lenSet) : d.IsLength :=
  LocalEvent.isLength_of_mem_lenSet hd

lemma hex_of_mem {d : ContMetric} (hd : d ∈ LocalEvent.lenSet) :
    ∀ a b : ℂ, ∃ η, IsGeod01 d a b η :=
  exists_isGeod01_of_bcpt d (isLen_of_mem hd) (LocalEvent.bcpt_of_mem_lenSet hd)

lemma proper_of_mem {d : ContMetric} (hd : d ∈ LocalEvent.lenSet) : ProperSpace d.Space :=
  properSpace_of_bcpt d (LocalEvent.bcpt_of_mem_lenSet hd)

/-- `D̃(u, ∂B_ρ(z))` is determined by the internal metric of `B_R(z)`, `ρ < R` -/
lemma setDist_sphere_le_of_internal_eq {d₁ d₂ : ContMetric}
    (h₂ : d₂ ∈ LocalEvent.lenSet) {z u : ℂ} {ρ R : ℝ} (hu : ‖u - z‖ < ρ) (hρR : ρ < R)
    (he : d₁.internal (ball z R) = d₂.internal (ball z R)) :
    setDist d₁ {u} (sphere z ρ) ≤ setDist d₂ {u} (sphere z ρ) := by
  have := proper_of_mem h₂
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hu.le
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere z ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hρ)
    ((d₂.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hy' : ENNReal.ofReal (d₂.1 (u, y)) ≤ setDist d₂ {u} (sphere z ρ) :=
    le_setDist_singleton fun w hw => ENNReal.ofReal_le_ofReal (hmin hw)
  have hyU : y ∈ ball z R := by
    rw [mem_ball, dist_eq_norm, (mem_sphere_iff_norm.1 hy)]; exact hρR
  have huU : u ∈ ball z R := by rw [mem_ball, dist_eq_norm]; linarith
  have hint : d₂.internal (ball z R) u y = ENNReal.ofReal (d₂.1 (u, y)) :=
    internal_eq_of_le d₂ (isLen_of_mem h₂) isOpen_ball huU hyU
      (hy'.trans (setDist_sphere_le_frontier (hex_of_mem h₂) hu hρR))
  calc setDist d₁ {u} (sphere z ρ) ≤ ENNReal.ofReal (d₁.1 (u, y)) := setDist_singleton_le hy
    _ ≤ d₁.internal (ball z R) u y := by
        rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
    _ = ENNReal.ofReal (d₂.1 (u, y)) := by rw [he, hint]
    _ ≤ setDist d₂ {u} (sphere z ρ) := hy'

/-- the distance bounds behind GM l. 3008–3015, for one pair of metrics: if
`D̃(u,v) ≤ (c_*/C_*)² D̃(u, ∂B_{2r}(z))` then `D̃(u,v)` and `D(u,v)` are at most the distances
from `u` to `∂B_{3r}(z)` -/
lemma dist_le_of_tube {d d' : ContMetric} (hd' : d' ∈ LocalEvent.lenSet) {cs Cs : ℝ} (hcs : 0 < cs) (hCs : cs ≤ Cs)
    (rat : ∀ x y, cs * d.1 (x, y) ≤ d'.1 (x, y) ∧ d'.1 (x, y) ≤ Cs * d.1 (x, y))
    {z u v : ℂ} {r : ℝ} (hu : ‖u - z‖ ≤ r) (hr : 0 < r)
    (hset : ENNReal.ofReal (d'.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist d' {u} (sphere z (2 * r))) :
    ENNReal.ofReal (d'.1 (u, v)) ≤ setDist d' {u} (frontier (ball z (3 * r))) ∧
    ENNReal.ofReal (d.1 (u, v)) ≤ setDist d {u} (frontier (ball z (3 * r))) := by
  have hCs0 : 0 < Cs := hcs.trans_le hCs
  have hk0 : 0 ≤ (cs / Cs) ^ 2 := sq_nonneg _
  have hk1 : (cs / Cs) ^ 2 ≤ 1 := by
    rw [div_pow]; exact (div_le_one (by positivity)).2 (pow_le_pow_left₀ hcs.le hCs 2)
  have hu2 : ‖u - z‖ < 2 * r := by linarith
  have hex' := hex_of_mem hd'
  rw [frontier_ball z (by positivity : 3 * r ≠ 0)]
  -- `D̃(u,v) ≤ k D̃(u,y)` for `y` outside `B_{2r}(z)`
  have key : ∀ y, 2 * r ≤ ‖y - z‖ → d'.1 (u, v) ≤ (cs / Cs) ^ 2 * d'.1 (u, y) := by
    intro y hy
    have h2 := hset.trans (mul_le_mul_of_nonneg_left (setDist_sphere_le_of_geod hex' hu2 hy) (zero_le))
    rw [← ENNReal.ofReal_mul hk0] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0 (d'.nonneg _ _))).1 h2
  constructor
  · refine le_setDist_singleton fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := key y (by rw [mem_sphere_iff_norm.1 hy]; linarith)
    nlinarith [d'.nonneg u y]
  · refine le_setDist_singleton fun y hy => ENNReal.ofReal_le_ofReal ?_
    have h1 := key y (by rw [mem_sphere_iff_norm.1 hy]; linarith)
    have a1 := (rat u v).1
    have a2 := (rat u y).2
    have hdy := d.nonneg u y
    -- `cs D(u,v) ≤ D̃(u,v) ≤ k D̃(u,y) ≤ k C_* D(u,y)`, and `k C_* = c_*² / C_* ≤ c_*`
    have hkC : (cs / Cs) ^ 2 * Cs ≤ cs := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_pos hcs hCs0).le (sub_nonneg.2 hCs)]
    have : cs * d.1 (u, v) ≤ cs * d.1 (u, y) := by
      calc cs * d.1 (u, v) ≤ (cs / Cs) ^ 2 * d'.1 (u, y) := a1.trans h1
        _ ≤ (cs / Cs) ^ 2 * (Cs * d.1 (u, y)) := mul_le_mul_of_nonneg_left a2 hk0
        _ = ((cs / Cs) ^ 2 * Cs) * d.1 (u, y) := by ring
        _ ≤ cs * d.1 (u, y) := mul_le_mul_of_nonneg_right hkC hdy
    exact le_of_mul_le_mul_left this hcs

/-- **GM Lemma 5.7, deterministic core** (l. 3006–3017): for boundedly compact length metrics with
`c_* D ≤ D̃ ≤ C_* D`, the event `F_r(z)` (for an open `V ⊆ B_{3r}(z)`) is determined by the
internal metrics `D(·,·;B_{3r}(z))`, `D̃(·,·;B_{3r}(z))`. -/
theorem tubeEvent_saturated {D D' : DistC → ContMetric} {cs Cs c₁ η b ε r : ℝ} {z : ℂ}
    {V : Set ℂ} (hr : 0 < r) (hcs : 0 < cs) (hCs : cs ≤ Cs) (hVU : V ⊆ ball z (3 * r))
    {g₁ g₂ : DistC} (l1 : D g₁ ∈ LocalEvent.lenSet) (l1' : D' g₁ ∈ LocalEvent.lenSet)
    (l2 : D g₂ ∈ LocalEvent.lenSet) (l2' : D' g₂ ∈ LocalEvent.lenSet)
    (rat1 : ∀ x y, cs * (D g₁).1 (x, y) ≤ (D' g₁).1 (x, y) ∧ (D' g₁).1 (x, y) ≤ Cs * (D g₁).1 (x, y))
    (rat2 : ∀ x y, cs * (D g₂).1 (x, y) ≤ (D' g₂).1 (x, y) ∧ (D' g₂).1 (x, y) ≤ Cs * (D g₂).1 (x, y))
    (e : (D g₁).internal (ball z (3 * r)) = (D g₂).internal (ball z (3 * r)))
    (e' : (D' g₁).internal (ball z (3 * r)) = (D' g₂).internal (ball z (3 * r)))
    (h1 : g₁ ∈ tubeEvent D D' cs Cs c₁ η b ε r z V) :
    g₂ ∈ tubeEvent D D' cs Cs c₁ η b ε r z V := by
  obtain ⟨u, hu, v, hv, hb, hrat, hset, hsetv, huniq, hs1, hs2, hi1, hi2⟩ := h1
  set U := ball z (3 * r) with hU
  have hur : ‖u - z‖ ≤ r := by
    have := hu.2; rwa [mem_closedBall, dist_eq_norm] at this
  have hvr : ‖v - z‖ ≤ r := by
    have := hv.2; rwa [mem_closedBall, dist_eq_norm] at this
  have huU : u ∈ U := by rw [hU, mem_ball, dist_eq_norm]; linarith
  have hvU : v ∈ U := by rw [hU, mem_ball, dist_eq_norm]; linarith
  have hu2 : ‖u - z‖ < 2 * r := by linarith
  have h23 : 2 * r < 3 * r := by linarith
  -- `D̃(u, ∂B_{2r}(z))` is the same for both
  have hm : setDist (D' g₁) {u} (sphere z (2 * r)) = setDist (D' g₂) {u} (sphere z (2 * r)) :=
    le_antisymm (setDist_sphere_le_of_internal_eq l2' hu2 h23 e')
      (setDist_sphere_le_of_internal_eq l1' hu2 h23 e'.symm)
  have hv2 : ‖v - z‖ < 2 * r := by linarith
  have hmv : setDist (D' g₁) {v} (sphere z (2 * r)) = setDist (D' g₂) {v} (sphere z (2 * r)) :=
    le_antisymm (setDist_sphere_le_of_internal_eq l2' hv2 h23 e')
      (setDist_sphere_le_of_internal_eq l1' hv2 h23 e'.symm)
  -- `D̃(u,v)` and `D(u,v)` are internal distances in `U` for `g₁`
  obtain ⟨b1', b1⟩ := dist_le_of_tube l1' hcs hCs rat1 hur hr hset
  have := proper_of_mem l1'
  have := proper_of_mem l1
  have i1' : (D' g₁).internal U u v = ENNReal.ofReal ((D' g₁).1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l1') isOpen_ball huU hvU b1'
  have i1 : (D g₁).internal U u v = ENNReal.ofReal ((D g₁).1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l1) isOpen_ball huU hvU b1
  -- and for `g₂`
  have hset2 : ENNReal.ofReal ((D' g₂).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g₂) {u} (sphere z (2 * r)) := by
    calc ENNReal.ofReal ((D' g₂).1 (u, v)) ≤ (D' g₂).internal U u v := by
          rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
      _ = ENNReal.ofReal ((D' g₁).1 (u, v)) := by rw [← e', i1']
      _ ≤ _ := hm ▸ hset
  obtain ⟨b2', b2⟩ := dist_le_of_tube l2' hcs hCs rat2 hur hr hset2
  have := proper_of_mem l2'
  have := proper_of_mem l2
  have i2' : (D' g₂).internal U u v = ENNReal.ofReal ((D' g₂).1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l2') isOpen_ball huU hvU b2'
  have i2 : (D g₂).internal U u v = ENNReal.ofReal ((D g₂).1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l2) isOpen_ball huU hvU b2
  have d' : (D' g₂).1 (u, v) = (D' g₁).1 (u, v) := by
    rw [← ENNReal.ofReal_eq_ofReal_iff ((D' g₂).nonneg _ _) ((D' g₁).nonneg _ _), ← i1', ← i2',
      e']
  have d : (D g₂).1 (u, v) = (D g₁).1 (u, v) := by
    rw [← ENNReal.ofReal_eq_ofReal_iff ((D g₂).nonneg _ _) ((D g₁).nonneg _ _), ← i1, ← i2, e]
  -- the geodesics are the same
  have hg : ∀ γ, IsGeod01 (D' g₂) u v γ ↔ IsGeod01 (D' g₁) u v γ := fun γ => by
    have := proper_of_mem l1'
    have := proper_of_mem l2'
    show (D' g₂).IsGeod01 u v γ ↔ (D' g₁).IsGeod01 u v γ
    rw [isGeod01_iff_isGeodI _ (isLen_of_mem l2') isOpen_ball huU hvU b2',
      isGeod01_iff_isGeodI _ (isLen_of_mem l1') isOpen_ball huU hvU b1', e']
  have hiV : (D' g₂).internal V = (D' g₁).internal V := (internal_eq_of_internal_eq hVU e').symm
  refine ⟨u, hu, v, hv, hb, ?_, ?_, ?_, ?_, hs1, hs2, ?_, ?_⟩
  · rw [d, d']; exact hrat
  · rw [← hm, d']; exact hset
  · rw [← hmv, d']; exact hsetv
  · simp only [UniqueGeodIn, UniqueGeod, hg]; exact huniq
  · intro w hw; rw [hiV, d']; exact hi1 w hw
  · intro w hw; rw [hiV, d']; exact hi2 w hw

end LQGMetric.GM
