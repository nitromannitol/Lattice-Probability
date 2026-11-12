/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event3Sat1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Det

/-!
# GM Lemma 5.9, deterministic part I: the event of Lemma 5.8 is determined by internal metrics
(task P2-M2M4, D83 P4b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.9 (l. 3293–3302): "the event of Lemma 5.8 is determined by `h|_{𝔸_{r/4,4r}(0)}` … as in
the proof of Lemma 5.7". As in `tubeEvent_saturated` (`Tubes57Det`, GM l. 3006–3017): for
boundedly compact length metrics with `c_* D ≤ D̃ ≤ C_* D`, condition (1) of `linkEvent` at
`u ∈ 𝔸_{(1−4ρ)r,(1+4ρ)r}(0)` forces `D̃(u,v) ≤ D̃(u, ∂B_{4ρr}(u))` and `D(u,v) ≤ D(u, ∂B_{4ρr}(u))`,
so both are internal distances in any open `A ⊇ B_{5ρr}(u)`; `D̃(u, ∂B_{4ρr}(u))` is computed from
the internal metric of `B_{5ρr}(u)`; the geodesics from `u` to `v` are those of `D̃(·,·;A)`.

* `dist_le_sphere_of_link`: the distance bounds (as `dist_le_of_tube`);
* `linkEvent_saturated`: `linkEvent` is determined by `D(·,·;A)`, `D̃(·,·;A)` for an open `A`
  containing the tubes and the balls `B_{5ρr}(w)`, `w ∈ 𝔸_{(1−4ρ)r,(1+4ρ)r}(0)`.
Own elementary arguments for the metric facts GM uses implicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- condition (1)'s bound at `u` gives `D̃(u,v) ≤ D̃(u, F)` and `D(u,v) ≤ D(u, F)` for every set
`F` outside `B_ρ(u)` -/
lemma dist_le_sphere_of_link {d d' : ContMetric} (hd' : d' ∈ LocalEvent.lenSet) {cs Cs : ℝ}
    (hcs : 0 < cs) (hCs : cs ≤ Cs)
    (rat : ∀ x y, cs * d.1 (x, y) ≤ d'.1 (x, y) ∧ d'.1 (x, y) ≤ Cs * d.1 (x, y))
    {u v : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hset : ENNReal.ofReal (d'.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist d' {u} (sphere u ρ))
    {F : Set ℂ} (hF : ∀ y ∈ F, ρ ≤ ‖y - u‖) :
    ENNReal.ofReal (d'.1 (u, v)) ≤ setDist d' {u} F ∧
    ENNReal.ofReal (d.1 (u, v)) ≤ setDist d {u} F := by
  have hCs0 : 0 < Cs := hcs.trans_le hCs
  have hk0 : 0 ≤ (cs / Cs) ^ 2 := sq_nonneg _
  have hex' := hex_of_mem hd'
  have hu : ‖u - u‖ < ρ := by rw [sub_self, norm_zero]; exact hρ
  have key : ∀ y ∈ F, d'.1 (u, v) ≤ (cs / Cs) ^ 2 * d'.1 (u, y) := by
    intro y hy
    have h2 := hset.trans (mul_le_mul_of_nonneg_left (setDist_sphere_le_of_geod hex' hu (hF y hy))
      (zero_le))
    rw [← ENNReal.ofReal_mul hk0] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0 (d'.nonneg _ _))).1 h2
  have hk1 : (cs / Cs) ^ 2 ≤ 1 := by
    rw [div_pow]; exact (div_le_one (by positivity)).2 (pow_le_pow_left₀ hcs.le hCs 2)
  constructor
  · refine le_setDist_singleton fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := key y hy
    nlinarith [d'.nonneg u y]
  · refine le_setDist_singleton fun y hy => ENNReal.ofReal_le_ofReal ?_
    have h1 := key y hy
    have a1 := (rat u v).1
    have a2 := (rat u y).2
    have hdy := d.nonneg u y
    have hkC : (cs / Cs) ^ 2 * Cs ≤ cs := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_pos hcs hCs0).le (sub_nonneg.2 hCs)]
    have : cs * d.1 (u, v) ≤ cs * d.1 (u, y) := by
      calc cs * d.1 (u, v) ≤ (cs / Cs) ^ 2 * d'.1 (u, y) := a1.trans h1
        _ ≤ (cs / Cs) ^ 2 * (Cs * d.1 (u, y)) := mul_le_mul_of_nonneg_left a2 hk0
        _ = ((cs / Cs) ^ 2 * Cs) * d.1 (u, y) := by ring
        _ ≤ cs * d.1 (u, y) := mul_le_mul_of_nonneg_right hkC hdy
    exact le_of_mul_le_mul_left this hcs

/-- the points of `frontier A` lie outside `B_ρ(u)` if `B_ρ(u) ⊆ A`, `A` open -/
lemma frontier_far {A : Set ℂ} (hA : IsOpen A) {u : ℂ} {ρ : ℝ} (hB : ball u ρ ⊆ A) :
    ∀ y ∈ frontier A, ρ ≤ ‖y - u‖ := fun y hy => by
  by_contra h
  push Not at h
  have : y ∈ A := hB (by rw [mem_ball, dist_eq_norm]; exact h)
  exact (hA.frontier_eq ▸ hy).2 this

/-- one end point of condition (1): the distances `D(u,v)`, `D̃(u,v)`, `D̃(u, ∂B_{4ρr}(u))` and the
geodesics agree for two fields with the same internal metrics on `A` -/
lemma link_end_eq {d₁ d₁' d₂ d₂' : ContMetric} (l1 : d₁ ∈ LocalEvent.lenSet)
    (l1' : d₁' ∈ LocalEvent.lenSet) (l2 : d₂ ∈ LocalEvent.lenSet) (l2' : d₂' ∈ LocalEvent.lenSet)
    {cs Cs : ℝ} (hcs : 0 < cs) (hCs : cs ≤ Cs)
    (rat1 : ∀ x y, cs * d₁.1 (x, y) ≤ d₁'.1 (x, y) ∧ d₁'.1 (x, y) ≤ Cs * d₁.1 (x, y))
    (rat2 : ∀ x y, cs * d₂.1 (x, y) ≤ d₂'.1 (x, y) ∧ d₂'.1 (x, y) ≤ Cs * d₂.1 (x, y))
    {A : Set ℂ} (hA : IsOpen A) (e : d₁.internal A = d₂.internal A)
    (e' : d₁'.internal A = d₂'.internal A) {u v : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hB : ball u (5 / 4 * ρ) ⊆ A) (hvA : v ∈ A)
    (hset : ENNReal.ofReal (d₁'.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist d₁' {u} (sphere u ρ)) :
    setDist d₁' {u} (sphere u ρ) = setDist d₂' {u} (sphere u ρ) ∧
      d₂'.1 (u, v) = d₁'.1 (u, v) ∧ d₂.1 (u, v) = d₁.1 (u, v) ∧
      ∀ γ, IsGeod01 d₂' u v γ ↔ IsGeod01 d₁' u v γ := by
  have huA : u ∈ A := hB (mem_ball_self (by positivity))
  have hu : ‖u - u‖ < ρ := by rw [sub_self, norm_zero]; exact hρ
  have hρ5 : ρ < 5 / 4 * ρ := by linarith
  have eB' : d₁'.internal (ball u (5 / 4 * ρ)) = d₂'.internal (ball u (5 / 4 * ρ)) :=
    internal_eq_of_internal_eq hB e'
  have hm : setDist d₁' {u} (sphere u ρ) = setDist d₂' {u} (sphere u ρ) :=
    le_antisymm (setDist_sphere_le_of_internal_eq l2' hu hρ5 eB')
      (setDist_sphere_le_of_internal_eq l1' hu hρ5 eB'.symm)
  have hF := frontier_far hA hB
  have hF' : ∀ y ∈ frontier A, ρ ≤ ‖y - u‖ := fun y hy => by linarith [hF y hy]
  obtain ⟨b1', b1⟩ := dist_le_sphere_of_link l1' hcs hCs rat1 hρ hset hF'
  have := proper_of_mem l1'
  have := proper_of_mem l1
  have i1' : d₁'.internal A u v = ENNReal.ofReal (d₁'.1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l1') hA huA hvA b1'
  have i1 : d₁.internal A u v = ENNReal.ofReal (d₁.1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l1) hA huA hvA b1
  have hset2 : ENNReal.ofReal (d₂'.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist d₂' {u} (sphere u ρ) := by
    calc ENNReal.ofReal (d₂'.1 (u, v)) ≤ d₂'.internal A u v := by
          rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
      _ = ENNReal.ofReal (d₁'.1 (u, v)) := by rw [← e', i1']
      _ ≤ _ := hm ▸ hset
  obtain ⟨b2', b2⟩ := dist_le_sphere_of_link l2' hcs hCs rat2 hρ hset2 hF'
  have := proper_of_mem l2'
  have := proper_of_mem l2
  have i2' : d₂'.internal A u v = ENNReal.ofReal (d₂'.1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l2') hA huA hvA b2'
  have i2 : d₂.internal A u v = ENNReal.ofReal (d₂.1 (u, v)) :=
    internal_eq_of_le _ (isLen_of_mem l2) hA huA hvA b2
  refine ⟨hm, ?_, ?_, fun γ => ?_⟩
  · rw [← ENNReal.ofReal_eq_ofReal_iff (d₂'.nonneg _ _) (d₁'.nonneg _ _), ← i1', ← i2', e']
  · rw [← ENNReal.ofReal_eq_ofReal_iff (d₂.nonneg _ _) (d₁.nonneg _ _), ← i1, ← i2, e]
  · show d₂'.IsGeod01 u v γ ↔ d₁'.IsGeod01 u v γ
    rw [isGeod01_iff_isGeodI _ (isLen_of_mem l2') hA huA hvA b2',
      isGeod01_iff_isGeodI _ (isLen_of_mem l1') hA huA hvA b1', e']

/-- **GM Lemma 5.9 for the event of Lemma 5.8** (deterministic core, l. 3293–3302 "as in Lemma
5.7"): `linkEvent` is determined by the internal metrics of an open `A` containing the tubes
and the balls `B_{5ρr}(w)`, `w ∈ 𝔸_{(1−4ρ)r,(1+4ρ)r}(0)` -/
theorem linkEvent_saturated {D D' : DistC → ContMetric} {cs Cs c₁ η δ ρ b ε r : ℝ}
    {U : ℂ → ℂ → Set ℂ} (hρr : 0 < ρ * r) (hcs : 0 < cs) (hCs : cs ≤ Cs) {A : Set ℂ}
    (hA : IsOpen A)
    (hUA : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
      U x y ⊆ A)
    (hBA : ∀ w ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ),
      ball w (5 * ρ * r) ⊆ A)
    {g₁ g₂ : DistC} (l1 : D g₁ ∈ LocalEvent.lenSet) (l1' : D' g₁ ∈ LocalEvent.lenSet)
    (l2 : D g₂ ∈ LocalEvent.lenSet) (l2' : D' g₂ ∈ LocalEvent.lenSet)
    (rat1 : ∀ x y, cs * (D g₁).1 (x, y) ≤ (D' g₁).1 (x, y) ∧ (D' g₁).1 (x, y) ≤ Cs * (D g₁).1 (x, y))
    (rat2 : ∀ x y, cs * (D g₂).1 (x, y) ≤ (D' g₂).1 (x, y) ∧ (D' g₂).1 (x, y) ≤ Cs * (D g₂).1 (x, y))
    (e : (D g₁).internal A = (D g₂).internal A) (e' : (D' g₁).internal A = (D' g₂).internal A)
    (h1 : g₁ ∈ linkEvent D D' cs Cs c₁ η δ ρ b ε r U) :
    g₂ ∈ linkEvent D D' cs Cs c₁ η δ ρ b ε r U := by
  intro x hx y hy hxy
  obtain ⟨u, hu, v, hv, hb, hrat, hset, hsetv, huniq, hs1, hs2, hi1, hi2⟩ := h1 x hx y hy hxy
  have hUA' := hUA x hx y hy hxy
  have h4 : 0 < 4 * ρ * r := by linarith
  have hB : ∀ w ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ),
      ball w (5 / 4 * (4 * ρ * r)) ⊆ A := fun w hw => by
    rw [show 5 / 4 * (4 * ρ * r) = 5 * ρ * r by ring]; exact hBA w hw
  obtain ⟨hm, d', d, hg⟩ := link_end_eq l1 l1' l2 l2' hcs hCs rat1 rat2 hA e e' h4 (hB u hu.1)
    (hUA' hv.2) hset
  have hvu1 : (D' g₁).1 (v, u) = (D' g₁).1 (u, v) := (D' g₁).2.symm v u
  obtain ⟨hmv, -, -, -⟩ := link_end_eq l1 l1' l2 l2' hcs hCs rat1 rat2 hA e e' h4 (hB v hv.1)
    (hUA' hu.2) (by rw [hvu1]; exact hsetv)
  have hiV : (D' g₂).internal (U x y) = (D' g₁).internal (U x y) :=
    (internal_eq_of_internal_eq hUA' e').symm
  refine ⟨u, hu, v, hv, hb, ?_, ?_, ?_, ?_, hs1, hs2, ?_, ?_⟩
  · rw [d, d']; exact hrat
  · rw [← hm, d']; exact hset
  · rw [← hmv, d']; exact hsetv
  · simp only [UniqueGeodIn, UniqueGeod, hg]; exact huniq
  · intro w hw; rw [hiV, d']; exact hi1 w hw
  · intro w hw; rw [hiV, d']; exact hi2 w hw

end LQGMetric.GM
