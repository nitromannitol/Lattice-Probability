/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bL53 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bEvt
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_21Proof

/-!
# Towards GM Lemma 5.3: on `𝔈_r`, distances are internal to `B_{4r}(z)` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 5.3, l. 2779–2788: for times `s, t` with
`D̃(P(s), P(t)) ≤ (c_*/C_*) D̃(P(s), ∂B_{3r})` one has `D̃(P(s),P(t)) = D̃(P(s),P(t); B_{3r})`, and
`D(P(s), P(t))` is determined by the stopped geodesic. Here (the `[0,1]` parametrization does not
carry `D(𝕫,𝕨)`) both `D` and `D̃` are replaced by their internal metrics in `B_{4r}(z)`, using
the bi-Lipschitz bounds `c_* D ≤ D̃ ≤ C_* D`:
* `setDist_spheres_pos`, `setDist_sphere_add_le` : `D(x, ∂B_R) ≥ D(x, ∂B_ρ) + D(∂B_ρ, ∂B_R)` for
  a length metric (crossing argument), so `D(x, ∂B_ρ) < D(x, ∂B_R)` (`setDist_sphere_lt`);
* `internal_eq_of_le_setDist` : `D(x,y) ≤ D(x, ∂B_{3r})` ⇒ `D(x,y; B_{4r}) = D(x,y)` (no
  properness needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma setDist_singleton_eq_cm (D : ContMetric) (x : ℂ) (S : Set ℂ) :
    setDist D {x} S = infEDist (D.pt x) (D.pt '' S) := by
  rw [setDist, image_singleton, MetricGeometry.setEDist, iInf_singleton]

lemma setDist_le_of_mem_cm (D : ContMetric) {A B : Set ℂ} {u v : ℂ} (hu : u ∈ A) (hv : v ∈ B) :
    setDist D A B ≤ ENNReal.ofReal (D.1 (u, v)) := by
  rw [setDist_eq_iInf]; exact iInf₂_le_of_le u hu (iInf₂_le v hv)

lemma setDist_spheres_pos (D : ContMetric) (z : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    0 < setDist D (sphere z ρ) (sphere z R) := by
  have hK : IsCompact (sphere z ρ ×ˢ sphere z R) := (isCompact_sphere z ρ).prod (isCompact_sphere z R)
  have hne : (sphere z ρ ×ˢ sphere z R).Nonempty :=
    (NormedSpace.sphere_nonempty.2 hρ.le).prod (NormedSpace.sphere_nonempty.2 (by linarith))
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne D.1.continuous.continuousOn
  have hne' : p.1 ≠ p.2 := by
    intro h
    have h1 := hp.1; have h2 := hp.2
    rw [mem_sphere_iff_norm] at h1 h2
    rw [h] at h1; linarith
  have hpos : 0 < D.1 p := by
    have : D.1 (p.1, p.2) = dist (D.pt p.1) (D.pt p.2) := rfl
    rw [show p = (p.1, p.2) from rfl, this]
    exact dist_pos.2 hne'
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) ?_
  rw [setDist_eq_iInf]
  exact le_iInf₂ fun u hu => le_iInf₂ fun v hv =>
    ENNReal.ofReal_le_ofReal (hmin (show (u, v) ∈ sphere z ρ ×ˢ sphere z R from ⟨hu, hv⟩))

/-- crossing: `D(x, ∂B_ρ) + D(∂B_ρ, ∂B_R) ≤ D(x, ∂B_R)` for `x ∈ B_ρ`, `ρ < R` -/
lemma setDist_sphere_add_le (D : ContMetric) (hD : D.IsLength) {z x : ℂ} {ρ R : ℝ}
    (hx : ‖x - z‖ < ρ) (hρR : ρ < R) :
    setDist D {x} (sphere z ρ) + setDist D (sphere z ρ) (sphere z R) ≤
      setDist D {x} (sphere z R) := by
  rw [setDist_singleton_eq_cm D x (sphere z R)]
  refine le_infEDist.2 fun w hw => ?_
  obtain ⟨y, hy, rfl⟩ := hw
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hab, hPc, hPa, hPb, hlen⟩ :=
    MetricGeometry.isLengthSpace_iff_curves.1 hD (D.pt x) (D.pt y) ε (by exact_mod_cast hε)
  set f : ℝ → ℝ := fun t => ‖D.unpt (P t) - z‖ with hf
  have hfc : ContinuousOn f (Icc a b) :=
    (continuous_norm.comp (D.continuous_unpt.sub continuous_const)).comp_continuousOn hPc
  have hfa : f a ≤ ρ := by simp only [hf, hPa]; exact hx.le
  have hfb : ρ ≤ f b := by
    simp only [hf, hPb]; rw [mem_sphere_iff_norm] at hy; show ρ ≤ ‖y - z‖; linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hfc ⟨hfa, hfb⟩
  have hwt : D.unpt (P t) ∈ sphere z ρ := mem_sphere_iff_norm.2 hft
  have h1 : setDist D {x} (sphere z ρ) ≤ edist (P a) (P t) := by
    rw [hPa]
    exact (setDist_le_of_mem_cm D (mem_singleton x) hwt).trans
      (le_of_eq (ContMetric.edist_pt D x (D.unpt (P t))).symm)
  have h2 : setDist D (sphere z ρ) (sphere z R) ≤ edist (P t) (P b) := by
    rw [hPb]
    exact (setDist_le_of_mem_cm D hwt hy).trans
      (le_of_eq (ContMetric.edist_pt D (D.unpt (P t)) y).symm)
  calc setDist D {x} (sphere z ρ) + setDist D (sphere z ρ) (sphere z R)
      ≤ MetricGeometry.curveLength P a t + MetricGeometry.curveLength P t b :=
        add_le_add (h1.trans (MetricGeometry.edist_le_curveLength P ht.1))
          (h2.trans (MetricGeometry.edist_le_curveLength P ht.2))
    _ = MetricGeometry.curveLength P a b := MetricGeometry.curveLength_add P ht.1 ht.2
    _ ≤ edist (D.pt x) (D.pt y) + ENNReal.ofReal ε := hlen
    _ = edist (D.pt x) (D.pt y) + ε := by rw [ENNReal.ofReal_coe_nnreal]

lemma setDist_sphere_lt (D : ContMetric) (hD : D.IsLength) {z x : ℂ} {ρ R : ℝ}
    (hx : ‖x - z‖ < ρ) (hρR : ρ < R) :
    setDist D {x} (sphere z ρ) < setDist D {x} (sphere z R) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hx
  have hfin : setDist D {x} (sphere z ρ) ≠ ⊤ := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := z) (r := ρ)).2 hρ.le
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (setDist_le_of_mem_cm D (mem_singleton x) hw)
  calc setDist D {x} (sphere z ρ) < setDist D {x} (sphere z ρ) +
        setDist D (sphere z ρ) (sphere z R) :=
        ENNReal.lt_add_right hfin (setDist_spheres_pos D z hρ hρR).ne'
    _ ≤ _ := setDist_sphere_add_le D hD hx hρR

/-- `D(x,y) ≤ D(x, ∂B_ρ(z))`, `x ∈ B_ρ(z)`, `ρ < R` ⇒ `D(x, y; B_R(z)) = D(x, y)` -/
lemma internal_eq_of_le_setDist (D : ContMetric) (hD : D.IsLength) {z x y : ℂ} {ρ R : ℝ}
    (hx : ‖x - z‖ < ρ) (hρR : ρ < R)
    (hle : ENNReal.ofReal (D.1 (x, y)) ≤ setDist D {x} (sphere z ρ)) :
    D.internal (ball z R) x y = ENNReal.ofReal (D.1 (x, y)) := by
  have hR : 0 < R := by linarith [norm_nonneg (x - z), lt_of_le_of_lt (norm_nonneg _) hx]
  have hlt := hle.trans_lt (setDist_sphere_lt D hD hx hρR)
  rw [← frontier_ball z hR.ne', setDist_singleton_eq_cm, ← ContMetric.edist_pt] at hlt
  have hxR : x ∈ ball z R := by rw [mem_ball, dist_eq_norm]; linarith
  rw [← ContMetric.edist_pt]
  exact (ContMetric.internal_eq_of_lt_infEDist_frontier hD isOpen_ball hxR hlt).2

/-- (5.4) with `D`, `D̃` replaced by their internal metrics in `B_{4r}(z)` -/
def frkDistIn (Dg D'g : ContMetric) (cs Cs c₂ b₀ r : ℝ) (z : ℂ) (Q : unitInterval → ℂ) : Prop :=
  ∃ s t : unitInterval, 0 < s ∧ s < t ∧ t < 1 ∧
    Q s ∈ ball z (3 / 2 * r) ∧ Q t ∈ ball z (3 / 2 * r) ∧ b₀ * r ≤ ‖Q s - Q t‖ ∧
    D'g.internal (ball z (4 * r)) (Q s) (Q t) ≤
      ENNReal.ofReal c₂ * Dg.internal (ball z (4 * r)) (Q s) (Q t) ∧
    D'g.internal (ball z (4 * r)) (Q s) (Q t) ≤
      ENNReal.ofReal (cs / Cs) * DFGPS.setDistIn D'g {Q s} (sphere z (3 * r)) (ball z (4 * r))

/-- the key step of GM l. 2783–2788: `D̃(x,y) ≤ (c_*/C_*) D̃(x, ∂B_{3r})` forces both distances
to be internal to `B_{4r}(z)` -/
lemma internal_eq_of_frk {d d' : ContMetric} (hL : d.IsLength) (hL' : d'.IsLength) {cs Cs : ℝ}
    (hcs : 0 < cs) (hcC : cs ≤ Cs)
    (hbl : ∀ x y : ℂ, cs * d.1 (x, y) ≤ d'.1 (x, y) ∧ d'.1 (x, y) ≤ Cs * d.1 (x, y))
    {z x y : ℂ} {r : ℝ} (hx : x ∈ ball z (3 / 2 * r))
    (hA : ENNReal.ofReal (d'.1 (x, y)) ≤ ENNReal.ofReal (cs / Cs) * setDist d' {x} (sphere z (3 * r))) :
    d'.internal (ball z (4 * r)) x y = ENNReal.ofReal (d'.1 (x, y)) ∧
      d.internal (ball z (4 * r)) x y = ENNReal.ofReal (d.1 (x, y)) := by
  have hCs : 0 < Cs := lt_of_lt_of_le hcs hcC
  have hx' : ‖x - z‖ < 3 * r := by
    rw [mem_ball, dist_eq_norm] at hx
    have : 0 < r := by linarith [norm_nonneg (x - z)]
    linarith
  have hr : 0 < r := by linarith [norm_nonneg (x - z)]
  have h34 : 3 * r < 4 * r := by linarith
  have hk1 : ENNReal.ofReal (cs / Cs) ≤ 1 := ENNReal.ofReal_le_one.2 ((div_le_one hCs).2 hcC)
  -- `D̃(x, ∂B) ≤ C_* D(x, ∂B)`
  have hS : setDist d' {x} (sphere z (3 * r)) ≤
      ENNReal.ofReal Cs * setDist d {x} (sphere z (3 * r)) := by
    rw [setDist_eq_iInf, setDist_eq_iInf, ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hCs).ne'
      ENNReal.ofReal_ne_top]
    refine iInf_mono fun u => ?_
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hCs).ne' ENNReal.ofReal_ne_top]
    refine iInf_mono fun _ => ?_
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hCs).ne' ENNReal.ofReal_ne_top]
    refine iInf_mono fun w => ?_
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hCs).ne' ENNReal.ofReal_ne_top]
    refine iInf_mono fun _ => ?_
    rw [← ENNReal.ofReal_mul hCs.le]
    exact ENNReal.ofReal_le_ofReal (hbl u w).2
  refine ⟨internal_eq_of_le_setDist d' hL' hx' h34 (hA.trans ?_),
    internal_eq_of_le_setDist d hL hx' h34 ?_⟩
  · calc ENNReal.ofReal (cs / Cs) * setDist d' {x} (sphere z (3 * r))
        ≤ 1 * setDist d' {x} (sphere z (3 * r)) := by gcongr
      _ = _ := one_mul _
  · have hcs0 : ENNReal.ofReal cs ≠ 0 := (ENNReal.ofReal_pos.2 hcs).ne'
    rw [← ENNReal.mul_le_mul_iff_right hcs0 ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul hcs.le]
    calc ENNReal.ofReal (cs * d.1 (x, y)) ≤ ENNReal.ofReal (d'.1 (x, y)) :=
          ENNReal.ofReal_le_ofReal (hbl x y).1
      _ ≤ ENNReal.ofReal (cs / Cs) * setDist d' {x} (sphere z (3 * r)) := hA
      _ ≤ ENNReal.ofReal (cs / Cs) * (ENNReal.ofReal Cs * setDist d {x} (sphere z (3 * r))) := by
          gcongr
      _ = ENNReal.ofReal cs * setDist d {x} (sphere z (3 * r)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hcs.le hCs.le), div_mul_cancel₀ _ hCs.ne']

/-- **(5.4) is internal to `B_{4r}(z)`** (GM l. 2779–2788), for length metrics with
`c_* D ≤ D̃ ≤ C_* D` -/
theorem frkDist_iff_frkDistIn {D D' : DistC → ContMetric} {g : DistC} (hL : (D g).IsLength)
    (hL' : (D' g).IsLength) {cs Cs c₂ b₀ r : ℝ} (hcs : 0 < cs) (hcC : cs ≤ Cs) (hc₂ : 0 ≤ c₂)
    (hbl : ∀ x y : ℂ, cs * (D g).1 (x, y) ≤ (D' g).1 (x, y) ∧
      (D' g).1 (x, y) ≤ Cs * (D g).1 (x, y)) {z : ℂ} (Q : C(unitInterval, ℂ)) :
    frkDist D D' cs Cs c₂ b₀ r z g Q ↔ frkDistIn (D g) (D' g) cs Cs c₂ b₀ r z Q := by
  have hS : ∀ x ∈ ball z (3 / 2 * r), DFGPS.setDistIn (D' g) {x} (sphere z (3 * r))
      (ball z (4 * r)) = setDist (D' g) {x} (sphere z (3 * r)) := by
    intro x hx
    have hr : 0 < r := by rw [mem_ball, dist_eq_norm] at hx; linarith [norm_nonneg (x - z)]
    refine (DFGPS.L321.setDist_eq_setDistIn (D' g) hL' (fun w hw => ?_) fun w hw => ?_).symm
    · rw [mem_singleton_iff.1 hw]; rw [mem_ball] at hx ⊢; linarith
    · rw [mem_ball, dist_eq_norm]; linarith
  constructor
  · rintro ⟨s, t, h0, hst, h1, hs, ht, hb, hc, hd⟩
    obtain ⟨e1, e2⟩ := internal_eq_of_frk hL hL' hcs hcC hbl hs hd
    refine ⟨s, t, h0, hst, h1, hs, ht, hb, ?_, ?_⟩
    · rw [e1, e2, ← ENNReal.ofReal_mul hc₂]; exact ENNReal.ofReal_le_ofReal hc
    · rw [e1, hS _ hs]; exact hd
  · rintro ⟨s, t, h0, hst, h1, hs, ht, hb, hc, hd⟩
    have hA : ENNReal.ofReal ((D' g).1 (Q s, Q t)) ≤
        ENNReal.ofReal (cs / Cs) * setDist (D' g) {Q s} (sphere z (3 * r)) := by
      rw [← hS _ hs]
      refine le_trans ?_ hd
      rw [← ContMetric.edist_pt]
      exact MetricGeometry.edist_le_internalEDist _ _ _
    obtain ⟨e1, e2⟩ := internal_eq_of_frk hL hL' hcs hcC hbl hs hA
    refine ⟨s, t, h0, hst, h1, hs, ht, hb, ?_, hA⟩
    rw [e1, e2, ← ENNReal.ofReal_mul hc₂] at hc
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc₂ (ContMetric.nonneg _ _ _))).1 hc

end LQGMetric.GM
