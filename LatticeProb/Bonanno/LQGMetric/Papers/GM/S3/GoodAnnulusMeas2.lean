/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulusClosed

/-!
# GM Lemma 3.7: conditions 2 and 3 of `𝖤_r(z)` through the internal metrics (task P2-M2E2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, proof
of Lemma 3.7, l. 1348–1353: "it is obvious that condition 3 … is determined by
`h|_{𝔸_{r/2,2r}(z)}`. For `u ∈ ∂B_{αr}(z)` and `v ∈ ∂B_r(z)`, we can determine whether
`D_h(u,v) > D_h(u, ∂𝔸_{r/2,2r}(z))` from the internal metric `D_h(·,·; 𝔸_{r/2,2r}(z))` … Hence
condition 2 … is determined by `h|_{𝔸_{r/2,2r}(z)}`."

Deterministic form: with `J = D_h(·,·;U)`, `J' = D̃_h(·,·;U)`, `U = 𝔸_{r/2,2r}(z)`,

* `mem_gaLong_iff_internal`: condition 2 holds iff `gaLongI J J'` (for proper length metrics,
  a.s. true for weak LQG metrics, GM.S1.1);
* `mem_gaAround_iff_internal`: condition 3 holds iff `gaAroundI J` (for length metrics),

using `lenFun_internal`, `setDist_spheres_eq_internal`, `setDist_frontier_lt_iff` and
`setDist_frontier_eq_iSup` (`GoodAnnulusMeas.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `D(u, ∂U)` through the internal metric `J = D(·,·;U)` (`setDist_frontier_eq_iSup`) -/
def bdFun (J : ℂ → ℂ → ℝ≥0∞) (U : Set ℂ) (u : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ y ∈ nearFrontier U (1 / (n + 1)), J u y

/-- condition 2 of `𝖤_r(z)` through the internal metrics `J`, `J'` of `𝔸_{r/2,2r}(z)` -/
def gaLongI (J J' : ℂ → ℂ → ℝ≥0∞) (α r : ℝ) (z : ℂ) : Prop :=
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r,
    (bdFun J (annulus z (r / 2) (2 * r)) u < J u v ∨
      bdFun J' (annulus z (r / 2) (2 * r)) u < J' u v) →
    ∀ (a b : ℝ) (P : ℝ → ℂ), a ≤ b → ContinuousOn P (Icc a b) → P a = u → P b = v →
      P '' Icc a b ⊆ closure (annulus z (α * r) r : Set ℂ) → J u v < lenFun J P a b

/-- condition 3 of `𝖤_r(z)` through the internal metric `J` of `𝔸_{r/2,2r}(z)` -/
def gaAroundI (J : ℂ → ℂ → ℝ≥0∞) (α A r : ℝ) (z : ℂ) : Prop :=
  ∃ (a b : ℝ) (G : ℝ → ℂ), a ≤ b ∧ ContinuousOn G (Icc a b) ∧
    G '' Icc a b ⊆ (annulus z (α * r) r : Set ℂ) ∧
    Disconnects (G '' Icc a b) (sphere z (α * r)) (sphere z r) ∧
    lenFun J G a b ≤ ENNReal.ofReal A * ⨅ x ∈ sphere z (α * r), ⨅ y ∈ sphere z r, J x y

section Annulus
variable {α r : ℝ} {z : ℂ}

lemma closedAnnulus_subset (hα : 1 / 2 < α) (hr : 0 < r) {w : ℂ} (h1 : α * r ≤ ‖w - z‖)
    (h2 : ‖w - z‖ ≤ r) : w ∈ (annulus z (r / 2) (2 * r) : Set ℂ) := by
  show r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 2 * r
  constructor <;> nlinarith

lemma closure_annulus_subset (hα : 1 / 2 < α) (hr : 0 < r) :
    closure (annulus z (α * r) r : Set ℂ) ⊆ (annulus z (r / 2) (2 * r) : Set ℂ) := fun _ hw =>
  closedAnnulus_subset hα hr (mem_closure_annulus hw).1 (mem_closure_annulus hw).2

lemma isBounded_annulus (r₁ r₂ : ℝ) : Bornology.IsBounded (annulus z r₁ r₂ : Set ℂ) :=
  (isBounded_ball (x := z) (r := r₂)).subset fun w hw => by
    rw [mem_ball, dist_eq_norm]; exact hw.2

end Annulus

/-- **GM l. 1350–1353**: condition 2 is determined by the internal metrics of
`𝔸_{r/2,2r}(z)`, for proper length metrics `D_h`, `D̃_h`. -/
theorem mem_gaLong_iff_internal {D D' : DistC → ContMetric} {α r : ℝ} {z : ℂ} {g : DistC}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) (hL : (D g).IsLength) (hL' : (D' g).IsLength)
    [ProperSpace (D g).Space] [ProperSpace (D' g).Space] :
    g ∈ gaLong D D' α r z ↔ gaLongI ((D g).internal (annulus z (r / 2) (2 * r)))
      ((D' g).internal (annulus z (r / 2) (2 * r))) α r z := by
  set U : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ)
  have hUo : IsOpen U := (annulus z (r / 2) (2 * r)).isOpen
  have hUb : Bornology.IsBounded U := isBounded_annulus _ _
  have hsph1 : ∀ u ∈ sphere z (α * r), u ∈ U := fun u hu =>
    closedAnnulus_subset hα hr (mem_sphere_iff_norm.1 hu).ge
      ((mem_sphere_iff_norm.1 hu).le.trans (by nlinarith))
  have hsph2 : ∀ v ∈ sphere z r, v ∈ U := fun v hv =>
    closedAnnulus_subset hα hr ((mem_sphere_iff_norm.1 hv).ge.trans' (by nlinarith))
      (mem_sphere_iff_norm.1 hv).le
  simp only [gaLong, gaLongI, mem_ofPred_eq]
  refine forall₂_congr fun u hu => forall₂_congr fun v hv => ?_
  have hb : ∀ (E : ContMetric), E.IsLength → ProperSpace E.Space →
      (setDist E {u} (frontier U) < ENNReal.ofReal (E.1 (u, v)) ↔
        bdFun (E.internal U) U u < E.internal U u v) := fun E hE _ => by
    rw [setDist_frontier_lt_iff E hE hUo (hsph1 u hu) (hsph2 v hv),
      setDist_frontier_eq_iSup E hE hUo hUb (hsph1 u hu)]
    rfl
  rw [hb _ hL inferInstance, hb _ hL' inferInstance]
  refine imp_congr_right fun _ => forall₃_congr fun a b P => imp_congr_right fun _ =>
    forall_congr' fun hP => imp_congr_right fun _ => imp_congr_right fun _ =>
      forall_congr' fun hK => ?_
  rw [lenFun_internal (D g) hP fun t ht => closure_annulus_subset hα hr (hK ⟨t, ht, rfl⟩)]

/-- **GM l. 1348**: condition 3 is determined by the internal metric of `𝔸_{r/2,2r}(z)`, for a
length metric `D_h`. -/
theorem mem_gaAround_iff_internal {D : DistC → ContMetric} {α A r : ℝ} {z : ℂ} {g : DistC}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) (hL : (D g).IsLength) :
    g ∈ gaAround D α A r z ↔ gaAroundI ((D g).internal (annulus z (r / 2) (2 * r))) α A r z := by
  have hset := setDist_spheres_eq_internal (D g) hL (V := (annulus z (r / 2) (2 * r) : Set ℂ))
    (z := z) (ρ₁ := α * r) (ρ₂ := r) (by nlinarith) fun w h1 h2 => closedAnnulus_subset hα hr h1 h2
  simp only [gaAround, gaAroundI, mem_ofPred_eq, hset]
  refine exists₃_congr fun a b G => and_congr_right fun _ => and_congr_right fun hG =>
    and_congr_right fun hsub => and_congr_right fun _ => ?_
  rw [lenFun_internal (D g) hG fun t ht => closure_annulus_subset hα hr
    (subset_closure (hsub ⟨t, ht, rfl⟩))]

end LQGMetric.GM
