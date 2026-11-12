/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes55Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs
import LatticeProb.Bonanno.LQGMetric.Metric.Midpoint
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace

/-!
# GM Lemma 5.5, deterministic part (task P2-M2L)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.5, l. 2899–2912.

* `internal_le_of_isGeod01`: a geodesic contained in `V` bounds the internal metric of `V`.
* `uniqueGeodIn_translate`: GM's use of Axiom IV′ (l. 2907), transport of `UniqueGeodIn`.
* `endpoint_core`: on the intersection of the tightness events and the event of Lemma 2.11, a
  `D̃_h`-geodesic from `u ∈ ∂B_{αr}(z)` to `v ∈ ∂B_r(z)` contained in `cl 𝔸_{αr,r}(z)` lies in the
  closure of one of four fixed half-annuli and satisfies condition 3 of the lemma.

Deviation P2-M2L-3 (detail of GM's proof): GM's tightness event "two points of `𝔸_{3r/4,r}(z)` not
in a single quarter-annulus are at `D̃_h`-distance `≥ s𝔠_r e^{ξh_r(z)}`" is replaced by the same
statement for points at Euclidean distance `≥ r/4` (same source, Axiom V via `Tight.gm_S2_4a_sep`);
then the geodesic lies in `B_{r/4}(u)`, which is contained in one of the four half-planes
`{Re((w − z) ē) > 0}`, `e ∈ {1, i, −1, −i}` (own elementary argument).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- A `D`-geodesic contained in `V` bounds the internal metric: `D(u,v;V) ≤ D(u,v)`. -/
theorem internal_le_of_isGeod01 {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)} {V : Set ℂ}
    (hη : IsGeod01 D u v η) (hV : range η ⊆ V) :
    D.internal V u v ≤ ENNReal.ofReal (D.1 (u, v)) := by
  set P : ℝ → D.Space := fun t => D.pt (η (Set.projIcc 0 1 zero_le_one t)) with hPdef
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ D.1 (u, v) * dist s t := by
    intro s hs t ht
    have e1 : dist (P s) (P t) = D.1 (η (Set.projIcc 0 1 zero_le_one s),
      η (Set.projIcc 0 1 zero_le_one t)) := rfl
    rw [e1, hη.2.2, Set.projIcc_of_mem _ hs, Set.projIcc_of_mem _ ht, Real.dist_eq, abs_sub_comm,
      mul_comm]
  have hnn : 0 ≤ D.1 (u, v) := by
    have : dist (D.pt u) (D.pt v) = D.1 (u, v) := rfl
    rw [← this]; exact dist_nonneg
  obtain ⟨hc, hlen⟩ := curveLength_le_of_dist_le_mul hnn hd
  have h0 : P 0 = D.pt u := by
    simp only [hPdef, Set.projIcc_left]
    rw [← hη.1]; rfl
  have h1 : P 1 = D.pt v := by
    simp only [hPdef, Set.projIcc_right]
    rw [← hη.2.1]; rfl
  have hmaps : MapsTo P (Icc 0 1) (D.pt '' V) := fun t _ =>
    ⟨_, hV ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩, rfl⟩
  have := internalEDist_le_curveLength zero_le_one hc hmaps
  rw [h0, h1] at this
  exact this.trans hlen

/-- `t ↦ η(t) + z` -/
def shiftPath (η : C(unitInterval, ℂ)) (z : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => η t + z, η.continuous.add continuous_const⟩

@[simp] lemma shiftPath_apply (η : C(unitInterval, ℂ)) (z : ℂ) (t : unitInterval) :
    shiftPath η z t = η t + z := rfl

lemma isGeod01_shift {D₁ D₂ : ContMetric} {z : ℂ} (hD : ∀ a b, D₁.1 (a, b) = D₂.1 (a + z, b + z))
    {u v : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 D₁ u v η) :
    IsGeod01 D₂ (u + z) (v + z) (shiftPath η z) := by
  refine ⟨by simp [hη.1], by simp [hη.2.1], fun s t => ?_⟩
  simp only [shiftPath_apply]
  rw [← hD, ← hD, hη.2.2]

lemma isGeod01_unshift {D₁ D₂ : ContMetric} {z : ℂ} (hD : ∀ a b, D₁.1 (a, b) = D₂.1 (a + z, b + z))
    {u v : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 D₂ (u + z) (v + z) η) :
    IsGeod01 D₁ u v (shiftPath η (-z)) := by
  refine ⟨by simp [hη.1], by simp [hη.2.1], fun s t => ?_⟩
  simp only [shiftPath_apply]
  rw [hD, hD]
  simp only [neg_add_cancel_right]
  rw [hη.2.2]

/-- Transport of "the geodesic is unique and contained in `S`" under a translation. -/
theorem uniqueGeodIn_translate {D₁ D₂ : ContMetric} {z : ℂ}
    (hD : ∀ a b, D₁.1 (a, b) = D₂.1 (a + z, b + z)) {u v : ℂ} {S : Set ℂ}
    (h : UniqueGeodIn D₁ u v S) : UniqueGeodIn D₂ (u + z) (v + z) ((· + z) '' S) := by
  obtain ⟨⟨η, hη, huniq⟩, hin⟩ := h
  refine ⟨⟨shiftPath η z, isGeod01_shift hD hη, fun η' hη' => ?_⟩, fun η' hη' => ?_⟩
  · have := huniq _ (isGeod01_unshift hD hη')
    ext t
    have ht := congrArg (fun f : C(unitInterval, ℂ) => f t) this
    simp only [shiftPath_apply] at ht ⊢
    rw [← ht]; ring
  · rintro _ ⟨t, rfl⟩
    refine ⟨η' t + -z, hin _ (isGeod01_unshift hD hη') ⟨t, rfl⟩, ?_⟩
    simp

lemma uniqueGeodIn_mono {D : ContMetric} {u v : ℂ} {S T : Set ℂ} (h : UniqueGeodIn D u v S)
    (hST : S ⊆ T) : UniqueGeodIn D u v T :=
  ⟨h.1, fun η hη => (h.2 η hη).trans hST⟩

lemma image_closure_annulus_subset (z : ℂ) (a b : ℝ) :
    (· + z) '' closure (annulus 0 a b : Set ℂ) ⊆ closure (annulus z a b : Set ℂ) := by
  refine (image_closure_subset_closure_image (continuous_id.add continuous_const)).trans
    (closure_mono ?_)
  rintro _ ⟨w, hw, rfl⟩
  have hw' : a < ‖w‖ ∧ ‖w‖ < b := by simpa [annulus] using hw
  show a < ‖w + z - z‖ ∧ ‖w + z - z‖ < b
  simpa using hw'

lemma closure_annulus_subset_closedAnnulus (z : ℂ) (a b : ℝ) :
    closure (annulus z a b : Set ℂ) ⊆ {w | a ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ b} := by
  refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) ?_
  exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)

/-- the four directions of the half-annuli of GM's proof -/
def dirs : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

lemma norm_dirs (k : Fin 4) : ‖dirs k‖ = 1 := by
  fin_cases k <;> simp [dirs]

/-- the half-annulus `𝔸_{a,b}(z) ∩ {Re((w − z) ē_k) > 0}` -/
def halfAnn (z : ℂ) (a b : ℝ) (k : Fin 4) : Set ℂ :=
  (annulus z a b : Set ℂ) ∩ {w | 0 < ((w - z) * (starRingEnd ℂ) (dirs k)).re}

lemma isHalfAnnulus_halfAnn (z : ℂ) (a b : ℝ) (k : Fin 4) : IsHalfAnnulus (halfAnn z a b k) z a b :=
  ⟨dirs k, norm_dirs k, rfl⟩

lemma isOpen_halfPlane (z e : ℂ) : IsOpen {w : ℂ | 0 < ((w - z) * (starRingEnd ℂ) e).re} :=
  isOpen_lt continuous_const
    (Complex.continuous_re.comp ((continuous_id.sub continuous_const).mul continuous_const))

/-- a point at distance `≥ 3r/4` from `z` has `Re((w − z) ē_k) ≥ r/4` for some `k` -/
lemma exists_dir {w z : ℂ} {r : ℝ} (hr : 0 < r) (hw : 3 / 4 * r ≤ ‖w - z‖) :
    ∃ k : Fin 4, r / 4 ≤ ((w - z) * (starRingEnd ℂ) (dirs k)).re := by
  by_contra hne
  push Not at hne
  have h0 := hne 0
  have h1 := hne 1
  have h2 := hne 2
  have h3 := hne 3
  simp [dirs, Complex.mul_re] at h0 h1 h2 h3
  have hsq : ‖w - z‖ ^ 2 = (w - z).re * (w - z).re + (w - z).im * (w - z).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hn : (3 / 4 * r) ^ 2 ≤ ‖w - z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hw 2
  simp only [Complex.sub_re, Complex.sub_im] at hsq h0 h1 h2 h3
  nlinarith

lemma tubes_cm_nonneg (D : ContMetric) (a b : ℂ) : 0 ≤ D.1 (a, b) := by
  have : dist (D.pt a) (D.pt b) = D.1 (a, b) := rfl
  rw [← this]; exact dist_nonneg

lemma geod_le_of_start {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)} (hη : IsGeod01 D u v η)
    (t : unitInterval) : D.1 (u, η t) ≤ D.1 (u, v) := by
  have h := hη.2.2 0 t
  rw [hη.1] at h
  rw [h]
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have : |(t : ℝ) - ((0 : unitInterval) : ℝ)| ≤ 1 := by
    simp only [Set.Icc.coe_zero, sub_zero, abs_of_nonneg ht0]; exact ht1
  nlinarith [tubes_cm_nonneg D u v, abs_nonneg ((t : ℝ) - ((0 : unitInterval) : ℝ))]

/-- **Deterministic core of GM Lemma 5.5** (l. 2899–2912), for `D₁ = D̃_h`,
`σ = 𝔠_r e^{ξh_r(z)}`, `κ = (c_*/C_*)²`. -/
theorem endpoint_core {D₁ : ContMetric} {z u v : ℂ} {r α σ s s₁ s₂ S₀ S κ : ℝ}
    (hr : 0 < r) (hα : 3 / 4 ≤ α) (hσ : 0 < σ) (hs1 : s ≤ s₁) (hs2 : s ≤ κ * s₂)
    (hκ : 0 ≤ κ) (hS0 : 0 ≤ S₀) (hS : S₀ < S)
    (hA1 : ∀ x y : ℂ, 3 / 4 * r ≤ ‖x - z‖ → ‖x - z‖ ≤ r → 3 / 4 * r ≤ ‖y - z‖ → ‖y - z‖ ≤ r →
      r / 4 ≤ ‖x - y‖ → s₁ * σ < D₁.1 (x, y))
    (hA2 : ∀ x : ℂ, 3 / 4 * r ≤ ‖x - z‖ → ‖x - z‖ ≤ r → ∀ y ∈ Metric.sphere z (2 * r),
      s₂ * σ < D₁.1 (x, y))
    (hA3 : ∀ x y : ℂ, ‖x - z‖ ≤ r → ‖y - z‖ ≤ r → D₁.1 (x, y) ≤ S₀ * σ)
    (hA4 : ∀ x ∈ closure (annulus z (α * r) r : Set ℂ), ∀ y ∈ closure (annulus z (α * r) r : Set ℂ),
      s * σ ≤ D₁.1 (x, y) →
        ENNReal.ofReal (S * σ) ≤ D₁.internal (closure (annulus z (α * r) r : Set ℂ)) x y)
    (hu : u ∈ Metric.sphere z (α * r)) (hv : v ∈ Metric.sphere z r)
    (hgeo : UniqueGeodIn D₁ u v (closure (annulus z (α * r) r : Set ℂ))) :
    ∃ k : Fin 4, UniqueGeodIn D₁ u v (closure (halfAnn z (α * r) r k)) ∧
      ENNReal.ofReal (D₁.1 (u, v)) ≤
        ENNReal.ofReal κ * setDist D₁ (annulus z (α * r) r) (Metric.sphere z (2 * r)) := by
  obtain ⟨⟨η, hη, huniq⟩, hin⟩ := hgeo
  have hcl := closure_annulus_subset_closedAnnulus z (α * r) r
  have hu' : ‖u - z‖ = α * r := mem_sphere_iff_norm.1 hu
  have hv' : ‖v - z‖ = r := mem_sphere_iff_norm.1 hv
  have hrange := hin η hη
  have hlt : D₁.1 (u, v) < s * σ := by
    by_contra hge
    push Not at hge
    have huA : u ∈ closure (annulus z (α * r) r : Set ℂ) := hη.1 ▸ hrange ⟨0, rfl⟩
    have hvA : v ∈ closure (annulus z (α * r) r : Set ℂ) := hη.2.1 ▸ hrange ⟨1, rfl⟩
    have h4 := hA4 u huA v hvA hge
    have h5 := internal_le_of_isGeod01 hη hrange
    have h6 := hA3 u v (by have := (hcl huA).2; linarith) (le_of_eq hv')
    have h7 : ENNReal.ofReal (S * σ) ≤ ENNReal.ofReal (S₀ * σ) :=
      h4.trans (h5.trans (ENNReal.ofReal_le_ofReal h6))
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h7
    nlinarith
  have hnear : ∀ t : unitInterval, ‖η t - u‖ < r / 4 := by
    intro t
    by_contra hge
    push Not at hge
    have hxA := hcl (hrange ⟨t, rfl⟩)
    have h1 := hA1 u (η t) (by rw [hu']; nlinarith) (by rw [hu']; linarith [hxA.1, hxA.2])
      (by nlinarith [hxA.1]) hxA.2 (by rwa [norm_sub_rev])
    have h2 := geod_le_of_start hη t
    nlinarith
  obtain ⟨k, hk⟩ := exists_dir hr (w := u) (z := z) (by rw [hu']; nlinarith)
  refine ⟨k, ⟨⟨η, hη, huniq⟩, fun η' hη' => ?_⟩, ?_⟩
  · rw [huniq η' hη']
    rintro _ ⟨t, rfl⟩
    have hhp : η t ∈ {w : ℂ | 0 < ((w - z) * (starRingEnd ℂ) (dirs k)).re} := by
      show 0 < ((η t - z) * (starRingEnd ℂ) (dirs k)).re
      have e : (η t - z) * (starRingEnd ℂ) (dirs k) =
          (u - z) * (starRingEnd ℂ) (dirs k) + (η t - u) * (starRingEnd ℂ) (dirs k) := by ring
      have hn : ‖(η t - u) * (starRingEnd ℂ) (dirs k)‖ = ‖η t - u‖ := by
        rw [norm_mul, Complex.norm_conj, norm_dirs, mul_one]
      have hre := Complex.abs_re_le_norm ((η t - u) * (starRingEnd ℂ) (dirs k))
      rw [e, Complex.add_re]
      have := hnear t
      have := neg_abs_le ((η t - u) * (starRingEnd ℂ) (dirs k)).re
      linarith
    have := (isOpen_halfPlane z (dirs k)).inter_closure ⟨hhp, hrange ⟨t, rfl⟩⟩
    rwa [inter_comm] at this
  · have hsd : ENNReal.ofReal (s₂ * σ) ≤
        setDist D₁ (annulus z (α * r) r) (Metric.sphere z (2 * r)) := by
      unfold setDist
      rw [setEDist_eq_iInf]
      refine le_iInf₂ fun _ hx' => le_iInf₂ fun _ hy' => ?_
      obtain ⟨x, hx, rfl⟩ := hx'
      obtain ⟨y, hy, rfl⟩ := hy'
      have hx2 : α * r < ‖x - z‖ ∧ ‖x - z‖ < r := hx
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal
        (hA2 x (by nlinarith [hx2.1]) hx2.2.le y hy).le
    calc ENNReal.ofReal (D₁.1 (u, v)) ≤ ENNReal.ofReal (κ * (s₂ * σ)) := by
          apply ENNReal.ofReal_le_ofReal; nlinarith
      _ = ENNReal.ofReal κ * ENNReal.ofReal (s₂ * σ) := ENNReal.ofReal_mul hκ
      _ ≤ _ := by gcongr

end LQGMetric.GM
