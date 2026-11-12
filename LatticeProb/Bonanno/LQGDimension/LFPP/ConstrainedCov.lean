/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovEst

/-!
# Node `L32c`: the constrained covariance limit (Lemma 3.2, third parametrization, and (3.3))

We prove `Blueprint.Draft.ConstrainedCovLimit` from `Blueprint.Draft.TwoScaleCovBound`
(Lemma 3.1, used exactly as in the paper: for the `O(δ²)` replacement of the constrained polygon
by a displaced graph, and for the Hölder-`1/2` modulus).

* Clause 2 (the energy expansion (3.3)) is `uLen_energy_est` (explicit error `O(δ²)`).
* Clause 3 (the modulus) is `clause3_bound`.
* Clause 1: `clause1_err` replaces the configuration by chords cut into `M` edges and displaced
  graphs `chord(t) + i δ f(t)`, at cost `O(δ^{3/2})`; the covariance of the latter is computed
  by the core of node `L32g` (`logCov_four`, `inner_subst`, `core_tendsto`), applied along the
  filter `𝓝[>] 0 ×ˢ 𝓟 K` of the compact parameter set `K`, which gives the uniformity.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft GraphCov

/-! ## Parameters -/

/-- The parameters `(f, f', p₀, p₁, p₀', p₁')` of a pair of constrained configurations. -/
structure Prm where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  p₀ : ℂ
  p₁ : ℂ
  p₀' : ℂ
  p₁' : ℂ

/-- The parameter set of `ConstrainedCovLimit`. -/
def Kset (n : ℕ) (B A : ℝ) : Set Prm :=
  {q | q.f ∈ V n ∧ q.f' ∈ V n ∧ (∀ x, |q.f x| ≤ B) ∧ (∀ x, |q.f' x| ≤ B) ∧ ‖q.p₀‖ ≤ A ∧
    ‖q.p₁‖ ≤ A ∧ ‖q.p₀'‖ ≤ A ∧ ‖q.p₁'‖ ≤ A}

/-- The displaced-graph four-term covariance (the main term). -/
def mainCov (n : ℕ) (δ : ℝ) (q : Prm) : ℝ :=
  ((chordM (16 ^ n) (xp δ q.p₀) (yp δ q.p₁)).sub
      (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ q.f q.p₀ q.p₁))).logCov
    ((chordM (16 ^ n) (xp δ q.p₀') (yp δ q.p₁')).sub
      (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ q.f' q.p₀' q.p₁')))

/-- The limit `Cov(Z_{f+g} - Z_g, Z_{f'+g'} - Z_{g'})`. -/
def limCov (q : Prm) : ℝ :=
  zDiffCov q.f (affineFn q.p₀.im q.p₁.im) q.f' (affineFn q.p₀'.im q.p₁'.im)

/-! ## Affine profiles -/

lemma abs_affineFn_le {t₀ t₁ A : ℝ} (h0 : |t₀| ≤ A) (h1 : |t₁| ≤ A) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : |affineFn t₀ t₁ x| ≤ A := by
  unfold affineFn
  rw [show t₀ + (t₁ - t₀) * x = (1 - x) * t₀ + x * t₁ by ring]
  calc _ ≤ |(1 - x) * t₀| + |x * t₁| := abs_add_le _ _
    _ = (1 - x) * |t₀| + x * |t₁| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.2]), abs_of_nonneg hx.1]
    _ ≤ (1 - x) * A + x * A := by gcongr <;> linarith [hx.1, hx.2]
    _ = A := by ring

lemma abs_affineFn_sub {t₀ t₁ : ℝ} (x y : ℝ) :
    |affineFn t₀ t₁ x - affineFn t₀ t₁ y| = |t₁ - t₀| * |x - y| := by
  unfold affineFn
  rw [show t₀ + (t₁ - t₀) * x - (t₀ + (t₁ - t₀) * y) = (t₁ - t₀) * (x - y) by ring, abs_mul]

lemma continuous_affineFn (t₀ t₁ : ℝ) : Continuous (affineFn t₀ t₁) := by
  unfold affineFn; fun_prop

lemma abs_im_le {p : ℂ} {A : ℝ} (h : ‖p‖ ≤ A) : |p.im| ≤ A := (Complex.abs_im_le_norm p).trans h

lemma abs_re_le {p : ℂ} {A : ℝ} (h : ‖p‖ ≤ A) : |p.re| ≤ A := (Complex.abs_re_le_norm p).trans h

/-! ## The limit as an integral -/

/-- The pointwise limit integrand `2π Σ σ_k |b0_k|`. -/
def Bq (q : Prm) (x : ℝ) : ℝ :=
  2 * π * ∑ k, σ4 k * |bvec (affineFn q.p₀.im q.p₁.im x)
    ((affineFn q.p₀.im q.p₁.im + q.f) x) (affineFn q.p₀'.im q.p₁'.im x)
    ((affineFn q.p₀'.im q.p₁'.im + q.f') x) k|

lemma continuous_Bq (q : Prm) (hf : Continuous q.f) (hf' : Continuous q.f') :
    Continuous (Bq q) := by
  unfold Bq
  refine continuous_const.mul (continuous_finset_sum _ fun k _ => continuous_const.mul ?_)
  refine (continuous_bvec ?_ ?_ ?_ ?_ k).abs
  · exact continuous_affineFn _ _
  · exact (continuous_affineFn _ _).add hf
  · exact continuous_affineFn _ _
  · exact (continuous_affineFn _ _).add hf'

lemma limCov_eq (q : Prm) (hf : Continuous q.f) (hf' : Continuous q.f') :
    limCov q = ∫ x in (0:ℝ)..1, Bq q x := by
  have hg := continuous_affineFn q.p₀.im q.p₁.im
  have hg' := continuous_affineFn q.p₀'.im q.p₁'.im
  have e : ∀ x, Bq q x = π *
      ((|(q.f + affineFn q.p₀.im q.p₁.im) x| + |(q.f' + affineFn q.p₀'.im q.p₁'.im) x| -
          |(q.f + affineFn q.p₀.im q.p₁.im) x - (q.f' + affineFn q.p₀'.im q.p₁'.im) x|) -
        (|(q.f + affineFn q.p₀.im q.p₁.im) x| + |affineFn q.p₀'.im q.p₁'.im x| -
          |(q.f + affineFn q.p₀.im q.p₁.im) x - affineFn q.p₀'.im q.p₁'.im x|) -
        (|affineFn q.p₀.im q.p₁.im x| + |(q.f' + affineFn q.p₀'.im q.p₁'.im) x| -
          |affineFn q.p₀.im q.p₁.im x - (q.f' + affineFn q.p₀'.im q.p₁'.im) x|) +
        (|affineFn q.p₀.im q.p₁.im x| + |affineFn q.p₀'.im q.p₁'.im x| -
          |affineFn q.p₀.im q.p₁.im x - affineFn q.p₀'.im q.p₁'.im x|)) := by
    intro x
    simp only [Bq, σ4, bvec, Fin.sum_univ_four, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    ring_nf
  have ii : ∀ F G : ℝ → ℝ, Continuous F → Continuous G →
      IntervalIntegrable (fun x => |F x| + |G x| - |F x - G x|) volume 0 1 :=
    fun F G hF hG => (by fun_prop : Continuous fun x => |F x| + |G x| - |F x - G x|).intervalIntegrable 0 1
  have i1 := ii (q.f + affineFn q.p₀.im q.p₁.im) (q.f' + affineFn q.p₀'.im q.p₁'.im)
    (hf.add hg) (hf'.add hg')
  have i2 := ii (q.f + affineFn q.p₀.im q.p₁.im) (affineFn q.p₀'.im q.p₁'.im) (hf.add hg) hg'
  have i3 := ii (affineFn q.p₀.im q.p₁.im) (q.f' + affineFn q.p₀'.im q.p₁'.im) hg (hf'.add hg')
  have i4 := ii (affineFn q.p₀.im q.p₁.im) (affineFn q.p₀'.im q.p₁'.im) hg hg'
  unfold limCov zDiffCov zCov
  rw [intervalIntegral.integral_congr (fun x _ => e x), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((i1.sub i2).sub i3) i4,
    intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2]
  ring

/-! ## The substituted kernel data -/

/-- Slope `α' = 1 + δ (p₁' - p₀').re` of the real part of the second chord. -/
def al (r : ℝ × Prm) : ℝ := 1 + r.1 * (r.2.p₁' - r.2.p₀').re

/-- Offset `β' = δ p₀'.re`. -/
def be (r : ℝ × Prm) : ℝ := r.1 * r.2.p₀'.re

/-- The substitution `y(w) = (δ/α') w + (A x - β')/α'`. -/
def yw (r : ℝ × Prm) (x w : ℝ) : ℝ :=
  (r.1 / al r) * w + (Aff r.1 r.2.p₀ r.2.p₁ x - be r) / al r

def bb (r : ℝ × Prm) (x w : ℝ) : Fin 4 → ℝ :=
  bvec (affineFn r.2.p₀.im r.2.p₁.im x) ((affineFn r.2.p₀.im r.2.p₁.im + r.2.f) x)
    (affineFn r.2.p₀'.im r.2.p₁'.im (yw r x w))
    ((affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') (yw r x w))

def bb0 (r : ℝ × Prm) (x : ℝ) : Fin 4 → ℝ :=
  bvec (affineFn r.2.p₀.im r.2.p₁.im x) ((affineFn r.2.p₀.im r.2.p₁.im + r.2.f) x)
    (affineFn r.2.p₀'.im r.2.p₁'.im x) ((affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') x)

def ww0 (r : ℝ × Prm) (x : ℝ) : ℝ := (be r - Aff r.1 r.2.p₀ r.2.p₁ x) / r.1

def ww1 (r : ℝ × Prm) (x : ℝ) : ℝ := (al r + be r - Aff r.1 r.2.p₀ r.2.p₁ x) / r.1

lemma Aff'_eq (r : ℝ × Prm) (y : ℝ) : Aff r.1 r.2.p₀' r.2.p₁' y = al r * y + be r := by
  unfold Aff al be; ring

lemma Bq_eq (r : ℝ × Prm) (x : ℝ) : Bq r.2 x = 2 * π * ∑ k, σ4 k * |bb0 r x k| := rfl

section Main

variable {n : ℕ} {B A : ℝ}

lemma al_ge {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) : 7 / 8 ≤ al r :=
  one_add_re_pos hs hq.2.2.2.2.2.2.1 hq.2.2.2.2.2.2.2

lemma abs_Aff_le {δ : ℝ} {p₀ p₁ : ℂ} (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |Aff δ p₀ p₁ x| ≤ 2 := by
  have hδ := hs.pos
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hr0 := abs_re_le h0
  have hr := abs_re_le (show ‖p₁ - p₀‖ ≤ 2 * A from (norm_sub_le _ _).trans (by linarith))
  unfold Aff
  have e1 : |δ * p₀.re| ≤ δ * A := by rw [abs_mul, abs_of_pos hδ]; gcongr
  have e2 : |x * (1 + δ * (p₁ - p₀).re)| ≤ 1 * (1 + δ * (2 * A)) := by
    rw [abs_mul, abs_of_nonneg hx.1]
    gcongr
    · exact hx.2
    · calc |1 + δ * (p₁ - p₀).re| ≤ |1| + |δ * (p₁ - p₀).re| := abs_add_le _ _
        _ ≤ 1 + δ * (2 * A) := by
            rw [abs_one, abs_mul, abs_of_pos hδ]; gcongr
  calc _ ≤ |δ * p₀.re| + |x * (1 + δ * (p₁ - p₀).re)| := abs_add_le _ _
    _ ≤ δ * A + 1 * (1 + δ * (2 * A)) := add_le_add e1 e2
    _ ≤ 2 := by linarith [hs.hA]

lemma yw_mem {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) {x w : ℝ}
    (hw : w ∈ Icc (ww0 r x) (ww1 r x)) : yw r x w ∈ Icc (0 : ℝ) 1 := by
  have hδ := hs.pos
  have hα : 0 < al r := lt_of_lt_of_le (by norm_num) (al_ge hs hq)
  unfold ww0 ww1 at hw
  obtain ⟨h1, h2⟩ := hw
  rw [div_le_iff₀ hδ] at h1
  rw [le_div_iff₀ hδ] at h2
  unfold yw
  constructor
  · rw [show r.1 / al r * w + (Aff r.1 r.2.p₀ r.2.p₁ x - be r) / al r =
      (w * r.1 + Aff r.1 r.2.p₀ r.2.p₁ x - be r) / al r by ring]
    apply div_nonneg _ hα.le
    linarith
  · rw [show r.1 / al r * w + (Aff r.1 r.2.p₀ r.2.p₁ x - be r) / al r =
      (w * r.1 + Aff r.1 r.2.p₀ r.2.p₁ x - be r) / al r by ring, div_le_one hα]
    linarith

lemma abs_yw_sub_le {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (w : ℝ) : |yw r x w - x| ≤ 2 * r.1 * (|w| + 6 * A) := by
  have hδ := hs.pos
  have hα := al_ge hs hq
  have hα0 : 0 < al r := lt_of_lt_of_le (by norm_num) hα
  obtain ⟨-, -, -, -, h0, h1, h0', h1'⟩ := hq
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have e1 : yw r x w - x = (r.1 * w + (Aff r.1 r.2.p₀ r.2.p₁ x - be r - al r * x)) / al r := by
    unfold yw
    rw [eq_div_iff hα0.ne']
    field_simp
    ring
  have e2 : Aff r.1 r.2.p₀ r.2.p₁ x - be r - al r * x = r.1 * (r.2.p₀.re - r.2.p₀'.re +
      x * ((r.2.p₁ - r.2.p₀).re - (r.2.p₁' - r.2.p₀').re)) := by
    unfold Aff be al; ring
  have e : yw r x w - x = r.1 * (w + (r.2.p₀.re - r.2.p₀'.re +
      x * ((r.2.p₁ - r.2.p₀).re - (r.2.p₁' - r.2.p₀').re))) / al r := by
    rw [e1, e2]; ring
  rw [e, abs_div, abs_of_pos hα0, div_le_iff₀ hα0, abs_mul, abs_of_pos hδ]
  have hr0 := abs_re_le h0
  have hr0' := abs_re_le h0'
  have hr1 := abs_re_le (show ‖r.2.p₁ - r.2.p₀‖ ≤ 2 * A from (norm_sub_le _ _).trans (by linarith))
  have hr1' := abs_re_le (show ‖r.2.p₁' - r.2.p₀'‖ ≤ 2 * A from
    (norm_sub_le _ _).trans (by linarith))
  have hxin : |x * ((r.2.p₁ - r.2.p₀).re - (r.2.p₁' - r.2.p₀').re)| ≤ 4 * A := by
    rw [abs_mul, abs_of_nonneg hx.1]
    calc x * |(r.2.p₁ - r.2.p₀).re - (r.2.p₁' - r.2.p₀').re| ≤ 1 * (2 * A + 2 * A) := by
          gcongr
          · exact hx.2
          · exact (abs_sub _ _).trans (by linarith)
      _ = 4 * A := by ring
  have hin : |w + (r.2.p₀.re - r.2.p₀'.re + x * ((r.2.p₁ - r.2.p₀).re -
      (r.2.p₁' - r.2.p₀').re))| ≤ |w| + 6 * A := by
    calc _ ≤ |w| + |r.2.p₀.re - r.2.p₀'.re + x * ((r.2.p₁ - r.2.p₀).re -
          (r.2.p₁' - r.2.p₀').re)| := abs_add_le _ _
      _ ≤ |w| + (|r.2.p₀.re| + |r.2.p₀'.re| + 4 * A) := by
          gcongr
          calc _ ≤ |r.2.p₀.re - r.2.p₀'.re| + |x * ((r.2.p₁ - r.2.p₀).re -
                (r.2.p₁' - r.2.p₀').re)| := abs_add_le _ _
            _ ≤ (|r.2.p₀.re| + |r.2.p₀'.re|) + 4 * A := add_le_add (abs_sub _ _) hxin
      _ ≤ |w| + 6 * A := by linarith
  calc r.1 * |w + (r.2.p₀.re - r.2.p₀'.re + x * ((r.2.p₁ - r.2.p₀).re -
        (r.2.p₁' - r.2.p₀').re))| ≤ r.1 * (|w| + 6 * A) := by gcongr
    _ ≤ 2 * r.1 * (|w| + 6 * A) * (7 / 8) := by
        have : 0 ≤ r.1 * (|w| + 6 * A) := by positivity
        nlinarith
    _ ≤ 2 * r.1 * (|w| + 6 * A) * al r := by
        have : 0 ≤ 2 * r.1 * (|w| + 6 * A) := by positivity
        gcongr

end Main

section Main2

variable {n : ℕ} {B A : ℝ}

lemma chordM_eq_pc (n : ℕ) (δ : ℝ) (p₀ p₁ : ℂ) :
    chordM (16 ^ n) (xp δ p₀) (yp δ p₁) =
      pc (16 ^ n) (dc (Aff δ p₀ p₁) δ (affineFn p₀.im p₁.im)) := by
  rw [← chordPt_eq_dc, pc_eq_wc]; rfl

lemma zvwc_eq_pc (n : ℕ) (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) :
    wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f p₀ p₁) =
      pc (16 ^ n) (dc (Aff δ p₀ p₁) δ (affineFn p₀.im p₁.im + f)) := by
  rw [← zC_eq_dc, pc_eq_wc]; rfl

lemma bound_g {p₀ p₁ : ℂ} (hB : 0 ≤ B) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) :
    ∀ x ∈ Icc (0:ℝ) 1, |affineFn p₀.im p₁.im x| ≤ A + B := fun x hx =>
  (abs_affineFn_le (abs_im_le h0) (abs_im_le h1) hx).trans (by linarith)

lemma bound_gf {p₀ p₁ : ℂ} {f : ℝ → ℝ} (hfB : ∀ x, |f x| ≤ B) (h0 : ‖p₀‖ ≤ A)
    (h1 : ‖p₁‖ ≤ A) : ∀ x ∈ Icc (0:ℝ) 1, |(affineFn p₀.im p₁.im + f) x| ≤ A + B := fun x hx =>
  (abs_add_le _ _).trans (add_le_add (abs_affineFn_le (abs_im_le h0) (abs_im_le h1) hx) (hfB x))

/-- The main term as an iterated integral in `(x, w)`. -/
lemma mainCov_repr {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) :
    r.1⁻¹ * mainCov n r.1 r.2 =
      (1 / al r) * ∫ x in (0:ℝ)..1, ∫ w in ww0 r x..ww1 r x, Kf σ4 w (bb r x w) := by
  obtain ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩ := hq
  have hM := M_pos n
  have hδ := hs.pos
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hα : 0 < al r := lt_of_lt_of_le (by norm_num) (al_ge hs ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩)
  have hfc := Subadd.V_continuous hf
  have hf'c := Subadd.V_continuous hf'
  have hAc : ∀ p₀ p₁ : ℂ, Continuous (Aff r.1 p₀ p₁) := fun p₀ p₁ => by unfold Aff; fun_prop
  unfold mainCov
  rw [chordM_eq_pc, zvwc_eq_pc, chordM_eq_pc, zvwc_eq_pc]
  have m1 : MeshAff (16 ^ n) (dc (Aff r.1 r.2.p₀ r.2.p₁) r.1 (affineFn r.2.p₀.im r.2.p₁.im)) := by
    rw [← chordPt_eq_dc]; exact meshAff_chordPt _ hM _ _
  have m2 : MeshAff (16 ^ n)
      (dc (Aff r.1 r.2.p₀ r.2.p₁) r.1 (affineFn r.2.p₀.im r.2.p₁.im + r.2.f)) := by
    rw [← zC_eq_dc]; exact meshAff_zC hf _ _ _
  have m3 : MeshAff (16 ^ n)
      (dc (Aff r.1 r.2.p₀' r.2.p₁') r.1 (affineFn r.2.p₀'.im r.2.p₁'.im)) := by
    rw [← chordPt_eq_dc]; exact meshAff_chordPt _ hM _ _
  have m4 : MeshAff (16 ^ n)
      (dc (Aff r.1 r.2.p₀' r.2.p₁') r.1 (affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f')) := by
    rw [← zC_eq_dc]; exact meshAff_zC hf' _ _ _
  have hA1 := fun x (hx : x ∈ Icc (0:ℝ) 1) => abs_Aff_le hs h0 h1 hx
  have c1 := continuous_affineFn r.2.p₀.im r.2.p₁.im
  have c2 := (continuous_affineFn r.2.p₀.im r.2.p₁.im).add hfc
  have c3 := continuous_affineFn r.2.p₀'.im r.2.p₁'.im
  have c4 := (continuous_affineFn r.2.p₀'.im r.2.p₁'.im).add hf'c
  have b1 := bound_g hB h0 h1
  have b2 := bound_gf hfB h0 h1
  have b3 := bound_g hB h0' h1'
  have b4 := bound_gf hf'B h0' h1'
  rw [logCov_four hM hM hM hM m1 m2 m3 m4
    (logDom_dc (hAc _ _) hα (Aff'_eq r) c1 c3 hA1 b1 b3)
    (logDom_dc (hAc _ _) hα (Aff'_eq r) c1 c4 hA1 b1 b4)
    (logDom_dc (hAc _ _) hα (Aff'_eq r) c2 c3 hA1 b2 b3)
    (logDom_dc (hAc _ _) hα (Aff'_eq r) c2 c4 hA1 b2 b4)]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [inner_subst hδ hα (Aff r.1 r.2.p₀ r.2.p₁) (Aff r.1 r.2.p₀' r.2.p₁') (Aff'_eq r)]
  rw [← mul_assoc, show r.1⁻¹ * (r.1 / al r) = 1 / al r by
    rw [mul_div_assoc', inv_mul_cancel₀ hδ.ne']]
  rfl

end Main2

/-! ## Clause 1, main term: uniform convergence -/

section Main3

variable {n : ℕ} {B A : ℝ}

lemma cont_bb (r : ℝ × Prm) (hfc : Continuous r.2.f) (hf'c : Continuous r.2.f') (k : Fin 4) :
    Continuous fun p : ℝ × ℝ => bb r p.1 p.2 k := by
  have hyw : Continuous fun p : ℝ × ℝ => yw r p.1 p.2 := by unfold yw Aff; fun_prop
  have hg := continuous_affineFn r.2.p₀.im r.2.p₁.im
  have hg' := continuous_affineFn r.2.p₀'.im r.2.p₁'.im
  exact continuous_bvec (u₁ := fun p : ℝ × ℝ => affineFn r.2.p₀.im r.2.p₁.im p.1)
    (u₂ := fun p : ℝ × ℝ => (affineFn r.2.p₀.im r.2.p₁.im + r.2.f) p.1)
    (v₃ := fun p : ℝ × ℝ => affineFn r.2.p₀'.im r.2.p₁'.im (yw r p.1 p.2))
    (v₄ := fun p : ℝ × ℝ => (affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') (yw r p.1 p.2))
    (hg.comp continuous_fst) ((hg.add hfc).comp continuous_fst) (hg'.comp hyw)
    ((hg'.add hf'c).comp hyw) k

lemma cont_bb0 (r : ℝ × Prm) (hfc : Continuous r.2.f) (hf'c : Continuous r.2.f') (k : Fin 4) :
    Continuous fun x : ℝ => bb0 r x k := by
  have hg := continuous_affineFn r.2.p₀.im r.2.p₁.im
  have hg' := continuous_affineFn r.2.p₀'.im r.2.p₁'.im
  exact continuous_bvec (u₁ := fun x : ℝ => affineFn r.2.p₀.im r.2.p₁.im x)
    (u₂ := fun x : ℝ => (affineFn r.2.p₀.im r.2.p₁.im + r.2.f) x)
    (v₃ := fun x : ℝ => affineFn r.2.p₀'.im r.2.p₁'.im x)
    (v₄ := fun x : ℝ => (affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') x) hg (hg.add hfc) hg'
    (hg'.add hf'c) k

lemma abs_bb_sub_le {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (w : ℝ) (k : Fin 4) :
    |bb r x w k - bb0 r x k| ≤
      (4 * A + 2 * B * (16 : ℝ) ^ n) * (2 * r.1 * (|w| + 6 * A)) := by
  obtain ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩ := hq
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hyx := abs_yw_sub_le hs ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩ hx w
  set y := yw r x w
  have hsl : |r.2.p₁'.im - r.2.p₀'.im| ≤ 2 * A :=
    (abs_sub _ _).trans (by linarith [abs_im_le h0', abs_im_le h1'])
  have e3 : |affineFn r.2.p₀'.im r.2.p₁'.im y - affineFn r.2.p₀'.im r.2.p₁'.im x| ≤
      2 * A * |y - x| := by
    rw [abs_affineFn_sub]; gcongr
  have e4 : |(affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') y -
      (affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') x| ≤
      (2 * A + 2 * B * (16 : ℝ) ^ n) * |y - x| := by
    simp only [Pi.add_apply]
    rw [show affineFn r.2.p₀'.im r.2.p₁'.im y + r.2.f' y -
        (affineFn r.2.p₀'.im r.2.p₁'.im x + r.2.f' x) =
        (affineFn r.2.p₀'.im r.2.p₁'.im y - affineFn r.2.p₀'.im r.2.p₁'.im x) +
          (r.2.f' y - r.2.f' x) by ring]
    have := V_lip hf' hf'B y x
    calc _ ≤ _ + _ := abs_add_le _ _
      _ ≤ 2 * A * |y - x| + 2 * B * (16 : ℝ) ^ n * |y - x| := add_le_add e3 this
      _ = _ := by ring
  have h := abs_bvec_sub_le (affineFn r.2.p₀.im r.2.p₁.im x)
    ((affineFn r.2.p₀.im r.2.p₁.im + r.2.f) x) (affineFn r.2.p₀'.im r.2.p₁'.im y)
    ((affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') y) (affineFn r.2.p₀.im r.2.p₁.im x)
    ((affineFn r.2.p₀.im r.2.p₁.im + r.2.f) x) (affineFn r.2.p₀'.im r.2.p₁'.im x)
    ((affineFn r.2.p₀'.im r.2.p₁'.im + r.2.f') x) k
  simp only [sub_self, abs_zero, zero_add] at h
  have hnn : 0 ≤ |y - x| := abs_nonneg _
  calc |bb r x w k - bb0 r x k| ≤ _ := h
    _ ≤ 2 * A * |y - x| + (2 * A + 2 * B * (16 : ℝ) ^ n) * |y - x| := add_le_add e3 e4
    _ = (4 * A + 2 * B * (16 : ℝ) ^ n) * |y - x| := by ring
    _ ≤ _ := by gcongr

lemma ww0_le {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (hsm : 4 * A * r.1 ≤ x / 2) : ww0 r x ≤ (-x / 2) * r.1⁻¹ := by
  obtain ⟨-, -, -, -, h0, h1, h0', -⟩ := hq
  have hδ := hs.pos
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hr0 := abs_re_le h0
  have hr0' := abs_re_le h0'
  have hr1 := abs_re_le (show ‖r.2.p₁ - r.2.p₀‖ ≤ 2 * A from (norm_sub_le _ _).trans (by linarith))
  have hb : be r - Aff r.1 r.2.p₀ r.2.p₁ x ≤ -x / 2 := by
    unfold be Aff
    have a1 : r.1 * r.2.p₀'.re ≤ r.1 * A := by
      gcongr; exact (le_abs_self _).trans hr0'
    have a2 : -(r.1 * r.2.p₀.re) ≤ r.1 * A := by
      rw [← mul_neg]; gcongr; exact (neg_le_abs _).trans hr0
    have a3 : -(x * (r.1 * (r.2.p₁ - r.2.p₀).re)) ≤ r.1 * (2 * A) := by
      have h := neg_abs_le (x * (r.1 * (r.2.p₁ - r.2.p₀).re))
      have h2 : |x * (r.1 * (r.2.p₁ - r.2.p₀).re)| ≤ 1 * (r.1 * (2 * A)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx.1, abs_of_pos hδ]
        gcongr
        exact hx.2
      linarith
    nlinarith
  unfold ww0
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (inv_nonneg.2 hδ.le)

lemma ww1_ge {r : ℝ × Prm} (hs : Small n B A r.1) (hq : r.2 ∈ Kset n B A) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (hsm : 6 * A * r.1 ≤ (1 - x) / 2) :
    ((1 - x) / 2) * r.1⁻¹ ≤ ww1 r x := by
  obtain ⟨-, -, -, -, h0, h1, h0', h1'⟩ := hq
  have hδ := hs.pos
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hr0 := abs_re_le h0
  have hr0' := abs_re_le h0'
  have hr1 := abs_re_le (show ‖r.2.p₁ - r.2.p₀‖ ≤ 2 * A from (norm_sub_le _ _).trans (by linarith))
  have hr1' := abs_re_le (show ‖r.2.p₁' - r.2.p₀'‖ ≤ 2 * A from
    (norm_sub_le _ _).trans (by linarith))
  have hb : (1 - x) / 2 ≤ al r + be r - Aff r.1 r.2.p₀ r.2.p₁ x := by
    unfold al be Aff
    have a1 : -(r.1 * A * 2) ≤ r.1 * (r.2.p₁' - r.2.p₀').re := by
      have := neg_abs_le ((r.2.p₁' - r.2.p₀').re)
      nlinarith
    have a2 : -(r.1 * A) ≤ r.1 * r.2.p₀'.re := by
      have := neg_abs_le (r.2.p₀'.re); nlinarith
    have a3 : -(r.1 * A) ≤ -(r.1 * r.2.p₀.re) := by
      have := le_abs_self (r.2.p₀.re); nlinarith
    have a4 : -(r.1 * (2 * A)) ≤ -(x * (r.1 * (r.2.p₁ - r.2.p₀).re)) := by
      have h := le_abs_self (x * (r.1 * (r.2.p₁ - r.2.p₀).re))
      have h2 : |x * (r.1 * (r.2.p₁ - r.2.p₀).re)| ≤ 1 * (r.1 * (2 * A)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx.1, abs_of_pos hδ]
        gcongr
        exact hx.2
      linarith
    nlinarith
  unfold ww1
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (inv_nonneg.2 hδ.le)

/-- **Clause 1, main term.**  Uniformly on the compact parameter set, the displaced-graph
covariance divided by `δ` converges to `Cov(Z_{f+g} - Z_g, Z_{f'+g'} - Z_{g'})`. -/
theorem clause1_main (n : ℕ) (B A : ℝ) :
    Tendsto (fun r : ℝ × Prm => r.1⁻¹ * mainCov n r.1 r.2 - limCov r.2)
      (𝓝[>] (0:ℝ) ×ˢ 𝓟 (Kset n B A)) (𝓝 0) := by
  set l := 𝓝[>] (0:ℝ) ×ˢ 𝓟 (Kset n B A) with hl
  have hK : ∀ᶠ r in l, r.2 ∈ Kset n B A :=
    Filter.eventually_prod_principal_iff.2 (Eventually.of_forall fun δ q hq => hq)
  have hsm : ∀ᶠ r in l, Small n B A r.1 := tendsto_fst.eventually (eventually_small n B A)
  have hδ0 : Tendsto (fun r : ℝ × Prm => r.1) l (𝓝 0) :=
    (tendsto_fst (f := 𝓝[>] (0:ℝ)) (g := 𝓟 (Kset n B A))).mono_right nhdsWithin_le_nhds
  have hinv : Tendsto (fun r : ℝ × Prm => r.1⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp tendsto_fst
  -- hypotheses of the dominated convergence
  have hmeas : ∀ᶠ r in l, (∀ k, Measurable (fun p : ℝ × ℝ => bb r p.1 p.2 k)) ∧
      (∀ k, Measurable (fun x => bb0 r x k)) ∧ Measurable (ww0 r) ∧ Measurable (ww1 r) := by
    filter_upwards [hK] with r hr
    have hfc := Subadd.V_continuous hr.1
    have hf'c := Subadd.V_continuous hr.2.1
    refine ⟨fun k => (cont_bb r hfc hf'c k).measurable,
      fun k => (cont_bb0 r hfc hf'c k).measurable, ?_, ?_⟩
    · exact (by unfold ww0 Aff; fun_prop : Continuous (ww0 r)).measurable
    · exact (by unfold ww1 Aff; fun_prop : Continuous (ww1 r)).measurable
  have hle : ∀ᶠ r in l, ∀ x ∈ Icc (0:ℝ) 1, ww0 r x ≤ ww1 r x := by
    filter_upwards [hsm, hK] with r hs hq x _
    unfold ww0 ww1
    apply div_le_div_of_nonneg_right _ hs.pos.le
    linarith [al_ge hs hq]
  have hbB : ∀ᶠ r in l, ∀ x ∈ Icc (0:ℝ) 1,
      (∀ w ∈ Icc (ww0 r x) (ww1 r x), ∀ k, |bb r x w k| ≤ 2 * (A + B)) ∧
        ∀ k, |bb0 r x k| ≤ 2 * (A + B) := by
    filter_upwards [hsm, hK] with r hs hq x hx
    have hq' := hq
    obtain ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩ := hq
    have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
    refine ⟨fun w hw k => ?_, fun k => ?_⟩
    · have hy := yw_mem hs hq' hw
      exact abs_bvec_le (bound_g hB h0 h1 x hx) (bound_gf hfB h0 h1 x hx)
        (bound_g hB h0' h1' _ hy) (bound_gf hf'B h0' h1' _ hy) k
    · exact abs_bvec_le (bound_g hB h0 h1 x hx) (bound_gf hfB h0 h1 x hx)
        (bound_g hB h0' h1' x hx) (bound_gf hf'B h0' h1' x hx) k
  have hconv : ∀ x ∈ Ioo (0:ℝ) 1, ∀ w k,
      Tendsto (fun r => bb r x w k - bb0 r x k) l (𝓝 0) := by
    intro x hx w k
    have hx' : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
    have hlim : Tendsto (fun r : ℝ × Prm =>
        (4 * A + 2 * B * (16 : ℝ) ^ n) * (2 * r.1 * (|w| + 6 * A))) l (𝓝 0) := by
      have := ((hδ0.const_mul 2).mul_const (|w| + 6 * A)).const_mul
        (4 * A + 2 * B * (16 : ℝ) ^ n)
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hsm, hK] with r hs hq
    rw [Real.norm_eq_abs]
    exact abs_bb_sub_le hs hq hx' w k
  have hw0 : ∀ x ∈ Ioo (0:ℝ) 1, Tendsto (fun r => ww0 r x) l atBot := by
    intro x hx
    have hsmall : ∀ᶠ r in l, 4 * A * r.1 ≤ x / 2 := by
      have := hδ0.const_mul (4 * A)
      rw [mul_zero] at this
      exact this.eventually (eventually_le_nhds (by linarith [hx.1]))
    refine tendsto_atBot_mono' l ?_
      (Tendsto.const_mul_atTop_of_neg (show -x / 2 < 0 by linarith [hx.1]) hinv)
    filter_upwards [hsm, hK, hsmall] with r hs hq h
    exact ww0_le hs hq (Ioo_subset_Icc_self hx) h
  have hw1 : ∀ x ∈ Ioo (0:ℝ) 1, Tendsto (fun r => ww1 r x) l atTop := by
    intro x hx
    have hsmall : ∀ᶠ r in l, 6 * A * r.1 ≤ (1 - x) / 2 := by
      have := hδ0.const_mul (6 * A)
      rw [mul_zero] at this
      exact this.eventually (eventually_le_nhds (by linarith [hx.2]))
    refine tendsto_atTop_mono' l ?_
      (Tendsto.const_mul_atTop (show 0 < (1 - x) / 2 by linarith [hx.2]) hinv)
    filter_upwards [hsm, hK, hsmall] with r hs hq h
    exact ww1_ge hs hq (Ioo_subset_Icc_self hx) h
  obtain ⟨hII, hT⟩ := core_tendsto σ4 (2 * (A + B)) bb bb0 ww0 ww1 hmeas hle hbB hconv hw0 hw1
  -- the bound
  have hbound : ∀ᶠ r in l, |r.1⁻¹ * mainCov n r.1 r.2 - limCov r.2| ≤
      2 * |∫ x in (0:ℝ)..1, ((∫ w in ww0 r x..ww1 r x, Kf σ4 w (bb r x w)) -
        2 * π * ∑ k, σ4 k * |bb0 r x k|)| + 24 * π * A * (A + B) * r.1 := by
    filter_upwards [hsm, hK, hII] with r hs hq hIIr
    have hq' := hq
    obtain ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩ := hq
    have hA : 0 ≤ A := (norm_nonneg _).trans h0
    have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
    have hδ := hs.pos
    have hfc := Subadd.V_continuous hf
    have hf'c := Subadd.V_continuous hf'
    have hα := al_ge hs hq'
    have hα0 : 0 < al r := lt_of_lt_of_le (by norm_num) hα
    rw [mainCov_repr hs hq', limCov_eq r.2 hfc hf'c]
    set J := ∫ x in (0:ℝ)..1, ((∫ w in ww0 r x..ww1 r x, Kf σ4 w (bb r x w)) -
        2 * π * ∑ k, σ4 k * |bb0 r x k|) with hJ
    set Z := ∫ x in (0:ℝ)..1, Bq r.2 x with hZ
    have hBqc := continuous_Bq r.2 hfc hf'c
    have hsplit : ∫ x in (0:ℝ)..1, ∫ w in ww0 r x..ww1 r x, Kf σ4 w (bb r x w) = J + Z := by
      rw [hJ, hZ, ← intervalIntegral.integral_add hIIr (hBqc.intervalIntegrable 0 1)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [Bq_eq r x]
      ring
    rw [hsplit]
    have hZb : |Z| ≤ 8 * π * (A + B) := by
      rw [hZ, ← Real.norm_eq_abs]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (f := Bq r.2) (C := 8 * π * (A + B)) (fun x hx => by
          rw [uIoc_of_le zero_le_one] at hx
          have hx' := Ioc_subset_Icc_self hx
          rw [Real.norm_eq_abs, Bq_eq r x, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
          calc 2 * π * |∑ k, σ4 k * (|bb0 r x k|)| ≤ 2 * π * ∑ k, |σ4 k * (|bb0 r x k|)| := by
                gcongr; exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ 2 * π * ∑ k : Fin 4, (1 / 2) * (2 * (A + B)) := by
                gcongr with k
                rw [abs_mul, abs_abs]
                have hbk := abs_bvec_le (bound_g hB h0 h1 x hx') (bound_gf hfB h0 h1 x hx')
                  (bound_g hB h0' h1' x hx') (bound_gf hf'B h0' h1' x hx') k
                have hσ : |σ4 k| ≤ 1 / 2 := by
                  fin_cases k <;> simp [σ4, abs_div]
                exact mul_le_mul hσ hbk (abs_nonneg _) (by norm_num)
            _ = 8 * π * (A + B) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring)
      rw [sub_zero, abs_one, mul_one] at this
      exact this
    have hal : |1 / al r - 1| ≤ 3 * A * r.1 := by
      rw [show 1 / al r - 1 = (1 - al r) / al r by rw [sub_div, div_self hα0.ne'],
        show 1 - al r = -(r.1 * (r.2.p₁' - r.2.p₀').re) by unfold al; ring,
        abs_div, abs_neg, abs_of_pos hα0, abs_mul, abs_of_pos hδ, div_le_iff₀ hα0]
      have h2 := abs_re_le (show ‖r.2.p₁' - r.2.p₀'‖ ≤ 2 * A from
        (norm_sub_le _ _).trans (by linarith))
      have : r.1 * |(r.2.p₁' - r.2.p₀').re| ≤ r.1 * (2 * A) := by gcongr
      nlinarith [mul_nonneg hA hδ.le]
    have hinvα : |1 / al r| ≤ 2 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ hα0]; linarith
    calc |1 / al r * (J + Z) - Z| = |1 / al r * J + (1 / al r - 1) * Z| := by congr 1; ring
      _ ≤ |1 / al r * J| + |(1 / al r - 1) * Z| := abs_add_le _ _
      _ = |1 / al r| * |J| + |1 / al r - 1| * |Z| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * |J| + (3 * A * r.1) * (8 * π * (A + B)) := by
          gcongr
      _ = 2 * |J| + 24 * π * A * (A + B) * r.1 := by ring
  have hlim : Tendsto (fun r : ℝ × Prm => 2 * |∫ x in (0:ℝ)..1,
      ((∫ w in ww0 r x..ww1 r x, Kf σ4 w (bb r x w)) - 2 * π * ∑ k, σ4 k * |bb0 r x k|)| +
      24 * π * A * (A + B) * r.1) l (𝓝 0) := by
    have := (hT.abs.const_mul 2).add (hδ0.const_mul (24 * π * A * (A + B)))
    simpa using this
  exact squeeze_zero_norm' (by
    filter_upwards [hbound] with r hr
    rw [Real.norm_eq_abs]; exact hr) hlim

end Main3

/-! ## The theorem -/

/-- **Node `L32c` (Lemma 3.2, third parametrization, and (3.3))**, from Lemma 3.1. -/
theorem constrainedCovLimit_of (hL31 : TwoScaleCovBound) : ConstrainedCovLimit := by
  intro n B A
  obtain ⟨Lmod, hLmod⟩ := clause3_bound hL31 n B A
  obtain ⟨K₁, hK₁⟩ := clause1_err hL31 n B A
  refine ⟨Lmod, fun θ hθ => ?_⟩
  have hmain := clause1_main n B A
  have h1 : ∀ᶠ r in 𝓝[>] (0:ℝ) ×ˢ 𝓟 (Kset n B A),
      |r.1⁻¹ * mainCov n r.1 r.2 - limCov r.2| < θ / 2 := by
    have := (hmain.abs).eventually (gt_mem_nhds (show |(0:ℝ)| < θ / 2 by
      rw [abs_zero]; linarith))
    exact this
  rw [Filter.eventually_prod_principal_iff] at h1
  have h2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), |K₁| * (δ + Real.sqrt δ) < θ / 2 := by
    have ht : Tendsto (fun δ : ℝ => |K₁| * (δ + Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      have hs : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      simpa using (h0.add hs).const_mul |K₁|
    exact ht.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ δ in 𝓝[>] (0:ℝ), 3 * (2 * B * (16 : ℝ) ^ n) ^ 4 * δ ^ 2 ≤ θ := by
    have ht : Tendsto (fun δ : ℝ => 3 * (2 * B * (16 : ℝ) ^ n) ^ 4 * δ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (h0.pow 2).const_mul (3 * (2 * B * (16 : ℝ) ^ n) ^ 4)
    exact ht.eventually (ge_mem_nhds hθ)
  filter_upwards [eventually_small n B A, h1, h2, h3] with δ hs hδ1 hδ2 hδ3
  intro f hf f' hf' p₀ p₁ p₀' p₁' hfB hf'B h0 h1 h0' h1'
  have hδ := hs.pos
  have hq : (⟨f, f', p₀, p₁, p₀', p₁'⟩ : Prm) ∈ Kset n B A :=
    ⟨hf, hf', hfB, hf'B, h0, h1, h0', h1'⟩
  refine ⟨?_, ?_, hLmod δ hs f f' p₀ p₁ p₀' p₁' hf hf' hfB hf'B h0 h1 h0' h1'⟩
  · -- clause 1
    have hm := hδ1 _ hq
    simp only [mainCov, limCov] at hm
    have he := hK₁ δ hs f f' p₀ p₁ p₀' p₁' hf hf' hfB hf'B h0 h1 h0' h1'
    set L := (cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).logCov
      (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁'))
    set Lm := ((chordM (16 ^ n) (xp δ p₀) (yp δ p₁)).sub
          (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f p₀ p₁))).logCov
        ((chordM (16 ^ n) (xp δ p₀') (yp δ p₁')).sub
          (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f' p₀' p₁')))
    have hsq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
    have hdiff : |δ⁻¹ * L - δ⁻¹ * Lm| ≤ |K₁| * (δ + Real.sqrt δ) := by
      rw [← mul_sub, abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ]
      calc |L - Lm| ≤ K₁ * (δ ^ 2 + δ * Real.sqrt δ) := he
        _ ≤ |K₁| * (δ ^ 2 + δ * Real.sqrt δ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = δ * (|K₁| * (δ + Real.sqrt δ)) := by ring
    calc |δ⁻¹ * L - zDiffCov f (affineFn p₀.im p₁.im) f' (affineFn p₀'.im p₁'.im)|
        ≤ |δ⁻¹ * L - δ⁻¹ * Lm| + |δ⁻¹ * Lm - zDiffCov f (affineFn p₀.im p₁.im) f'
            (affineFn p₀'.im p₁'.im)| := abs_sub_le _ _ _
      _ ≤ θ / 2 + θ / 2 := by linarith
      _ = θ := by ring
  · -- clause 2
    have hne := xp_ne_yp hs h0 h1
    have hlen : polyLen (constrCfg (16 ^ n) δ f p₀ p₁).2 / ‖(1 + (δ : ℂ) * p₁) - (δ : ℂ) * p₀‖ =
        uLen (16 ^ n) δ f := by
      have e := polyLen_constrPoly (16 ^ n) δ f hne
      simp only [constrCfg]
      rw [show (δ : ℂ) * p₀ = xp δ p₀ from rfl, show 1 + (δ : ℂ) * p₁ = yp δ p₁ from rfl, e]
      have : ‖yp δ p₁ - xp δ p₀‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hne))
      exact mul_div_cancel_left₀ _ this
    rw [hlen]
    obtain ⟨-, -, h⟩ := uLen_energy_est n hf hfB hδ hs.eta_le'
    exact h.trans hδ3

end LQGDimension.ConstrCov

namespace LQGDimension

/-- **Node `L32c` (Lemma 3.2, third parametrization, and (3.3)).** -/
theorem constrainedCovLimit (hL31 : Blueprint.Draft.TwoScaleCovBound) :
    Blueprint.Draft.ConstrainedCovLimit :=
  ConstrCov.constrainedCovLimit_of hL31

end LQGDimension
