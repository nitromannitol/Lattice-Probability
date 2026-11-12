/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux1

/-!
# Lemma 5.1, auxiliary file 2: point potentials of graph measures

For `f, g ∈ V n` let `gdiff M δ f g = μ_{δ,f} - μ_{δ,g}` (graph measures, weight `1/M` per edge),
and for a point `Q = x + i δ Y` (`hpt δ x Y`):

* `pot_eq`: the log potential `⟨log|Q - ·|⁻¹, μ_{δ,f} - μ_{δ,g}⟩` equals
  `δ ∫ (lk (Y - g(x+δu)) u - lk (Y - f(x+δu)) u) / 2 du` (substitution `y = x + δ u`);
* `abs_pot_sub_le`, `tendsto_eta`: **(5.5)** — uniformly in `x ∈ ℝ` and `|Y| ≤ Y₀`,
  `δ⁻¹ pot → π (|Y - g x| - |Y - f x|)`, with the explicit error
  `η(δ) = ∫ min (L δ) (lk B u) du → 0`;
* `gaussPair_pt_graph_le`: small scales, `0 ≤ gaussPair t δ_Q μ_{δ,f} ≤ 2√π t`;
* `abs_gaussPair_vdip_le`: large scales, for a *vertical* dipole `Q, Q'` (same real part),
  `|gaussPair t (δ_Q - δ_Q') (μ_{δ,f} - μ_{δ,g})| ≤ 2√π δ² |Y - Y'| W / t`
  (mixed second difference of the Gaussian kernel).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft HeatKernel

/-! ## Lipschitz bound for `V n` (copied from `ConstrainedCovGeom`, which is not yet built) -/

/-- `f` is `L`-Lipschitz on `s`. -/
def LipOnL (f : ℝ → ℝ) (L : ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * |x - y|

lemma lipOnL_union {f : ℝ → ℝ} {L : ℝ} (_hL : 0 ≤ L) {s t : Set ℝ} {b : ℝ}
    (hs : ∀ x ∈ s, x ≤ b) (ht : ∀ x ∈ t, b ≤ x) (hbs : b ∈ s) (hbt : b ∈ t)
    (h1 : LipOnL f L s) (h2 : LipOnL f L t) : LipOnL f L (s ∪ t) := by
  have mixed : ∀ x ∈ s, ∀ y ∈ t, |f x - f y| ≤ L * |x - y| := by
    intro x hx y hy
    have e1 := h1 x hx b hbs
    have e2 := h2 b hbt y hy
    have hxb := hs x hx
    have hby := ht y hy
    calc |f x - f y| ≤ |f x - f b| + |f b - f y| := abs_sub_le _ _ _
      _ ≤ L * |x - b| + L * |b - y| := add_le_add e1 e2
      _ = L * |x - y| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith)]
          ring
  intro x hx y hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact h1 x hx y hy
  · exact mixed x hx y hy
  · rw [abs_sub_comm, abs_sub_comm x]; exact mixed y hy x hx
  · exact h2 x hx y hy

/-- Functions of `V n` bounded by `B` are `2 B 16ⁿ`-Lipschitz on `ℝ`. -/
lemma V_lipL {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (x y : ℝ) :
    |f x - f y| ≤ 2 * B * (16 : ℝ) ^ n * |x - y| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hN : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
  set L := 2 * B * (16 : ℝ) ^ n with hLdef
  have hL : 0 ≤ L := by positivity
  have hpiece : ∀ k : ℕ, k < 16 ^ n →
      LipOnL f L (Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n)) := by
    intro k hk u hu v hv
    rw [Subadd.V_piece hf hk hu, Subadd.V_piece hf hk hv]
    have hd := abs_sub (f (((k : ℝ) + 1) / 16 ^ n)) (f ((k : ℝ) / 16 ^ n))
    have h1 := hfB (((k : ℝ) + 1) / 16 ^ n)
    have h2 := hfB ((k : ℝ) / 16 ^ n)
    rw [show f ((k : ℝ) / 16 ^ n) + (16 ^ n * u - k) * (f (((k : ℝ) + 1) / 16 ^ n) -
        f ((k : ℝ) / 16 ^ n)) - (f ((k : ℝ) / 16 ^ n) + (16 ^ n * v - k) *
        (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n))) =
        (16 : ℝ) ^ n * (u - v) * (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)) by ring,
      abs_mul, abs_mul, abs_of_pos hN]
    calc (16 : ℝ) ^ n * |u - v| * |f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)|
        ≤ (16 : ℝ) ^ n * |u - v| * (2 * B) := by gcongr; linarith
      _ = L * |u - v| := by rw [hLdef]; ring
  have hind : ∀ k : ℕ, k ≤ 16 ^ n → LipOnL f L (Icc 0 ((k : ℝ) / 16 ^ n)) := by
    intro k
    induction k with
    | zero =>
      intro _ u hu v hv
      simp only [Nat.cast_zero, zero_div, Icc_self, mem_singleton_iff] at hu hv
      subst hu; subst hv; simp
    | succ k ih =>
      intro hk
      have h1 : (0 : ℝ) ≤ (k : ℝ) / 16 ^ n := by positivity
      have h2 : (k : ℝ) / 16 ^ n ≤ ((k : ℝ) + 1) / 16 ^ n := by gcongr; linarith
      rw [Nat.cast_succ, ← Icc_union_Icc_eq_Icc h1 h2]
      exact lipOnL_union hL (fun u hu => hu.2) (fun u hu => hu.1) ⟨h1, le_rfl⟩ ⟨le_rfl, h2⟩
        (ih (by omega)) (hpiece k (by omega))
  have h01 : LipOnL f L (Icc 0 1) := by
    have := hind (16 ^ n) le_rfl
    rwa [Nat.cast_pow, Nat.cast_ofNat, div_self hN.ne'] at this
  have hIic : LipOnL f L (Iic 0) := by
    intro u hu v hv
    rw [Subadd.V_zero_of_le hf (Or.inl hu), Subadd.V_zero_of_le hf (Or.inl hv)]
    simp only [sub_self, abs_zero]; positivity
  have hIci : LipOnL f L (Ici 1) := by
    intro u hu v hv
    rw [Subadd.V_zero_of_le hf (Or.inr hu), Subadd.V_zero_of_le hf (Or.inr hv)]
    simp only [sub_self, abs_zero]; positivity
  have h1 := lipOnL_union (s := Iic 0) (t := Icc 0 1) (b := 0) hL (fun u hu => hu)
    (fun u hu => hu.1) (mem_Iic.2 le_rfl) ⟨le_rfl, zero_le_one⟩ hIic h01
  rw [Iic_union_Icc_eq_Iic zero_le_one] at h1
  have h2 := lipOnL_union (s := Iic 1) (t := Ici 1) (b := 1) hL (fun u hu => hu)
    (fun u hu => hu) (mem_Iic.2 le_rfl) (mem_Ici.2 le_rfl) h1 hIci
  rw [Iic_union_Ici] at h2
  exact h2 x (mem_univ _) y (mem_univ _)

/-! ## Point against a mesh-affine curve -/

lemma dsum_pt_pc {M : ℕ} (hM : 0 < M) {P : ℝ → ℂ} (hP : GraphCov.MeshAff M P) (κ : ℂ → ℝ)
    (Q : ℂ) (hint : IntervalIntegrable (fun y => κ (Q - P y)) volume 0 1) :
    dsum (fun e e' => ∫ s in (0:ℝ)..1, ∫ s' in (0:ℝ)..1,
        κ ((e.1 + (s : ℂ) * (e.2 - e.1)) - (e'.1 + (s' : ℂ) * (e'.2 - e'.1)))) (pt Q)
        (GraphCov.pc M P) = ∫ y in (0:ℝ)..1, κ (Q - P y) := by
  unfold dsum pt GraphCov.pc
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map,
    one_mul]
  rw [GraphCov.list_sum_map_range, ← GraphCov.sum_pieces hM _ hint]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Function.comp_apply, sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_const, sub_zero, one_smul,
    ← GraphCov.piece_integral hM (fun y => κ (Q - P y)) i]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  rw [hP i (Finset.mem_range.1 hi) s hs]

/-- The graph difference combination `μ_{δ,f} - μ_{δ,g}`. -/
def gdiff (M : ℕ) (δ : ℝ) (f g : ℝ → ℝ) : SegComb := (graphComb M δ f).sub (graphComb M δ g)

/-- The point `x + i δ Y`. -/
def hpt (δ x Y : ℝ) : ℂ := (x : ℂ) + ((δ * Y : ℝ) : ℂ) * Complex.I

lemma hpt_sub_gc (δ x Y y : ℝ) (f : ℝ → ℝ) :
    hpt δ x Y - GraphCov.gc δ f y = ((x - y : ℝ) : ℂ) + ((δ * (Y - f y) : ℝ) : ℂ) * Complex.I := by
  unfold hpt GraphCov.gc; push_cast; ring

lemma continuous_gc {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) :
    Continuous (GraphCov.gc δ f) := by
  have := Subadd.V_continuous hf
  unfold GraphCov.gc; fun_prop

/-! ## The log potential -/

lemma intervalIntegrable_neglog {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) (Q : ℂ) :
    IntervalIntegrable (fun y => -Real.log ‖Q - GraphCov.gc δ f y‖) volume 0 1 := by
  obtain ⟨B, hB⟩ := GraphCov.exists_bound_V hf
  have hd : GraphCov.LogDom (fun (_ : ℝ) (y : ℝ) =>
      -Real.log ‖(fun _ : ℝ => Q) 0 - GraphCov.gc δ f y‖) := by
    refine GraphCov.logDom_curve (P := fun _ : ℝ => Q) (Q := GraphCov.gc δ f) continuous_const
      (continuous_gc hf δ) (κ := 1) one_pos (fun _ => Q.re) (K := |Q.re|)
      (Cu := ‖Q‖ + 1 + |δ| * |B|) (fun _ _ => le_rfl) ?_ ?_
    · intro x _ y _
      rw [one_mul, abs_sub_comm]
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      simp [GraphCov.gc]
    · intro x _ y hy
      calc ‖Q - GraphCov.gc δ f y‖ ≤ ‖Q‖ + ‖GraphCov.gc δ f y‖ := norm_sub_le _ _
        _ ≤ ‖Q‖ + (1 + |δ| * |B|) := by
          gcongr
          unfold GraphCov.gc
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
          exact add_le_add hy.2
            (mul_le_mul_of_nonneg_left ((hB y).trans (le_abs_self B)) (abs_nonneg δ))
        _ = ‖Q‖ + 1 + |δ| * |B| := by ring
  exact hd.ii (x := 0) ⟨le_rfl, zero_le_one⟩

lemma logCov_pt_graph {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) (Q : ℂ) :
    (pt Q).logCov (graphComb (16 ^ n) δ f) =
      ∫ y in (0:ℝ)..1, -Real.log ‖Q - GraphCov.gc δ f y‖ := by
  rw [logCov_eq_dsum, GraphCov.graphComb_eq]
  exact dsum_pt_pc (by positivity) (GraphCov.meshAff_gc hf δ) (fun z => -Real.log ‖z‖) Q
    (intervalIntegrable_neglog hf δ Q)

lemma hpt_sub_gc_shift (δ x Y u : ℝ) (f : ℝ → ℝ) :
    hpt δ x Y - GraphCov.gc δ f (x + δ * u) =
      (((-(δ * u)) : ℝ) : ℂ) + ((δ * (Y - f (x + δ * u)) : ℝ) : ℂ) * Complex.I := by
  unfold hpt GraphCov.gc; push_cast; ring

/-- **The log potential of `μ_{δ,f} - μ_{δ,g}` at `x + iδY`, after the substitution
`y = x + δu`.** -/
lemma pot_eq {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {δ : ℝ} (hδ : 0 < δ)
    (x Y : ℝ) :
    (pt (hpt δ x Y)).logCov (gdiff (16 ^ n) δ f g) =
      δ * ∫ u, (GraphCov.lk (Y - g (x + δ * u)) u - GraphCov.lk (Y - f (x + δ * u)) u) / 2 := by
  set Q := hpt δ x Y with hQ
  set H : ℝ → ℝ := fun y => -Real.log ‖Q - GraphCov.gc δ f y‖ +
    Real.log ‖Q - GraphCov.gc δ g y‖ with hH
  have h1 : (pt Q).logCov (gdiff (16 ^ n) δ f g) = ∫ y in (0:ℝ)..1, H y := by
    rw [gdiff, logCov_eq_dsum, dsum_sub_right, ← logCov_eq_dsum, ← logCov_eq_dsum,
      logCov_pt_graph hf, logCov_pt_graph hg,
      ← intervalIntegral.integral_sub (intervalIntegrable_neglog hf δ Q)
        (intervalIntegrable_neglog hg δ Q)]
    congr 1; funext y; simp only [hH]; ring
  have hzero : ∀ y, y ∉ Ioc (0:ℝ) 1 → H y = 0 := by
    intro y hy
    have hy' : y ≤ 0 ∨ 1 ≤ y := by
      by_contra hc
      push Not at hc
      exact hy ⟨hc.1, hc.2.le⟩
    have hfy := Subadd.V_zero_of_le hf hy'
    have hgy := Subadd.V_zero_of_le hg hy'
    have e : GraphCov.gc δ f y = GraphCov.gc δ g y := by
      unfold GraphCov.gc; rw [hfy, hgy]
    show -Real.log ‖Q - GraphCov.gc δ f y‖ + Real.log ‖Q - GraphCov.gc δ g y‖ = 0
    rw [e]; ring
  have h2 : ∫ y in (0:ℝ)..1, H y = ∫ y, H y := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have h3 : ∫ y, H y = δ * ∫ u, H (x + δ * u) := by
    have e1 := Measure.integral_comp_mul_left (fun v => H (x + v)) δ
    have e2 : ∫ v, H (x + v) = ∫ y, H y := integral_add_left_eq_self H x
    rw [e1, e2, abs_of_pos (inv_pos.2 hδ), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hδ.ne',
      one_mul]
  rw [h1, h2, h3]
  congr 1
  refine integral_congr_ae ((GraphCov.ae_ne_real 0).mono fun u hu => ?_)
  simp only [hH]
  rw [hQ, hpt_sub_gc_shift, hpt_sub_gc_shift]
  have ef := GraphCov.neglog_norm_eq hδ hu (t := Y - f (x + δ * u))
  have eg := GraphCov.neglog_norm_eq hδ hu (t := Y - g (x + δ * u))
  linarith

/-! ## The uniform convergence (5.5) -/

lemma integrable_lk_comp {c : ℝ → ℝ} (hc : Measurable c) {B : ℝ} (hB : ∀ u, |c u| ≤ B) :
    Integrable (fun u => GraphCov.lk (c u) u) := by
  refine Integrable.mono' (GraphCov.integrable_lk B) ?_ (ae_of_all _ fun u => ?_)
  · exact (GraphCov.measurable_lk.comp (hc.prodMk measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (GraphCov.lk_nonneg _ _)]
    exact GraphCov.lk_mono ((hB u).trans (le_abs_self B)) u

lemma measurable_min_lk (L B : ℝ) : Measurable fun u => min L (GraphCov.lk B u) :=
  measurable_const.min (GraphCov.measurable_lk.comp (measurable_const.prodMk measurable_id))

lemma integrable_min_lk {L : ℝ} (hL : 0 ≤ L) (B : ℝ) :
    Integrable fun u => min L (GraphCov.lk B u) := by
  refine Integrable.mono' (GraphCov.integrable_lk B) (measurable_min_lk L B).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hL (GraphCov.lk_nonneg _ _))]
  exact min_le_right _ _

/-- One profile: `|lk (Y - h(x+δu)) u - lk (Y - h x) u| ≤ min (L δ) (lk B u)`. -/
lemma abs_lk_shift_le {h : ℝ → ℝ} {L K : ℝ} (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hK : ∀ x, |h x| ≤ K) {δ : ℝ} (hδ : 0 ≤ δ) (x Y : ℝ) {Y₀ : ℝ} (hY : |Y| ≤ Y₀) {u : ℝ}
    (hu : u ≠ 0) :
    |GraphCov.lk (Y - h (x + δ * u)) u - GraphCov.lk (Y - h x) u| ≤
      min (L * δ) (GraphCov.lk (Y₀ + K) u) := by
  refine le_min ?_ ?_
  · refine (GraphCov.lk_lip hu _ _).trans ?_
    have hau : 0 < |u| := abs_pos.2 hu
    rw [div_le_iff₀ hau, show Y - h (x + δ * u) - (Y - h x) = h x - h (x + δ * u) by ring]
    calc |h x - h (x + δ * u)| ≤ L * |x - (x + δ * u)| := hlip _ _
      _ = L * δ * |u| := by
        rw [show x - (x + δ * u) = -(δ * u) by ring, abs_neg, abs_mul, abs_of_nonneg hδ]; ring
  · have hb : ∀ z, GraphCov.lk (Y - h z) u ≤ GraphCov.lk (Y₀ + K) u := by
      intro z
      refine GraphCov.lk_mono ?_ u
      calc |Y - h z| ≤ |Y| + |h z| := abs_sub _ _
        _ ≤ Y₀ + K := add_le_add hY (hK z)
        _ ≤ |Y₀ + K| := le_abs_self _
    have h1 := hb (x + δ * u)
    have h2 := hb x
    have h3 := GraphCov.lk_nonneg (Y - h (x + δ * u)) u
    have h4 := GraphCov.lk_nonneg (Y - h x) u
    rw [abs_le]; constructor <;> linarith

lemma integral_lk_half_sub (a b : ℝ) :
    ∫ u, (GraphCov.lk a u - GraphCov.lk b u) / 2 = π * (|a| - |b|) := by
  rw [integral_div, integral_sub (GraphCov.integrable_lk a) (GraphCov.integrable_lk b),
    GraphCov.integral_lk, GraphCov.integral_lk]
  ring

/-- **(5.5), with an explicit uniform error.** -/
lemma abs_pot_sub_le {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {K : ℝ}
    (hfK : ∀ x, |f x| ≤ K) (hgK : ∀ x, |g x| ≤ K) {δ : ℝ} (hδ : 0 < δ) (x Y : ℝ) {Y₀ : ℝ}
    (hY : |Y| ≤ Y₀) :
    |(pt (hpt δ x Y)).logCov (gdiff (16 ^ n) δ f g) / δ - π * (|Y - g x| - |Y - f x|)| ≤
      ∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (Y₀ + K) u) := by
  set L : ℝ := 2 * K * (16 : ℝ) ^ n with hL
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hfK 0)
  have hL0 : 0 ≤ L := by positivity
  have hflip : ∀ x y, |f x - f y| ≤ L * |x - y| := fun x y => V_lipL hf hfK x y
  have hglip : ∀ x y, |g x - g y| ≤ L * |x - y| := fun x y => V_lipL hg hgK x y
  have hfc := Subadd.V_continuous hf
  have hgc := Subadd.V_continuous hg
  have hBd : ∀ (h : ℝ → ℝ), (∀ x, |h x| ≤ K) → ∀ z, |Y - h z| ≤ Y₀ + K := fun h hK z =>
    (abs_sub _ _).trans (add_le_add hY (hK z))
  have hmeas : ∀ h : ℝ → ℝ, Continuous h → Measurable fun u => Y - h (x + δ * u) := by
    intro h hh; exact (measurable_const.sub (hh.measurable.comp (by fun_prop)))
  have iA := integrable_lk_comp (hmeas g hgc) (fun u => hBd g hgK _)
  have iB := integrable_lk_comp (hmeas f hfc) (fun u => hBd f hfK _)
  have iC := GraphCov.integrable_lk (Y - g x)
  have iD := GraphCov.integrable_lk (Y - f x)
  have iAB : Integrable (fun u => (GraphCov.lk (Y - g (x + δ * u)) u -
      GraphCov.lk (Y - f (x + δ * u)) u) / 2) := (iA.sub iB).div_const 2
  have iCD : Integrable (fun u => (GraphCov.lk (Y - g x) u - GraphCov.lk (Y - f x) u) / 2) :=
    (iC.sub iD).div_const 2
  rw [pot_eq hf hg hδ, mul_div_cancel_left₀ _ hδ.ne', ← integral_lk_half_sub,
    ← integral_sub iAB iCD]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    (integrable_min_lk (by positivity) _) ((GraphCov.ae_ne_real 0).mono fun u hu => ?_)
  have e1 := abs_lk_shift_le hglip hgK hδ.le x Y hY hu
  have e2 := abs_lk_shift_le hflip hfK hδ.le x Y hY hu
  have : (GraphCov.lk (Y - g (x + δ * u)) u - GraphCov.lk (Y - f (x + δ * u)) u) / 2 -
      (GraphCov.lk (Y - g x) u - GraphCov.lk (Y - f x) u) / 2 =
      ((GraphCov.lk (Y - g (x + δ * u)) u - GraphCov.lk (Y - g x) u) -
        (GraphCov.lk (Y - f (x + δ * u)) u - GraphCov.lk (Y - f x) u)) / 2 := by ring
  simp only
  rw [this, abs_div, abs_two]
  have := abs_sub (GraphCov.lk (Y - g (x + δ * u)) u - GraphCov.lk (Y - g x) u)
    (GraphCov.lk (Y - f (x + δ * u)) u - GraphCov.lk (Y - f x) u)
  linarith

/-- The error of (5.5) tends to zero. -/
lemma tendsto_eta {L : ℝ} (hL : 0 ≤ L) (B : ℝ) :
    Tendsto (fun δ => ∫ u, min (L * δ) (GraphCov.lk B u)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun δ u => min (L * δ) (GraphCov.lk B u)) (f := fun _ => 0)
    (fun u => GraphCov.lk B u) ?_ ?_ (GraphCov.integrable_lk B) ?_
  · simpa using h
  · exact Eventually.of_forall fun δ => (measurable_min_lk _ B).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (mul_nonneg hL (le_of_lt hδ))
        (GraphCov.lk_nonneg _ _))]
      exact min_le_right _ _
  · refine ae_of_all _ fun u => ?_
    have h1 : Tendsto (fun δ : ℝ => L * δ) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => L * δ) (𝓝 0) (𝓝 (L * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := h1.min (tendsto_const_nhds (x := GraphCov.lk B u))
    rwa [min_eq_left (GraphCov.lk_nonneg B u)] at h2

/-! ## The Gaussian kernel along a graph -/

/-- `E_t(s) = exp(-s²/(4t²))`. -/
def ek (t s : ℝ) : ℝ := Real.exp (-s ^ 2 / (4 * t ^ 2))

lemma ek_pos (t s : ℝ) : 0 < ek t s := Real.exp_pos _

lemma ek_le_one (t s : ℝ) : ek t s ≤ 1 := by
  unfold ek
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

lemma exp_norm_ri (t a b : ℝ) :
    Real.exp (-‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 / (4 * t ^ 2)) = ek t a * ek t b := by
  unfold ek
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity), ← Real.exp_add]
  congr 1; ring

lemma gauss_hk_graph (t δ x Y y : ℝ) (f : ℝ → ℝ) :
    Real.exp (-‖hpt δ x Y - GraphCov.gc δ f y‖ ^ 2 / (4 * t ^ 2)) =
      ek t (x - y) * ek t (δ * (Y - f y)) := by
  rw [hpt_sub_gc, exp_norm_ri]

lemma gaussPair_pt_graph {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (t δ : ℝ) (Q : ℂ) :
    gaussPair t (pt Q) (graphComb (16 ^ n) δ f) =
      ∫ y in (0:ℝ)..1, Real.exp (-‖Q - GraphCov.gc δ f y‖ ^ 2 / (4 * t ^ 2)) := by
  rw [gaussPair_eq_dsum, GraphCov.graphComb_eq]
  have hc : Continuous fun y => Real.exp (-‖Q - GraphCov.gc δ f y‖ ^ 2 / (4 * t ^ 2)) := by
    have := continuous_gc hf δ; fun_prop
  exact dsum_pt_pc (by positivity) (GraphCov.meshAff_gc hf δ)
    (fun z => Real.exp (-‖z‖ ^ 2 / (4 * t ^ 2))) Q (hc.intervalIntegrable 0 1)

lemma integral_ek (t : ℝ) (ht : 0 < t) (x : ℝ) : ∫ y, ek t (x - y) = 2 * √π * t := by
  rw [integral_sub_left_eq_self (fun y => ek t y) volume x]
  have e : (fun y => ek t y) = fun y => Real.exp (-(1 / (4 * t ^ 2)) * y ^ 2) := by
    funext y; unfold ek; congr 1; ring
  rw [e, integral_gaussian]
  have h1 : π / (1 / (4 * t ^ 2)) = (2 * √π * t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; field_simp; ring
  rw [h1, Real.sqrt_sq (by positivity)]

lemma integrable_ek (t : ℝ) (ht : 0 < t) (x : ℝ) : Integrable fun y => ek t (x - y) := by
  have h : Integrable fun y : ℝ => Real.exp (-(1 / (4 * t ^ 2)) * y ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have h2 := h.comp_sub_left x
  refine h2.congr (ae_of_all _ fun y => ?_)
  simp only [ek]; congr 1; ring

lemma intervalIntegral_ek_le (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ∫ y in (0:ℝ)..1, ek t (x - y) ≤ 2 * √π * t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_ek t ht x]
  exact setIntegral_le_integral (integrable_ek t ht x) (ae_of_all _ fun y => (ek_pos t _).le)

/-- **Small scales.** -/
lemma gaussPair_pt_graph_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {t : ℝ} (ht : 0 < t) (δ x Y : ℝ) :
    0 ≤ gaussPair t (pt (hpt δ x Y)) (graphComb (16 ^ n) δ f) ∧
      gaussPair t (pt (hpt δ x Y)) (graphComb (16 ^ n) δ f) ≤ 2 * √π * t := by
  rw [gaussPair_pt_graph hf]
  simp_rw [gauss_hk_graph]
  have hfc := Subadd.V_continuous hf
  have hc1 : Continuous fun y => ek t (x - y) * ek t (δ * (Y - f y)) := by unfold ek; fun_prop
  have hc2 : Continuous fun y => ek t (x - y) := by unfold ek; fun_prop
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun y _ =>
    (mul_pos (ek_pos _ _) (ek_pos _ _)).le, ?_⟩
  refine le_trans ?_ (intervalIntegral_ek_le t ht x)
  refine intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1) fun y _ => ?_
  exact mul_le_of_le_one_right (ek_pos _ _).le (ek_le_one _ _)

lemma abs_gaussPair_pt_gdiff_le {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {t : ℝ}
    (ht : 0 < t) (δ x Y : ℝ) :
    |gaussPair t (pt (hpt δ x Y)) (gdiff (16 ^ n) δ f g)| ≤ 2 * √π * t := by
  rw [gdiff, gaussPair_eq_dsum, dsum_sub_right, ← gaussPair_eq_dsum, ← gaussPair_eq_dsum]
  obtain ⟨a1, a2⟩ := gaussPair_pt_graph_le hf ht δ x Y
  obtain ⟨b1, b2⟩ := gaussPair_pt_graph_le hg ht δ x Y
  rw [abs_le]; constructor <;> linarith

/-! ## Large scales: the mixed second difference -/

lemma hasDerivAt_of_eq {f g : ℝ → ℝ} {f' g' x : ℝ} (h : HasDerivAt f f' x) (hfg : f = g)
    (h' : f' = g') : HasDerivAt g g' x := by
  subst hfg; subst h'; exact h

lemma hasDerivAt_ek (t s : ℝ) : HasDerivAt (ek t) (-(s / (2 * t ^ 2)) * ek t s) s := by
  have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
  have h1 := (h0.const_mul (-1 / (4 * t ^ 2))).exp
  refine hasDerivAt_of_eq h1 ?_ ?_
  · funext x; unfold ek; congr 1; ring
  · unfold ek
    rw [show -1 / (4 * t ^ 2) * s ^ 2 = -s ^ 2 / (4 * t ^ 2) by ring]
    ring

/-- `E_t'`. -/
def ek1 (t s : ℝ) : ℝ := -(s / (2 * t ^ 2)) * ek t s

lemma hasDerivAt_ek1 (t s : ℝ) :
    HasDerivAt (ek1 t) ((s ^ 2 / (4 * t ^ 4) - 1 / (2 * t ^ 2)) * ek t s) s := by
  have h1 := ((hasDerivAt_id s).const_mul (-(1 / (2 * t ^ 2)))).mul (hasDerivAt_ek t s)
  refine hasDerivAt_of_eq h1 ?_ ?_
  · funext x; simp only [Pi.mul_apply, id]; unfold ek1; ring
  · simp only [id]; ring

lemma abs_ek2_le (t s : ℝ) (ht : t ≠ 0) :
    |(s ^ 2 / (4 * t ^ 4) - 1 / (2 * t ^ 2)) * ek t s| ≤ 1 / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  set v : ℝ := s ^ 2 / (4 * t ^ 2) with hv
  have hv0 : 0 ≤ v := by positivity
  have hek : ek t s = Real.exp (-v) := by unfold ek; rw [hv, neg_div]
  have e1 : s ^ 2 / (4 * t ^ 4) = v / t ^ 2 := by rw [hv]; field_simp
  rw [e1, hek, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hq := Real.quadratic_le_exp_of_nonneg hv0
  have hexp : v * Real.exp (-v) ≤ 1 / 2 := by
    have h2 : 2 * v ≤ Real.exp v := by nlinarith [sq_nonneg (v - 1)]
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos v)]
    linarith
  have hexp1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hab : |v / t ^ 2 - 1 / (2 * t ^ 2)| ≤ (v + 1 / 2) / t ^ 2 := by
    rw [abs_le]; constructor
    · rw [show v / t ^ 2 - 1 / (2 * t ^ 2) = (v - 1 / 2) / t ^ 2 by field_simp]
      rw [neg_le, ← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) ht2.le
    · rw [show v / t ^ 2 - 1 / (2 * t ^ 2) = (v - 1 / 2) / t ^ 2 by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) ht2.le
  calc |v / t ^ 2 - 1 / (2 * t ^ 2)| * Real.exp (-v)
      ≤ (v + 1 / 2) / t ^ 2 * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right hab (Real.exp_pos _).le
    _ = (v * Real.exp (-v) + Real.exp (-v) / 2) / t ^ 2 := by ring
    _ ≤ (1 / 2 + 1 / 2) / t ^ 2 := div_le_div_of_nonneg_right (by linarith) ht2.le
    _ = 1 / t ^ 2 := by norm_num

lemma abs_ek1_sub_le (t : ℝ) (ht : t ≠ 0) (p q : ℝ) : |ek1 t p - ek1 t q| ≤ |p - q| / t ^ 2 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := ek1 t) (f' := fun s => (s ^ 2 / (4 * t ^ 4) - 1 / (2 * t ^ 2)) * ek t s)
    (C := 1 / t ^ 2) (s := univ) (x := q) (y := p)
    (fun s _ => (hasDerivAt_ek1 t s).hasDerivWithinAt) (fun s _ => by
      rw [Real.norm_eq_abs]; exact abs_ek2_le t s ht) convex_univ (mem_univ _) (mem_univ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [div_eq_mul_inv, mul_comm]
  simpa [one_div] using h

/-- **Mixed second difference of the Gaussian kernel.** -/
lemma abs_ek_mixed_le (t : ℝ) (ht : t ≠ 0) (A h k : ℝ) :
    |ek t (A + h + k) - ek t (A + h) - ek t (A + k) + ek t A| ≤ |h| * |k| / t ^ 2 := by
  set ψ : ℝ → ℝ := fun s => ek t (s + h) - ek t s with hψ
  have hder : ∀ s, HasDerivAt ψ (ek1 t (s + h) - ek1 t s) s := by
    intro s
    have h1 := (hasDerivAt_ek t (s + h)).comp s ((hasDerivAt_id s).add_const h)
    have h2 := hasDerivAt_ek t s
    have := h1.sub h2
    simp only [mul_one] at this
    exact this
  have hb : ∀ s, ‖ek1 t (s + h) - ek1 t s‖ ≤ |h| / t ^ 2 := by
    intro s
    rw [Real.norm_eq_abs]
    have := abs_ek1_sub_le t ht (s + h) s
    rwa [add_sub_cancel_left] at this
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := ψ) (f' := fun s => ek1 t (s + h) - ek1 t s) (C := |h| / t ^ 2) (s := univ)
    (x := A) (y := A + k) (fun s _ => (hder s).hasDerivWithinAt) (fun s _ => hb s) convex_univ
    (mem_univ _) (mem_univ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at key
  have e : ψ (A + k) - ψ A = ek t (A + h + k) - ek t (A + h) - ek t (A + k) + ek t A := by
    simp only [hψ]; rw [show A + k + h = A + h + k by ring]; ring
  rw [← e]
  calc |ψ (A + k) - ψ A| ≤ |h| / t ^ 2 * |k| := key
    _ = |h| * |k| / t ^ 2 := by ring

/-- **Large scales**: a vertical dipole against `μ_{δ,f} - μ_{δ,g}`. -/
lemma abs_gaussPair_vdip_le {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {W : ℝ}
    (hW : ∀ y, |f y - g y| ≤ W) {t : ℝ} (ht : 0 < t) {δ : ℝ} (hδ : 0 ≤ δ) (x Y Y' : ℝ) :
    |gaussPair t ((pt (hpt δ x Y)).sub (pt (hpt δ x Y'))) (gdiff (16 ^ n) δ f g)| ≤
      2 * √π * δ ^ 2 * |Y - Y'| * W / t := by
  have hfc := Subadd.V_continuous hf
  have hgc := Subadd.V_continuous hg
  have hcont : ∀ (h : ℝ → ℝ), Continuous h → ∀ Z : ℝ,
      Continuous fun y => ek t (x - y) * ek t (δ * (Z - h y)) := by
    intro h hh Z; unfold ek; fun_prop
  have hrep : ∀ (h : ℝ → ℝ), h ∈ V n → ∀ Z : ℝ,
      gaussPair t (pt (hpt δ x Z)) (graphComb (16 ^ n) δ h) =
        ∫ y in (0:ℝ)..1, ek t (x - y) * ek t (δ * (Z - h y)) := by
    intro h hh Z
    rw [gaussPair_pt_graph hh]
    simp_rw [gauss_hk_graph]
  have i1 : IntervalIntegrable (fun y => ek t (x - y) * ek t (δ * (Y - f y)) -
      ek t (x - y) * ek t (δ * (Y - g y))) volume 0 1 :=
    ((hcont f hfc Y).sub (hcont g hgc Y)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun y => ek t (x - y) * ek t (δ * (Y' - f y)) -
      ek t (x - y) * ek t (δ * (Y' - g y))) volume 0 1 :=
    ((hcont f hfc Y').sub (hcont g hgc Y')).intervalIntegrable 0 1
  rw [gdiff, gaussPair_eq_dsum, dsum_sub_left, dsum_sub_right, dsum_sub_right,
    ← gaussPair_eq_dsum, ← gaussPair_eq_dsum, ← gaussPair_eq_dsum, ← gaussPair_eq_dsum,
    hrep f hf, hrep g hg, hrep f hf, hrep g hg,
    ← intervalIntegral.integral_sub ((hcont f hfc Y).intervalIntegrable 0 1)
      ((hcont g hgc Y).intervalIntegrable 0 1),
    ← intervalIntegral.integral_sub ((hcont f hfc Y').intervalIntegrable 0 1)
      ((hcont g hgc Y').intervalIntegrable 0 1),
    ← intervalIntegral.integral_sub i1 i2]
  have hpt' : ∀ y, |ek t (x - y) * ek t (δ * (Y - f y)) - ek t (x - y) * ek t (δ * (Y - g y)) -
      (ek t (x - y) * ek t (δ * (Y' - f y)) - ek t (x - y) * ek t (δ * (Y' - g y)))| ≤
      ek t (x - y) * (δ ^ 2 * |Y - Y'| * W / t ^ 2) := by
    intro y
    have hm := abs_ek_mixed_le t ht.ne' (δ * (Y' - f y)) (δ * (f y - g y)) (δ * (Y - Y'))
    have e1 : δ * (Y' - f y) + δ * (f y - g y) + δ * (Y - Y') = δ * (Y - g y) := by ring
    have e2 : δ * (Y' - f y) + δ * (f y - g y) = δ * (Y' - g y) := by ring
    have e3 : δ * (Y' - f y) + δ * (Y - Y') = δ * (Y - f y) := by ring
    rw [e1, e2, e3] at hm
    have e4 : ek t (x - y) * ek t (δ * (Y - f y)) - ek t (x - y) * ek t (δ * (Y - g y)) -
        (ek t (x - y) * ek t (δ * (Y' - f y)) - ek t (x - y) * ek t (δ * (Y' - g y))) =
        -(ek t (x - y) * (ek t (δ * (Y - g y)) - ek t (δ * (Y' - g y)) - ek t (δ * (Y - f y)) +
          ek t (δ * (Y' - f y)))) := by ring
    rw [e4, abs_neg, abs_mul, abs_of_pos (ek_pos _ _)]
    refine mul_le_mul_of_nonneg_left (hm.trans ?_) (ek_pos _ _).le
    rw [abs_mul, abs_mul, abs_of_nonneg hδ]
    have := hW y
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right ht2]
    calc δ * |f y - g y| * (δ * |Y - Y'|) = (δ ^ 2 * |Y - Y'|) * |f y - g y| := by ring
      _ ≤ (δ ^ 2 * |Y - Y'|) * W := mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ ^ 2 * |Y - Y'| * W := by ring
  have hc2 : Continuous fun y => ek t (x - y) * (δ ^ 2 * |Y - Y'| * W / t ^ 2) := by
    unfold ek; fun_prop
  calc |∫ y in (0:ℝ)..1, (ek t (x - y) * ek t (δ * (Y - f y)) -
        ek t (x - y) * ek t (δ * (Y - g y)) -
        (ek t (x - y) * ek t (δ * (Y' - f y)) - ek t (x - y) * ek t (δ * (Y' - g y))))|
      ≤ ∫ y in (0:ℝ)..1, ek t (x - y) * (δ ^ 2 * |Y - Y'| * W / t ^ 2) := by
        rw [← Real.norm_eq_abs]
        refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
          (ae_of_all _ fun y _ => ?_) (hc2.intervalIntegrable 0 1)
        rw [Real.norm_eq_abs]; exact hpt' y
    _ = (∫ y in (0:ℝ)..1, ek t (x - y)) * (δ ^ 2 * |Y - Y'| * W / t ^ 2) :=
        intervalIntegral.integral_mul_const _ _
    _ ≤ (2 * √π * t) * (δ ^ 2 * |Y - Y'| * W / t ^ 2) := by
        have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
        gcongr
        exact intervalIntegral_ek_le t ht x
    _ = 2 * √π * δ ^ 2 * |Y - Y'| * W / t := by field_simp

end LQGDimension.L51
