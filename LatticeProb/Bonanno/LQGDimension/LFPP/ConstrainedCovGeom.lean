/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCovGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovAux
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovPoly

/-!
# Geometry of the constrained configuration for small `δ`

For `x = δ p₀`, `y = 1 + δ p₁` we introduce the chord points, the displaced graph points
`chord(i/M) + i δ f(i/M)` and the polygon vertices `x + (y - x) uv_i`, express the configuration in
edge-indexed form, and collect all the bounds (vertex sizes, edge lengths, weights, couplings)
used by the covariance estimates, under explicit smallness conditions on `δ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft GraphCov

/-! ## Lipschitz bound for `V n` -/

/-- `f` is `L`-Lipschitz on `s`. -/
def LipOn (f : ℝ → ℝ) (L : ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * |x - y|

lemma lipOn_union {f : ℝ → ℝ} {L : ℝ} (_hL : 0 ≤ L) {s t : Set ℝ} {b : ℝ}
    (hs : ∀ x ∈ s, x ≤ b) (ht : ∀ x ∈ t, b ≤ x) (hbs : b ∈ s) (hbt : b ∈ t)
    (h1 : LipOn f L s) (h2 : LipOn f L t) : LipOn f L (s ∪ t) := by
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
lemma V_lip {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (x y : ℝ) :
    |f x - f y| ≤ 2 * B * (16 : ℝ) ^ n * |x - y| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hN : (0 : ℝ) < (16 : ℝ) ^ n := by positivity
  set L := 2 * B * (16 : ℝ) ^ n with hLdef
  have hL : 0 ≤ L := by positivity
  have hpiece : ∀ k : ℕ, k < 16 ^ n →
      LipOn f L (Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n)) := by
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
  have hind : ∀ k : ℕ, k ≤ 16 ^ n → LipOn f L (Icc 0 ((k : ℝ) / 16 ^ n)) := by
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
      exact lipOn_union hL (fun u hu => hu.2) (fun u hu => hu.1) ⟨h1, le_rfl⟩ ⟨le_rfl, h2⟩
        (ih (by omega)) (hpiece k (by omega))
  have h01 : LipOn f L (Icc 0 1) := by
    have := hind (16 ^ n) le_rfl
    rwa [Nat.cast_pow, Nat.cast_ofNat, div_self hN.ne'] at this
  have hIic : LipOn f L (Iic 0) := by
    intro u hu v hv
    rw [Subadd.V_zero_of_le hf (Or.inl hu), Subadd.V_zero_of_le hf (Or.inl hv)]
    simp only [sub_self, abs_zero]; positivity
  have hIci : LipOn f L (Ici 1) := by
    intro u hu v hv
    rw [Subadd.V_zero_of_le hf (Or.inr hu), Subadd.V_zero_of_le hf (Or.inr hv)]
    simp only [sub_self, abs_zero]; positivity
  have h1 := lipOn_union (s := Iic 0) (t := Icc 0 1) (b := 0) hL (fun u hu => hu)
    (fun u hu => hu.1) (mem_Iic.2 le_rfl) ⟨le_rfl, zero_le_one⟩ hIic h01
  rw [Iic_union_Icc_eq_Iic zero_le_one] at h1
  have h2 := lipOn_union (s := Iic 1) (t := Ici 1) (b := 1) hL (fun u hu => hu)
    (fun u hu => hu) (mem_Iic.2 le_rfl) (mem_Ici.2 le_rfl) h1 hIci
  rw [Iic_union_Ici] at h2
  exact h2 x (mem_univ _) y (mem_univ _)

/-! ## Curves of the configuration -/

/-- Real part of the chord point: `A(t) = δ p₀.re + t (1 + δ (p₁ - p₀).re)`. -/
def Aff (δ : ℝ) (p₀ p₁ : ℂ) (t : ℝ) : ℝ := δ * p₀.re + t * (1 + δ * (p₁ - p₀).re)

/-- The chord `[δ p₀, 1 + δ p₁]`. -/
def xp (δ : ℝ) (p₀ : ℂ) : ℂ := (δ : ℂ) * p₀

def yp (δ : ℝ) (p₁ : ℂ) : ℂ := 1 + (δ : ℂ) * p₁

lemma chordPt_eq_dc (δ : ℝ) (p₀ p₁ : ℂ) :
    chordPt (xp δ p₀) (yp δ p₁) = dc (Aff δ p₀ p₁) δ (affineFn p₀.im p₁.im) := by
  funext t
  apply Complex.ext <;>
    simp only [chordPt, dc, Aff, affineFn, xp, yp, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.one_im] <;> ring

/-- The displaced graph curve `chord(t) + i δ f(t)`. -/
def zC (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) (t : ℝ) : ℂ :=
  chordPt (xp δ p₀) (yp δ p₁) t + ((δ * f t : ℝ) : ℂ) * Complex.I

lemma zC_eq_dc (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) :
    zC δ f p₀ p₁ = dc (Aff δ p₀ p₁) δ (affineFn p₀.im p₁.im + f) := by
  funext t
  apply Complex.ext <;>
    simp only [zC, chordPt, dc, Aff, affineFn, xp, yp, Pi.add_apply, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im, Complex.sub_im,
      Complex.one_im] <;> ring

lemma meshAff_chordPt (M : ℕ) (hM : 0 < M) (x y : ℂ) : MeshAff M (chordPt x y) := by
  intro i _ s _
  rw [chordPt_piece x y hM i s]

lemma meshAff_zC {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) (δ : ℝ) (p₀ p₁ : ℂ) :
    MeshAff (16 ^ n) (zC δ f p₀ p₁) := by
  have hM : 0 < 16 ^ n := by positivity
  intro i hi s hs
  have h1 := chordPt_piece (xp δ p₀) (yp δ p₁) hM i s
  have h2 := meshAff_gc hf δ i hi s hs
  have e : ∀ t : ℝ, zC δ f p₀ p₁ t = chordPt (xp δ p₀) (yp δ p₁) t + gc δ f t - (t : ℂ) := by
    intro t; unfold zC gc; ring
  simp only [e]
  rw [← h1, h2]
  push_cast
  ring

lemma pc_eq_wc (M : ℕ) (P : ℝ → ℂ) :
    pc M P = wc M (fun _ => 1 / (M : ℝ)) (fun i => P ((i : ℝ) / M)) := by
  unfold pc wc
  refine List.map_congr_left fun i _ => ?_
  simp only [Nat.cast_add, Nat.cast_one]

/-! ## The configuration in edge-indexed form -/

/-- Vertices of the constrained polygon. -/
def Zv (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) (i : ℕ) : ℂ :=
  xp δ p₀ + (yp δ p₁ - xp δ p₀) * uv M δ f i

/-- Displaced graph vertices. -/
def zv (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) (i : ℕ) : ℂ := zC δ f p₀ p₁ ((i : ℝ) / M)

/-- Chord vertices. -/
def cv (M : ℕ) (δ : ℝ) (p₀ p₁ : ℂ) (i : ℕ) : ℂ := chordPt (xp δ p₀) (yp δ p₁) ((i : ℝ) / M)

lemma polyComb_pair {x y : ℂ} (hxy : x ≠ y) : polyComb [x, y] = [((1 : ℝ), x, y)] := by
  have h : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  simp [polyComb, polyLen, edges, h]

lemma cfgComb_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) (hxy : xp δ p₀ ≠ yp δ p₁) :
    cfgComb (constrCfg M δ f p₀ p₁) =
      SegComb.sub [((1 : ℝ), xp δ p₀, yp δ p₁)] (wc M (uW M δ f) (Zv M δ f p₀ p₁)) := by
  unfold cfgComb constrCfg
  simp only
  rw [show (δ : ℂ) * p₀ = xp δ p₀ from rfl, show 1 + (δ : ℂ) * p₁ = yp δ p₁ from rfl,
    polyComb_pair hxy, polyComb_constrPoly M δ f hxy]
  rfl

/-! ## Smallness of `δ` -/

/-- The smallness conditions on `δ` used throughout (with `M = 16ⁿ`). -/
structure Small (n : ℕ) (B A δ : ℝ) : Prop where
  pos : 0 < δ
  le_one : δ ≤ 1
  hA : δ * A ≤ 1 / 16
  hB : δ * B ≤ 1 / 16
  hη : (2 * B * (16 : ℝ) ^ n * δ) ^ 2 ≤ 1 / (4 * (16 : ℝ) ^ n)

lemma eventually_small (n : ℕ) (B A : ℝ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Small n B A δ := by
  have hN : (0 : ℝ) < 4 * (16 : ℝ) ^ n := by positivity
  have t0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have t1 : Tendsto (fun δ : ℝ => δ * A) (𝓝[>] 0) (𝓝 0) := by simpa using t0.mul_const A
  have t2 : Tendsto (fun δ : ℝ => δ * B) (𝓝[>] 0) (𝓝 0) := by simpa using t0.mul_const B
  have t3 : Tendsto (fun δ : ℝ => (2 * B * (16 : ℝ) ^ n * δ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((t0.const_mul (2 * B * (16 : ℝ) ^ n)).pow 2)
  filter_upwards [self_mem_nhdsWithin, t0.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num)),
    t1.eventually (eventually_le_nhds (show (0:ℝ) < 1 / 16 by norm_num)),
    t2.eventually (eventually_le_nhds (show (0:ℝ) < 1 / 16 by norm_num)),
    t3.eventually (eventually_le_nhds (show (0:ℝ) < 1 / (4 * (16 : ℝ) ^ n) by positivity))]
    with δ h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2, h3, h4⟩

section Facts

variable {n : ℕ} {B A δ : ℝ} {f : ℝ → ℝ} {p₀ p₁ : ℂ}

/-- `η = (2 B M δ)²`. -/
def etaS (n : ℕ) (B δ : ℝ) : ℝ := (2 * B * (16 : ℝ) ^ n * δ) ^ 2

lemma etaS_nonneg (n : ℕ) (B δ : ℝ) : 0 ≤ etaS n B δ := sq_nonneg _

lemma Small.eta_le (hs : Small n B A δ) : etaS n B δ ≤ 1 / (4 * (16 : ℝ) ^ n) := hs.hη

lemma Small.eta_le' (hs : Small n B A δ) : etaS n B δ ≤ 1 / 4 := by
  refine hs.hη.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  linarith

lemma aj_sq_le (hs : Small n B A δ) (hfB : ∀ x, |f x| ≤ B) (j : ℕ) :
    aj (16 ^ n) δ f j ^ 2 ≤ etaS n B δ := by
  unfold etaS
  rw [← sq_abs]
  have := abs_aj_le (M := 16 ^ n) hs.pos.le hfB j
  push_cast at this
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma norm_xp_le (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) : ‖xp δ p₀‖ ≤ 1 / 16 := by
  have hδ := hs.pos
  unfold xp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc δ * ‖p₀‖ ≤ δ * A := by gcongr
    _ ≤ 1 / 16 := hs.hA

lemma norm_yx_sub_one_le (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) :
    ‖yp δ p₁ - xp δ p₀ - 1‖ ≤ 1 / 8 := by
  have hδ := hs.pos
  unfold xp yp
  rw [show 1 + (δ : ℂ) * p₁ - (δ : ℂ) * p₀ - 1 = (δ : ℂ) * (p₁ - p₀) by ring, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have h2 : ‖p₁ - p₀‖ ≤ A + A := (norm_sub_le _ _).trans (by linarith)
  calc δ * ‖p₁ - p₀‖ ≤ δ * (A + A) := by gcongr
    _ ≤ 1 / 8 := by linarith [hs.hA]

lemma norm_yx_bounds (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) :
    7 / 8 ≤ ‖yp δ p₁ - xp δ p₀‖ ∧ ‖yp δ p₁ - xp δ p₀‖ ≤ 9 / 8 := by
  have h := norm_yx_sub_one_le hs h0 h1
  have e := abs_le.1 ((abs_norm_sub_norm_le (yp δ p₁ - xp δ p₀) 1).trans h)
  rw [norm_one] at e
  constructor <;> linarith [e.1, e.2]

lemma re_yx_ge (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) :
    7 / 8 ≤ (yp δ p₁ - xp δ p₀).re := by
  have h := norm_yx_sub_one_le hs h0 h1
  have := (Complex.abs_re_le_norm (yp δ p₁ - xp δ p₀ - 1))
  rw [Complex.sub_re, Complex.one_re] at this
  have := abs_le.1 (this.trans h)
  linarith [this.1]

lemma xp_ne_yp (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) : xp δ p₀ ≠ yp δ p₁ := by
  intro h
  have := (norm_yx_bounds hs h0 h1).1
  rw [h, sub_self, norm_zero] at this
  norm_num at this

lemma one_add_re_pos (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) :
    7 / 8 ≤ 1 + δ * (p₁ - p₀).re := by
  have h := re_yx_ge hs h0 h1
  unfold xp yp at h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [Complex.sub_re]; linarith

end Facts

section Facts2

variable {n : ℕ} {B A δ : ℝ} {f : ℝ → ℝ} {p₀ p₁ : ℂ}

lemma M_pos (n : ℕ) : 0 < 16 ^ n := by positivity

lemma Mr_eq (n : ℕ) : ((16 ^ n : ℕ) : ℝ) = (16 : ℝ) ^ n := by push_cast; ring

lemma uLen_facts (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) :
    1 ≤ uLen (16 ^ n) δ f ∧ uLen (16 ^ n) δ f - 1 ≤ etaS n B δ := by
  obtain ⟨h1, h2, -⟩ := uLen_energy_est n hf hfB hs.pos hs.eta_le'
  exact ⟨h1, h2⟩

lemma abs_uW_sub_le' {M : ℕ} (hM : 0 < M) {δ : ℝ} {f : ℝ → ℝ} (hf1 : f 1 = 0)
    (ha : ∀ j, aj M δ f j ^ 2 ≤ 1) (hL1 : 1 ≤ uLen M δ f) {i : ℕ} (hi : i < M) :
    |uW M δ f i - 1 / (M : ℝ)| ≤ uLen M δ f - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  exact abs_uW_sub_le m δ f hf1 ha hL1 hi

lemma uW_facts (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) :
    (∀ i, 0 ≤ uW (16 ^ n) δ f i) ∧ (∑ i ∈ Finset.range (16 ^ n), uW (16 ^ n) δ f i = 1) ∧
    (∀ i < 16 ^ n, |uW (16 ^ n) δ f i - 1 / ((16 ^ n : ℕ) : ℝ)| ≤ etaS n B δ) := by
  obtain ⟨hL1, hLη⟩ := uLen_facts hs hf hfB
  have hL0 : 0 < uLen (16 ^ n) δ f := by linarith
  refine ⟨uW_nonneg _ _ _ hL0, sum_uW _ _ _ hL0, fun i hi => ?_⟩
  refine (abs_uW_sub_le' (M_pos n) hf.2.1 (fun j => (aj_sq_le hs hfB j).trans
    (hs.eta_le'.trans (by norm_num))) hL1 hi).trans hLη

lemma uW_le (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) {i : ℕ}
    (hi : i < 16 ^ n) : uW (16 ^ n) δ f i ≤ 5 / 4 / ((16 ^ n : ℕ) : ℝ) := by
  have h := (abs_le.1 ((uW_facts hs hf hfB).2.2 i hi)).2
  have h2 := hs.eta_le
  rw [← Mr_eq] at h2
  have e : 5 / 4 / ((16 ^ n : ℕ) : ℝ) = 1 / ((16 ^ n : ℕ) : ℝ) + 1 / (4 * ((16 ^ n : ℕ) : ℝ)) := by
    ring
  rw [e]; linarith

/-- Every edge of the unit constrained polygon has length at least `1/M`. -/
lemma unit_edge_ge (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) {i : ℕ}
    (hi : i < 16 ^ n) :
    1 / ((16 ^ n : ℕ) : ℝ) ≤ ‖uv (16 ^ n) δ f (i + 1) - uv (16 ^ n) δ f i‖ := by
  have ha : ∀ j, aj (16 ^ n) δ f j ^ 2 ≤ 1 := fun j => (aj_sq_le hs hfB j).trans
    (hs.eta_le'.trans (by norm_num))
  obtain ⟨m, hm⟩ : ∃ m, 16 ^ n = m + 1 := ⟨16 ^ n - 1, by have := M_pos n; omega⟩
  have ha' : ∀ j, aj (m + 1) δ f j ^ 2 ≤ 1 := by rw [← hm]; exact ha
  rw [hm] at hi ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hi' | hi'
  · exact (norm_uv_step δ f (by omega) (ha' (i + 1))).ge
  · rw [hi', norm_uv_last m δ f hf.2.1]
    have hS : 0 ≤ shortS m δ f := Finset.sum_nonneg fun j _ =>
      (one_sub_sqrt_le (sq_nonneg (aj (m + 1) δ f j)) (ha' j)).1
    have h1 : 1 + shortS m δ f ≤
        Real.sqrt ((1 + shortS m δ f) ^ 2 + aj (m + 1) δ f (m + 1) ^ 2) := by
      have := Real.sqrt_le_sqrt (show (1 + shortS m δ f) ^ 2 ≤
        (1 + shortS m δ f) ^ 2 + aj (m + 1) δ f (m + 1) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    push_cast
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc 1 / ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) * (1 + shortS m δ f) := by
          rw [le_mul_iff_one_le_right (by positivity)]; linarith
      _ ≤ _ := by gcongr

lemma norm_uv_le2 (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) {i : ℕ}
    (hi : i ≤ 16 ^ n) : ‖uv (16 ^ n) δ f i‖ ≤ 2 := by
  have h := norm_uv_le (M_pos n) hf.2.1 hs.pos.le hfB (etaS_nonneg n B δ) (hs.eta_le'.trans
    (by norm_num)) (aj_sq_le hs hfB) hi
  linarith [hs.eta_le', hs.hB]

end Facts2

section Facts3

variable {n : ℕ} {B A δ : ℝ} {f : ℝ → ℝ} {p₀ p₁ : ℂ}

lemma t_mem (n i : ℕ) (hi : i ≤ 16 ^ n) : (i : ℝ) / ((16 ^ n : ℕ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hM : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast M_pos n
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hM]; exact_mod_cast hi

lemma norm_chordPt_le (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖chordPt (xp δ p₀) (yp δ p₁) t‖ ≤ 2 := by
  unfold chordPt
  have hx := norm_xp_le hs h0
  have hyx := (norm_yx_bounds hs h0 h1).2
  calc _ ≤ ‖xp δ p₀‖ + ‖(t : ℂ) * (yp δ p₁ - xp δ p₀)‖ := norm_add_le _ _
    _ = ‖xp δ p₀‖ + t * ‖yp δ p₁ - xp δ p₀‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ 1 / 16 + 1 * (9 / 8) := by gcongr; exact ht.2
    _ ≤ 2 := by norm_num

lemma norm_cv_le (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) {i : ℕ}
    (hi : i ≤ 16 ^ n) : ‖cv (16 ^ n) δ p₀ p₁ i‖ ≤ 3 :=
  (norm_chordPt_le hs h0 h1 (t_mem n i hi)).trans (by norm_num)

lemma norm_cv_sub_zv (hs : Small n B A δ) (hfB : ∀ x, |f x| ≤ B) (i : ℕ) :
    ‖cv (16 ^ n) δ p₀ p₁ i - zv (16 ^ n) δ f p₀ p₁ i‖ ≤ δ * B := by
  have hδ := hs.pos
  unfold cv zv zC
  rw [show chordPt (xp δ p₀) (yp δ p₁) ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) -
      (chordPt (xp δ p₀) (yp δ p₁) ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) +
        ((δ * f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) =
      -(((δ * f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) by ring, norm_neg,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hδ]
  gcongr
  exact hfB _

lemma norm_zv_le (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A)
    (hfB : ∀ x, |f x| ≤ B) {i : ℕ} (hi : i ≤ 16 ^ n) : ‖zv (16 ^ n) δ f p₀ p₁ i‖ ≤ 3 := by
  have h1' := norm_chordPt_le hs h0 h1 (t_mem n i hi)
  have h2 := norm_cv_sub_zv (p₀ := p₀) (p₁ := p₁) hs hfB i
  have h3 := norm_le_norm_sub_add (zv (16 ^ n) δ f p₀ p₁ i) (cv (16 ^ n) δ p₀ p₁ i)
  rw [norm_sub_rev] at h3
  unfold cv at h2 h3
  linarith [hs.hB]

lemma norm_Zv_le (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B)
    (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) {i : ℕ} (hi : i ≤ 16 ^ n) :
    ‖Zv (16 ^ n) δ f p₀ p₁ i‖ ≤ 3 := by
  unfold Zv
  have hx := norm_xp_le hs h0
  have hyx := (norm_yx_bounds hs h0 h1).2
  have hu := norm_uv_le2 hs hf hfB hi
  calc _ ≤ ‖xp δ p₀‖ + ‖(yp δ p₁ - xp δ p₀) * uv (16 ^ n) δ f i‖ := norm_add_le _ _
    _ = ‖xp δ p₀‖ + ‖yp δ p₁ - xp δ p₀‖ * ‖uv (16 ^ n) δ f i‖ := by rw [norm_mul]
    _ ≤ 1 / 16 + 9 / 8 * 2 := by gcongr
    _ ≤ 3 := by norm_num

/-- Coupling constant between displaced graph and polygon: `‖zv - Zv‖ ≤ c₁ δ²`. -/
def c₁ (n : ℕ) (B A : ℝ) : ℝ := 2 * (2 * B * (16 : ℝ) ^ n) ^ 2 + 2 * A * B

lemma norm_zv_sub_Zv (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B)
    (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) {i : ℕ} (hi : i ≤ 16 ^ n) :
    ‖zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f p₀ p₁ i‖ ≤ c₁ n B A * δ ^ 2 := by
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hδ := hs.pos
  have e : zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f p₀ p₁ i =
      -((yp δ p₁ - xp δ p₀) * (uv (16 ^ n) δ f i - gpt (16 ^ n) δ f i) +
        (yp δ p₁ - xp δ p₀ - 1) * (((δ * f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) *
          Complex.I)) := by
    unfold zv zC Zv gpt chordPt; ring
  rw [e, norm_neg]
  have hg := norm_uv_sub_gpt_le (M_pos n) hf.2.1 (etaS_nonneg n B δ)
    (hs.eta_le'.trans (by norm_num)) (aj_sq_le hs hfB) hi
  have hyx := (norm_yx_bounds hs h0 h1).2
  have hyx1 : ‖yp δ p₁ - xp δ p₀ - 1‖ ≤ 2 * A * δ := by
    unfold xp yp
    rw [show 1 + (δ : ℂ) * p₁ - (δ : ℂ) * p₀ - 1 = (δ : ℂ) * (p₁ - p₀) by ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.pos]
    have := (norm_sub_le p₁ p₀).trans (by linarith : ‖p₁‖ + ‖p₀‖ ≤ 2 * A)
    nlinarith [hs.pos]
  have hf' : ‖((δ * f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I‖ ≤ δ * B := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hs.pos]
    gcongr; exact hfB _
  calc _ ≤ ‖(yp δ p₁ - xp δ p₀) * (uv (16 ^ n) δ f i - gpt (16 ^ n) δ f i)‖ +
        ‖(yp δ p₁ - xp δ p₀ - 1) * (((δ * f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) *
          Complex.I)‖ := norm_add_le _ _
    _ ≤ 9 / 8 * etaS n B δ + 2 * A * δ * (δ * B) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ ≤ c₁ n B A * δ ^ 2 := by
        unfold etaS c₁
        have : 0 ≤ (2 * B * (16 : ℝ) ^ n * δ) ^ 2 := sq_nonneg _
        nlinarith

lemma cv_edge (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) (i : ℕ) :
    7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤ ‖cv (16 ^ n) δ p₀ p₁ (i + 1) - cv (16 ^ n) δ p₀ p₁ i‖ := by
  have hM : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast M_pos n
  have e : cv (16 ^ n) δ p₀ p₁ (i + 1) - cv (16 ^ n) δ p₀ p₁ i =
      ((1 / ((16 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * (yp δ p₁ - xp δ p₀) := by
    unfold cv chordPt; push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := (norm_yx_bounds hs h0 h1).1
  calc 7 / 8 / ((16 ^ n : ℕ) : ℝ) = 1 / ((16 ^ n : ℕ) : ℝ) * (7 / 8) := by ring
    _ ≤ _ := by gcongr

lemma zv_edge (hs : Small n B A δ) (h0 : ‖p₀‖ ≤ A) (h1 : ‖p₁‖ ≤ A) (i : ℕ) :
    7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤
      ‖zv (16 ^ n) δ f p₀ p₁ (i + 1) - zv (16 ^ n) δ f p₀ p₁ i‖ := by
  have hM : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast M_pos n
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  have e : zv (16 ^ n) δ f p₀ p₁ (i + 1) - zv (16 ^ n) δ f p₀ p₁ i =
      ((1 / ((16 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * (yp δ p₁ - xp δ p₀) +
        ((δ * (f (((i + 1 : ℕ) : ℝ) / ((16 ^ n : ℕ) : ℝ)) -
          f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ))) : ℝ) : ℂ) * Complex.I := by
    unfold zv zC chordPt; push_cast; ring
  have hre : (zv (16 ^ n) δ f p₀ p₁ (i + 1) - zv (16 ^ n) δ f p₀ p₁ i).re =
      1 / ((16 ^ n : ℕ) : ℝ) * (yp δ p₁ - xp δ p₀).re := by
    rw [e]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hr := re_yx_ge hs h0 h1
  rw [hre, abs_of_nonneg (by positivity)]
  calc 7 / 8 / ((16 ^ n : ℕ) : ℝ) = 1 / ((16 ^ n : ℕ) : ℝ) * (7 / 8) := by ring
    _ ≤ _ := by gcongr

lemma Zv_edge (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) (h0 : ‖p₀‖ ≤ A)
    (h1 : ‖p₁‖ ≤ A) {i : ℕ} (hi : i < 16 ^ n) :
    7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤ ‖Zv (16 ^ n) δ f p₀ p₁ (i + 1) - Zv (16 ^ n) δ f p₀ p₁ i‖ := by
  unfold Zv
  rw [show xp δ p₀ + (yp δ p₁ - xp δ p₀) * uv (16 ^ n) δ f (i + 1) -
      (xp δ p₀ + (yp δ p₁ - xp δ p₀) * uv (16 ^ n) δ f i) =
      (yp δ p₁ - xp δ p₀) * (uv (16 ^ n) δ f (i + 1) - uv (16 ^ n) δ f i) by ring, norm_mul]
  have h1' := (norm_yx_bounds hs h0 h1).1
  have h2 := unit_edge_ge hs hf hfB hi
  calc 7 / 8 / ((16 ^ n : ℕ) : ℝ) = 7 / 8 * (1 / ((16 ^ n : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

end Facts3

end LQGDimension.ConstrCov
