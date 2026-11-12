/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma33 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Section2.ZCovPSD
import LatticeProb.Bonanno.LQGDimension.Section2.Bounds
import LatticeProb.Bonanno.LQGDimension.Section2.Subadditive
import LatticeProb.Bonanno.LQGDimension.Assembly.AStarProved
import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Lemma 3.3 (node `L33`)

For every `C₀` there is `C` such that, for `n ≥ 1`, `k ∈ ℕ` and every nonempty finite family of
triples `(f, t₀, t₁)` with `f ∈ V n`, `E(f) ≤ k + 2` and `|t₀|, |t₁| ≤ C₀ 16^{-2n}`,
`E max {Z_{f+g} - Z_g - k} ≤ min (a_n + C, C n^{3/4} (k+1)^{1/4} - k + C)`, `g = affineFn t₀ t₁`.

## Proof

Let `U` be a Gram representation of `zCov` on the finite set of all `f`, `g`, `f + g`, and put
`v_q = U(f + g) - U(g)`, so that `⟪v_q, v_q'⟫ = zDiffCov`.  Writing `d(a,b)² = 2π ∫₀¹ |a - b|`
for the canonical distance of `Z`, the four-point identity
`‖(A - B) - (C - D)‖² = d(A,C)² + d(B,D)² - d(A,D)² - d(C,B)² + d(A,B)² + d(C,D)²`
and three pointwise triangle inequalities give (without any `(1 + s)` loss)
`‖v_q - v_q'‖² ≤ d(f, f')² + 4 d(g, g')²`.
Hence Sudakov–Fernique compares the family with `(U f, 2 U g)` in `E × E`, whose expected
maximum is at most `E max (Z_f - k) + E max 2 Z_g`.  The second term is bounded by chaining on the
two-dimensional box of endpoint parameters (`‖2Ug - 2Ug'‖² ≤ 8π ‖t - t'‖_∞`), uniformly in `n`.
The first term is bounded by `a_n + 2` (as `-k ≤ -E(f) + 2`), and by `(2.2)` with `R = k + 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

open Blueprint.Draft

namespace L33

/-! ## Elementary facts -/

lemma affineFn_continuous (t₀ t₁ : ℝ) : Continuous (affineFn t₀ t₁) := by
  unfold affineFn; fun_prop

lemma zero_mem_V (n : ℕ) : (0 : ℝ → ℝ) ∈ V n :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => ⟨0, 0, fun x _ => by simp⟩⟩

/-- A member of `V n` built from a function (junk value `0` outside `V n`). -/
def toV (n : ℕ) (f : ℝ → ℝ) : V n := by
  classical
  exact if h : f ∈ V n then ⟨f, h⟩ else ⟨0, zero_mem_V n⟩

lemma toV_coe {n : ℕ} {f : ℝ → ℝ} (h : f ∈ V n) : ((toV n f : V n) : ℝ → ℝ) = f := by
  unfold toV
  simp [h]

/-- The four-point identity for the squared norm of a difference of increments. -/
lemma four_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b c d : E) :
    ‖(a - b) - (c - d)‖ ^ 2 = ‖a - c‖ ^ 2 + ‖b - d‖ ^ 2 - ‖a - d‖ ^ 2 - ‖c - b‖ ^ 2 +
      ‖a - b‖ ^ 2 + ‖c - d‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

/-- `∫₀¹ u ≤ ∫₀¹ v + ∫₀¹ w` from a pointwise bound, for continuous integrands. -/
lemma integral_le_add_of_le {u v w : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (h : ∀ x, u x ≤ v x + w x) :
    (∫ x in (0:ℝ)..1, u x) ≤ (∫ x in (0:ℝ)..1, v x) + ∫ x in (0:ℝ)..1, w x := by
  rw [← intervalIntegral.integral_add (hv.intervalIntegrable 0 1) (hw.intervalIntegrable 0 1)]
  exact intervalIntegral.integral_mono_on zero_le_one (hu.intervalIntegrable 0 1)
    ((hv.add hw).intervalIntegrable 0 1) fun x _ => h x

/-- Two affine functions on `[0,1]` differ by at most the sup-distance of their endpoint values. -/
lemma affine_diff_le (t₀ t₁ s₀ s₁ : ℝ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |affineFn t₀ t₁ x - affineFn s₀ s₁ x| ≤ ‖(![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]‖ := by
  set N := ‖(![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]‖ with hN
  have h0 : |t₀ - s₀| ≤ N := by
    have := norm_le_pi_norm ((![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]) 0
    simpa [hN] using this
  have h1 : |t₁ - s₁| ≤ N := by
    have := norm_le_pi_norm ((![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]) 1
    simpa [hN] using this
  have e : affineFn t₀ t₁ x - affineFn s₀ s₁ x = (1 - x) * (t₀ - s₀) + x * (t₁ - s₁) := by
    simp only [affineFn]; ring
  obtain ⟨hx0, hx1⟩ := hx
  rw [e]
  calc |(1 - x) * (t₀ - s₀) + x * (t₁ - s₁)|
      ≤ |(1 - x) * (t₀ - s₀)| + |x * (t₁ - s₁)| := abs_add_le _ _
    _ = (1 - x) * |t₀ - s₀| + x * |t₁ - s₁| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x), abs_of_nonneg hx0]
    _ ≤ (1 - x) * N + x * N := by
        gcongr
    _ = N := by ring

lemma integral_affine_diff_le (t₀ t₁ s₀ s₁ : ℝ) :
    (∫ x in (0:ℝ)..1, |affineFn t₀ t₁ x - affineFn s₀ s₁ x|) ≤
      ‖(![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]‖ := by
  have hc : Continuous fun x => |affineFn t₀ t₁ x - affineFn s₀ s₁ x| :=
    ((affineFn_continuous t₀ t₁).sub (affineFn_continuous s₀ s₁)).abs
  calc (∫ x in (0:ℝ)..1, |affineFn t₀ t₁ x - affineFn s₀ s₁ x|)
      ≤ ∫ _ in (0:ℝ)..1, ‖(![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]‖ :=
        intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1) fun x hx => affine_diff_le t₀ t₁ s₀ s₁ hx
    _ = ‖(![t₀, t₁] : Fin 2 → ℝ) - ![s₀, s₁]‖ := by simp

/-! ## The canonical distance of the increment family -/

/-- `‖v_q - v_q'‖² ≤ d(f,f')² + 4 d(g,g')²` for `v_q = U(f+g) - U(g)`. -/
lemma dist_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : (ℝ → ℝ) → E) (P : (ℝ → ℝ) → Prop) (hU : ∀ a, P a → ∀ b, P b → ⟪U a, U b⟫ = zCov a b)
    {f g f' g' : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hf' : Continuous f')
    (hg' : Continuous g') (P1 : P f) (P2 : P g) (P3 : P (f + g)) (P4 : P f') (P5 : P g')
    (P6 : P (f' + g')) :
    ‖(U (f + g) - U g) - (U (f' + g') - U g')‖ ^ 2 ≤
      ‖U f - U f'‖ ^ 2 + 4 * ‖U g - U g'‖ ^ 2 := by
  have D : ∀ a b, P a → P b → Continuous a → Continuous b →
      ‖U a - U b‖ ^ 2 = 2 * π * ∫ x in (0:ℝ)..1, |a x - b x| := fun a b ha hb hac hbc =>
    Subadd.zCov_dist_sq U hac hbc (hU a ha a ha) (hU b hb b hb) (hU a ha b hb)
  have hfg : Continuous (f + g) := hf.add hg
  have hfg' : Continuous (f' + g') := hf'.add hg'
  rw [four_point, D _ _ P3 P6 hfg hfg', D _ _ P2 P5 hg hg', D _ _ P3 P5 hfg hg',
    D _ _ P6 P2 hfg' hg, D _ _ P3 P2 hfg hg, D _ _ P6 P5 hfg' hg', D _ _ P1 P4 hf hf']
  have i1 : (∫ x in (0:ℝ)..1, |(f + g) x - (f' + g') x|) ≤
      (∫ x in (0:ℝ)..1, |f x - f' x|) + ∫ x in (0:ℝ)..1, |g x - g' x| :=
    integral_le_add_of_le (hfg.sub hfg').abs (hf.sub hf').abs (hg.sub hg').abs fun x => by
      simp only [Pi.add_apply]
      calc |f x + g x - (f' x + g' x)| = |(f x - f' x) + (g x - g' x)| := by
            congr 1; ring
        _ ≤ _ := abs_add_le _ _
  have i2 : (∫ x in (0:ℝ)..1, |(f + g) x - g x|) ≤
      (∫ x in (0:ℝ)..1, |(f + g) x - g' x|) + ∫ x in (0:ℝ)..1, |g x - g' x| :=
    integral_le_add_of_le (hfg.sub hg).abs (hfg.sub hg').abs (hg.sub hg').abs fun x => by
      rw [abs_sub_comm (g x) (g' x)]
      exact abs_sub_le _ _ _
  have i3 : (∫ x in (0:ℝ)..1, |(f' + g') x - g' x|) ≤
      (∫ x in (0:ℝ)..1, |(f' + g') x - g x|) + ∫ x in (0:ℝ)..1, |g x - g' x| :=
    integral_le_add_of_le (hfg'.sub hg').abs (hfg'.sub hg).abs (hg.sub hg').abs fun x =>
      abs_sub_le _ _ _
  have hpi : 0 ≤ 2 * π := by positivity
  nlinarith [mul_le_mul_of_nonneg_left i1 hpi, mul_le_mul_of_nonneg_left i2 hpi,
    mul_le_mul_of_nonneg_left i3 hpi]

/-! ## Finite Gaussian maxima -/

section VecEM

variable {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma vecEM_congr (F : Finset ι) {v v' : ι → E} {b b' : ι → ℝ} (hv : ∀ i ∈ F, v i = v' i)
    (hb : ∀ i ∈ F, b i = b' i) : vecExpectedMax F v b = vecExpectedMax F v' b' := by
  unfold vecExpectedMax
  congr 1
  funext x
  congr 1
  funext i
  rw [hv i i.2, hb i i.2]

/-- A constant drift comes out of the expected maximum. -/
lemma vecEM_const (F : Finset ι) (hF : F.Nonempty) (v : ι → E) (c : ℝ) :
    vecExpectedMax F v (fun _ => c) = vecExpectedMax F v 0 + c := by
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i, x⟫ + c) = (⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) + c := by
    intro x
    rw [ciSup_add (Finite.bddAbove_range _)]
    simp
  unfold vecExpectedMax
  calc ∫ x, (⨆ i : F, ⟪v i, x⟫ + c) ∂stdGaussian E
      = ∫ x, ((⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) + c) ∂stdGaussian E := by
        congr 1; funext x; exact hpt x
    _ = _ := by
        rw [integral_add (integrable_iSup_inner_add F v 0) (integrable_const c), integral_const,
          probReal_univ, one_smul]

/-- A family of pairs is dominated by the sum of the two marginal families. -/
lemma vecEM_prod_le {E' : Type} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (F : Finset ι) (v₁ : ι → E) (v₂ : ι → E') (b : ι → ℝ) :
    vecExpectedMax F (fun i => (WithLp.toLp 2 (v₁ i, v₂ i) : WithLp 2 (E × E'))) b ≤
      vecExpectedMax F v₁ b + vecExpectedMax F v₂ 0 := by
  calc vecExpectedMax F (fun i => (WithLp.toLp 2 (v₁ i, v₂ i) : WithLp 2 (E × E'))) b
      = vecExpectedMax F (fun i => (WithLp.toLp 2 (v₁ i, (0 : E')) : WithLp 2 (E × E')) +
          WithLp.toLp 2 ((0 : E), v₂ i)) (fun i => b i + (0 : ι → ℝ) i) := by
        congr 1
        · funext i; rw [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
        · funext i; simp
    _ ≤ vecExpectedMax F (fun i => (WithLp.toLp 2 (v₁ i, (0 : E')) : WithLp 2 (E × E'))) b +
          vecExpectedMax F (fun i => (WithLp.toLp 2 ((0 : E), v₂ i) : WithLp 2 (E × E'))) 0 :=
        Subadd.vecEM_add_le maxIntegrable F _ _ b 0
    _ = vecExpectedMax F v₁ b + vecExpectedMax F v₂ 0 := by
        congr 1
        · exact vecExpectedMax_eq_of_gram_eq F _ _ b fun i _ j _ => by simp
        · exact vecExpectedMax_eq_of_gram_eq F _ _ 0 fun i _ j _ => by simp

/-- Chaining bound for a family with a two-dimensional Hölder-`1/2` parametrization. -/
lemma vecEM_le_chain (F : Finset ι) (w : ι → E) (p : ι → Fin 2 → ℝ) {L a : ℝ} (hL : 0 ≤ L)
    (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hw : ∀ i ∈ F, ∀ j ∈ F, ‖w i - w j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    vecExpectedMax F w 0 ≤ 20 * √5 * L * √((((2:ℕ):ℝ) + 1) * a) := by
  refine le_trans ?_ (ChainBox.chainingBox_bound F p w hL hp hw hi₀)
  refine sudakovFernique ι E E F w (fun i => w i - w i₀) 0 fun i _ j _ => ?_
  rw [sub_sub_sub_cancel_right]

/-- A family `U ∘ φ` with `φ` valued in `V n` and `U` a Gram representation of `zCov`. -/
lemma vecEM_toV (n : ℕ) (F : Finset ι) (φ : ι → V n) (U : (ℝ → ℝ) → E)
    (hU : ∀ i ∈ F, ∀ j ∈ F, ⟪U (φ i), U (φ j)⟫ = zCov (φ i) (φ j)) (β : V n → ℝ) :
    vecExpectedMax F (fun i => U (φ i)) (fun i => β (φ i)) =
      gaussianExpectedMax (F.image φ) (fun f g => zCov f g) β := by
  classical
  rw [Subadd.vecEM_comp_image F φ (fun f : V n => U f) β,
    ← gramBridge (V n) E (F.image φ) (fun f => U f) β]
  apply gaussianExpectedMax_congr
  intro f hf f' hf'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hf
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hf'
  exact hU i hi j hj

end VecEM

/-! ## The comparison -/

/-- The chaining constant. -/
def chainConst (A : ℝ) : ℝ := 20 * √5 * √(8 * π) * √((((2:ℕ):ℝ) + 1) * (2 * A))

lemma chainConst_nonneg (A : ℝ) : 0 ≤ chainConst A := by
  unfold chainConst; positivity

/-- **Core comparison.**  `E max_q (Z_{f+g} - Z_g + b) ≤ E max_q (Z_f + b) + chainConst A`. -/
lemma core_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : (ℝ → ℝ) → E) (P : (ℝ → ℝ) → Prop) (hU : ∀ a, P a → ∀ b, P b → ⟪U a, U b⟫ = zCov a b)
    (F : Finset ((ℝ → ℝ) × ℝ × ℝ)) (hFne : F.Nonempty) (A : ℝ)
    (hF : ∀ q ∈ F, Continuous q.1 ∧ P q.1 ∧ P (affineFn q.2.1 q.2.2) ∧
      P (q.1 + affineFn q.2.1 q.2.2) ∧ |q.2.1| ≤ A ∧ |q.2.2| ≤ A)
    (b : ℝ) :
    gaussianExpectedMax F
        (fun q q' => zDiffCov q.1 (affineFn q.2.1 q.2.2) q'.1 (affineFn q'.2.1 q'.2.2))
        (fun _ => b) ≤
      vecExpectedMax F (fun q => U q.1) (fun _ => b) + chainConst A := by
  let v : ((ℝ → ℝ) × ℝ × ℝ) → E := fun q => U (q.1 + affineFn q.2.1 q.2.2) - U (affineFn q.2.1 q.2.2)
  let w : ((ℝ → ℝ) × ℝ × ℝ) → WithLp 2 (E × E) := fun q =>
    WithLp.toLp 2 (U q.1, (2:ℝ) • U (affineFn q.2.1 q.2.2))
  -- Step 1: Gram vectors of the increment family
  have step1 : gaussianExpectedMax F
      (fun q q' => zDiffCov q.1 (affineFn q.2.1 q.2.2) q'.1 (affineFn q'.2.1 q'.2.2))
      (fun _ => b) = vecExpectedMax F v (fun _ => b) := by
    rw [← gramBridge ((ℝ → ℝ) × ℝ × ℝ) E F v]
    apply gaussianExpectedMax_congr
    intro q hq q' hq'
    obtain ⟨-, -, Pg, Pfg, -, -⟩ := hF q hq
    obtain ⟨-, -, Pg', Pfg', -, -⟩ := hF q' hq'
    simp only [v, inner_sub_left, inner_sub_right]
    rw [hU _ Pfg _ Pfg', hU _ Pfg _ Pg', hU _ Pg _ Pfg', hU _ Pg _ Pg']
    simp only [zDiffCov]
    ring
  -- Step 2: Sudakov–Fernique against the pair family
  have step2 : vecExpectedMax F v (fun _ => b) ≤ vecExpectedMax F w (fun _ => b) := by
    refine sudakovFernique ((ℝ → ℝ) × ℝ × ℝ) E (WithLp 2 (E × E)) F v w (fun _ => b) fun q hq q' hq' => ?_
    obtain ⟨hc, Pf, Pg, Pfg, -, -⟩ := hF q hq
    obtain ⟨hc', Pf', Pg', Pfg', -, -⟩ := hF q' hq'
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hw : ‖w q - w q'‖ ^ 2 = ‖U q.1 - U q'.1‖ ^ 2 +
        4 * ‖U (affineFn q.2.1 q.2.2) - U (affineFn q'.2.1 q'.2.2)‖ ^ 2 := by
      simp only [w]
      rw [← WithLp.toLp_sub, WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, Prod.fst_sub, Prod.snd_sub]
      rw [← smul_sub, norm_smul, mul_pow]
      norm_num
    rw [hw]
    exact dist_sq_le U P hU hc (affineFn_continuous _ _) hc' (affineFn_continuous _ _)
      Pf Pg Pfg Pf' Pg' Pfg'
  -- Step 3: split the pair family
  have step3 := vecEM_prod_le F (fun q => U q.1) (fun q => (2:ℝ) • U (affineFn q.2.1 q.2.2))
    (fun _ => b)
  -- Step 4: chaining for the endpoint part
  obtain ⟨q₀, hq₀⟩ := hFne
  have step4 : vecExpectedMax F (fun q => (2:ℝ) • U (affineFn q.2.1 q.2.2)) 0 ≤
      chainConst A := by
    have hL : (0:ℝ) ≤ √(8 * π) := Real.sqrt_nonneg _
    have h := vecEM_le_chain F (fun q => (2:ℝ) • U (affineFn q.2.1 q.2.2))
      (fun q => ![q.2.1, q.2.2]) (a := 2 * A) hL ?_ ?_ hq₀
    · refine h.trans (le_of_eq ?_)
      unfold chainConst
      ring
    · intro i hi j hj
      obtain ⟨-, -, -, -, hi1, hi2⟩ := hF i hi
      obtain ⟨-, -, -, -, hj1, hj2⟩ := hF j hj
      have hA : 0 ≤ A := (abs_nonneg _).trans hi1
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
      have k1 := abs_le.1 hi1
      have k2 := abs_le.1 hi2
      have k3 := abs_le.1 hj1
      have k4 := abs_le.1 hj2
      fin_cases m
      · simp only [Fin.zero_eta, Pi.sub_apply, Matrix.cons_val_zero, Real.norm_eq_abs]
        rw [abs_le]; constructor <;> linarith
      · simp only [Fin.mk_one, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
          Real.norm_eq_abs]
        rw [abs_le]; constructor <;> linarith
    · intro i hi j hj
      obtain ⟨-, -, Pg, -, -, -⟩ := hF i hi
      obtain ⟨-, -, Pg', -, -, -⟩ := hF j hj
      rw [← smul_sub, norm_smul, mul_pow, Real.sq_sqrt (by positivity),
        Subadd.zCov_dist_sq U (affineFn_continuous _ _) (affineFn_continuous _ _)
          (hU _ Pg _ Pg) (hU _ Pg' _ Pg') (hU _ Pg _ Pg')]
      have hI := integral_affine_diff_le i.2.1 i.2.2 j.2.1 j.2.2
      have h8 : (0:ℝ) ≤ 8 * π := by positivity
      have := mul_le_mul_of_nonneg_left hI h8
      have h2 : ‖(2:ℝ)‖ ^ 2 = 4 := by norm_num
      rw [h2]
      linarith
  rw [step1]
  refine step2.trans (step3.trans ?_)
  exact add_le_add le_rfl step4

/-! ## Numerical facts -/

lemma rpow_quarter_le {k : ℝ} (hk : 0 ≤ k) :
    (k + 2) ^ (1/4 : ℝ) ≤ 2 * (k + 1) ^ (1/4 : ℝ) := by
  have h1 : (k + 2) ^ (1/4:ℝ) ≤ (2 * (k + 1)) ^ (1/4:ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have h2 : (2:ℝ) ^ (1/4:ℝ) ≤ 2 := by
    calc (2:ℝ) ^ (1/4:ℝ) ≤ 2 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _))

end L33

open L33 in
/-- **Lemma 3.3** (node `L33`), from finiteness and subadditivity of `a_n` and `(2.2)`. -/
theorem lemma33_of (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE)
    (hS : Blueprint.ZSupBound) : Blueprint.Draft.Lemma33 := by
  classical
  intro C₀
  obtain ⟨Cs, hCs⟩ := hS
  have hCch0 := chainConst_nonneg |C₀|
  refine ⟨2 + chainConst |C₀| + 2 * max Cs 0, fun n hn k F hFne hF => ?_⟩
  -- `a_n` is finite and bounds every finite family
  have ha1nb : aE 1 ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Bounds.aE_nonneg 1)
  have ha1 : aE 1 = ((aE 1).toReal : EReal) := (EReal.coe_toReal h1 ha1nb).symm
  obtain ⟨an, han, -⟩ := Bounds.aE_finite_le h2 ha1 n hn
  have hGa : ∀ G : Finset (V n),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ a n := by
    intro G
    have hG : ((gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal)
        ≤ aE n :=
      le_iSup (fun G : Finset (V n) => ((gaussianExpectedMax G (fun f g => zCov f g)
        (fun f => -energy f) : ℝ) : EReal)) G
    rw [han] at hG
    have e : a n = an := by rw [a, han, EReal.toReal_coe]
    rw [e]
    exact EReal.coe_le_coe_iff.1 hG
  -- the Gram representation
  set S : Finset (ℝ → ℝ) := F.image Prod.fst ∪ F.image (fun q => affineFn q.2.1 q.2.2) ∪
    F.image (fun q => q.1 + affineFn q.2.1 q.2.2) with hSdef
  have hcont : ∀ q ∈ F, Continuous q.1 := fun q hq => Subadd.V_continuous (hF q hq).1
  have hScont : ∀ a ∈ S, Continuous a := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
        exact hcont q hq
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
        exact affineFn_continuous _ _
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
      exact (hcont q hq).add (affineFn_continuous _ _)
  obtain ⟨U, hU⟩ := gramRepresentation (ℝ → ℝ) S zCov
    (zCovPSD S fun a ha => (hScont a ha).intervalIntegrable 0 1)
  have m1 : ∀ q ∈ F, q.1 ∈ S := fun q hq =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
  have m2 : ∀ q ∈ F, affineFn q.2.1 q.2.2 ∈ S := fun q hq =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun q => affineFn q.2.1 q.2.2) hq))
  have m3 : ∀ q ∈ F, q.1 + affineFn q.2.1 q.2.2 ∈ S := fun q hq =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun q => q.1 + affineFn q.2.1 q.2.2) hq)
  have hM : (1:ℝ) ≤ (16:ℝ) ^ (2 * n) := one_le_pow₀ (by norm_num)
  have hend : ∀ t : ℝ, |t| ≤ C₀ / (16:ℝ) ^ (2 * n) → |t| ≤ |C₀| := fun t ht =>
    ht.trans ((div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
      (div_le_self (abs_nonneg _) hM))
  have hcore := core_bound U (· ∈ S) hU F hFne |C₀| (fun q hq => ⟨hcont q hq, m1 q hq, m2 q hq,
    m3 q hq, hend _ (hF q hq).2.2.1, hend _ (hF q hq).2.2.2⟩) (-(k:ℝ))
  -- pass to `V n`
  have hφ : ∀ q ∈ F, ((toV n q.1 : V n) : ℝ → ℝ) = q.1 := fun q hq => toV_coe (hF q hq).1
  have hUφ : ∀ i ∈ F, ∀ j ∈ F, ⟪U (toV n i.1), U (toV n j.1)⟫ =
      zCov (toV n i.1) (toV n j.1) := by
    intro i hi j hj
    rw [hφ i hi, hφ j hj]
    exact hU _ (m1 i hi) _ (m1 j hj)
  have hswap : vecExpectedMax F (fun q => U q.1) (fun _ => -(k:ℝ)) =
      vecExpectedMax F (fun q => U (toV n q.1)) (fun _ => -(k:ℝ)) :=
    vecEM_congr F (fun q hq => by rw [hφ q hq]) (fun _ _ => rfl)
  rw [hswap] at hcore
  refine le_min ?_ ?_
  · -- first bound: `a_n + C`
    have hA : vecExpectedMax F (fun q => U (toV n q.1)) (fun _ => -(k:ℝ)) ≤ a n + 2 := by
      refine (Bounds.vecEM_le_add_const F (fun q => U (toV n q.1)) (fun _ => -(k:ℝ))
        (fun q => -energy (toV n q.1)) (by norm_num : (0:ℝ) ≤ 2) fun q hq => ?_).trans ?_
      · rw [hφ q hq]
        have := (hF q hq).2.1
        linarith
      · rw [vecEM_toV n F (fun q => toV n q.1) U hUφ (fun f => -energy f)]
        linarith [hGa (F.image fun q => toV n q.1)]
    have := le_max_right Cs 0
    linarith
  · -- second bound: `C n^{3/4} (k+1)^{1/4} - k + C`
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hB : vecExpectedMax F (fun q => U (toV n q.1)) (fun _ => -(k:ℝ)) ≤
        Cs * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 2) ^ (1/4:ℝ) - k := by
      rw [vecEM_const F hFne]
      have e := vecEM_toV n F (fun q => toV n q.1) U hUφ 0
      have hZ := hCs n hn ((k:ℝ) + 2) (by positivity) (F.image fun q => toV n q.1) (by
        intro f hf
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hf
        rw [hφ q hq]
        exact (hF q hq).2.1)
      have e' : vecExpectedMax F (fun q => U (toV n q.1)) 0 =
          gaussianExpectedMax (F.image fun q => toV n q.1) (fun f g => zCov f g) 0 := e
      rw [e']
      linarith
    have hn34 : 0 ≤ (n:ℝ) ^ (3/4:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hk14 : 0 ≤ ((k:ℝ) + 1) ^ (1/4:ℝ) := Real.rpow_nonneg (by positivity) _
    have hk24 : 0 ≤ ((k:ℝ) + 2) ^ (1/4:ℝ) := Real.rpow_nonneg (by positivity) _
    have hq := rpow_quarter_le hk0
    have hmax : Cs * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 2) ^ (1/4:ℝ) ≤
        max Cs 0 * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 2) ^ (1/4:ℝ) := by
      have := le_max_left Cs 0
      have := mul_nonneg hn34 hk24
      nlinarith
    have hmax2 : max Cs 0 * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 2) ^ (1/4:ℝ) ≤
        (2 + chainConst |C₀| + 2 * max Cs 0) * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 1) ^ (1/4:ℝ) := by
      have hm0 := le_max_right Cs 0
      have h3 : max Cs 0 * (n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 2) ^ (1/4:ℝ) ≤
          max Cs 0 * (n:ℝ) ^ (3/4:ℝ) * (2 * ((k:ℝ) + 1) ^ (1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hm0 hn34)
      have h4 : 0 ≤ (2 + chainConst |C₀|) * ((n:ℝ) ^ (3/4:ℝ) * ((k:ℝ) + 1) ^ (1/4:ℝ)) :=
        mul_nonneg (by linarith) (mul_nonneg hn34 hk14)
      nlinarith
    have := le_max_right Cs 0
    linarith

/-- **Lemma 3.3** (node `L33`), unconditionally. -/
theorem lemma33 : Blueprint.Draft.Lemma33 :=
  lemma33_of aOneFinite aSubadditiveE (zSupBound_of aOneFinite aSubadditiveE)

end LQGDimension
