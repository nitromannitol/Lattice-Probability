/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ExpectedSupLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.Chatterjee
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of covariances implies asymptotic domination of expected maxima (node `ESL`)

We prove `Blueprint.Draft.ExpectedSupLimit` from `Blueprint.Draft.ExpectedMaxCovLipschitz`
(node `G6`, proved in `LQGDimension.Gaussian.Chatterjee`) and the chaining bound on a box
(`ChainBox.chainingBox_bound`, node `G4`).

Given `θ > 0`:
* `K ⊆ q₀ + [-a, a]^d`; the level-`k` cells `cell a k` (from `ChainingBox`) have sup-diameter
  `< η = a / 4^k` and at most `n = (4^{k+1})^d` of them meet `K`.  Each point `p ∈ K` is sent to a
  fixed point `π p ∈ K` of its cell (`netProj`).
* For a finite `F ⊆ K`, realise the covariance `Cδ δ` on `F ∪ π(F)` by Gram vectors `v`.  Then
  `E max_F (X + bδ) ≤ E max_{π(F)} (X + bδ) + E max_{p ∈ F} ⟪v p - v (π p), x⟫ + osc`, where the
  oscillation of the drift is `≤ 2γ + θ/4` by uniform convergence and uniform continuity of `b`.
* The middle term is a chaining term: in the parameter
  `P p = (p - π p, η · (binary code of the cell of p)) ∈ ℝ^{d + 2(k+1)d}` the family
  `w p = v p - v (π p)` satisfies `‖w p - w q‖² ≤ 4 L ‖P p - P q‖` with `diam P ≤ 2η`, so by
  `chainingBox_bound` it is `≤ 40 √5 √L √((3d + 2kd + 1) 2η) → 0` as `k → ∞`.
* On `G = π(F)`, which has at most `n` points, `G6` compares `Cδ δ` with `C`:
  the error is `≤ 2 √(2 γ log n)`, small once `γ` is small; and `bδ → b` uniformly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

namespace ESLimit

open ChainBox

/-! ### Elementary comparisons of expected maxima -/

/-- Recentering a centered family at one of its members does not change `E max`
(Sudakov–Fernique in both directions: the canonical distances agree). -/
lemma vecExpectedMax_le_sub {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (w : ι → E) (i₀ : ι) :
    vecExpectedMax F w 0 ≤ vecExpectedMax F (fun i => w i - w i₀) 0 :=
  sudakovFernique ι E E F w (fun i => w i - w i₀) 0 fun i _ j _ => by
    rw [sub_sub_sub_cancel_right]

section Gaussian

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Projection of the index set: `E max_F (X + c) ≤ E max_G (X + c) + E max_F (X_p - X_{π p})
+ B` whenever `π` maps `F` into `G` and `c p - c (π p) ≤ B` on `F`. -/
lemma vecExpectedMax_le_proj (F G : Finset ι) (hF : F.Nonempty) (pr : ι → ι)
    (hπ : ∀ p ∈ F, pr p ∈ G) (v : ι → E) (c : ι → ℝ) {B : ℝ}
    (hB : ∀ p ∈ F, c p - c (pr p) ≤ B) :
    vecExpectedMax F v c ≤
      vecExpectedMax G v c + vecExpectedMax F (fun p => v p - v (pr p)) 0 + B := by
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i, x⟫ + c i) ≤
      ((⨆ q : G, ⟪v q, x⟫ + c q) + (⨆ i : F, ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i)) + B := by
    intro x
    refine ciSup_le fun i => ?_
    have h1 : ⟪v (pr i), x⟫ + c (pr i) ≤ ⨆ q : G, ⟪v q, x⟫ + c q :=
      le_ciSup (f := fun q : G => ⟪v q, x⟫ + c q) (Set.finite_range _).bddAbove
        ⟨pr i, hπ i i.2⟩
    have h2 : ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i ≤
        ⨆ j : F, ⟪v j - v (pr j), x⟫ + (0 : ι → ℝ) j :=
      le_ciSup (f := fun j : F => ⟪v j - v (pr j), x⟫ + (0 : ι → ℝ) j)
        (Set.finite_range _).bddAbove i
    have e : ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i = ⟪v i, x⟫ - ⟪v (pr i), x⟫ := by
      rw [inner_sub_left, Pi.zero_apply, add_zero]
    rw [e] at h2
    have h3 := hB i i.2
    linarith
  have hG := integrable_iSup_inner_add G v c
  have hW : Integrable (fun x => ⨆ i : F, ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i)
      (stdGaussian E) := integrable_iSup_inner_add F (fun p => v p - v (pr p)) 0
  unfold vecExpectedMax
  beta_reduce
  calc ∫ x, (⨆ i : F, ⟪v i, x⟫ + c i) ∂(stdGaussian E)
      ≤ ∫ x, (((⨆ q : G, ⟪v q, x⟫ + c q) +
          (⨆ i : F, ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i)) + B) ∂(stdGaussian E) :=
        integral_mono (integrable_iSup_inner_add F v c)
          ((hG.fun_add hW).fun_add (integrable_const B)) hpt
    _ = (∫ x, (⨆ q : G, ⟪v q, x⟫ + c q) ∂(stdGaussian E)) +
          (∫ x, (⨆ i : F, ⟪v i - v (pr i), x⟫ + (0 : ι → ℝ) i) ∂(stdGaussian E)) + B := by
        rw [integral_add (hG.fun_add hW) (integrable_const B), integral_add hG hW,
          integral_const]
        simp

/-- Changing the drift by at most `γ` changes `E max` by at most `γ`. -/
lemma vecExpectedMax_le_of_drift_le (G : Finset ι) (hG : G.Nonempty) (v : ι → E)
    (c c' : ι → ℝ) {γ : ℝ} (h : ∀ q ∈ G, c q ≤ c' q + γ) :
    vecExpectedMax G v c ≤ vecExpectedMax G v c' + γ := by
  have : Nonempty G := hG.to_subtype
  have hpt : ∀ x : E, (⨆ q : G, ⟪v q, x⟫ + c q) ≤ (⨆ q : G, ⟪v q, x⟫ + c' q) + γ := by
    intro x
    refine ciSup_le fun q => ?_
    have h1 : ⟪v q, x⟫ + c' q ≤ ⨆ q : G, ⟪v q, x⟫ + c' q :=
      le_ciSup (f := fun q : G => ⟪v q, x⟫ + c' q) (Set.finite_range _).bddAbove q
    linarith [h q q.2]
  unfold vecExpectedMax
  calc ∫ x, (⨆ q : G, ⟪v q, x⟫ + c q) ∂(stdGaussian E)
      ≤ ∫ x, ((⨆ q : G, ⟪v q, x⟫ + c' q) + γ) ∂(stdGaussian E) :=
        integral_mono (integrable_iSup_inner_add G v c)
          ((integrable_iSup_inner_add G v c').add (integrable_const γ)) hpt
    _ = _ := by
        rw [integral_add (integrable_iSup_inner_add G v c') (integrable_const γ), integral_const]
        simp

end Gaussian

/-! ### The net and the chaining parameter -/

section Net

variable {d : ℕ}

open scoped Classical in
/-- A fixed point of `K` in the level-`k` cell `c` (or `q₀` if there is none). -/
def netRep (K : Set (Fin d → ℝ)) (q₀ : Fin d → ℝ) (a : ℝ) (k : ℕ) (c : Fin d → ℤ) :
    Fin d → ℝ :=
  if h : ∃ q ∈ K, cell a k q = c then h.choose else q₀

/-- The net point attached to `p`: the representative of its level-`k` cell. -/
def netProj (K : Set (Fin d → ℝ)) (q₀ : Fin d → ℝ) (a : ℝ) (k : ℕ) (p : Fin d → ℝ) :
    Fin d → ℝ :=
  netRep K q₀ a k (cell a k p)

open scoped Classical in
/-- The index of a cell of the box `box a k q₀` (and `0` outside the box). -/
def cellIdx (q₀ : Fin d → ℝ) (a : ℝ) (k : ℕ) (c : Fin d → ℤ) : ℕ :=
  if h : c ∈ box a k q₀ then (Fintype.equivFin (box a k q₀) ⟨c, h⟩ : ℕ) else 0

/-- The chaining parameter `(p - π p, η · bits of the cell index of p)`, `η = a / 4^k`. -/
def netParam (K : Set (Fin d → ℝ)) (q₀ : Fin d → ℝ) (a : ℝ) (k : ℕ) (p : Fin d → ℝ) :
    Fin (d + 2 * (k + 1) * d) → ℝ :=
  Fin.append (p - netProj K q₀ a k p)
    (fun j => if (cellIdx q₀ a k (cell a k p)).testBit j then a / 4 ^ k else 0)

variable {K : Set (Fin d → ℝ)} {q₀ : Fin d → ℝ} {a : ℝ} {k : ℕ}

lemma netProj_mem (hq₀ : q₀ ∈ K) (p : Fin d → ℝ) : netProj K q₀ a k p ∈ K := by
  unfold netProj netRep
  split_ifs with h
  · exact h.choose_spec.1
  · exact hq₀

lemma cell_netProj {p : Fin d → ℝ} (hp : p ∈ K) :
    cell a k (netProj K q₀ a k p) = cell a k p := by
  have h : ∃ q ∈ K, cell a k q = cell a k p := ⟨p, hp, rfl⟩
  unfold netProj netRep
  rw [dite_eq_left h]
  exact h.choose_spec.2

lemma norm_netProj_sub_lt (ha : 0 < a) {p : Fin d → ℝ} (hp : p ∈ K) :
    ‖netProj K q₀ a k p - p‖ < a / 4 ^ k :=
  norm_sub_lt_of_cell_eq ha k (cell_netProj hp)

lemma cellIdx_lt {c : Fin d → ℤ} (hc : c ∈ box a k q₀) :
    cellIdx q₀ a k c < 2 ^ (2 * (k + 1) * d) := by
  unfold cellIdx
  rw [dite_eq_left hc]
  refine lt_of_lt_of_le (Fin.is_lt _) ?_
  rw [Fintype.card_coe]
  refine (card_box_le a k q₀).trans (le_of_eq ?_)
  rw [pow_mul, pow_mul]
  norm_num

lemma cellIdx_injOn {c c' : Fin d → ℤ} (hc : c ∈ box a k q₀) (hc' : c' ∈ box a k q₀)
    (h : cellIdx q₀ a k c = cellIdx q₀ a k c') : c = c' := by
  unfold cellIdx at h
  rw [dite_eq_left hc, dite_eq_left hc'] at h
  exact Subtype.mk.inj ((Fintype.equivFin (box a k q₀)).injective (Fin.ext h))

lemma exists_testBit_ne {m n n' : ℕ} (hn : n < 2 ^ m) (hn' : n' < 2 ^ m) (hne : n ≠ n') :
    ∃ j < m, n.testBit j ≠ n'.testBit j := by
  by_contra hcon
  apply hne
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < m
  · by_contra h'
    exact hcon ⟨j, hj, h'⟩
  · have hmj : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hj)
    rw [Nat.testBit_lt_two_pow (hn.trans_le hmj),
      Nat.testBit_lt_two_pow (hn'.trans_le hmj)]

lemma netParam_sub_left (p p' : Fin d → ℝ) (i : Fin d) :
    (netParam K q₀ a k p - netParam K q₀ a k p') (Fin.castAdd _ i) =
      (p i - netProj K q₀ a k p i) - (p' i - netProj K q₀ a k p' i) := by
  simp only [netParam, Pi.sub_apply, Fin.append_left]

lemma netParam_sub_right (p p' : Fin d → ℝ) (j : Fin (2 * (k + 1) * d)) :
    (netParam K q₀ a k p - netParam K q₀ a k p') (Fin.natAdd d j) =
      (if (cellIdx q₀ a k (cell a k p)).testBit j then a / 4 ^ k else 0) -
      (if (cellIdx q₀ a k (cell a k p')).testBit j then a / 4 ^ k else 0) := by
  simp only [netParam, Pi.sub_apply, Fin.append_right]

lemma norm_netParam_sub_le (ha : 0 < a) {p p' : Fin d → ℝ} (hp : p ∈ K) (hp' : p' ∈ K) :
    ‖netParam K q₀ a k p - netParam K q₀ a k p'‖ ≤ 2 * (a / 4 ^ k) := by
  have hη : 0 < a / 4 ^ k := by positivity
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [netParam_sub_left, Real.norm_eq_abs]
    have h1 := norm_netProj_sub_lt (q₀ := q₀) (k := k) ha hp
    have h2 := norm_netProj_sub_lt (q₀ := q₀) (k := k) ha hp'
    have e1 := (norm_le_pi_norm (netProj K q₀ a k p - p) i).trans h1.le
    have e2 := (norm_le_pi_norm (netProj K q₀ a k p' - p') i).trans h2.le
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le] at e1 e2
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · rw [netParam_sub_right, Real.norm_eq_abs]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma norm_sub_le_netParam_of_cell_eq {p p' : Fin d → ℝ} (h : cell a k p = cell a k p') :
    ‖p - p'‖ ≤ ‖netParam K q₀ a k p - netParam K q₀ a k p'‖ := by
  have hπ : netProj K q₀ a k p = netProj K q₀ a k p' := by unfold netProj; rw [h]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have := norm_le_pi_norm (netParam K q₀ a k p - netParam K q₀ a k p') (Fin.castAdd _ i)
  rw [netParam_sub_left, hπ] at this
  have e : (p i - netProj K q₀ a k p' i) - (p' i - netProj K q₀ a k p' i) = (p - p') i := by
    rw [Pi.sub_apply]; ring
  rwa [e] at this

lemma le_norm_netParam_sub_of_cell_ne (ha : 0 < a) {p p' : Fin d → ℝ} (hp : p ∈ K)
    (hp' : p' ∈ K) (hqa : ∀ q ∈ K, ‖q - q₀‖ ≤ a) (h : cell a k p ≠ cell a k p') :
    a / 4 ^ k ≤ ‖netParam K q₀ a k p - netParam K q₀ a k p'‖ := by
  have hb := cell_mem_box ha k (hqa p hp)
  have hb' := cell_mem_box ha k (hqa p' hp')
  have hne : cellIdx q₀ a k (cell a k p) ≠ cellIdx q₀ a k (cell a k p') :=
    fun heq => h (cellIdx_injOn hb hb' heq)
  obtain ⟨j, hj, hbit⟩ := exists_testBit_ne (cellIdx_lt hb) (cellIdx_lt hb') hne
  have hle := norm_le_pi_norm (netParam K q₀ a k p - netParam K q₀ a k p')
    (Fin.natAdd d ⟨j, hj⟩)
  rw [netParam_sub_right] at hle
  refine le_trans ?_ hle
  have hη : 0 < a / 4 ^ k := by positivity
  rw [Real.norm_eq_abs]
  cases h1 : (cellIdx q₀ a k (cell a k p)).testBit j <;>
    cases h2 : (cellIdx q₀ a k (cell a k p')).testBit j
  · rw [h1, h2] at hbit; exact absurd rfl hbit
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_sub, abs_neg, abs_of_pos hη, le_refl]
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, abs_of_pos hη, le_refl]
  · rw [h1, h2] at hbit; exact absurd rfl hbit

/-- **The chaining term.** -/
lemma chain_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ha : 0 < a) (hqa : ∀ q ∈ K, ‖q - q₀‖ ≤ a) {F : Finset (Fin d → ℝ)} (hFK : ↑F ⊆ K)
    (hF : F.Nonempty) (v : (Fin d → ℝ) → E) {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ p ∈ F ∪ F.image (netProj K q₀ a k), ∀ q ∈ F ∪ F.image (netProj K q₀ a k),
      ‖v p - v q‖ ^ 2 ≤ L * ‖p - q‖) :
    vecExpectedMax F (fun p => v p - v (netProj K q₀ a k p)) 0 ≤
      20 * √5 * (2 * √L) * √((((d + 2 * (k + 1) * d : ℕ) : ℝ) + 1) * (2 * (a / 4 ^ k))) := by
  have hη : 0 < a / 4 ^ k := by positivity
  have hmemF : ∀ p ∈ F, p ∈ F ∪ F.image (netProj K q₀ a k) := fun p hp =>
    Finset.mem_union_left _ hp
  have hmemG : ∀ p ∈ F, netProj K q₀ a k p ∈ F ∪ F.image (netProj K q₀ a k) := fun p hp =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  have hw1 : ∀ p ∈ F, ‖v p - v (netProj K q₀ a k p)‖ ^ 2 ≤ L * (a / 4 ^ k) := by
    intro p hp
    have h := hv p (hmemF p hp) _ (hmemG p hp)
    have h2 : ‖p - netProj K q₀ a k p‖ < a / 4 ^ k := by
      rw [norm_sub_rev]; exact norm_netProj_sub_lt ha (hFK hp)
    exact h.trans (mul_le_mul_of_nonneg_left h2.le hL)
  have hwv : ∀ i ∈ F, ∀ j ∈ F,
      ‖(v i - v (netProj K q₀ a k i)) - (v j - v (netProj K q₀ a k j))‖ ^ 2 ≤
        (2 * √L) ^ 2 * ‖netParam K q₀ a k i - netParam K q₀ a k j‖ := by
    intro i hi j hj
    rw [mul_pow, Real.sq_sqrt hL]
    have hPn := norm_nonneg (netParam K q₀ a k i - netParam K q₀ a k j)
    by_cases hc : cell a k i = cell a k j
    · have hπij : netProj K q₀ a k i = netProj K q₀ a k j := by unfold netProj; rw [hc]
      have e : (v i - v (netProj K q₀ a k i)) - (v j - v (netProj K q₀ a k j)) = v i - v j := by
        rw [hπij]; abel
      rw [e]
      have h1 := hv i (hmemF i hi) j (hmemF j hj)
      have h2 : ‖i - j‖ ≤ ‖netParam K q₀ a k i - netParam K q₀ a k j‖ :=
        norm_sub_le_netParam_of_cell_eq hc
      nlinarith
    · have h1 := hw1 i hi
      have h2 := hw1 j hj
      have h3 : a / 4 ^ k ≤ ‖netParam K q₀ a k i - netParam K q₀ a k j‖ :=
        le_norm_netParam_sub_of_cell_ne ha (hFK hi) (hFK hj) hqa hc
      set x := v i - v (netProj K q₀ a k i)
      set y := v j - v (netProj K q₀ a k j)
      have h4 : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        nlinarith [norm_sub_le x y, norm_nonneg (x - y), norm_nonneg x, norm_nonneg y,
          sq_nonneg (‖x‖ - ‖y‖)]
      nlinarith
  have hdiam : ∀ i ∈ F, ∀ j ∈ F,
      ‖netParam K q₀ a k i - netParam K q₀ a k j‖ ≤ 2 * (a / 4 ^ k) :=
    fun i hi j hj => norm_netParam_sub_le ha (hFK hi) (hFK hj)
  obtain ⟨p₀, hp₀⟩ := hF
  calc vecExpectedMax F (fun p => v p - v (netProj K q₀ a k p)) 0
      ≤ vecExpectedMax F (fun i => (v i - v (netProj K q₀ a k i)) -
          (v p₀ - v (netProj K q₀ a k p₀))) 0 :=
        vecExpectedMax_le_sub F (fun p => v p - v (netProj K q₀ a k p)) p₀
    _ ≤ _ := chainingBox_bound F (netParam K q₀ a k) (fun p => v p - v (netProj K q₀ a k p))
        (by positivity) hdiam hwv hp₀

end Net

/-- The chaining error tends to `0` as the level `k → ∞`. -/
lemma tendsto_chain_bound (d : ℕ) (a L : ℝ) :
    Tendsto (fun k : ℕ => 20 * √5 * (2 * √L) *
      √((((d + 2 * (k + 1) * d : ℕ) : ℝ) + 1) * (2 * (a / 4 ^ k)))) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
  have hg : Tendsto (fun k : ℕ => (((d + 2 * (k + 1) * d : ℕ) : ℝ) + 1) * (2 * (a / 4 ^ k)))
      atTop (𝓝 0) := by
    have := (h0.const_mul (2 * a * (3 * d + 1))).add (h1.const_mul (4 * a * d))
    simp only [mul_zero, add_zero] at this
    refine Tendsto.congr (fun k => ?_) this
    push_cast
    field_simp
    ring
  have := ((Real.continuous_sqrt.tendsto 0).comp hg).const_mul (20 * √5 * (2 * √L))
  simpa using this

end ESLimit

open ESLimit ChainBox

/-- **Node `ESL`** (`Blueprint.Draft.ExpectedSupLimit`), from Chatterjee's bound (node `G6`). -/
theorem expectedSupLimit_of (hG6 : Blueprint.Draft.ExpectedMaxCovLipschitz) :
    Blueprint.Draft.ExpectedSupLimit := by
  intro d K hK Cδ C bδ b L hCδpsd hCpsd hconv hmod hb θ hθ
  rcases K.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · refine Eventually.of_forall fun δ F hF => ⟨∅, by simp, ?_⟩
    have hF0 : F = ∅ := by
      rw [← Finset.coe_eq_empty]
      exact Set.subset_empty_iff.1 hF
    subst hF0
    simp [gaussianExpectedMax, hθ.le]
  -- constants
  have hLp0 : 0 ≤ max L 0 := le_max_right _ _
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall q₀).1 hK.isBounded
  have ha : 0 < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hqa : ∀ q ∈ K, ‖q - q₀‖ ≤ max r 1 := fun q hq => by
    have := hr hq
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨ρ, hρ, hbρ⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hb) (θ / 4) (by positivity)
  -- the level `k` of the net
  have hev : ∀ᶠ k : ℕ in atTop, max r 1 / 4 ^ k < ρ ∧
      20 * √5 * (2 * √(max L 0)) *
        √((((d + 2 * (k + 1) * d : ℕ) : ℝ) + 1) * (2 * (max r 1 / 4 ^ k))) < θ / 4 := by
    refine Eventually.and ?_
      ((tendsto_chain_bound d (max r 1) (max L 0)).eventually (gt_mem_nhds (by positivity)))
    have : Tendsto (fun k : ℕ => max r 1 / 4 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    exact this.eventually (gt_mem_nhds hρ)
  obtain ⟨k, hkρ, hkchain⟩ := hev.exists
  -- the covariance tolerance `γ`
  set n : ℕ := (4 ^ (k + 1)) ^ d with hn_def
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  set γ := min (θ / 8) (θ ^ 2 / (512 * (Real.log n + 1))) with hγ_def
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  have hγ8 : γ ≤ θ / 8 := min_le_left _ _
  have hγsqrt : 2 * Real.sqrt (2 * γ * Real.log n) ≤ θ / 8 := by
    have h1 : 2 * γ * Real.log n ≤ (θ / 16) ^ 2 := by
      have h2 : γ ≤ θ ^ 2 / (512 * (Real.log n + 1)) := min_le_right _ _
      have h3 : γ * (512 * (Real.log n + 1)) ≤ θ ^ 2 := by
        rwa [le_div_iff₀ (by positivity)] at h2
      nlinarith
    have := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (by positivity)] at this
    linarith
  filter_upwards [hconv γ hγ, hmod, self_mem_nhdsWithin] with δ hδconv hδmod hδpos
  intro F hFK
  rcases F.eq_empty_or_nonempty with rfl | hF
  · exact ⟨∅, by simp, by simp [gaussianExpectedMax, hθ.le]⟩
  have hπK : ∀ p, netProj K q₀ (max r 1) k p ∈ K := netProj_mem hq₀
  have hGK : ↑(F.image (netProj K q₀ (max r 1) k)) ⊆ K := by
    intro q hq
    rw [Finset.coe_image] at hq
    obtain ⟨p, _, rfl⟩ := hq
    exact hπK p
  refine ⟨F.image (netProj K q₀ (max r 1) k), hGK, ?_⟩
  set pr := netProj K q₀ (max r 1) k with hπ_def
  set G := F.image pr with hG_def
  have hGne : G.Nonempty := hF.image pr
  have hSK : ↑(F ∪ G) ⊆ K := by
    rw [Finset.coe_union]
    exact Set.union_subset hFK hGK
  obtain ⟨v, hv⟩ := exists_gram_of_psdOn (F ∪ G) (Cδ δ) (hCδpsd δ hδpos (F ∪ G) hSK)
  have hFS : F ⊆ F ∪ G := Finset.subset_union_left
  have hGS : G ⊆ F ∪ G := Finset.subset_union_right
  have eF : gaussianExpectedMax F (Cδ δ) (bδ δ) = vecExpectedMax F v (bδ δ) := by
    rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact gaussianExpectedMax_congr F _ fun i hi j hj => (hv i (hFS hi) j (hFS hj)).symm
  have eG : gaussianExpectedMax G (Cδ δ) b = vecExpectedMax G v b := by
    rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact gaussianExpectedMax_congr G _ fun i hi j hj => (hv i (hGS hi) j (hGS hj)).symm
  -- the modulus for the Gram vectors
  have hvmod : ∀ p ∈ F ∪ G, ∀ q ∈ F ∪ G, ‖v p - v q‖ ^ 2 ≤ max L 0 * ‖p - q‖ := by
    intro p hp q hq
    have e : ‖v p - v q‖ ^ 2 = Cδ δ p p - 2 * Cδ δ p q + Cδ δ q q := by
      rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hv p hp p hp, hv p hp q hq, hv q hq q hq]
    rw [e]
    exact (hδmod p (hSK hp) q (hSK hq)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- step 1: projection onto the net
  have hB : ∀ p ∈ F, bδ δ p - bδ δ (pr p) ≤ 2 * γ + θ / 4 := by
    intro p hp
    have hpK := hFK hp
    have h1 := (hδconv p hpK p hpK).2
    have h2 := (hδconv (pr p) (hπK p) (pr p) (hπK p)).2
    have hd : dist p (pr p) < ρ := by
      rw [dist_eq_norm, norm_sub_rev]
      exact (norm_netProj_sub_lt ha hpK).trans hkρ
    have h3 := hbρ p hpK (pr p) (hπK p) hd
    rw [Real.dist_eq] at h3
    rw [abs_le] at h1 h2
    have h3' := abs_lt.1 h3
    linarith [h1.1, h1.2, h2.1, h2.2, h3'.1, h3'.2]
  have step1 := vecExpectedMax_le_proj F G hF pr (fun p hp => Finset.mem_image_of_mem pr hp) v
    (bδ δ) hB
  -- step 2: the chaining term
  have step2 : vecExpectedMax F (fun p => v p - v (pr p)) 0 ≤ θ / 4 :=
    (chain_bound ha hqa hFK hF v hLp0 hvmod).trans hkchain.le
  -- step 3: the drift
  have step3 : vecExpectedMax G v (bδ δ) ≤ vecExpectedMax G v b + γ :=
    vecExpectedMax_le_of_drift_le G hGne v (bδ δ) b fun q hq => by
      have h := (hδconv q (hGK hq) q (hGK hq)).2
      rw [abs_le] at h
      linarith [h.2]
  -- step 4: Chatterjee's bound on the net image
  have step4 := hG6 _ G (Cδ δ) C b γ (hCδpsd δ hδpos G hGK) (hCpsd G hGK)
    (fun i hi j hj => (hδconv i (hGK hi) j (hGK hj)).1)
  rw [abs_le, eG] at step4
  have hGcard : G.card ≤ n := by
    have e : G = (F.image (cell (max r 1) k)).image (netRep K q₀ (max r 1) k) := by
      rw [Finset.image_image]
      rfl
    rw [e]
    refine Finset.card_image_le.trans ((Finset.card_le_card ?_).trans (card_box_le (max r 1) k q₀))
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact cell_mem_box ha k (hqa p (hFK hp))
  have hlog : Real.log G.card ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hGne.card_pos) (by exact_mod_cast hGcard)
  have hsq : 2 * Real.sqrt (2 * γ * Real.log G.card) ≤ 2 * Real.sqrt (2 * γ * Real.log n) := by
    gcongr
  rw [eF]
  linarith [step1, step2, step3, step4.2, hsq, hγsqrt, hγ8]

/-- **Node `ESL`** (`Blueprint.Draft.ExpectedSupLimit`), unconditionally. -/
theorem expectedSupLimit : Blueprint.Draft.ExpectedSupLimit :=
  expectedSupLimit_of expectedMaxCovLipschitz

end LQGDimension
