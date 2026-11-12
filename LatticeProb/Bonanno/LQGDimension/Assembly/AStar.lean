/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.AStar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2
import LatticeProb.Bonanno.LQGDimension.Statement.Main
import Mathlib.Analysis.Subadditive

/-!
# Assembly: the first assertion of Theorem 1.1

This file assembles `Theorem11_AStar` from the three obligations of `LQGDimension.Blueprint`
(`AOneFinite`, `ASubadditiveE`, `ALinearLowerBound`).  The main ingredients are:

* `aE n ≥ 0` for every `n`, taking `F = ∅` in the defining supremum;
* `V 0` consists only of the identically-zero function, so `aE 0 = 0`;
* `aE n ≤ n • aE 1` by induction from subadditivity, hence every `aE n` is finite;
* the real sequence `a n := (aE n).toReal` is genuinely subadditive (`Subadditive a`), so
  Fekete's lemma (`Subadditive.tendsto_lim`) applies and identifies its limit with
  `aStar = ⨅ n : ℕ+, a n / n`;
* positivity of `aStar` from the linear lower bound `ALinearLowerBound`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

namespace Assembly

/-- `V 0` consists only of the function that is identically zero: with a single mesh interval
covering all of `[0,1]`, vanishing at both endpoints forces the affine piece to be `0`. -/
lemma v_zero_eq : V 0 = {(fun _ => (0:ℝ)) } := by
  ext f
  simp only [V, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hf0, hf1, hout, haff⟩
    obtain ⟨α, β, hab⟩ := haff 0 (by norm_num)
    simp only [Nat.cast_zero, pow_zero, div_one, zero_add] at hab
    have hβ : β = 0 := by have := hab 0 (by norm_num); rw [hf0] at this; nlinarith
    have hα : α = 0 := by
      have := hab 1 (by norm_num)
      rw [hf1, hβ] at this
      nlinarith
    funext x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · have := hab x hx
      rw [hα, hβ] at this
      simpa using this
    · exact hout x hx
  · rintro rfl
    refine ⟨rfl, rfl, fun x _ => rfl, ?_⟩
    intro k hk
    exact ⟨0, 0, fun x _ => by simp⟩

/-- `0 ≤ aE n` for every `n`, via the `F = ∅` term of the supremum: the integrand of the
`F = ∅` term is the (junk) value `0` of an empty supremum, whose integral vanishes. -/
lemma aE_nonneg (n : ℕ) : 0 ≤ aE n := by
  have hzero : gaussianExpectedMax (∅ : Finset (V n)) (fun f g => zCov f g)
      (fun f => -energy (f:ℝ→ℝ)) = 0 := by
    unfold gaussianExpectedMax
    have : (fun x : EuclideanSpace ℝ (∅ : Finset (V n)) =>
        ⨆ i : (∅ : Finset (V n)), x i + (-energy (i:ℝ→ℝ))) = fun _ => (0:ℝ) := by
      funext x
      exact (iSup_of_empty' _).trans Real.sSup_empty
    rw [this]
    exact integral_zero _ _
  have hle : ((gaussianExpectedMax (∅ : Finset (V n)) (fun f g => zCov f g)
      (fun f => -energy (f:ℝ→ℝ)) : ℝ) : EReal) ≤ aE n := by
    show _ ≤ ⨆ F : Finset (V n),
      ((gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy (f:ℝ→ℝ)) : ℝ) : EReal)
    exact le_iSup
      (fun F : Finset (V n) =>
        ((gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy (f:ℝ→ℝ)) : ℝ) : EReal))
      (∅ : Finset (V n))
  rw [hzero] at hle
  simpa using hle

open ProbabilityTheory in
/-- The mean of a coordinate of a multivariate Gaussian is the corresponding entry of the mean
vector, via the coordinate projection as a continuous linear map. -/
lemma integral_eval_multivariateGaussian {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (i : κ) :
    ∫ x, x i ∂ (multivariateGaussian μ S) = μ i := by
  have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) (i := i))
    (μ := multivariateGaussian μ S) ProbabilityTheory.IsGaussian.integrable_id
  simp only [EuclideanSpace.coe_proj, id_eq] at h
  rw [h, integral_id_multivariateGaussian]

/-- `V 0` is a subsingleton (in fact a singleton). -/
lemma v_zero_unique (f g : ↥(V 0)) : f = g := by
  apply Subtype.ext
  have hf : (f:ℝ→ℝ) ∈ ({(fun _ => (0:ℝ))} : Set (ℝ→ℝ)) := by rw [← v_zero_eq]; exact f.2
  have hg : (g:ℝ→ℝ) ∈ ({(fun _ => (0:ℝ))} : Set (ℝ→ℝ)) := by rw [← v_zero_eq]; exact g.2
  rw [Set.mem_singleton_iff] at hf hg
  rw [hf, hg]

/-- `aE 0 ≤ 0`: every finite subfamily of `V 0` is either empty or the singleton `{0}`, and on
that singleton the Gaussian family is degenerate (zero energy, zero covariance) with expected
maximum `0`. -/
lemma aE_zero_le_zero : aE 0 ≤ 0 := by
  apply iSup_le
  intro F
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · have hzero : gaussianExpectedMax (∅ : Finset (V 0)) (fun f g => zCov f g)
        (fun f => -energy (f:ℝ→ℝ)) = 0 := by
      unfold gaussianExpectedMax
      have : (fun x : EuclideanSpace ℝ (∅ : Finset (V 0)) =>
          ⨆ i : (∅ : Finset (V 0)), x i + (-energy (i:ℝ→ℝ))) = fun _ => (0:ℝ) := by
        funext x
        exact (iSup_of_empty' _).trans Real.sSup_empty
      rw [this]
      exact integral_zero _ _
    simp [hzero]
  · have hF : F = {i₀} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hi₀, fun j _ => v_zero_unique j i₀⟩
    subst hF
    have hi0 : (i₀ : ℝ→ℝ) = (fun _ => (0:ℝ)) := by
      have h2 : (i₀:ℝ→ℝ) ∈ V 0 := i₀.2
      have h3 := (Set.ext_iff.mp v_zero_eq (i₀:ℝ→ℝ)).mp h2
      simpa using h3
    have henergy : energy (i₀:ℝ→ℝ) = 0 := by
      rw [hi0]
      unfold energy
      simp
    have hval : gaussianExpectedMax ({i₀} : Finset (V 0)) (fun f g => zCov f g)
        (fun f => -energy (f:ℝ→ℝ)) = 0 := by
      unfold gaussianExpectedMax
      have hsup : (fun x : EuclideanSpace ℝ ({i₀} : Finset (V 0)) =>
          ⨆ i : ({i₀} : Finset (V 0)), x i + (-energy (i:ℝ→ℝ))) =
          fun x => x (default : ({i₀} : Finset (V 0))) := by
        funext x
        rw [ciSup_unique]
        have hd : ((default : ({i₀} : Finset (V 0))) : ↥(V 0)) = i₀ := Finset.default_singleton i₀
        rw [hd, henergy]
        ring
      rw [hsup]
      exact integral_eval_multivariateGaussian _ _ (default : ({i₀} : Finset (V 0)))
    simp [hval]

lemma aE_zero_eq_zero : aE 0 = 0 := le_antisymm aE_zero_le_zero (aE_nonneg 0)

lemma aE_ne_bot (n : ℕ) : aE n ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (aE_nonneg n)

/-- `aE n ≤ n • aE 1`, by induction from subadditivity. -/
lemma aE_le_nsmul (h2 : Blueprint.ASubadditiveE) : ∀ n : ℕ, aE n ≤ n • aE 1
  | 0 => by simp [aE_zero_eq_zero]
  | (n+1) => by
    calc aE (n+1) ≤ aE n + aE 1 := h2 n 1
    _ ≤ n • aE 1 + aE 1 := by gcongr; exact aE_le_nsmul h2 n
    _ = (n+1) • aE 1 := (succ_nsmul (aE 1) n).symm

lemma aE_ne_top (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) (n : ℕ) :
    aE n ≠ ⊤ := by
  have h1' : aE 1 ≠ ⊥ := aE_ne_bot 1
  have hns : (n : ℕ) • aE 1 ≠ ⊤ := by
    rw [← EReal.coe_toReal h1 h1', ← EReal.coe_nsmul]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top hns (aE_le_nsmul h2 n)

/-- `aE n` equals the coercion of the real number `a n`. -/
lemma aE_eq_coe (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) (n : ℕ) :
    ((a n : ℝ) : EReal) = aE n :=
  EReal.coe_toReal (aE_ne_top h1 h2 n) (aE_ne_bot n)

lemma a_nonneg (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) (n : ℕ) :
    0 ≤ a n := by
  have := aE_nonneg n
  rw [← aE_eq_coe h1 h2 n] at this
  exact_mod_cast this

/-- `a` is subadditive for *all* `n, m : ℕ` (including `0`), not just `n, m ≥ 1`. -/
lemma a_subadd (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    ∀ n m : ℕ, a (n + m) ≤ a n + a m := by
  intro n m
  have hnm := h2 n m
  rw [← aE_eq_coe h1 h2 (n+m), ← aE_eq_coe h1 h2 n, ← aE_eq_coe h1 h2 m, ← EReal.coe_add] at hnm
  exact_mod_cast hnm

lemma subadditive_a (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    Subadditive a := fun n m => a_subadd h1 h2 n m

/-- `aStar` (the infimum over `n : ℕ+`) agrees with the mathlib `Subadditive.lim` (the infimum
over `n : ℕ`, `n ≥ 1`), since these are infima of the same set of values. -/
lemma aStar_eq_lim (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    aStar = (subadditive_a h1 h2).lim := by
  rw [aStar, Subadditive.lim, iInf]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n:ℕ), n.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

lemma a_div_nonneg (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) (n : ℕ) :
    0 ≤ a n / (n : ℝ) := div_nonneg (a_nonneg h1 h2 n) (Nat.cast_nonneg n)

lemma bddBelow_a_div (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    BddBelow (Set.range fun n : ℕ => a n / (n : ℝ)) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact a_div_nonneg h1 h2 n⟩

/-- Fekete's lemma: `a n / n → aStar`. -/
lemma tendsto_a_div (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 aStar) := by
  rw [aStar_eq_lim h1 h2]
  exact (subadditive_a h1 h2).tendsto_lim (bddBelow_a_div h1 h2)

lemma aStar_pos (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE)
    (h3 : Blueprint.ALinearLowerBound) : 0 < aStar := by
  have hlb : ∀ n : ℕ+, (3 * (2:ℝ) ^ (-13/3 : ℝ)) ≤ a (n:ℕ) / ((n:ℕ):ℝ) := by
    intro n
    have h3n := h3 (n:ℕ)
    rw [← aE_eq_coe h1 h2 (n:ℕ)] at h3n
    have h3n' : (3 * (2:ℝ) ^ (-13/3 : ℝ)) * (n:ℕ) ≤ a (n:ℕ) := by exact_mod_cast h3n
    rw [le_div_iff₀ (by exact_mod_cast n.2)]
    linarith
  have : (3 * (2:ℝ) ^ (-13/3 : ℝ)) ≤ aStar := by
    rw [aStar]
    exact le_ciInf hlb
  have hpos : (0:ℝ) < 3 * (2:ℝ) ^ (-13/3 : ℝ) := by positivity
  linarith

end Assembly

open Assembly in
/-- Theorem 1.1, first assertion, assembled from the three `Section2` blueprint obligations. -/
theorem theorem11_aStar_of (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE)
    (h3 : Blueprint.ALinearLowerBound) : Theorem11_AStar := by
  refine ⟨aE_ne_top h1 h2, fun n m _ _ => a_subadd h1 h2 n m, aStar_pos h1 h2 h3,
    tendsto_a_div h1 h2⟩

end LQGDimension
