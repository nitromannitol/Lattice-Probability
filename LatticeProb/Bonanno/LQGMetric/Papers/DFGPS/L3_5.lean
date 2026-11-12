/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Topo.CircleUnion
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.5 (`lem-connected`,
T:1573–1596), used in the upper bound of Proposition 3.1 (T:1549).

* `GoodCover good ν M ε 𝕣` is the conclusion of DFGPS Lemma 3.2 (`lem-good-annulus-all`,
  T:1453–1456) for a predicate `good w r` standing for "`E_r(w; C)` occurs" (`annEvent`): every
  `z ∈ B_{𝕣ε^{-M}}(0)` lies in `B_{𝕣ε^{1+ν}/2}(w)` for some `w ∈ B_{𝕣ε^{-M}}(0) ∩ (ε^{1+ν}𝕣/4)ℤ²`
  and `r ∈ [ε^{1+ν}𝕣, ε𝕣] ∩ {2^{-k}𝕣}_{k∈ℕ}` with `good w r`.
* `lem3_5`: on `GoodCover good 1 M ε 𝕣` (the event `F^ε_𝕣` with `ν = 1`), for `ε` small depending
  on `K₁, K₂, U` (and `M`), there is a path from `𝕣K₁` to `𝕣K₂` contained in `𝕣U` and in the union
  of the circles `∂B_r(w)` over the admissible good `(w, r)` with `w ∈ B_{ε𝕣}(𝕣U)`.

The proof is the paper's: the deterministic core (minimal disc cover, connectedness of the union
of its circles, circles meeting `K₁`, `K₂` by the diameter condition) is
`TopoCircle.exists_joinedIn_biUnion_sphere_of_path` (`LQGMetric/Topo/CircleUnion.lean`, which
follows T:1581–1596 step by step). Here we supply the cover: T:1580 "since `U` is connected, the
union of the balls contains a path from `𝕣K₁` to `𝕣K₂` contained in `𝕣U`": we fix a path `γ₀`
from `K₁` to `K₂` in `U`, cover the compact set `𝕣 γ₀` by finitely many good balls `B_r(w)` (each
`z` lies in `B_{𝕣ε²/2}(w) ⊆ B_r(w)`), and apply the core.

Departures (see the report / DEVIATIONS): (a) `U` is assumed connected; Proposition 3.1
(T:1415) only says "open", but its proof uses connectedness (T:1580) and the proposition is
false otherwise. (b) The paper's `U` bounded and `K₁ ∩ K₂ = ∅` are not needed and are dropped.
(c) The conclusion is strengthened by `B̄_{2r}(w) ⊆ 𝕣U` for every circle used, which the upper
bound of Proposition 3.1 needs (the internal distance in `𝔸_{r/2,2r}(w)` must bound
`D_h(·,·; 𝕣U)`); the paper's choice of balls (T:1580) does not state it, it holds for the balls
meeting the fixed path `𝕣γ₀` once `3ε < dist(γ₀, ∂U)`.
-/

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS
open Blueprint

/-- The conclusion of DFGPS Lemma 3.2 (T:1453–1456) for a predicate `good w r`
(`= "E_r(w; C)` occurs"): every `z ∈ B_{𝕣ε^{-M}}(0)` lies in `B_{𝕣ε^{1+ν}/2}(w)` for some
`w ∈ B_{𝕣ε^{-M}}(0) ∩ (ε^{1+ν}𝕣/4)ℤ²` and `r ∈ [ε^{1+ν}𝕣, ε𝕣] ∩ {2^{-k}𝕣}_{k∈ℕ}` with
`good w r`. -/
def GoodCover (good : ℂ → ℝ → Prop) (ν M ε 𝕣 : ℝ) : Prop :=
  ∀ z ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M)),
    ∃ w ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M)) ∩ gridPts (ε ^ (1 + ν) * 𝕣 / 4),
      ∃ r : ℝ, (∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣) ∧ ε ^ (1 + ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧
        good w r ∧ z ∈ ball w (𝕣 * ε ^ (1 + ν) / 2)

/-- **DFGPS Lemma 3.5** (`lem-connected`, T:1573–1596). Let `U` be open and connected and
`K₁, K₂ ⊆ U` connected compact sets which are not singletons, and `M > 0`. For all small enough
`ε > 0`, every `𝕣 > 0` and every predicate `good` (`E_r(w; C)`): if `GoodCover good 1 M ε 𝕣`
(the event `F^ε_𝕣`), then there is a path from `𝕣K₁` to `𝕣K₂` contained in `𝕣U` each point of
which lies on a circle `∂B_r(w)` with `w ∈ B_{ε𝕣}(𝕣U) ∩ (ε²𝕣/4)ℤ²`,
`r ∈ [ε²𝕣, ε𝕣] ∩ {2^{-k}𝕣}_{k∈ℕ}` and `good w r`; moreover `B̄_{2r}(w) ⊆ 𝕣U`. -/
theorem lem3_5 {U K₁ K₂ : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hK₁ : IsCompact K₁) (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial)
    (hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂) (hK₂n : K₂.Nontrivial)
    (h₁U : K₁ ⊆ U) (h₂U : K₂ ⊆ U) {M : ℝ} (hM : 0 < M) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ 𝕣 > 0, ∀ good : ℂ → ℝ → Prop, GoodCover good 1 M ε 𝕣 →
      ∃ x ∈ scaleSet 𝕣 0 K₁, ∃ y ∈ scaleSet 𝕣 0 K₂, ∃ γ : Path x y, ∀ t,
        γ t ∈ scaleSet 𝕣 0 U ∧ ∃ w : ℂ, ∃ r : ℝ, w ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 U) ∧
          w ∈ gridPts (ε ^ 2 * 𝕣 / 4) ∧ (∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣) ∧
          ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧ good w r ∧ γ t ∈ sphere w r ∧
          closedBall w (2 * r) ⊆ scaleSet 𝕣 0 U := by
  classical
  obtain ⟨p, hp⟩ := hK₁c.nonempty
  obtain ⟨q, hq⟩ := hK₂c.nonempty
  have hUp : IsPathConnected U := (hU.isConnected_iff_isPathConnected).1 hUc
  have hj : JoinedIn U p q := hUp.joinedIn p (h₁U hp) q (h₂U hq)
  set γ₀ := hj.somePath with hγ₀def
  have hγ₀U : ∀ t, γ₀ t ∈ U := hj.somePath_mem
  have hP : IsCompact (range γ₀) := isCompact_range γ₀.continuous
  obtain ⟨δ, hδ, hδU⟩ := hP.exists_cthickening_subset_open hU (range_subset_iff.2 hγ₀U)
  obtain ⟨ρ, hρ⟩ := isBounded_iff_forall_norm_le.1 hP.isBounded
  obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hK₁n
  obtain ⟨a₂, ha₂, b₂, hb₂, hab₂⟩ := hK₂n
  set ρ' := max ρ 1 with hρ'def
  have hρ' : 0 < ρ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hd₁ := dist_pos.2 hab₁
  have hd₂ := dist_pos.2 hab₂
  have hρpos := Real.rpow_pos_of_pos hρ' (-(1 / M))
  refine ⟨min (min (δ / 3) (dist a₁ b₁ / 2)) (min (dist a₂ b₂ / 2) (ρ' ^ (-(1 / M)))),
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) hρpos), ?_⟩
  rintro ε ⟨hε0, hε⟩ 𝕣 h𝕣 good hgood
  simp only [lt_min_iff] at hε
  obtain ⟨⟨hεδ, hε1⟩, hε2, hερ⟩ := hε
  have hεM : ρ' < ε ^ (-M) := by
    have := Real.rpow_lt_rpow_of_neg hε0 hερ (neg_neg_of_pos hM)
    rwa [← Real.rpow_mul hρ'.le, show -(1 / M) * -M = 1 by field_simp, Real.rpow_one] at this
  have e2 : ε ^ ((1 : ℝ) + 1) = ε ^ 2 := by
    rw [show (1 : ℝ) + 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  simp only [GoodCover, e2] at hgood
  have hch : ∀ z : ℂ, ∃ w : ℂ, ∃ r : ℝ, z ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M)) →
      (w ∈ gridPts (ε ^ 2 * 𝕣 / 4) ∧ (∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣) ∧ ε ^ 2 * 𝕣 ≤ r ∧
        r ≤ ε * 𝕣 ∧ good w r ∧ z ∈ ball w (𝕣 * ε ^ 2 / 2)) := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M))
    · obtain ⟨w, ⟨-, hw⟩, r, hk, h1, h2, hg, hzw⟩ := hgood z hz
      exact ⟨w, r, fun _ => ⟨hw, hk, h1, h2, hg, hzw⟩⟩
    · exact ⟨0, 0, fun h => absurd h hz⟩
  choose W R hWR using hch
  let f : ℂ → ℂ := fun x => (𝕣 : ℂ) * x + 0
  have hf : Continuous f := by fun_prop
  have h𝕣C : (𝕣 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h𝕣.ne'
  have hdist : ∀ x y : ℂ, dist (f x) (f y) = 𝕣 * dist x y := by
    intro x y
    simp only [f, add_zero, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h𝕣]
  let γ : Path (f p) (f q) := γ₀.map hf
  have hγ : ∀ t, γ t = f (γ₀ t) := fun t => rfl
  have hin : ∀ t, γ t ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M)) := by
    intro t
    rw [hγ, mem_ball_zero_iff]
    simp only [f, add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
    have h1 := hρ _ (mem_range_self t)
    have h2 : ρ ≤ ρ' := le_max_left _ _
    exact mul_lt_mul_of_pos_left (by linarith) h𝕣
  have hRpos : ∀ t, 0 < R (γ t) := by
    intro t
    obtain ⟨-, ⟨k, hk⟩, -⟩ := hWR _ (hin t)
    rw [hk]; positivity
  have hmem : ∀ t, γ t ∈ ball (W (γ t)) (R (γ t)) := by
    intro t
    obtain ⟨-, -, h1, -, -, hz⟩ := hWR _ (hin t)
    have := hRpos t
    rw [mem_ball] at hz ⊢
    nlinarith
  obtain ⟨T, hTs, hTcov⟩ := (isCompact_range γ.continuous).elim_nhds_subcover
    (fun x => ball (W x) (R x)) (fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact isOpen_ball.mem_nhds (hmem t))
  have hTr : ∀ i ∈ T, ∃ t, i = γ t := fun i hi => by
    obtain ⟨t, ht⟩ := hTs i hi
    exact ⟨t, ht.symm⟩
  have hdiam : ∀ {K : Set ℂ}, IsCompact K → ∀ {a b : ℂ}, a ∈ K → b ∈ K →
      ∀ i ∈ T, 2 * ε * 𝕣 < 𝕣 * dist a b → 2 * R i < diam (scaleSet 𝕣 0 K) := by
    intro K hK a b ha hb i hi hlt
    obtain ⟨t, rfl⟩ := hTr i hi
    obtain ⟨-, -, -, h2, -⟩ := hWR _ (hin t)
    have hle : dist (f a) (f b) ≤ diam (scaleSet 𝕣 0 K) :=
      dist_le_diam_of_mem (hK.image hf).isBounded (mem_image_of_mem f ha) (mem_image_of_mem f hb)
    rw [hdist] at hle
    linarith
  obtain ⟨S, hST, -, x, hx, y, hy, hJ⟩ := TopoCircle.exists_joinedIn_biUnion_sphere_of_path W R T
    (fun i hi => by obtain ⟨t, rfl⟩ := hTr i hi; exact hRpos t)
    (K₁ := scaleSet 𝕣 0 K₁) (K₂ := scaleSet 𝕣 0 K₂)
    (hK₁c.image f hf.continuousOn).isPreconnected (hK₂c.image f hf.continuousOn).isPreconnected
    (fun i hi => hdiam hK₁ ha₁ hb₁ i hi (by nlinarith))
    (fun i hi => hdiam hK₂ ha₂ hb₂ i hi (by nlinarith))
    γ (mem_image_of_mem f hp) (mem_image_of_mem f hq) hTcov
  refine ⟨x, hx, y, hy, hJ.somePath, fun t => ?_⟩
  obtain ⟨i, hiS, hit⟩ := mem_iUnion₂.1 (hJ.somePath_mem t)
  obtain ⟨s, rfl⟩ := hTr i (hST hiS)
  obtain ⟨hw, hk, h1, h2, hg, hz⟩ := hWR _ (hin s)
  have hRs := hRpos s
  rw [mem_ball] at hz
  have hball : closedBall (W (γ s)) (2 * R (γ s)) ⊆ scaleSet 𝕣 0 U := by
    intro v hv
    rw [mem_closedBall] at hv
    have htri := dist_triangle v (W (γ s)) (γ s)
    rw [dist_comm (W (γ s))] at htri
    have hv' : dist v (γ s) = 𝕣 * dist (v / 𝕣) (γ₀ s) := by
      rw [← hdist, hγ]
      simp only [f, add_zero]
      rw [mul_div_cancel₀ v h𝕣C]
    have hle : dist (v / 𝕣) (γ₀ s) ≤ δ := by
      have : 𝕣 * dist (v / 𝕣) (γ₀ s) ≤ 𝕣 * δ := by nlinarith
      exact le_of_mul_le_mul_left this h𝕣
    refine ⟨v / 𝕣, hδU (mem_cthickening_of_dist_le _ (γ₀ s) δ _ (mem_range_self s) hle), ?_⟩
    simp only [add_zero]
    exact mul_div_cancel₀ v h𝕣C
  have hγs : γ s ∈ scaleSet 𝕣 0 U := ⟨γ₀ s, hγ₀U s, rfl⟩
  refine ⟨hball (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hit),
    W (γ s), R (γ s), mem_thickening_iff.2 ⟨γ s, hγs, ?_⟩, hw, hk, h1, h2, hg, hit, hball⟩
  rw [dist_comm]
  nlinarith

end LQGMetric.DFGPS
