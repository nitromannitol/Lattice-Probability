/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J1b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_7A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The fields `x`, `Act`, `hAct`, `hxf`, `hstar` of the CONF Theorem 3.9 iteration (D120 §2.2, J2)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1543–1590. For the arcs `J_{k,i}(ω) = t39gArc (D (h ω)) z₀ (s_k ω) (I₀ i ω)` (`𝓘_k`, C:1543):

* `t39j_arcs_of_L27`: CONF Lemma 2.7 (`confLem2_7`): a.s., for `0 < τ < s'` and disjoint
  connected `Iᵢ ⊆ ∂𝓑^•_τ`, the `t39gArc … s' Iᵢ` are connected (if nonempty) and pairwise
  disjoint (C:1550).
* `t39jX`, `t39jAct`: the centres `x_{k,i}` (selected by `t39jCtr`) and the events `Act k i`
  (`t39jGoodAct`), with the fields `t39j_hAct` (by definition), `t39j_hxf`, and **`t39j_hstar`**
  ((3.21′) on `confReg`, C:1586–1590, from `t39j_star_at`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- **`t39gArc` is the set `I′` of CONF Lemma 2.7** when every point of `∂𝓑^•_{s'}` has a
(Blueprint) leftmost geodesic (CONF Lemma 2.4): the D-D1 leftmost geodesic (`DD.IsLeftmostGeod`,
used by `t39gArc`) and the Blueprint one coincide on `[0, s']` (`isLeftmost_of_side`,
`DD.right_antisymm`). -/
theorem t39j_gArc_eq {D : ContMetric} {z₀ : ℂ} {s' : ℝ} (hL : D.IsLength)
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z₀ (ratPt q))
    (hex : ∀ y ∈ frontier (filledBall D z₀ s'), ∃ Q, IsLeftmostGeod D z₀ s' y Q) (I : Set ℂ) :
    t39gArc D z₀ s' I = {y | y ∈ frontier (filledBall D z₀ s') ∧ ∃ Q,
      IsLeftmostGeod D z₀ s' y Q ∧ ∃ u ∈ Icc 0 s', Q u ∈ I} := by
  have hpos : ∀ t ∈ Ioo 0 s', ∃ φ θ, DD.IsPosJordanLift (frontier (filledBall D z₀ t)) z₀ φ θ :=
    fun t ht => DD.posLift_filledBall ht.1 hL (isBounded_ballM_of_bc hbc z₀ t)
      (GM.gm_j1b D z₀ t ht.1 hL (isBounded_ballM_of_bc hbc z₀ t))
  ext y
  constructor
  · rintro ⟨hyf, P, hP, u, hu, hPu⟩
    obtain ⟨Q, hQ⟩ := hex y hyf
    have hQ' := isLeftmost_of_side hbc hgeo hq hQ
    have h1 : DD.WeaklyRightOf D z₀ s' Q P := by simpa using hP.2.2 Q hQ.2.1
    have h2 : DD.WeaklyRightOf D z₀ s' P Q := by simpa using hQ'.2.2 P hP.2.1
    have heq := DD.right_antisymm hP.2.1 hQ.2.1 hyf hpos h1 h2
    exact ⟨hyf, Q, hQ, u, hu, heq hu ▸ hPu⟩
  · rintro ⟨hyf, Q, hQ, u, hu, hQu⟩
    exact ⟨hyf, Q, isLeftmost_of_side hbc hgeo hq hQ, u, hu, hQu⟩

/-- **CONF Lemma 2.7 for indexed families** (C:617–645, used at C:1550): a.s., for `0 < τ < s'`
and pairwise disjoint `Iᵢ ⊆ ∂𝓑^•_τ`, connected when nonempty, the sets `t39gArc … s' Iᵢ` are
connected when nonempty and pairwise disjoint. -/
theorem t39j_arcs_of_L27 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ τ s' : ℝ, 0 < τ → τ < s' → ∀ {ι : Type} [Fintype ι] (I : ι → Set ℂ),
      (∀ i, I i ⊆ frontier (filledBall (D (h ω)) z₀ τ)) →
      (∀ i, (I i).Nonempty → IsPreconnected (I i)) → Pairwise (Disjoint on I) →
      (∀ i, (t39gArc (D (h ω)) z₀ s' (I i)).Nonempty →
        IsPreconnected (t39gArc (D (h ω)) z₀ s' (I i))) ∧
      Pairwise (Disjoint on fun i => t39gArc (D (h ω)) z₀ s' (I i)) := by
  filter_upwards [confLem2_7 h38 γ hγ hγ2 D c hD P h hh z₀, confLem2_4 h38 γ hγ hγ2 D c hD P h hh z₀,
    GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, GM.gm_S1_1 h38 hγ hγ2 hD P h hh,
    hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh), confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀]
    with ω hω h24 hc hg hL hq
  intro τ s' hτ hs' ι _ I hIf hIc hId
  have heq : ∀ I : Set ℂ, t39gArc (D (h ω)) z₀ s' I = {y | y ∈ frontier
      (filledBall (D (h ω)) z₀ s') ∧ ∃ Q, IsLeftmostGeod (D (h ω)) z₀ s' y Q ∧
        ∃ u ∈ Icc 0 s', Q u ∈ I} :=
    t39j_gArc_eq hL hc hg hq fun y hy => (h24 s' (hτ.trans hs') y hy true).1
  simp only [heq]
  set 𝓘 : Set (Set ℂ) := I '' {i | (I i).Nonempty} with h𝓘
  have hfin : 𝓘.Finite := (Set.finite_range I).subset (image_subset_range _ _)
  have hbdy : ∀ S ∈ 𝓘, IsBdyArc (D (h ω)) z₀ τ S := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨hIf i, hi, hIc i hi⟩
  have hpd : 𝓘.PairwiseDisjoint id := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, -, rfl⟩ hne
    exact hId fun e => hne (e ▸ rfl)
  obtain ⟨hconn, hdisj⟩ := hω τ s' hτ hs' 𝓘 hfin hbdy hpd
  have hempty : ∀ i, ¬ (I i).Nonempty → {y | y ∈ frontier
      (filledBall (D (h ω)) z₀ s') ∧ ∃ Q, IsLeftmostGeod (D (h ω)) z₀ s' y Q ∧
        ∃ u ∈ Icc 0 s', Q u ∈ I i} = ∅ := by
    intro i hi
    ext x
    constructor
    · rintro ⟨-, Q, -, u, -, hu⟩; exact absurd ⟨_, hu⟩ hi
    · intro hx; exact hx.elim
  refine ⟨fun i hne => ?_, fun i j hij => ?_⟩
  · by_cases hi : (I i).Nonempty
    · rcases hconn (I i) ⟨i, hi, rfl⟩ with he | hb
      · exact absurd he hne.ne_empty
      · exact hb.2.isPreconnected
    · rw [hempty i hi] at hne; exact absurd hne (by simp)
  · by_cases hi : (I i).Nonempty
    · by_cases hj : (I j).Nonempty
      · have hIij : I i ≠ I j := by
          intro e
          obtain ⟨x, hx⟩ := hi
          exact Set.disjoint_left.1 (hId hij) hx (e ▸ hx)
        exact hdisj ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩ hIij
      · rw [Function.onFun, hempty j hj]; exact disjoint_empty _
    · rw [Function.onFun, hempty i hi]; exact empty_disjoint _

/-- **the arcs at level `s₀ = τ`** (C:1543 with `k = 0`): `t39gArc … τ I = I` for `I ⊆ ∂𝓑^•_τ`
when every point of `∂𝓑^•_τ` has a (Blueprint) leftmost geodesic (CONF Lemma 2.4): a geodesic to
`∂𝓑^•_τ` meets `∂𝓑^•_τ` only at its endpoint (`geod_hit_eq`). -/
theorem t39j_gArc_self {D : ContMetric} {z₀ : ℂ} {τ : ℝ}
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z₀ (ratPt q))
    (hex : ∀ y ∈ frontier (filledBall D z₀ τ), ∃ Q, IsLeftmostGeod D z₀ τ y Q) {I : Set ℂ}
    (hI : I ⊆ frontier (filledBall D z₀ τ)) : t39gArc D z₀ τ I = I := by
  ext x
  constructor
  · rintro ⟨-, P, hP, u, hu, hPu⟩
    have hut := geod_hit_eq hbc hP.2.1 hu (hI hPu)
    rw [hut, hP.2.1.2.2.1] at hPu
    exact hPu
  · intro hx
    obtain ⟨Q, hQ⟩ := hex x (hI hx)
    refine ⟨hI hx, Q, isLeftmost_of_side hbc hgeo hq hQ, τ, ⟨hQ.2.1.1, le_rfl⟩, ?_⟩
    rw [hQ.2.1.2.2.1]; exact hx

/-- **CONF Lemma 2.7 at all levels `s ≥ τ`** (C:1543–1556): a.s., for `0 < τ ≤ s` and pairwise
disjoint `Iᵢ ⊆ ∂𝓑^•_τ`, connected when nonempty, the arcs `t39gArc … s Iᵢ` are connected when
nonempty and pairwise disjoint (`s = τ`: `t39j_gArc_self`; `s > τ`: `t39j_arcs_of_L27`). -/
theorem t39j_arcs_ge (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ τ s : ℝ, 0 < τ → τ ≤ s → ∀ {ι : Type} [Fintype ι] (I : ι → Set ℂ),
      (∀ i, I i ⊆ frontier (filledBall (D (h ω)) z₀ τ)) →
      (∀ i, (I i).Nonempty → IsPreconnected (I i)) → Pairwise (Disjoint on I) →
      (∀ i, (t39gArc (D (h ω)) z₀ s (I i)).Nonempty →
        IsPreconnected (t39gArc (D (h ω)) z₀ s (I i))) ∧
      Pairwise (Disjoint on fun i => t39gArc (D (h ω)) z₀ s (I i)) := by
  filter_upwards [t39j_arcs_of_L27 h38 hγ hγ2 hD P h hh z₀,
    confLem2_4 h38 γ hγ hγ2 D c hD P h hh z₀, GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh,
    GM.gm_S1_1 h38 hγ hγ2 hD P h hh, confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀]
    with ω hω h24 hc hg hq
  intro τ s hτ hτs ι _ I hIf hIc hId
  rcases hτs.lt_or_eq with hlt | rfl
  · exact hω τ s hτ hlt I hIf hIc hId
  · have he : ∀ i, t39gArc (D (h ω)) z₀ τ (I i) = I i := fun i =>
      t39j_gArc_self hc hg hq (fun y hy => (h24 τ hτ y hy true).1) (hIf i)
    simp only [he]
    exact ⟨hIc, hId⟩

/-- **the centres `x_{k,i}`** (C:1586): `t39jCtr` at radius `ε_k 𝕣/2`, `ε_k = 2^{-t39gExp n_k}` -/
def t39jX (D : DistC → ContMetric) {Ω : Type} (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) {ι : Type}
    (I₀ : ι → Ω → Set ℂ) (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ) (k : ℕ) (i : ι) (ω : Ω) : ℂ :=
  t39jCtr (filledBall (D (h ω)) z₀ (s k ω)) (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))
    ((2 : ℝ)⁻¹ ^ t39gExp (n k ω) * R / 2)

/-- **the events `Act k i`** (C:1586): the arc `J_{k,i}` is disconnected from `∞` by a ball of
radius `< ε_k 𝕣` around `x_{k,i}` -/
def t39jAct (D : DistC → ContMetric) {Ω : Type} (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) {ι : Type}
    (I₀ : ι → Ω → Set ℂ) (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ) (k : ℕ) (i : ι) : Set Ω :=
  {ω | t39jGoodAct (filledBall (D (h ω)) z₀ (s k ω)) (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))
    (n k ω) R}

/-- the field `hAct` of `T39JRestData` (DEC-120 §5) -/
theorem t39j_hAct (D : DistC → ContMetric) {Ω : Type} (h : Ω → DistC) (z₀ : ℂ) (R : ℝ)
    {ι : Type} (I₀ : ι → Ω → Set ℂ) (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ) :
    ∀ k i ω, ω ∈ t39jAct D h z₀ R I₀ s n k i → 1 ≤ t39gExp (n k ω) ∧
      (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧
      t39jX D h z₀ R I₀ s n k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω)) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (2 : ℝ)⁻¹ ^ t39gExp (n k ω) * R ∧
        DisconnectsFromInfty (filledBall (D (h ω)) z₀ (s k ω))
          (ball (t39jX D h z₀ R I₀ s n k i ω) ρ) (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)) :=
  fun _ _ _ hω => hω

/-- the field `hxf` of `T39JRestData`: `x_{k,i} ∈ ∂𝓑^•_{s_k}` where `s_k > 0` and the ball is
bounded -/
theorem t39j_hxf {D : DistC → ContMetric} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} {z₀ : ℂ} {R : ℝ} {ι : Type} (I₀ : ι → Ω → Set ℂ) {s : ℕ → Ω → ℝ}
    (n : ℕ → Ω → ℕ)
    (hs : ∀ k, ∀ᵐ ω ∂P, 0 < s k ω ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (s k ω))) :
    ∀ k i, ∀ᵐ ω ∂P, t39jX D h z₀ R I₀ s n k i ω ∈
      frontier (filledBall (D (h ω)) z₀ (s k ω)) := by
  intro k i
  filter_upwards [hs k] with ω ⟨hs0, hbd⟩
  obtain ⟨R', -, hR', -⟩ := jb_exists_far hbd
  have hKb : Bornology.IsBounded (filledBall (D (h ω)) z₀ (s k ω)) :=
    isBounded_closedBall.subset (jb_filledBall_subset_closedBall hR')
  have hne : (frontier (filledBall (D (h ω)) z₀ (s k ω))).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨z₀, jo_mem_filledBall_self hs0⟩, fun he => ?_⟩
    have h1 := jb_filledBall_subset_closedBall hR' (he ▸ mem_univ (((|R'| + 1 : ℝ) : ℂ)))
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at h1
    linarith [le_abs_self R']
  exact t39jCtr_mem hKb hne _ _

open Classical in
/-- **the field `hstar` of `T39JRestData`** ((3.21′), C:1586–1590): on `confReg` (condition 1:
`B_{a𝕣}(z₀) ⊆ 𝓑^•_{τ_𝕣} ⊆ 𝓑^•_{s_k}`) and `s_k < τ_{3𝕣}` (`𝓑^•_{s_k} ⊆ B_{3𝕣}(z₀)`), for
`n_k ≥ N₁` at most `n_k/4` nonempty arcs are not in `Act k i`. The a.s. hypothesis collects
the inputs: length metric, bounded balls, `τ_𝕣 ≤ s_k`, and CONF Lemma 2.7 for the arcs. -/
theorem t39j_hstar {a : ℝ} (ha : 0 < a) : ∃ N₁ : ℕ,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℝ) (cc : ℝ → ℝ)
      (D : DistC → ContMetric) (h : Ω → DistC) (p : CONFParams) (χ : ℝ) (z₀ : ℂ) (R : ℝ),
      0 < R → ∀ {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (s : ℕ → Ω → ℝ)
      (n : ℕ → Ω → ℕ), (∀ k ω, n k ω = (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card) →
      (∀ᵐ ω ∂P, (D (h ω)).IsLength ∧ ∀ k, 0 < s k ω ∧
        Bornology.IsBounded (ballM (D (h ω)) z₀ (s k ω)) ∧ tauR D h z₀ R ω ≤ s k ω ∧
        (∀ i, (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty →
          IsPreconnected (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))) ∧
        Pairwise (Disjoint on fun i => t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))) →
      ∀ᵐ ω ∂P, ω ∈ confReg ξ cc D P h p χ z₀ R a → ∀ k,
        s k ω < tauR D h z₀ (3 * R) ω → N₁ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧
            ω ∉ t39jAct D h z₀ R I₀ s n k i).card ≤ n k ω := by
  obtain ⟨N₁, hN⟩ := t39j_star_at ha
  refine ⟨N₁, ?_⟩
  intro Ω _ P ξ cc D h p χ z₀ R hR ι _ I₀ s n hn hgood
  filter_upwards [hgood] with ω ⟨hL, hk⟩ hreg k hk3 hNk
  obtain ⟨hs0, hbd, hτ, hc, hd⟩ := hk k
  have hK1 : ball z₀ (a * R) ⊆ filledBall (D (h ω)) z₀ (s k ω) :=
    hreg.1.trans (gm_filledBall_mono _ _ hτ)
  have hK2 := t39g_filledBall_subset_of_lt_tauR hs0 hk3
  have h1 := hN hR hs0 hL hbd hK1 hK2 (fun i => t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))
    (fun i x hx => hx.1) hc hd (hn k ω ▸ hNk)
  rw [← hn k ω] at h1
  exact h1

open Classical in
/-- **the field `hstar` of `T39JRestData`** (DEC-120 §5; (3.21′), C:1586–1590) from the basic
iteration data only: the arcs `I₀ i ω ⊆ ∂𝓑^•_τ` (disjoint, connected when nonempty, a.s.),
`0 < τ`, `τ_𝕣 ≤ τ ≤ s_k` a.s.; the length property, bounded balls (DFGPS Lemma 3.8) and CONF
Lemmas 2.4/2.7 for the arcs `t39gArc … s_k (I₀ i)` are discharged here. -/
theorem t39j_hstar_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {a : ℝ} (ha : 0 < a) :
    ∃ N₁ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (p : CONFParams) (χ : ℝ) (z₀ : ℂ) (R : ℝ),
      0 < R → ∀ {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) (s : ℕ → Ω → ℝ)
      (n : ℕ → Ω → ℕ), (∀ k ω, n k ω = (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card) →
      (∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      (∀ᵐ ω ∂P, (∀ i, (I₀ i ω).Nonempty → IsPreconnected (I₀ i ω)) ∧
        Pairwise (Disjoint on fun i => I₀ i ω)) →
      (∀ᵐ ω ∂P, 0 < τ ω ∧ tauR D h z₀ R ω ≤ τ ω ∧ ∀ k, τ ω ≤ s k ω) →
      ∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k,
        s k ω < tauR D h z₀ (3 * R) ω → N₁ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧
            ω ∉ t39jAct D h z₀ R I₀ s n k i).card ≤ n k ω := by
  obtain ⟨N₁, hN⟩ := t39j_hstar ha
  refine ⟨N₁, ?_⟩
  intro Ω _ P _ h hh p χ z₀ R hR ι _ I₀ τ s n hn hI₀ hI₀c hτ
  refine hN P (xiGamma γ) c D h p χ z₀ R hR I₀ s n hn ?_
  filter_upwards [hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh),
    GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, t39j_arcs_ge h38 hγ hγ2 hD P h hh z₀, hI₀c, hτ]
    with ω hL hc harcs ⟨hIc, hId⟩ ⟨hτ0, hτR, hsk⟩
  refine ⟨hL, fun k => ⟨hτ0.trans_le (hsk k), isBounded_ballM_of_bc hc z₀ _,
    hτR.trans (hsk k), ?_⟩⟩
  exact harcs (τ ω) (s k ω) hτ0 (hsk k) (fun i => I₀ i ω) (fun i => hI₀ i ω) hIc hId

end CONF
end LQGMetric
