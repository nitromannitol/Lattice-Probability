/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21Path at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# DDDF Proposition 21, Step 2: from the coarse graining to a crossing (task P2-DDDF6c)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 984–990 (`eq:CoarseToPath`): "By taking the concatenation of straight paths in each box of
`π_n^K(ψ)`, we get a left-right crossing of `[0,1]²`", whence
`Σ_{P ∈ π^K} e^{ξ φ_{0,K}(P)} ≥ e^{-ξ max osc} 2^K L^{(K)}_{1,1}(φ)` (up to a constant).

Here (`DDDF.S6.rectLen_le_coarse`): for a left–right crossing `γ` of `[0,1]²` and weights `w` with
`e^{ξ f} ≤ w(P)` on the `3 × 3` neighbourhood `\hat P` of every block `P ∈ π^K(γ)`,
`L_{1,1}(f) ≤ 4 · 2^{-K} Σ_{P ∈ π^K(γ)} w(P)`.
The concatenation of straight segments is made explicit (own elementary argument, DDDF leave it
to the reader): the blocks of `π^K(γ)` with the "touching" relation form a graph in which the
block of `γ(0)` reaches a block of `γ(1)` (the trace of `γ` is connected and covered by these
closed blocks); along a simple path `P_0, …, P_m` of this graph we join `γ(0)`, points of `γ` in
`P_1, …, P_m`, and `γ(1)` by segments; the segment leaving `P_i` lies in `\hat P_i` and has length
`≤ 4 · 2^{-K}`, and every block is used once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6

open T20 T20D LFPP

/-- the touching graph on a finite set `S` of blocks -/
def blkGraph (S : Finset (ℤ × ℤ)) : SimpleGraph (ℤ × ℤ) where
  Adj a b := a ≠ b ∧ a ∈ S ∧ b ∈ S ∧ |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2.1, h.2.1, by rw [abs_sub_comm]; exact h.2.2.2.1,
    by rw [abs_sub_comm]; exact h.2.2.2.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma h_pos' (K : ℕ) : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity

lemma mem_dyBlock {K : ℕ} {b : ℤ × ℤ} {z : ℂ} (hz : z ∈ dyBlock K b) :
    (b.1 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ z.re ∧ z.re ≤ ((b.1 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K ∧
      (b.2 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ z.im ∧ z.im ≤ ((b.2 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by
  unfold dyBlock at hz
  rw [Complex.mem_reProdIm] at hz
  exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩

/-- intersecting blocks are within one step in each coordinate -/
lemma close_of_inter {K : ℕ} {a b : ℤ × ℤ} {z : ℂ} (ha : z ∈ dyBlock K a) (hb : z ∈ dyBlock K b) :
    |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1 := by
  have hp := h_pos' K
  obtain ⟨a1, a2, a3, a4⟩ := mem_dyBlock ha
  obtain ⟨b1, b2, b3, b4⟩ := mem_dyBlock hb
  have k : ∀ m n : ℤ, (m : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ ((n : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K → m ≤ n + 1 := by
    intro m n h
    have : (m : ℝ) ≤ n + 1 := le_of_mul_le_mul_right h hp
    exact_mod_cast this
  have e1 := k a.1 b.1 (a1.trans b2)
  have e2 := k b.1 a.1 (b1.trans a2)
  have e3 := k a.2 b.2 (a3.trans b4)
  have e4 := k b.2 a.2 (b3.trans a4)
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- every point of `[0,1]²` lies in a block of `blkIdx K` -/
lemma exists_blk {K : ℕ} {z : ℂ} (hz : z ∈ (rectAB 1 1).toSet) :
    ∃ b ∈ blkIdx K, z ∈ dyBlock K b := by
  have hp := h_pos' K
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hz
  have e1 : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  set h := (2 : ℝ)⁻¹ ^ K
  refine ⟨(⌊z.re / h⌋, ⌊z.im / h⌋), ?_, ?_⟩
  · have g : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (-1 : ℤ) ≤ ⌊t / h⌋ ∧ ⌊t / h⌋ ≤ 2 ^ K := by
      intro t h0 h1
      refine ⟨by have := Int.floor_nonneg.2 (div_nonneg h0 hp.le); omega, ?_⟩
      have : t / h ≤ 2 ^ K := by
        rw [div_le_iff₀ hp]; nlinarith
      exact_mod_cast (Int.floor_le _).trans this
    simp only [blkIdx, Finset.mem_product, Finset.mem_Icc]
    exact ⟨g _ hz.1.1 hz.1.2, g _ hz.2.1 hz.2.2⟩
  · unfold dyBlock
    rw [Complex.mem_reProdIm]
    have g : ∀ t : ℝ, ((⌊t / h⌋ : ℤ) : ℝ) * h ≤ t ∧ t ≤ ((⌊t / h⌋ : ℤ) + 1) * h := by
      intro t
      have f1 := Int.floor_le (t / h)
      have f2 := Int.lt_floor_add_one (t / h)
      constructor
      · have := mul_le_mul_of_nonneg_right f1 hp.le
        rwa [div_mul_cancel₀ _ hp.ne'] at this
      · have := mul_le_mul_of_nonneg_right f2.le hp.le
        rwa [div_mul_cancel₀ _ hp.ne'] at this
    exact ⟨g z.re, g z.im⟩

lemma convex_hatBox (K : ℕ) (b : ℤ × ℤ) : Convex ℝ (hatBox K b) :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

lemma convex_unit : Convex ℝ (rectAB 1 1).toSet :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- a segment from a block to a touching block stays in the neighbourhood of the first, and has
length `≤ 4 · 2^{-K}` -/
lemma seg_facts {K : ℕ} {a b : ℤ × ℤ} (hab : |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1) {x z : ℂ}
    (hx : x ∈ dyBlock K a) (hz : z ∈ dyBlock K b) :
    (∀ u ∈ Icc (0 : ℝ) 1, segPath x z u ∈ hatBox K a) ∧ ‖z - x‖ ≤ 4 * (2 : ℝ)⁻¹ ^ K := by
  have hp := h_pos' K
  obtain ⟨x1, x2, x3, x4⟩ := mem_dyBlock hx
  obtain ⟨z1, z2, z3, z4⟩ := mem_dyBlock hz
  obtain ⟨h1, h2⟩ := hab
  have c1 : (a.1 : ℝ) - 1 ≤ b.1 := by have := (abs_le.1 h1).2; exact_mod_cast (by omega : a.1 - 1 ≤ b.1)
  have c2 : (b.1 : ℝ) ≤ a.1 + 1 := by exact_mod_cast (by have := (abs_le.1 h1).1; omega : b.1 ≤ a.1 + 1)
  have c3 : (a.2 : ℝ) - 1 ≤ b.2 := by have := (abs_le.1 h2).2; exact_mod_cast (by omega : a.2 - 1 ≤ b.2)
  have c4 : (b.2 : ℝ) ≤ a.2 + 1 := by exact_mod_cast (by have := (abs_le.1 h2).1; omega : b.2 ≤ a.2 + 1)
  have hxH : x ∈ hatBox K a := by
    unfold hatBox; rw [Complex.mem_reProdIm]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  have hzH : z ∈ hatBox K a := by
    unfold hatBox; rw [Complex.mem_reProdIm]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  refine ⟨fun u hu => ?_, ?_⟩
  · unfold segPath
    exact (convex_hatBox K a).add_smul_sub_mem hxH hzH hu
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have r1 : |(z - x).re| ≤ 2 * (2 : ℝ)⁻¹ ^ K := by
      rw [Complex.sub_re, abs_le]; constructor <;> nlinarith
    have r2 : |(z - x).im| ≤ 2 * (2 : ℝ)⁻¹ ^ K := by
      rw [Complex.sub_im, abs_le]; constructor <;> nlinarith
    linarith

/-- the segment bound with the hypothesis on the segment only -/
lemma lfppLen_seg_le {ξ : ℝ} {f : ℂ → ℝ} (x z : ℂ) {B : ℝ}
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, Real.exp (ξ * f (segPath x z u)) ≤ B) :
    lfppLen ξ f (segPath x z) ≤ ENNReal.ofReal (B * ‖z - x‖) := by
  rw [lfppLen_eq]
  calc ∫⁻ t in Icc (0 : ℝ) 1, lenDens ξ f (segPath x z) t
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (B * ‖z - x‖) := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        rw [lenDens_segPath]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hB u hu) (norm_nonneg _))
    _ = ENNReal.ofReal (B * ‖z - x‖) := by simp

lemma concat_mem {P R : ℝ → ℂ} {U : Set ℂ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, R t ∈ U) : ∀ t ∈ Icc (0 : ℝ) 1, concatPath P R t ∈ U := by
  intro t ht
  unfold concatPath
  split_ifs with h
  · exact hP _ ⟨by linarith [ht.1], by linarith⟩
  · exact hR _ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩

variable {ξ : ℝ} {f : ℂ → ℝ} {K : ℕ} {S : Finset (ℤ × ℤ)} {w : ℤ × ℤ → ℝ}

/-- the polygon along a simple path of the touching graph -/
lemma walk_poly
    (hw : ∀ b ∈ S, ∀ x ∈ hatBox K b, Real.exp (ξ * f x) ≤ w b)
    (hpt : ∀ b ∈ S, (dyBlock K b ∩ (rectAB 1 1).toSet).Nonempty) :
    ∀ {u v : ℤ × ℤ} (p : (blkGraph S).Walk u v), p.IsPath → u ∈ S →
      ∀ x ∈ dyBlock K u ∩ (rectAB 1 1).toSet, ∀ y ∈ dyBlock K v ∩ (rectAB 1 1).toSet,
      ∃ Γ : ℝ → ℂ, IsPiecewiseC1Path Γ x y ∧ (∀ t ∈ Icc (0 : ℝ) 1, Γ t ∈ (rectAB 1 1).toSet) ∧
        p.support.toFinset ⊆ S ∧
        lfppLen ξ f Γ ≤ ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ K * ∑ b ∈ p.support.toFinset, w b) := by
  intro u v p
  induction p with
  | nil =>
    rename_i u
    intro _ hu x hx y hy
    obtain ⟨hseg, hlen⟩ := seg_facts (a := u) (b := u) (K := K) (by simp) hx.1 hy.1
    refine ⟨segPath x y, isPiecewiseC1Path_segPath x y, fun t ht => ?_, ?_, ?_⟩
    · unfold segPath; exact convex_unit.add_smul_sub_mem hx.2 hy.2 ht
    · simpa using hu
    · simp only [SimpleGraph.Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.sum_singleton]
      refine (lfppLen_seg_le x y fun t ht => hw u hu _ (hseg t ht)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hw0 : 0 ≤ w u := (Real.exp_pos _).le.trans (hw u hu _ (hseg 0 ⟨le_rfl, zero_le_one⟩))
      nlinarith
  | cons hadj p' ih =>
    rename_i u u' v
    intro hp hu x hx y hy
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hu' : u' ∈ S := hadj.2.2.1
    obtain ⟨z, hz⟩ := hpt u' hu'
    obtain ⟨Γ', hΓ'1, hΓ'2, hsub, hΓ'3⟩ := ih hp.1 hu' z hz y hy
    obtain ⟨hseg, hlen⟩ := seg_facts (K := K) ⟨hadj.2.2.2.1, hadj.2.2.2.2⟩ hx.1 hz.1
    have hw0 : 0 ≤ w u := (Real.exp_pos _).le.trans (hw u hu _ (hseg 0 ⟨le_rfl, zero_le_one⟩))
    have hj : segPath x z 1 = Γ' 0 := by rw [hΓ'1.source]; simp [segPath]
    refine ⟨concatPath (segPath x z) Γ', isPiecewiseC1Path_concatPath
      (isPiecewiseC1Path_segPath x z) hΓ'1, concat_mem (fun t ht => by
        unfold segPath; exact convex_unit.add_smul_sub_mem hx.2 hz.2 ht) hΓ'2, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
      exact Finset.insert_subset hu hsub
    · simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
      have hnot : u ∉ p'.support.toFinset := by simpa using hp.2
      rw [Finset.sum_insert hnot, lfppLen_concatPath hj]
      have hsum0 : 0 ≤ ∑ b ∈ p'.support.toFinset, w b := by
        refine Finset.sum_nonneg fun b hb => ?_
        have hbS := hsub hb
        obtain ⟨q, hq⟩ := hpt b hbS
        exact (Real.exp_pos _).le.trans (hw b hbS q (by
          obtain ⟨q1, q2, q3, q4⟩ := mem_dyBlock hq.1
          have hp := h_pos' K
          unfold hatBox; rw [Complex.mem_reProdIm]
          exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩))
      calc lfppLen ξ f (segPath x z) + lfppLen ξ f Γ'
          ≤ ENNReal.ofReal (w u * ‖z - x‖) +
              ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ K * ∑ b ∈ p'.support.toFinset, w b) :=
            add_le_add (lfppLen_seg_le x z fun t ht => hw u hu _ (hseg t ht)) hΓ'3
        _ = ENNReal.ofReal (w u * ‖z - x‖ +
              4 * (2 : ℝ)⁻¹ ^ K * ∑ b ∈ p'.support.toFinset, w b) :=
            (ENNReal.ofReal_add (by positivity) (by have := h_pos' K; positivity)).symm
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have := mul_le_mul_of_nonneg_left hlen hw0
            nlinarith

/-- the block of `γ(0)` reaches a block of `γ(1)` in the touching graph of `π^K(γ)` -/
lemma reach_end {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ) {u : ℤ × ℤ}
    (hu : u ∈ coarseBlocks K γ) (hu0 : γ 0 ∈ dyBlock K u) :
    ∃ v ∈ coarseBlocks K γ, γ 1 ∈ dyBlock K v ∧ (blkGraph (coarseBlocks K γ)).Reachable u v := by
  classical
  obtain ⟨z0, -, w1, -, hpc, hU⟩ := hγ
  set S := coarseBlocks K γ
  set R := S.filter fun b => (blkGraph S).Reachable u b
  set A : Set ℂ := ⋃ b ∈ R, dyBlock K b
  set B : Set ℂ := ⋃ b ∈ S \ R, dyBlock K b
  have hcl : ∀ b, IsClosed (dyBlock K b) := fun b =>
    (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)
  have hA : IsClosed A := isClosed_biUnion_finset fun b _ => hcl b
  have hB : IsClosed B := isClosed_biUnion_finset fun b _ => hcl b
  have hI : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image _ hpc.continuousOn
  have hmemS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b ∈ blkIdx K, γ t ∈ dyBlock K b → b ∈ S := fun t ht b hb h =>
    Finset.mem_filter.2 ⟨hb, t, ht, h⟩
  have hcov : γ '' Icc 0 1 ⊆ A ∪ B := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨b, hb, hbt⟩ := exists_blk (K := K) (hU t ht)
    have hbS := hmemS t ht b hb hbt
    by_cases hbR : b ∈ R
    · exact Or.inl (mem_biUnion hbR hbt)
    · exact Or.inr (mem_biUnion (Finset.mem_sdiff.2 ⟨hbS, hbR⟩) hbt)
  have hdisj : γ '' Icc 0 1 ∩ (A ∩ B) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyA, hyB⟩ => ?_
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 hyA
    obtain ⟨b', hb', hyb'⟩ := mem_iUnion₂.1 hyB
    obtain ⟨hb'S, hb'R⟩ := Finset.mem_sdiff.1 hb'
    obtain ⟨hbS, hreach⟩ := Finset.mem_filter.1 hb
    apply hb'R
    refine Finset.mem_filter.2 ⟨hb'S, ?_⟩
    by_cases e : b = b'
    · exact e ▸ hreach
    · exact hreach.trans (SimpleGraph.Adj.reachable ⟨e, hbS, hb'S, close_of_inter hyb hyb'⟩)
  have huR : u ∈ R := Finset.mem_filter.2 ⟨hu, SimpleGraph.Reachable.refl u⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hI) A B hA hB hcov hdisj with h | h
  · obtain ⟨v, hv, hv1⟩ := mem_iUnion₂.1 (h ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
    exact ⟨v, (Finset.mem_filter.1 hv).1, hv1, (Finset.mem_filter.1 hv).2⟩
  · exfalso
    have h0 : γ 0 ∈ γ '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have : γ 0 ∈ γ '' Icc 0 1 ∩ (A ∩ B) := ⟨h0, mem_biUnion huR hu0, h h0⟩
    rw [hdisj] at this; exact this

/-- **DDDF (`eq:CoarseToPath`)**, deterministic part (l. 984–990): if `e^{ξ f} ≤ w(P)` on the
neighbourhood `\hat P` of every block `P ∈ π^K(γ)` of a left–right crossing `γ` of `[0,1]²`, then
`L_{1,1}(f) ≤ 4 · 2^{-K} Σ_{P ∈ π^K(γ)} w(P)`. -/
theorem rectLen_le_coarse {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (hw : ∀ b ∈ coarseBlocks K γ, ∀ x ∈ hatBox K b, Real.exp (ξ * f x) ≤ w b) :
    rectLen ξ f (rectAB 1 1) ≤
      ENNReal.ofReal (4 * (2 : ℝ)⁻¹ ^ K * ∑ b ∈ coarseBlocks K γ, w b) := by
  classical
  have hγ' := hγ
  obtain ⟨z0, hz0, w1, hw1, hpc, hU⟩ := hγ'
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨u, hu, hu0⟩ := exists_blk (K := K) (hU 0 h0)
  have huS : u ∈ coarseBlocks K γ := Finset.mem_filter.2 ⟨hu, 0, h0, hu0⟩
  obtain ⟨v, hvS, hv1, hreach⟩ := reach_end hγ huS hu0
  have hpt : ∀ b ∈ coarseBlocks K γ, (dyBlock K b ∩ (rectAB 1 1).toSet).Nonempty := by
    intro b hb
    obtain ⟨-, t, ht, hbt⟩ := Finset.mem_filter.1 hb
    exact ⟨γ t, hbt, hU t ht⟩
  obtain ⟨q⟩ := hreach
  obtain ⟨Γ, hΓ1, hΓ2, hsub, hΓ3⟩ := walk_poly hw hpt q.bypass q.bypass_isPath huS (γ 0)
    ⟨hu0, hU 0 h0⟩ (γ 1) ⟨hv1, hU 1 h1⟩
  have hadm : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ Γ := by
    refine ⟨γ 0, ?_, γ 1, ?_, hΓ1, hΓ2⟩
    · rw [hpc.source]; exact hz0
    · rw [hpc.target]; exact hw1
  have hw0 : ∀ b ∈ coarseBlocks K γ, 0 ≤ w b := by
    intro b hb
    obtain ⟨q', hq⟩ := hpt b hb
    exact (Real.exp_pos _).le.trans (hw b hb q' (by
      obtain ⟨q1, q2, q3, q4⟩ := mem_dyBlock hq.1
      have hp := h_pos' K
      unfold hatBox; rw [Complex.mem_reProdIm]
      exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩))
  refine (crossLenIn_le_lfppLen hadm).trans (hΓ3.trans (ENNReal.ofReal_le_ofReal ?_))
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => hw0 b hb
  have hp := h_pos' K
  nlinarith

end S6
end DDDF
end LQGMetric
