/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep3
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiCont
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Approx
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Indep

/-!
# DDDF Theorem 20, Step 2 set-up: the block decomposition of `ψ_{K,n}` (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 360–376 ((2.19)–(2.20) = `eq:BlockDecompoPsi`) and
l. 1075–1081 (Step 2 of Theorem 20): `ψ_{0,n} = ψ_{0,K} + Σ_{P ∈ 𝒫_K} ψ_{K,n,P}` with all these
fields independent; only finitely many blocks matter for the field on `[0,1]²` (finite range).

* `T20B.hoBlock K b`: the half-open dyadic block `2^{-K}([i,i+1) × [j,j+1))` (the closed blocks
  of DDDF overlap on null sets; half-open ones are disjoint), `T20B.nearIdx K` a finite index set
  of blocks covering the `1/2`-neighbourhood of `[0,1]²` (`T20B.exists_nearIdx`).
* `T20B.blkVer`: a continuous version of `ψ_{a,b,B}` (`T20B.blkVer_spec`, Kolmogorov through
  `exists_continuous_modification_of_kernel`, the block kernel being dominated by the full one).
* `T20B.sum_blkVer_ae`: a.s. `ψ_{K,n} = Σ_{b ∈ nearIdx K} ψ_{K,n,b}` on `[0,1]²` (needs
  `PsiSmall Q`: range `2σ ≤ 1/2`).
* `T20B.iIndepFun_sumElim_prod`: an independent family read on both coordinates of `μ ⊗ μ`
  gives an independent family indexed by `ι ⊕ ι` (the resampling space of Efron–Stein).
* `T20B.fLen`: a measurable function of the field values on the dyadic centres that equals
  `log L_{1,1}` for continuous fields (`T20B.fLen_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

namespace T20B

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### Dyadic centres and the measurable length functional -/

/-- all dyadic block centres of `[0,1]²` -/
def dyD : Set ℂ := ⋃ k, (L23.grid k : Set ℂ)

instance : Countable dyD :=
  (Set.countable_iUnion fun k => (L23.grid k).countable_toSet).to_subtype

/-- restriction of a field to the dyadic centres -/
def restrD (f : ℂ → ℝ) : dyD → ℝ := fun c => f c

lemma measurable_restrD : Measurable restrD :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- the level-`k` grid values of a function on `dyD` -/
def gridOfD (k : ℕ) (v : dyD → ℝ) : L23.grid k → ℝ :=
  fun c => v ⟨c, Set.mem_iUnion.2 ⟨k, c.2⟩⟩

lemma measurable_gridOfD (k : ℕ) : Measurable (gridOfD k) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- `log L_{1,1}` as a measurable function of the dyadic-centre values (a `liminf` of the
discretizations of `L23Disc.lean`) -/
def fLen (ξ : ℝ) {ι : Type*} [Fintype ι] (v : ι → dyD → ℝ) : ℝ :=
  Filter.liminf (fun k => L23.discLogLen ξ k (gridOfD k (∑ i, v i))) atTop

lemma measurable_fLen (ξ : ℝ) {ι : Type*} [Fintype ι] :
    Measurable (fLen ξ (ι := ι)) := by
  refine Measurable.liminf fun k => ?_
  have h1 : Measurable fun v : ι → dyD → ℝ => ∑ i, v i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (L23.lipschitzWith_discLogLen ξ k).continuous.measurable.comp
    ((measurable_gridOfD k).comp h1)

lemma fLen_eq {ξ : ℝ} {ι : Type*} [Fintype ι] {v : ι → dyD → ℝ} {g : ℂ → ℝ}
    (hg : Continuous g) (hv : ∀ c : dyD, ∑ i, v i c = g c) : fLen ξ v = L23.logLen ξ g := by
  refine Tendsto.liminf_eq ?_
  have h := L23.tendsto_logLen_snap (ξ := ξ) hg
  refine h.congr fun k => ?_
  unfold L23.discLogLen gridOfD
  congr 1
  funext x
  rw [Finset.sum_apply, hv]

/-! ### Half-open dyadic blocks -/

/-- the half-open block `2^{-K}([i,i+1) × [j,j+1))` -/
def hoBlock (K : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  {y | ⌊y.re * 2 ^ K⌋ = b.1 ∧ ⌊y.im * 2 ^ K⌋ = b.2}

lemma measurableSet_hoBlock (K : ℕ) (b : ℤ × ℤ) : MeasurableSet (hoBlock K b) := by
  have h1 : Measurable fun y : ℂ => ⌊y.re * 2 ^ K⌋ :=
    Int.measurable_floor.comp (Complex.measurable_re.mul_const _)
  have h2 : Measurable fun y : ℂ => ⌊y.im * 2 ^ K⌋ :=
    Int.measurable_floor.comp (Complex.measurable_im.mul_const _)
  exact (h1 (measurableSet_singleton b.1)).inter (h2 (measurableSet_singleton b.2))

lemma pairwise_disjoint_hoBlock (K : ℕ) : Pairwise fun b b' => Disjoint (hoBlock K b) (hoBlock K b') := by
  intro b b' hbb
  refine Set.disjoint_left.2 fun y h1 h2 => hbb ?_
  exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)

/-- indices of the blocks that can meet the `1/2`-neighbourhood of `[0,1]²` -/
def nearIdx (K : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(2 : ℤ) ^ K) (2 ^ (K + 1)) ×ˢ Finset.Icc (-(2 : ℤ) ^ K) (2 ^ (K + 1))

lemma floor_mem_Icc (K : ℕ) {r : ℝ} (h1 : -1 < r) (h2 : r < 2) :
    ⌊r * 2 ^ K⌋ ∈ Finset.Icc (-(2 : ℤ) ^ K) (2 ^ (K + 1)) := by
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.le_floor]; push_cast; nlinarith
  · have := Int.floor_le (r * 2 ^ K)
    have h3 : ((⌊r * 2 ^ K⌋ : ℤ) : ℝ) ≤ ((2 ^ (K + 1) : ℤ) : ℝ) := by
      push_cast; rw [pow_succ]; nlinarith
    exact_mod_cast h3

lemma exists_nearIdx (K : ℕ) {x y : ℂ} (hx : x ∈ L23.sq01) (hxy : ‖x - y‖ < 2 * (1 / 4)) :
    ∃ b ∈ nearIdx K, y ∈ hoBlock K b := by
  rw [L23.mem_sq01] at hx
  have hre := Complex.abs_re_le_norm (x - y)
  have him := Complex.abs_im_le_norm (x - y)
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  refine ⟨(⌊y.re * 2 ^ K⌋, ⌊y.im * 2 ^ K⌋), ?_, rfl, rfl⟩
  rw [nearIdx, Finset.mem_product]
  exact ⟨floor_mem_Icc K (by linarith [hx.1.1]) (by linarith [hx.1.2]),
    floor_mem_Icc K (by linarith [hx.2.1]) (by linarith [hx.2.2])⟩

/-! ### Continuous versions of the block fields -/

lemma sq_norm_blockKernelL2_sub_le (Q : PsiParams) {a b : ℝ} (ha : 0 < a) {B : Set ℂ}
    (hB : MeasurableSet B) (x x' : ℂ) :
    ‖Q.blockKernelL2 a b B x - Q.blockKernelL2 a b B x'‖ ^ 2 ≤
      ‖Q.psiKernelL2 a b x - Q.psiKernelL2 a b x'‖ ^ 2 := by
  refine pow_le_pow_left₀ (norm_nonneg _) (Lp.norm_le_norm_of_ae_le ?_) 2
  filter_upwards [Lp.coeFn_sub (Q.blockKernelL2 a b B x) (Q.blockKernelL2 a b B x'),
    Lp.coeFn_sub (Q.psiKernelL2 a b x) (Q.psiKernelL2 a b x'),
    Q.coeFn_blockKernelL2 a b ha hB x, Q.coeFn_blockKernelL2 a b ha hB x',
    Q.coeFn_psiKernelL2 a b ha x, Q.coeFn_psiKernelL2 a b ha x'] with p e1 e2 e3 e4 e5 e6
  rw [e1, e2, Pi.sub_apply, Pi.sub_apply, e3, e4, e5, e6, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [PsiParams.blockKernel, ← sub_mul]
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  by_cases h : p.2 ∈ B <;> simp [h, indicator]

open Classical in
/-- a continuous version of the block field `ψ_{a,b,B}` (junk `0` if there is none) -/
def blkVer (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) (B : Set ℂ) :
    ℂ → Ω → ℝ :=
  if h : ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] psiBlock Q W a b B x then h.choose else 0

theorem blkVer_spec (hW : IsWhiteNoise P W) (Q : PsiParams) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {B : Set ℂ} (hB : MeasurableSet B) :
    (∀ ω, Continuous fun x => blkVer Q W P a b B x ω) ∧ (∀ x, Measurable (blkVer Q W P a b B x)) ∧
      ∀ x, (fun ω => blkVer Q W P a b B x ω) =ᵐ[P] psiBlock Q W a b B x := by
  have h : ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] psiBlock Q W a b B x := by
    obtain ⟨K, hK, hF⟩ := Q.exists_sq_norm_psiKernelL2_sub_le ha hab
    exact exists_continuous_modification_of_kernel hW (Q.blockKernelL2 a b B) hK
      (fun x x' => (sq_norm_blockKernelL2_sub_le Q ha hB x x').trans (hF x x')) _
  rw [blkVer, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-! ### The decomposition on `[0,1]²` -/

/-- the projection of `ℂ` onto `[0,1]²` -/
def sqClamp (x : ℂ) : ℂ :=
  ((projIcc (0 : ℝ) 1 zero_le_one x.re : ℝ) : ℂ) +
    ((projIcc (0 : ℝ) 1 zero_le_one x.im : ℝ) : ℂ) * Complex.I

lemma continuous_sqClamp : Continuous sqClamp :=
  (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
    (continuous_projIcc.comp Complex.continuous_re))).add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp
      (continuous_projIcc.comp Complex.continuous_im))).mul continuous_const)

lemma sqClamp_mem (x : ℂ) : sqClamp x ∈ L23.sq01 := by
  rw [L23.mem_sq01]
  simp only [sqClamp, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add, zero_mul]
  exact ⟨(projIcc (0 : ℝ) 1 zero_le_one x.re).2, (projIcc (0 : ℝ) 1 zero_le_one x.im).2⟩

lemma sqClamp_of_mem {x : ℂ} (hx : x ∈ L23.sq01) : sqClamp x = x := by
  rw [L23.mem_sq01] at hx
  apply Complex.ext <;> simp [sqClamp, projIcc_of_mem _ hx.1, projIcc_of_mem _ hx.2]

/-- the continuous block fields `ψ_{K,n,b}` -/
abbrev blkKn (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) (b : ℤ × ℤ) :
    ℂ → Ω → ℝ :=
  blkVer Q W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) (hoBlock K b)

theorem blkKn_spec (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    (b : ℤ × ℤ) :
    (∀ ω, Continuous fun x => blkKn Q W P K n b x ω) ∧ (∀ x, Measurable (blkKn Q W P K n b x)) ∧
      ∀ x, (fun ω => blkKn Q W P K n b x ω) =ᵐ[P]
        psiBlock Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) (hoBlock K b) x :=
  blkVer_spec hW Q (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn)
    (measurableSet_hoBlock K b)

/-- a.s. `ψ_{K,n} = Σ_{b ∈ nearIdx K} ψ_{K,n,b}` on `[0,1]²` (DDDF (2.19)–(2.20)) -/
theorem sum_blkKn_ae (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q) {K n : ℕ}
    (hKn : K ≤ n) :
    ∀ᵐ ω ∂P, ∀ x ∈ L23.sq01, ∑ b ∈ nearIdx K, blkKn Q W P K n b x ω = psiMN Q W P K n x ω := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW hKn
  have hS := fun b => blkKn_spec hW Q hKn b
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ 1 / 4 :=
    fun t ht => hQ t (lt_of_lt_of_le (by positivity) ht.1)
      (ht.2.trans (pow_le_one₀ (by positivity) hb1))
  have h := ae_eq_of_continuous_modification (P := P)
    (Y₁ := fun x ω => ∑ b ∈ nearIdx K, blkKn Q W P K n b (sqClamp x) ω)
    (Y₂ := fun x ω => psiMN Q W P K n (sqClamp x) ω)
    (fun ω => continuous_finsetSum _ fun b _ => ((hS b).1 ω).comp continuous_sqClamp)
    (fun ω => (hψ.cont ω).comp continuous_sqClamp) fun x => ?_
  · filter_upwards [h] with ω hω x hx
    have := hω x
    simp only [sqClamp_of_mem hx] at this
    exact this
  · have hdec := psi_eq_sum_psiBlock_ae hW Q ha (nearIdx K) (measurableSet_hoBlock K)
      (fun b _ b' _ hbb => pairwise_disjoint_hoBlock K hbb) hσ (sqClamp x)
      (fun y hy => exists_nearIdx K (sqClamp_mem x) hy)
    have hall : ∀ᵐ ω ∂P, ∀ b ∈ nearIdx K, blkKn Q W P K n b (sqClamp x) ω =
        psiBlock Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) (hoBlock K b) (sqClamp x) ω :=
      (Filter.eventually_all_finset _).2 fun b _ => (hS b).2.2 (sqClamp x)
    filter_upwards [hdec, hall, hψ.ae_eq (sqClamp x)] with ω e1 e2 e3
    rw [e3, e1]
    exact Finset.sum_congr rfl fun b hb => e2 b hb

/-! ### Independence on the resampling space -/

/-- an independent family read on both coordinates of `μ ⊗ μ` is independent (indexed by
`ι ⊕ ι`) -/
theorem iIndepFun_sumElim_prod {ι β : Type*} [Fintype ι] [MeasurableSpace β] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {R : ι → Ω → β} (hR : ∀ i, Measurable (R i))
    (h : iIndepFun R μ) :
    iIndepFun (fun k : ι ⊕ ι => Sum.elim (fun i (z : Ω × Ω) => R i z.1)
      (fun i (z : Ω × Ω) => R i z.2) k) (μ.prod μ) := by
  have hRv : Measurable fun ω i => R i ω := measurable_pi_iff.2 hR
  have hmeas : ∀ k : ι ⊕ ι, Measurable (Sum.elim (fun i (z : Ω × Ω) => R i z.1)
      (fun i (z : Ω × Ω) => R i z.2) k) := by
    rintro (i | i)
    · exact (hR i).comp measurable_fst
    · exact (hR i).comp measurable_snd
  rw [iIndepFun_iff_map_fun_eq_pi_map fun k => (hmeas k).aemeasurable]
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hR i).aemeasurable).1 h
  have hlaw : ∀ k : ι ⊕ ι, (μ.prod μ).map (Sum.elim (fun i (z : Ω × Ω) => R i z.1)
      (fun i (z : Ω × Ω) => R i z.2) k) = μ.map (R (Sum.elim id id k)) := by
    rintro (i | i)
    · exact map_comp_fst (hR i)
    · exact map_comp_snd (hR i)
  simp_rw [hlaw]
  have e := (measurePreserving_sumPiEquivProdPi_symm
    (fun k : ι ⊕ ι => μ.map (R (Sum.elim id id k)))).map_eq
  rw [← e]
  have h2 : (μ.prod μ).map (fun z : Ω × Ω => ((fun i => R i z.1), (fun i => R i z.2))) =
      (Measure.pi fun i => μ.map (R i)).prod (Measure.pi fun i => μ.map (R i)) := by
    rw [← hpi, Measure.map_prod_map _ _ hRv hRv]; rfl
  have h3 : (fun z : Ω × Ω => fun k : ι ⊕ ι => Sum.elim (fun i (z : Ω × Ω) => R i z.1)
      (fun i (z : Ω × Ω) => R i z.2) k z) =
      (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => β).symm ∘
        (fun z : Ω × Ω => ((fun i => R i z.1), (fun i => R i z.2))) := by
    funext z k; rcases k with i | i <;> rfl
  rw [h3, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), h2]
  rfl

end T20B

end DDDF
end LQGMetric
