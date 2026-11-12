/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsiBlock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiAdd
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseIndep

/-!
# Block fields of `ψ`, finite range and independence (task P2-DDDFPSI; blueprint DDDF.D2.psi)

DDDF (arXiv:1904.08021, `tightness.tex` l. 360–376): for a spatial block `P` (DDDF use the
dyadic blocks `𝒫_k = {2^{-k}([i,i+1] × [j,j+1])}`, (2.6) = `Pndef`, l. 322),
`ψ_{a,b,P}(x) := √π ∫_{a²}^{b²} ∫_P p^{Tr}_{t/2}(x − y) W(dy, dt)` — DDDF's `ψ_{k,P}` is
`(a,b) = (2^{-k}, 2^{-k+1})` and `ψ_{K,n,P}` is `(a,b) = (2^{-n}, 2^{-K})` (with D-DDDF-2: the
printed upper limit `2^{-2K+2}` double counts the times of `ψ_{0,K}`).

* `blockKernel_eq_zero_of_far`: **finite range**: the kernel vanishes when `|x − y| ≥ 2σ_t`
  ("thanks to the truncation, the fields have finite correlation length", l. 358).
* `supportedIn_blockKernelL2`: `ψ_{a,b,P}` only sees the noise on `[a², b²) × P`.
* `iIndepFun_psiBlock`: for pairwise disjoint blocks, the block fields (as random functions of
  `x`) are mutually independent (white noise on disjoint sets, `iIndepFun_of_pairwise_disjoint`).
* `psi_eq_sum_psiBlock_ae`: `ψ_{a,b}(x) = Σ_{P ∈ S} ψ_{a,b,P}(x)` a.s. for a finite family of
  pairwise disjoint blocks covering `{y : |x − y| < 2 s}`, `s ≥ sup_{[a²,b²]} σ` — the block
  decomposition (2.19)–(2.20) at a point (only finitely many blocks contribute).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace PsiParams

variable (Q : PsiParams)

/-- The block kernel `1_{[a²,b²]}(t) p^{Tr}_{t/2}(x − y) 1_B(y)`. -/
def blockKernel (a b : ℝ) (B : Set ℂ) (x : ℂ) (p : ℝ × ℂ) : ℝ :=
  Q.psiKernel a b x p * B.indicator 1 p.2

lemma measurable_blockKernel (a b : ℝ) {B : Set ℂ} (hB : MeasurableSet B) (x : ℂ) :
    Measurable (Q.blockKernel a b B x) :=
  (Q.measurable_psiKernel a b x).mul ((measurable_const.indicator hB).comp measurable_snd)

lemma abs_blockKernel_le (a b : ℝ) (B : Set ℂ) (x : ℂ) (p : ℝ × ℂ) :
    |Q.blockKernel a b B x p| ≤ |Q.psiKernel a b x p| := by
  unfold blockKernel
  by_cases h : p.2 ∈ B <;> simp [h, indicator]

lemma memLp_blockKernel (a b : ℝ) (ha : 0 < a) {B : Set ℂ} (hB : MeasurableSet B) (x : ℂ) :
    MemLp (Q.blockKernel a b B x) 2 (volume : Measure (ℝ × ℂ)) :=
  (Q.memLp_psiKernel a b ha x).of_le (Q.measurable_blockKernel a b hB x).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Q.abs_blockKernel_le a b B x p)

open Classical in
/-- The `L²` class of the block kernel (junk `0` unless `0 < a` and `B` is measurable). -/
def blockKernelL2 (a b : ℝ) (B : Set ℂ) (x : ℂ) : WNSpace :=
  if h : 0 < a ∧ MeasurableSet B then (Q.memLp_blockKernel a b h.1 h.2 x).toLp _ else 0

lemma coeFn_blockKernelL2 (a b : ℝ) (ha : 0 < a) {B : Set ℂ} (hB : MeasurableSet B) (x : ℂ) :
    (Q.blockKernelL2 a b B x : ℝ × ℂ → ℝ) =ᵐ[volume] Q.blockKernel a b B x := by
  rw [blockKernelL2, dite_eq_left_of_eq_true (eq_true ⟨ha, hB⟩)]
  exact MemLp.coeFn_toLp _

/-- **Finite range**: `p^{Tr}_{t/2}(x − y) = 0` when `|x − y| ≥ 2σ_t` (DDDF l. 358). -/
lemma psiKernel_eq_zero_of_far (a b : ℝ) (x : ℂ) {p : ℝ × ℂ} (ht : 0 < p.1)
    (hfar : 2 * Q.sigma p.1 ≤ ‖x - p.2‖) : Q.psiKernel a b x p = 0 := by
  have hs := Q.sigma_pos ht
  have hT : Q.trunc x p = 0 := by
    refine Q.cut.eq_zero _ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), le_inv_mul_iff₀ hs]
    linarith
  simp [psiKernel, hT]

lemma ae_ne_sq (b : ℝ) : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ b ^ 2 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {p : ℝ × ℂ | p.1 = b ^ 2} = {b ^ 2} ×ˢ univ := by ext p; simp
  rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
  simp

/-- `ψ_{a,b,B}` only sees the white noise on `[a², b²) × B`. -/
lemma supportedIn_blockKernelL2 {a : ℝ} (ha : 0 < a) (b : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) (x : ℂ) :
    SupportedIn (Ico (a ^ 2) (b ^ 2) ×ˢ B) (Q.blockKernelL2 a b B x) := by
  have h : ∀ᵐ p : ℝ × ℂ ∂volume, p ∈ (Ico (a ^ 2) (b ^ 2) ×ˢ B)ᶜ →
      (Q.blockKernelL2 a b B x : ℝ × ℂ → ℝ) p = 0 := by
    filter_upwards [Q.coeFn_blockKernelL2 a b ha hB x, ae_ne_sq b] with p h1 h2 hp
    rw [h1]
    simp only [blockKernel, psiKernel, phiKernel]
    by_cases hpB : p.2 ∈ B
    · have hq : p ∉ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := by
        intro hq
        refine hp ⟨⟨(mem_prod.mp hq).1.1, lt_of_le_of_ne (mem_prod.mp hq).1.2 h2⟩, hpB⟩
      simp [indicator_of_notMem hq]
    · simp [indicator_of_notMem hpB]
  exact (ae_restrict_iff' ((measurableSet_Ico.prod hB).compl)).mpr h

end PsiParams

/-- DDDF's block field `ψ_{a,b,B}(x) = √π ∫_{a²}^{b²} ∫_B p^{Tr}_{t/2}(x − y) W(dy, dt)`. -/
def psiBlock (Q : PsiParams) (W : WNSpace → Ω → ℝ) (a b : ℝ) (B : Set ℂ) (x : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (Q.blockKernelL2 a b B x) ω

/-- a.s. finite additivity `W (Σ f_i) = Σ W f_i`. -/
theorem IsWhiteNoise.sum_ae (hW : IsWhiteNoise P W) {ι : Type*} (S : Finset ι)
    (f : ι → WNSpace) : W (∑ i ∈ S, f i) =ᵐ[P] fun ω => ∑ i ∈ S, W (f i) ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := hW.smul_ae 0 0
    filter_upwards [h] with ω hω
    simp only [zero_smul, zero_mul] at hω
    simp [hω]
  | insert j S hj ih =>
    filter_upwards [hW.add_ae (f j) (∑ i ∈ S, f i), ih] with ω h1 h2
    rw [Finset.sum_insert hj, h1, h2, Finset.sum_insert hj]

/-- **Block decomposition at a point** (DDDF (2.19)–(2.20)): if the pairwise disjoint
measurable blocks `B i`, `i ∈ S`, cover `{y : |x − y| < 2s}` with `σ_t ≤ s` on `[a², b²]`, then
`ψ_{a,b}(x) = Σ_{i ∈ S} ψ_{a,b,B i}(x)` almost surely. -/
theorem psi_eq_sum_psiBlock_ae (hW : IsWhiteNoise P W) (Q : PsiParams) {a b s : ℝ}
    (ha : 0 < a) {ι : Type*} (S : Finset ι) {B : ι → Set ℂ} (hB : ∀ i, MeasurableSet (B i))
    (hd : (S : Set ι).PairwiseDisjoint B) (hσ : ∀ t ∈ Icc (a ^ 2) (b ^ 2), Q.sigma t ≤ s)
    (x : ℂ) (hcov : ∀ y : ℂ, ‖x - y‖ < 2 * s → ∃ i ∈ S, y ∈ B i) :
    psi Q W a b x =ᵐ[P] fun ω => ∑ i ∈ S, psiBlock Q W a b (B i) x ω := by
  have hL2 : Q.psiKernelL2 a b x = ∑ i ∈ S, Q.blockKernelL2 a b (B i) x := by
    refine Lp.ext ?_
    have h3 : ∀ᵐ p ∂(volume : Measure (ℝ × ℂ)), ∀ i ∈ S,
        (Q.blockKernelL2 a b (B i) x : ℝ × ℂ → ℝ) p = Q.blockKernel a b (B i) x p :=
      (Filter.eventually_all_finset S).mpr fun i _ => Q.coeFn_blockKernelL2 a b ha (hB i) x
    filter_upwards [Q.coeFn_psiKernelL2 a b ha x,
      Lp.coeFn_finsetSum S (fun i => Q.blockKernelL2 a b (B i) x), h3] with p h1 h2 h3
    rw [h1, h2, Finset.sum_apply, Finset.sum_congr rfl h3]
    simp only [PsiParams.blockKernel]
    rw [← Finset.mul_sum]
    by_cases h0 : Q.psiKernel a b x p = 0
    · rw [h0, zero_mul]
    · have hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := by
        by_contra hp
        exact h0 (by simp [PsiParams.psiKernel, phiKernel, indicator_of_notMem hp])
      have ht : 0 < p.1 := lt_of_lt_of_le (by positivity) (mem_prod.mp hp).1.1
      have hnear : ‖x - p.2‖ < 2 * s := by
        by_contra hfar
        push Not at hfar
        exact h0 (Q.psiKernel_eq_zero_of_far a b x ht
          ((mul_le_mul_of_nonneg_left (hσ _ (mem_prod.mp hp).1) (by norm_num)).trans hfar))
      obtain ⟨i, hiS, hi⟩ := hcov p.2 hnear
      rw [Finset.sum_eq_single i (fun j hjS hji => ?_) (fun h => absurd hiS h)]
      · simp [indicator_of_mem hi]
      · have : p.2 ∉ B j := fun hj => (Set.disjoint_left.mp (hd hjS hiS hji)) hj hi
        simp [indicator_of_notMem this]
  filter_upwards [hW.sum_ae S (fun i => Q.blockKernelL2 a b (B i) x)] with ω h
  simp only [psi, psiBlock]
  rw [hL2, h, Finset.mul_sum]

lemma PsiParams.supportedIn_psiKernelL2 (Q : PsiParams) {b : ℝ} (hb : 0 < b) (c : ℝ) (x : ℂ) :
    SupportedIn (Icc (b ^ 2) (c ^ 2) ×ˢ univ) (Q.psiKernelL2 b c x) := by
  have h : ∀ᵐ p : ℝ × ℂ ∂volume, p ∈ (Icc (b ^ 2) (c ^ 2) ×ˢ univ)ᶜ →
      (Q.psiKernelL2 b c x : ℝ × ℂ → ℝ) p = 0 := by
    filter_upwards [Q.coeFn_psiKernelL2 b c hb x] with p h1 hp
    rw [h1]
    simp [PsiParams.psiKernel, phiKernel, indicator_of_notMem hp]
  exact (ae_restrict_iff' ((measurableSet_Icc.prod MeasurableSet.univ).compl)).mpr h

/-- **Joint independence of `ψ_{b,c}` and the block fields `ψ_{a,b,B i}`** over pairwise
disjoint blocks (DDDF (2.20): `ψ_{0,K}` and the `ψ_{K,n,P}`, `P ∈ 𝒫_K`, are independent; this is
what the Efron–Stein resampling in Thm 20 uses). Index `none` is `ψ_{b,c}`. -/
theorem iIndepFun_psi_psiBlock (hW : IsWhiteNoise P W) (Q : PsiParams) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (c : ℝ) {ι : Type} {B : ι → Set ℂ} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise fun i j => Disjoint (B i) (B j)) :
    iIndepFun (fun (o : Option ι) ω (x : ℂ) => match o with
      | none => psi Q W b c x ω
      | some i => psiBlock Q W a b (B i) x ω) P := by
  have hb : 0 < b := ha.trans_le hab
  let A : Option ι → Set (ℝ × ℂ) := fun o => match o with
    | none => Icc (b ^ 2) (c ^ 2) ×ˢ univ
    | some i => Ico (a ^ 2) (b ^ 2) ×ˢ B i
  have hA : Pairwise fun o o' => Disjoint (A o) (A o') := by
    have htime : Disjoint (Icc (b ^ 2) (c ^ 2)) (Ico (a ^ 2) (b ^ 2)) :=
      Set.disjoint_left.mpr fun t h1 h2 => absurd h1.1 (not_le.mpr h2.2)
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact Set.disjoint_prod.mpr (Or.inl htime)
    · exact Set.disjoint_prod.mpr (Or.inl htime.symm)
    · exact Set.disjoint_prod.mpr (Or.inr (hd fun h => hij (by rw [h])))
  have hI := hW.iIndepFun_of_pairwise_disjoint hA
  let Φ : (o : Option ι) → ({f // SupportedIn (A o) f} → ℝ) → ℂ → ℝ := fun o =>
    match o with
    | none => fun F x => Real.sqrt Real.pi * F ⟨Q.psiKernelL2 b c x,
        Q.supportedIn_psiKernelL2 hb c x⟩
    | some i => fun F x => Real.sqrt Real.pi * F ⟨Q.blockKernelL2 a b (B i) x,
        Q.supportedIn_blockKernelL2 ha b (hB i) x⟩
  have hΦ : ∀ o, Measurable (Φ o) := by
    rintro (_ | i)
    · exact measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
    · exact measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  have h := hI.comp Φ hΦ
  convert h using 2 with o
  rcases o with _ | i <;> rfl

end WhiteNoise
end LQGMetric
