/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CDefs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRatio

/-!
# DDDF Theorem 20, Step 4: the pathwise bound for visited blocks (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1095–1155. For a block `P ∈ 𝒫_K` visited by the
geodesic, DDDF glue a circuit around `P^K` (l. 1103–1105, (5.65)), bound its length by long
crossings at scale `2^{-K}` (l. 1110–1123, (5.66)), lower-bound `L^{(n)}_{1,1}(ψ)` by short
crossings (l. 1131–1146, (5.67)), and gather both (l. 1150–1155):

  `Σ_P E[(log L^P_n − log L_n)_+²]
     ≤ C K^{2ε₀} E[ Σ_{π^K} e^{2ξψ_{0,K}} / (Σ_{π^K} e^{ξψ_{0,K}})² · (max L(R^L)/min L(R^S))²
                    · e^{Cξ max osc} · e^{8ξX} ]`.

`T20Step4Pathwise` is the pathwise inequality inside this expectation, in the form used here:

* blocks are the half-open `hoBlock K b`, `b ∈ nearIdx K`; "visited" means the
  `(1+η)`-near-geodesic `γ_n` (D-DDDF-5) comes within `2s` of the block, `s ≥ σ_t` on
  `[4^{-n}, 4^{-K}]` (`dddf_t20_step4_far` handles the others);
* near-geodesics add the term `C₀ 4^K η²` (`L^P ≤ (1+η)L + circuit`, and `|nearIdx K| ≤ 16·4^K`);
* `X = Xbig` and the oscillation `Obig` (via `‖∇φ_{0,K}‖`, DDDF (5.68)) are taken on
  `[-2,3]² ⊇` all blocks of `nearIdx K` and their circuits, not on `[0,1]²`: blocks at the
  boundary of `[0,1]²` have centres and circuits outside the square (DDDF l. 1097–1105 do not
  discuss this; deviation entry proposed in the report);
* the long/short crossings are the `φ_{K,n}` crossings `mrectLen` of `u 2^{-K} R_{3,1} + c`,
  `u 2^{-K} R_{1,3} + c` over finite families `J`, `J'` of at most `C₀ 4^K` rectangles.

`T20C.holder4`, `T20C.sum_lintegral_le`, `T20C.exists_sublinear` are the tools of the
assembly (`T20CAsm.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20C

/-- the offsets `c ∈ {-2,…,2}²`: the boxes `c + [0,1]²` cover `[-2,3]²` -/
def offs : Finset ℂ :=
  (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2).image fun p => (⟨p.1, p.2⟩ : ℂ)

lemma offs_nonempty : offs.Nonempty :=
  Finset.Nonempty.image ⟨((0 : ℤ), (0 : ℤ)), by simp⟩ _

lemma card_offs_le : offs.card ≤ 25 := by
  unfold offs
  refine Finset.card_image_le.trans (le_of_eq ?_)
  simp

/-- the corner of `[-2,3]²` -/
def cBig : ℂ := ⟨-2, -2⟩

/-- DDDF's `X` (l. 1112) on `[-2,3]²` -/
def Xbig (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (ω : Ω) : ℝ :=
  (XAB (fun n y => phiMN W P 0 n (y + cBig) ω) (fun n y => psiMN Q W P 0 n (y + cBig) ω) 5 5).toReal

/-- `2^{-K} sup_{[-2,3]²} ‖∇Y‖` for a `C¹` version `Y` of `φ_{0,K}` (DDDF (5.68)) -/
def Obig (K : ℕ) (Y : ℂ → Ω → ℝ) (ω : Ω) : ℝ :=
  offs.sup' offs_nonempty fun c =>
    ((2 : ℝ) ^ K)⁻¹ * ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c) ω) z‖

/-- `max_{J} L^{(K,n)}(R^L) / min_{J'} L^{(K,n)}(R^S)` (DDDF l. 1155) -/
def lsRatio (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) (J J' : Finset (Circle × ℂ))
    (hJ : J.Nonempty) (hJ' : J'.Nonempty) (ω : Ω) : ℝ :=
  J.sup' hJ (fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1) /
    J'.inf' hJ' (fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 1 3)

/-- `(log L^b_n(ψ) − log L_n(ψ))_+` (DDDF (5.58)) on `Ω × Ω` -/
def incr (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) (b : ℤ × ℤ)
    (z : Ω × Ω) : ℝ :=
  max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
    T20B.blkKn Q W P K n b x z.2) - L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0

/-- the near-geodesic comes within `2s` of the block `b` -/
def visSet (γ : ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ) (s : ℝ) : Set (Ω × Ω) :=
  {z | ∃ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∉ T20B.farSet (T20B.hoBlock K b) s}

end T20C

open T20C in
/-- **DDDF Step 4, pathwise part** (`tightness.tex` l. 1095–1155): the circuit gluing (5.65),
the numerator bound (5.66) and the denominator bound (5.67), summed over the visited blocks,
pathwise. Open (see `handoff/P2-DDDFT20c.md`). -/
def T20Step4Pathwise (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d : ℕ, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∃ (J J' : Finset (Circle × ℂ)) (hJ : J.Nonempty) (hJ' : J'.Nonempty),
      ((J.card : ℝ) + J'.card ≤ C₀ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ z ∂(P.prod P), ∑ b ∈ T20B.nearIdx K, (visSet γ n K b s).indicator
            (fun z => ENNReal.ofReal (incr ξ Q W P K n b z ^ 2)) z ≤
          ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) +
          ENNReal.ofReal (C₀ * ((K : ℝ) + 1) ^ d * Real.exp (C₀ * Xbig Q W P z.1) *
            Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y z.1) *
            lsRatio ξ W P K n J J' hJ hJ' z.1 ^ 2 *
            T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1))

namespace T20C

/-- Hölder's inequality for four functions -/
lemma holder4 {μ : Measure Ω} {f : Fin 4 → Ω → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ)
    {q : Fin 4 → ℝ} (hq : ∀ i, 0 < q i) (hsum : ∑ i, (q i)⁻¹ = 1) :
    ∫⁻ ω, ∏ i, f i ω ∂μ ≤ ∏ i, (∫⁻ ω, f i ω ^ q i ∂μ) ^ (q i)⁻¹ := by
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i ω => f i ω ^ q i) (fun i _ => (hf i).pow_const _) (p := fun i => (q i)⁻¹) hsum
    (fun i _ => (inv_pos.2 (hq i)).le)
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun ω => Finset.prod_congr rfl fun i _ => ?_
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (hq i).ne', ENNReal.rpow_one]

/-- superadditivity of the lower integral over a finite sum -/
lemma sum_lintegral_le {ι : Type*} (s : Finset ι) {μ : Measure Ω} (g : ι → Ω → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ ω, g i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, g i ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    simp_rw [Finset.sum_insert hi]
    exact (add_le_add_right ih _).trans (le_lintegral_add _ _)

/-- sublinear terms are eventually dominated: `B K^θ ≤ δ K` for `θ < 1` -/
lemma exists_sublinear {θ : ℝ} (hθ : θ < 1) (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → B * (K : ℝ) ^ θ ≤ δ * K := by
  have ht := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp
    tendsto_natCast_atTop_atTop
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < δ / (|B| + 1) by positivity))).and
    (eventually_ge_atTop 1)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨h1, h2⟩ := hK₀ K hK
  simp only [Function.comp_apply] at h1
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast h2
  have hK0 : (0 : ℝ) < K := by linarith
  have e : (K : ℝ) ^ θ = (K : ℝ) ^ (-(1 - θ)) * K := by
    rw [← Real.rpow_add_one hK0.ne']; congr 1; ring
  have hp : 0 ≤ (K : ℝ) ^ (-(1 - θ)) := by positivity
  have hB1 : 0 < |B| + 1 := by positivity
  calc B * (K : ℝ) ^ θ ≤ |B| * (K : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ (|B| + 1) * (K : ℝ) ^ θ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (|B| + 1) * (K : ℝ) ^ (-(1 - θ)) * K := by rw [e]; ring
    _ ≤ (|B| + 1) * (δ / (|B| + 1)) * K := by gcongr
    _ = δ * K := by field_simp

end T20C

end DDDF
end LQGMetric
