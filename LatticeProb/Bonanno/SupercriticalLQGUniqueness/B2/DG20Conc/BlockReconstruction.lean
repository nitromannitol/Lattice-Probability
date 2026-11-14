/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.BlockReconstruction at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep2

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 
def psiPiece (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) : Option (T20B.nearIdx K) → ℂ → Ω → ℝ
  | none => psiMN Q W P 0 K
  | some b => T20B.blkKn Q W P K n b.1

 


theorem iIndepFun_psi_piece (hW : IsWhiteNoise P W) (Q : PsiParams)
    {K n : ℕ} (hKn : K ≤ n) :
    iIndepFun (fun o : Option (T20B.nearIdx K) =>
      fun ω => T20B.restrD (fun x => psiPiece Q W P K n o x ω)) P := by
  have := hW.isProbabilityMeasure
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn
  have hI := iIndepFun_psi_psiBlock hW Q ha hab ((2 : ℝ)⁻¹ ^ 0)
    (ι := ℤ × ℤ) (B := T20B.hoBlock K) (T20B.measurableSet_hoBlock K)
    (T20B.pairwise_disjoint_hoBlock K)
  have hI2 := (hI.precomp (g := Option.map
    (Subtype.val : (T20B.nearIdx K) → ℤ × ℤ))
    (Option.map_injective Subtype.val_injective)).comp
    (fun _ => T20B.restrD) (fun _ => T20B.measurable_restrD)
  refine hI2.congr fun o => ?_
  rcases o with _ | b
  · have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
    have h : ∀ᵐ ω ∂P, ∀ c : T20B.dyD,
        psi Q W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) c ω =
          psiMN Q W P 0 K c ω :=
      ae_all_iff.2 fun c => (h0K.ae_eq c).symm
    filter_upwards [h] with ω hω
    funext c
    exact hω c
  · have hB := T20B.blkKn_spec hW Q hKn b.1
    have h : ∀ᵐ ω ∂P, ∀ c : T20B.dyD,
        psiBlock Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K)
          (T20B.hoBlock K b.1) c ω =
          T20B.blkKn Q W P K n b.1 c ω :=
      ae_all_iff.2 fun c => (hB.2.2 c).symm
    filter_upwards [h] with ω hω
    funext c
    exact hω c

end SupercriticalLQGUniqueness.B2.DG20Conc
