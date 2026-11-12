/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BStep2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinCopy

/-!
# DDDF Theorem 20, Steps 2–3: Efron–Stein for `log L^{(n)}_{1,1}(ψ)` (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1075–1091 ((5.58) = `eq:EfronStein`,
(5.59) = `eq:SndTerm`). With the block decomposition (2.19)–(2.20)
`ψ_{0,n} = ψ_{0,K} + Σ_{P ∈ 𝒫_K} ψ_{K,n,P}`, the Efron–Stein inequality (resampling one
independent piece at a time) gives

  `Var log L_n(ψ) ≤ E((log L^K_n − log L_n)_+²) + Σ_{P ∈ 𝒫_K} E((log L^P_n − log L_n)_+²)`,

and Step 3 bounds the first term by `C K`.

Formalization: the resampling space is `Ω × Ω` with `P ⊗ P` (the pieces on the first
coordinate, the independent copies on the second); the pieces are the continuous versions of
`ψ_{0,K}` and of the block fields `ψ_{K,n,b}` for the finitely many half-open blocks `b ∈ nearIdx K`
(the other blocks do not affect the field on `[0,1]²`: finite range, needs `PsiSmall Q`), read on
the countable set of dyadic centres (so that the a.s. identities hold simultaneously and the
length functional `T20B.fLen` is measurable). Efron–Stein: `efronStein_copy_posPart`
(Prob/EfronSteinCopy.lean). The first term is bounded by `dddf_t20_step3` (`C = 2ξ² log 2`).

Main result: `dddf_t20_step2`. The block terms (DDDF Step 4, l. 1093–1177) are left as they are.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20B

lemma sum_update_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] (v : ι → E)
    (i : ι) (w : E) : ∑ o, Function.update v i w o = ∑ o, v o - v i + w := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ v (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  abel

end T20B

open T20B in
/-- **DDDF (5.58) + (5.59)** (`tightness.tex` l. 1075–1091, Steps 2–3 of Theorem 20): with
`ψ^b_{0,n} = ψ_{0,n} − ψ_{K,n,b} + ψ̃_{K,n,b}` (the block field `b` resampled; the copy is read
on the second coordinate of `Ω × Ω`),
`Var log L^{(n)}_{1,1}(ψ) ≤ 2ξ² K log 2 + Σ_{b ∈ nearIdx K} E (log L(ψ^b_{0,n}) − log L(ψ_{0,n}))_+²`. -/
theorem dddf_t20_step2 (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) :
    Var[L24.logLenPsi ξ Q W P n; P] ≤ 2 * (ξ ^ 2 * (K * Real.log 2)) +
      ∑ b ∈ nearIdx K, ∫ z, max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
        L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2 ∂(P.prod P) := by
  classical
  have := hW.isProbabilityMeasure
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hKn' := isPsiVersion_psiMN (Q := Q) hW hKn
  have h0n := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hB := fun b => blkKn_spec hW Q hKn b
  let S := nearIdx K
  let G : Option S → ℂ → Ω → ℝ := fun o => match o with
    | none => psiMN Q W P 0 K
    | some b => blkKn Q W P K n b.1
  have hGc : ∀ o ω, Continuous fun x => G o x ω := by
    rintro (_ | b) ω
    · exact h0K.cont ω
    · exact (hB b.1).1 ω
  have hGm : ∀ o x, Measurable (G o x) := by
    rintro (_ | b) x
    · exact h0K.meas x
    · exact (hB b.1).2.1 x
  let R : Option S → Ω → (dyD → ℝ) := fun o ω => restrD fun x => G o x ω
  have hR : ∀ o, Measurable (R o) := fun o => measurable_pi_iff.2 fun c => hGm o c
  -- independence of the pieces under `P`
  have hindR : iIndepFun R P := by
    have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    have hab : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ K :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn
    have hI := iIndepFun_psi_psiBlock hW Q ha hab ((2 : ℝ)⁻¹ ^ 0) (ι := ℤ × ℤ)
      (B := hoBlock K) (measurableSet_hoBlock K) (pairwise_disjoint_hoBlock K)
    have hI2 := (hI.precomp (g := Option.map (Subtype.val : S → ℤ × ℤ))
      (Option.map_injective Subtype.val_injective)).comp (fun _ => restrD)
      (fun _ => measurable_restrD)
    refine hI2.congr fun o => ?_
    rcases o with _ | b
    · have h : ∀ᵐ ω ∂P, ∀ c : dyD, psi Q W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) c ω =
          psiMN Q W P 0 K c ω := ae_all_iff.2 fun c => (h0K.ae_eq c).symm
      filter_upwards [h] with ω hω
      funext c
      exact hω c
    · have h : ∀ᵐ ω ∂P, ∀ c : dyD,
          psiBlock Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) (hoBlock K b.1) c ω =
            blkKn Q W P K n b.1 c ω := ae_all_iff.2 fun c => ((hB b.1).2.2 c).symm
      filter_upwards [h] with ω hω
      funext c
      exact hω c
  -- the resampling space
  let X : Option S → Ω × Ω → (dyD → ℝ) := fun o z => R o z.1
  let X' : Option S → Ω × Ω → (dyD → ℝ) := fun o z => R o z.2
  have hX : ∀ o, Measurable (X o) := fun o => (hR o).comp measurable_fst
  have hX' : ∀ o, Measurable (X' o) := fun o => (hR o).comp measurable_snd
  have hind : iIndep (esCopySigma X X') (P.prod P) := by
    have h := (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_sumElim_prod hR hindR)
    convert h using 2 with k
    rcases k with i | i <;> rfl
  have hlaw : ∀ o, (P.prod P).map (X' o) = (P.prod P).map (X o) := fun o =>
    (map_comp_snd (hR o)).trans (map_comp_fst (hR o)).symm
  -- the a.s. decomposition on `[0,1]²`
  have hdecP : ∀ᵐ ω ∂P, (∀ x ∈ L23.sq01, ∑ o, G o x ω = psiMN Q W P 0 n x ω) ∧
      ∀ x, psiMN Q W P 0 n x ω = psiMN Q W P K n x ω + psiMN Q W P 0 K x ω := by
    filter_upwards [sum_blkKn_ae hW Q hQ hKn, psiMN_add_ae hW Q hKn] with ω h1 h2
    refine ⟨fun x hx => ?_, h2⟩
    rw [Fintype.sum_option]
    simp only [G]
    rw [Finset.sum_coe_sort S (fun b => blkKn Q W P K n b x ω), h1 x hx, h2 x, add_comm]
  have hdec : ∀ᵐ z ∂(P.prod P), (∀ x ∈ L23.sq01, ∑ o, G o x z.1 = psiMN Q W P 0 n x z.1) ∧
      ∀ x, psiMN Q W P 0 n x z.1 = psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.1 :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hdecP
  -- the length functional on the pieces
  have hfX : ∀ z, fLen ξ (fun j => X j z) = L23.logLen ξ (fun x => ∑ o, G o x z.1) := fun z =>
    fLen_eq (continuous_finsetSum _ fun o _ => hGc o z.1) fun c => by
      simp only [X, R, restrD, Finset.sum_apply]
  have hfU : ∀ z i, fLen ξ (Function.update (fun j => X j z) i (X' i z)) =
      L23.logLen ξ (fun x => ∑ o, G o x z.1 - G i x z.1 + G i x z.2) := fun z i =>
    fLen_eq (((continuous_finsetSum _ fun o _ => hGc o z.1).sub (hGc i z.1)).add (hGc i z.2))
      fun c => by
        rw [← Finset.sum_apply, sum_update_eq]
        simp only [X, X', R, restrD, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  have hlogEq : ∀ {f g : ℂ → ℝ}, (∀ x ∈ L23.sq01, f x = g x) →
      L23.logLen ξ f = L23.logLen ξ g := fun h => by
    simp only [L23.logLen]; rw [rectLen_congr _ h]
  have hFae : (fun z => fLen ξ (fun j => X j z)) =ᵐ[P.prod P]
      fun z => L24.logLenPsi ξ Q W P n z.1 := by
    filter_upwards [hdec] with z hz
    rw [hfX z]
    exact hlogEq hz.1
  have hmem : MemLp (L24.logLenPsi ξ Q W P n) 2 P :=
    ((L24.psi_memLp_variance hW Q ξ).choose_spec.2 n).1
  have hFmem : MemLp (fun z => fLen ξ (fun j => X j z)) 2 (P.prod P) :=
    (hmem.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).ae_eq hFae.symm
  have hES := efronStein_copy_posPart (μ := P.prod P) hX hX' hind hlaw (measurable_fLen ξ) hFmem
  -- the variance
  have hmF : AEMeasurable (L24.logLenPsi ξ Q W P n) ((P.prod P).map Prod.fst) := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hmem.aestronglyMeasurable.aemeasurable
  have hvar : Var[fun z => fLen ξ (fun j => X j z); P.prod P] = Var[L24.logLenPsi ξ Q W P n; P] := by
    rw [variance_congr hFae,
      show (fun z : Ω × Ω => L24.logLenPsi ξ Q W P n z.1) = L24.logLenPsi ξ Q W P n ∘ Prod.fst
        from rfl,
      ← variance_map hmF measurable_fst.aemeasurable,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hvar]
  refine hES.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (le_of_eq ?_)
  · -- Step 3
    have h3 := dddf_t20_step3 hW Q ξ hKn
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) h3.1 ?_)
      h3.2
    filter_upwards [hdec] with z hz
    rw [hfU, hfX]
    have e1 : L23.logLen ξ (fun x => ∑ o, G o x z.1 - G none x z.1 + G none x z.2) =
        L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.2) :=
      hlogEq fun x hx => by
        rw [hz.1 x hx, hz.2 x]; simp only [G]; ring
    have e2 : L23.logLen ξ (fun x => ∑ o, G o x z.1) =
        L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.1) :=
      hlogEq fun x hx => by rw [hz.1 x hx, hz.2 x]
    rw [e1, e2]
    set d := L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.2) -
      L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.1)
    rcases le_total d 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg d]
    · rw [max_eq_left h]
  · -- the block terms
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun b _ => integral_congr_ae ?_
    filter_upwards [hdec] with z hz
    rw [hfU, hfX]
    have e1 : L23.logLen ξ (fun x => ∑ o, G o x z.1 - G (some b) x z.1 + G (some b) x z.2) =
        L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 - blkKn Q W P K n b x z.1 +
          blkKn Q W P K n b x z.2) :=
      hlogEq fun x hx => by rw [hz.1 x hx]
    have e2 : L23.logLen ξ (fun x => ∑ o, G o x z.1) =
        L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1) := hlogEq hz.1
    rw [e1, e2]

end DDDF
end LQGMetric
