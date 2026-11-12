/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Conversions at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Section2.Lemma23
import LatticeProb.Bonanno.LQGDimension.Section2.Bounds
import LatticeProb.Bonanno.LQGDimension.Assembly.AStarProved
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import Mathlib.Probability.Moments.SubGaussian

/-!
# Conversions between the draft blueprint and the proved obligations

Three small conversion lemmas.  The draft blueprint `LQGDimension.Blueprint.Draft`
(`LQGDimension/Blueprint/Draft/LFPPPlan.lean`) restates some results that are already proved
in slightly different forms; here we derive the draft forms from the proved ones.

* `draftLemma23 : Blueprint.Draft.Lemma23`, from `LQGDimension.lemma23_of`: the draft statement
  quantifies over `F : Finset (ℝ → ℝ)` with membership constraints instead of `F : Finset (V n)`,
  so we push the finite family forward along the inclusion `V n ↪ (ℝ → ℝ)`
  (`Finset.image Subtype.val`).  The `gaussianExpectedMax` values agree by the general
  reindexing lemma `gaussianExpectedMax_image` below.
* `draftEnergyBallSup : Blueprint.Draft.EnergyBallSup`, from `Blueprint.ZSupBound`
  (`zSupBound_of`): the two statements are identical up to notation.
* `draftGaussConcentration : Blueprint.Draft.GaussConcentration`, from
  `LQGDimension.maxConcentration` and `LQGDimension.MaxConc.integrable_exp_max`, restating the
  mgf bound as `HasSubgaussianMGF` with `κ = π² / 4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

/-! ## A reindexing lemma for `gaussianExpectedMax` -/

/-- `gaussianExpectedMax` is invariant under reindexing a finite family along `Finset.image`,
when the covariance kernel is positive semidefinite both on the image and on the kernel pulled
back along `φ` over the original index set.  Proved by realising both sides as `vecExpectedMax`
for Gram vector families (`exists_vecExpectedMax_eq_gaussianExpectedMax`), where the reindexing
is the elementary fact `L23.vecExpectedMax_image` (invariance of a finite supremum under
`Finset.image`), and comparing the two (equal) Gram matrices with
`vecExpectedMax_eq_of_gram_eq`. -/
theorem gaussianExpectedMax_image {ι κ : Type*} [DecidableEq κ] (F : Finset ι) (φ : ι → κ)
    (C : κ → κ → ℝ) (b : κ → ℝ) (hPSD : PSDOn (F.image φ) C)
    (hPSD' : PSDOn F (fun i j => C (φ i) (φ j))) :
    gaussianExpectedMax (F.image φ) C b =
      gaussianExpectedMax F (fun i j => C (φ i) (φ j)) (fun i => b (φ i)) := by
  obtain ⟨v, hv, hgem⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax (F.image φ) C hPSD
  obtain ⟨w, hw, hgem'⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun i j => C (φ i) (φ j)) hPSD'
  rw [hgem b, hgem' (fun i => b (φ i)), L23.vecExpectedMax_image F φ v b]
  refine vecExpectedMax_eq_of_gram_eq F (fun i => v (φ i)) w (fun i => b (φ i))
    fun i hi j hj => ?_
  rw [hw i hi j hj]
  exact hv (φ i) (Finset.mem_image_of_mem φ hi) (φ j) (Finset.mem_image_of_mem φ hj)

/-! ## Lemma 2.3, restated over `Finset (ℝ → ℝ)` -/

/-- The draft form of Lemma 2.3 (`Blueprint.Draft.Lemma23`), from `LQGDimension.lemma23_of`:
push the finite family `F : Finset (V n)` forward along the inclusion `V n ↪ (ℝ → ℝ)`. -/
theorem draftLemma23 : Blueprint.Draft.Lemma23 := by
  classical
  obtain ⟨C, N, hCN⟩ := lemma23_of maxConcentration (zSupBound_of aOneFinite aSubadditiveE)
    zVarBound aOneFinite aSubadditiveE
  refine ⟨C, N, fun n hn => ?_⟩
  obtain ⟨F, ⟨f₀, hf₀F, hf₀0⟩, hE, hsup, hcard, hgem⟩ := hCN n hn
  have hf0eq : (f₀ : ℝ → ℝ) = 0 := funext hf₀0
  have hPSDimg : PSDOn (F.image (Subtype.val : V n → ℝ → ℝ)) zCov := by
    apply zCovPSD
    intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hf
    exact mem_V_intervalIntegrable g.2
  have hPSDV : PSDOn F (fun i j => zCov (Subtype.val i : ℝ → ℝ) (Subtype.val j)) := zCovPSD_V n F
  have hgemeq := gaussianExpectedMax_image F (Subtype.val : V n → ℝ → ℝ) zCov
    (fun f => -energy f) hPSDimg hPSDV
  refine ⟨F.image (Subtype.val : V n → ℝ → ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hf
    exact g.2
  · rw [← hf0eq]
    exact Finset.mem_image_of_mem _ hf₀F
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
    exact hE g hg
  · intro f hf x
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
    exact hsup g hg x
  · rw [Finset.card_image_of_injective F Subtype.val_injective]
    exact hcard
  · rw [hgemeq]
    exact hgem

/-! ## (2.2), unchanged -/

/-! ## Gaussian concentration, restated with `HasSubgaussianMGF` -/

end LQGDimension
