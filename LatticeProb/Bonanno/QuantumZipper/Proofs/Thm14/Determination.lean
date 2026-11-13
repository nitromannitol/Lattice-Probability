/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm14.Determination at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Theorem 1.4(b): the measurable-selection step

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.4(b) ("`h` determines `η_T`").

This file proves the measure-theoretic half of Theorem 1.4(b):

* `exists_measurable_of_partialGraph` (Lusin–Souslin): a Borel partial graph `G ⊆ S × E` of
  standard Borel spaces is contained in the graph of a measurable map `S → E`;
* `measurable_recoverDrive`, `recoverDrive_sampleDrive`: a continuous driver on `[0,T]` is
  recovered measurably from its values at (clamped) rational times;
* `theorem1_4b_of_weldingDeterminationGraph`: Theorem 1.4(b) follows from
  `WeldingDeterminationGraph`, i.e. from the existence (in every setup) of a countable family
  `ρ` of mass-zero test functions and a Borel partial graph in (pairings with `ρ`) × (driver at
  rational times) that almost surely contains the pair `((⟨h, ρ n⟩)_n, W|ℚ)`.

Theorem 1.4(b) exposes `h` only through its pairings with mass-zero test functions (the
distribution modulo additive constants, audit AUDIT-1 §2). The space `TestFun0 H → ℝ` is not
standard Borel, so Lusin–Souslin is applied to a countable subfamily of pairings. This loses
nothing, because `R_h` is a.s. a measurable function of countably many pairings.

`WeldingDeterminationGraph` is not a consequence of `theorem1_4a` alone (see the report of
task THM14B): one also needs that the true driver satisfies the hypotheses of 1.4(a) (Theorem
1.3), that `h` determines `0₋`, that the hull determines the driver, and Borel measurability of
the welding relation.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

namespace Thm14Determination

/-! ### Lusin–Souslin selection -/

/-- `G` is a partial graph: each first coordinate has at most one partner. -/
def IsPartialGraph {S E : Type*} (G : Set (S × E)) : Prop :=
  ∀ ⦃y : S⦄ ⦃z z' : E⦄, (y, z) ∈ G → (y, z') ∈ G → z = z'

/-- **Lusin–Souslin selection.** A measurable partial graph in a product of standard Borel
spaces is contained in the graph of a measurable map. -/
theorem exists_measurable_of_partialGraph {S E : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    {G : Set (S × E)} (hGm : MeasurableSet G) (hG : IsPartialGraph G) :
    ∃ F : S → E, Measurable F ∧ ∀ p ∈ G, F p.1 = p.2 := by
  have := hGm.standardBorel
  have emb : MeasurableEmbedding (fun p : G => (p : S × E).1) :=
    Measurable.measurableEmbedding (measurable_fst.comp measurable_subtype_coe)
      (fun a b hab => by
        have hb : ((a : S × E).1, (b : S × E).2) ∈ G := by
          have h2 := b.2
          rw [show (a : S × E).1 = (b : S × E).1 from hab]
          exact h2
        exact Subtype.ext (Prod.ext hab (hG a.2 hb)))
  obtain ⟨F, hF, hcomp⟩ := emb.exists_measurable_extend
    (g := fun p : G => (p : S × E).2) (measurable_snd.comp measurable_subtype_coe)
    (fun _ => inferInstance)
  exact ⟨F, hF, fun p hp => congrFun hcomp ⟨p, hp⟩⟩

/-- A.e. form of the selection: if `(Y, Z)` lies a.s. in a measurable partial graph, then `Z`
is a.s. a measurable function of `Y` (no measurability of `Y`, `Z` is needed). -/
theorem exists_measurable_ae_eq_of_partialGraph {Ω S E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace E] [StandardBorelSpace E]
    [Nonempty E] (P : Measure Ω) {G : Set (S × E)} (hGm : MeasurableSet G)
    (hG : IsPartialGraph G) (Y : Ω → S) (Z : Ω → E) (hmem : ∀ᵐ ω ∂P, (Y ω, Z ω) ∈ G) :
    ∃ F : S → E, Measurable F ∧ ∀ᵐ ω ∂P, F (Y ω) = Z ω := by
  obtain ⟨F, hF, hFG⟩ := exists_measurable_of_partialGraph hGm hG
  exact ⟨F, hF, by filter_upwards [hmem] with ω hω using hFG _ hω⟩

/-! ### Recovering a continuous driver from rational times -/

/-- Lower dyadic approximation `⌊t 2ⁿ⌋ / 2ⁿ`, as a rational. -/
def dyadicApprox (t : ℝ) (n : ℕ) : ℚ := (⌊t * 2 ^ n⌋ : ℚ) / 2 ^ n

theorem dyadicApprox_cast (t : ℝ) (n : ℕ) :
    ((dyadicApprox t n : ℚ) : ℝ) = (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n := by
  simp [dyadicApprox]

theorem dyadicApprox_le (t : ℝ) (n : ℕ) : ((dyadicApprox t n : ℚ) : ℝ) ≤ t := by
  rw [dyadicApprox_cast, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem dyadicApprox_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ ((dyadicApprox t n : ℚ) : ℝ) := by
  rw [dyadicApprox_cast]
  have : (0 : ℝ) ≤ (⌊t * 2 ^ n⌋ : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  positivity

theorem sub_lt_dyadicApprox (t : ℝ) (n : ℕ) :
    t - (1 / 2 : ℝ) ^ n < ((dyadicApprox t n : ℚ) : ℝ) := by
  rw [dyadicApprox_cast, lt_div_iff₀ (by positivity)]
  have h1 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have h2 := Int.sub_one_lt_floor (t * 2 ^ n)
  nlinarith

theorem tendsto_dyadicApprox (t : ℝ) :
    Tendsto (fun n => ((dyadicApprox t n : ℚ) : ℝ)) atTop (𝓝 t) := by
  have hlo : Tendsto (fun n : ℕ => t - (1 / 2 : ℝ) ^ n) atTop (𝓝 t) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_sub t
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => (sub_lt_dyadicApprox t n).le) (fun n => dyadicApprox_le t n)

/-- Values of a driver at rational times, clamped to `[0,T]`. -/
def sampleDrive (T : ℝ) (W : ℝ → ℝ) : ℚ → ℝ := fun q => W (max 0 (min (q : ℝ) T))

/-- Recovery of a function of time from its rational samples, as the limit along lower dyadic
approximations. -/
def recoverDrive (z : ℚ → ℝ) (t : ℝ) : ℝ := limUnder atTop (fun n => z (dyadicApprox t n))

theorem measurable_recoverDrive : Measurable recoverDrive := by
  refine measurable_pi_iff.2 fun t => ?_
  exact (StronglyMeasurable.limUnder (l := atTop)
    (f := fun (n : ℕ) (z : ℚ → ℝ) => z (dyadicApprox t n))
    (fun n => (measurable_pi_apply (dyadicApprox t n)).stronglyMeasurable)).measurable

theorem recoverDrive_sampleDrive {T : ℝ} {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : recoverDrive (sampleDrive T W) t = W t := by
  unfold recoverDrive
  refine Tendsto.limUnder_eq ?_
  have hclamp : ∀ n, sampleDrive T W (dyadicApprox t n) = W (dyadicApprox t n) := by
    intro n
    have h0 := dyadicApprox_nonneg ht.1 n
    have h1 := (dyadicApprox_le t n).trans ht.2
    simp only [sampleDrive, min_eq_left h1, max_eq_right h0]
  simp only [hclamp]
  exact (hW.tendsto t).comp (tendsto_dyadicApprox t)

/-! ### The reduction -/

/-- The pairings of a field sample with a countable family `ρ` of mass-zero test functions. -/
def pairSeq (ρ : ℕ → TestFun0 H) (x : FieldSample) : ℕ → ℝ := fun n => pairRaw x (ρ n).1.1

/-- Restricting a family of pairings to a countable subfamily is measurable (product
σ-algebras). -/
theorem measurable_restrictPairs (ρ : ℕ → TestFun0 H) :
    Measurable fun p : TestFun0 H → ℝ => fun n => p (ρ n) :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (ρ n)

/-- **Borel determination of the driver by the field modulo constants.** In every setup of
Theorem 1.4 there are a countable family `ρ` of mass-zero test functions supported in `ℍ` and a
measurable partial graph `G` in (pairings with `ρ`) × (driver values at rational times,
clamped to `[0,T]`) that almost surely contains `(pairSeq ρ h, W|ℚ)`, where
`h = couplingFieldRev κ W T X` and `W = √κ B`. -/
def WeldingDeterminationGraph : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∃ (ρ : ℕ → TestFun0 H) (G : Set ((ℕ → ℝ) × (ℚ → ℝ))), MeasurableSet G ∧ IsPartialGraph G ∧
      ∀ᵐ ω ∂P, (pairSeq ρ (couplingFieldRev κ (drive κ B ω) T (X ω)),
        sampleDrive T (drive κ B ω)) ∈ G

/-- **Theorem 1.4(b) from Borel determination.** -/
theorem theorem1_4b_of_weldingDeterminationGraph (hG : WeldingDeterminationGraph) :
    theorem1_4b := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B X hB hX hind
  obtain ⟨ρ, G, hGm, hGg, hmem⟩ := hG κ hκ0 hκ4 T hT P B X hB hX hind
  obtain ⟨F₀, hF₀, hF₀ae⟩ := exists_measurable_ae_eq_of_partialGraph P hGm hGg
    (fun ω => pairSeq ρ (couplingFieldRev κ (drive κ B ω) T (X ω)))
    (fun ω => sampleDrive T (drive κ B ω)) hmem
  refine ⟨fun p => recoverDrive (F₀ (fun n => p (ρ n))),
    measurable_recoverDrive.comp (hF₀.comp (measurable_restrictPairs ρ)), ?_⟩
  filter_upwards [hF₀ae, hB.cont] with ω hω hc t ht
  change recoverDrive (F₀ (pairSeq ρ (couplingFieldRev κ (drive κ B ω) T (X ω)))) t = _
  rw [hω]
  exact recoverDrive_sampleDrive (Thm14FromThm13.continuous_drive hc) ht

end Thm14Determination

end QuantumZipper
