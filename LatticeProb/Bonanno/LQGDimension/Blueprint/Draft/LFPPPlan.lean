/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.Draft.LFPPPlan at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.LFPP
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2
import Mathlib.Probability.Moments.SubGaussian

/-!
# Draft blueprint for Proposition 1.2 (Sections 3–5 of the paper)

This file contains *statements only* (`def … : Prop`) together with the auxiliary definitions
needed to state them.  Nothing here is proved.  The design note is `LFPP_PLAN.md` in the
project root; it contains the dependency DAG, the infrastructure gaps, the list of doubtful
steps of the manuscript, and size/model estimates.

Conventions.

* `M = 16 ^ n`, `δ = ξ ^ (2/3)`, so `ξ = δ ^ (3/2)` and `ξ / δ² = δ ^ (-1/2)`.
* All Gaussian objects are reduced to *finite* families.  A finite family of linear functionals
  of the field is a list of weighted segments (`SegComb`); its law under `IsGFFCircleAverage`
  is a centered multivariate Gaussian with covariance `SegComb.circCov` (node `P1`).
  Expected suprema over infinite families are always expressed as suprema over finite
  subfamilies (`gaussianExpectedMax`), exactly as in the definition of `aE`.
* The unregularized field `h` is never used pointwise: its covariance on zero-mass
  combinations is the deterministic kernel `SegComb.logCov`.
* The lower bound is carried out entirely in finite dimensions: band fields are realised by
  Gram vectors on finitely many points (no white noise, no Kolmogorov–Chentsov).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.Blueprint.Draft

/-! ## Segment averages and finite linear functionals of the field -/

/-- Average of `φ` over the segment `[a, b]` (normalized arclength; `φ a` if `a = b`):
`segAvg φ a b = ∫₀¹ φ(a + s (b - a)) ds`.  This is `⟨φ, ν_{[a,b]}⟩` of the paper. -/
def segAvg (φ : ℂ → ℝ) (a b : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1, φ (a + (s : ℂ) * (b - a))

/-- A finite linear combination `Σ wᵢ ν_{[aᵢ,bᵢ]}` of uniform segment measures, as a list of
triples `(wᵢ, aᵢ, bᵢ)`.  Points are the degenerate segments `a = b`. -/
abbrev SegComb := List (ℝ × ℂ × ℂ)

namespace SegComb

/-- `⟨φ, Σ wᵢ ν_{[aᵢ,bᵢ]}⟩`. -/
def avg (φ : ℂ → ℝ) (c : SegComb) : ℝ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => p.1 * segAvg φ p.2.1 p.2.2).sum

/-- Total mass `Σ wᵢ`. -/
def mass (c : SegComb) : ℝ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => p.1).sum

/-- `c - c'`. -/
def sub (c c' : SegComb) : SegComb :=
  c ++ c'.map fun (p : ℝ × ℂ × ℂ) => (-p.1, p.2)

/-- Scalar multiple. -/
def smul (r : ℝ) (c : SegComb) : SegComb :=
  c.map fun (p : ℝ × ℂ × ℂ) => (r * p.1, p.2)

/-- Image under a map of the plane (used with similarities `z ↦ α z + β`). -/
def image (T : ℂ → ℂ) (c : SegComb) : SegComb :=
  c.map fun (p : ℝ × ℂ × ℂ) => (p.1, T p.2.1, T p.2.2)

/-- The (positive) measure `Σ wᵢ ν_{[aᵢ,bᵢ]}` (weights are truncated at `0`). -/
def toMeasure (c : SegComb) : Measure ℂ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => ENNReal.ofReal p.1 •
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => p.2.1 + (s : ℂ) * (p.2.2 - p.2.1))).sum

/-- All weights are nonnegative and sum to one. -/
def IsProb (c : SegComb) : Prop :=
  (∀ p ∈ c, 0 ≤ p.1) ∧ c.mass = 1

/-- Every segment with nonzero weight is nondegenerate.  (The log kernel of a point mass with
itself is `+∞`; Lean's `Real.log 0 = 0` would make identities involving `logCov` false for
point masses, so they are excluded.  Polygon combinations always satisfy this.) -/
def Nondeg (c : SegComb) : Prop :=
  ∀ p ∈ c, p.1 ≠ 0 → p.2.1 ≠ p.2.2

end SegComb

/-- Covariance of the circle averages `h_ε` integrated over two segments:
`∫₀¹∫₀¹ gffCircleCov ε (a + s(b-a)) ε (a' + s'(b'-a')) ds ds'`. -/
def segCircCov (ε : ℝ) (a b a' b' : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
    gffCircleCov ε (a + (s : ℂ) * (b - a)) ε (a' + (s' : ℂ) * (b' - a'))

/-- Log-kernel pairing of two uniform segment measures:
`∫₀¹∫₀¹ -log |(a + s(b-a)) - (a' + s'(b'-a'))| ds ds'`. -/
def segLogPair (a b a' b' : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
    -Real.log ‖(a + (s : ℂ) * (b - a)) - (a' + (s' : ℂ) * (b' - a'))‖

namespace SegComb

/-- `Cov(⟨h_ε, c⟩, ⟨h_ε, c'⟩)`: the covariance of two finite functionals of the circle-average
field (bilinear extension of `segCircCov`). -/
def circCov (ε : ℝ) (c c' : SegComb) : ℝ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => (c'.map fun (p' : ℝ × ℂ × ℂ) => p.1 * p'.1 * segCircCov ε p.2.1 p.2.2 p'.2.1 p'.2.2).sum).sum

/-- The log-kernel covariance `∫∫ log|z - w|⁻¹ dc(z) dc'(w)`.  On zero-mass combinations this
is the covariance of the pairings with the (unregularized) GFF. -/
def logCov (c c' : SegComb) : ℝ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => (c'.map fun (p' : ℝ × ℂ × ℂ) => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum).sum

end SegComb

/-! ## Polygons -/

/-- The edges `[z₀,z₁], [z₁,z₂], …` of a vertex list. -/
def edges (z : List ℂ) : List (ℂ × ℂ) := z.zip z.tail

/-- Euclidean length of a polygon. -/
def polyLen (z : List ℂ) : ℝ := ((edges z).map fun (e : ℂ × ℂ) => ‖e.2 - e.1‖).sum

/-- Normalized arclength measure `ν_P` of a polygon, as a segment combination. -/
def polyComb (z : List ℂ) : SegComb :=
  (edges z).map fun (e : ℂ × ℂ) => (‖e.2 - e.1‖ / polyLen z, e.1, e.2)

/-- `⟨φ, ν_P⟩`. -/
def polyAvg (φ : ℂ → ℝ) (z : List ℂ) : ℝ := (polyComb z).avg φ

/-- A local configuration: a pair of polygons `(P₁, P₂)`; its Gaussian variable is
`⟨h, ν_{P₁} - ν_{P₂}⟩`.  In Section 4, `P₁` is a parent chord `[x, y]` and `P₂` is either the
polygon of child chords (small excess) or an adverse child chord (large excess). -/
abbrev Config := List ℂ × List ℂ

/-- Zero-mass test combination of a configuration. -/
def cfgComb (c : Config) : SegComb := (polyComb c.1).sub (polyComb c.2)

/-- Normalized local variable `δ^{-1/2} ⟨φ, ν_{P₁} - ν_{P₂}⟩ - k` of (4.3)–(4.5). -/
def cfgVal (φ : ℂ → ℝ) (δ : ℝ) (k : ℕ) (c : Config) : ℝ :=
  δ ^ (-(1 / 2 : ℝ)) * (polyAvg φ c.1 - polyAvg φ c.2) - k

/-- The similarity `z ↦ α z + β`. -/
def simMap (s : ℂ × ℂ) (z : ℂ) : ℂ := s.1 * z + s.2

/-- Image of a configuration under a similarity. -/
def cfgMap (s : ℂ × ℂ) (c : Config) : Config := (c.1.map (simMap s), c.2.map (simMap s))

/-- Graph of `δ f` over the mesh `i / M`, `0 ≤ i ≤ M` (the polygon `P_f` of Section 5). -/
def graphVerts (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) : List ℂ :=
  (List.range (M + 1)).map fun i => ((i : ℝ) / M : ℂ) + (δ * f ((i : ℝ) / M) : ℝ) * Complex.I

/-- Horizontal-coordinate measure `μ_{δ,f} = ∫₀¹ δ_{(x, δ f(x))} dx` of a mesh-affine `f`:
each edge carries weight `1 / M` (not its arclength). -/
def graphComb (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) : SegComb :=
  (edges (graphVerts M δ f)).map fun (e : ℂ × ℂ) => ((1 : ℝ) / M, e.1, e.2)

/-- Covariance of the limiting increments `Z_{f+g} - Z_g` and `Z_{f'+g'} - Z_{g'}` (from (1.2)). -/
def zDiffCov (f g f' g' : ℝ → ℝ) : ℝ :=
  zCov (f + g) (f' + g') - zCov (f + g) g' - zCov g (f' + g') + zCov g g'

/-- The affine function with values `t₀` at `0` and `t₁` at `1`. -/
def affineFn (t₀ t₁ : ℝ) : ℝ → ℝ := fun x => t₀ + (t₁ - t₀) * x


/-- Law of a centered Gaussian vector indexed by `F` with covariance `C`, on `F → ℝ`. -/
def gaussVecLaw {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) : Measure (F → ℝ) :=
  (multivariateGaussian 0 (Matrix.of fun i j : F => C i j)).map (fun x (i : F) => x i)

/-- Growth condition of Lemma 3.1: `μ(B(z,t)) ≤ L min(1, t/R)`. -/
def GrowthBound (μ : Measure ℂ) (L R : ℝ) : Prop :=
  ∀ z : ℂ, ∀ t > 0, (μ (Metric.ball z t)).toReal ≤ L * min 1 (t / R)

/-- `μ` and `ν` can be coupled with displacement at most `u`. -/
def CoupledWithin (μ ν : Measure ℂ) (u : ℝ) : Prop :=
  ∃ cpl : Measure (ℂ × ℂ), cpl.map Prod.fst = μ ∧ cpl.map Prod.snd = ν ∧ ∀ᵐ q ∂cpl, ‖q.1 - q.2‖ ≤ u

/-- Gaussian-kernel pairing `∫∫ exp(-|z-w|²/(4t²)) dc(z) dc'(w)` of two segment combinations. -/
def gaussPair (t : ℝ) (c c' : SegComb) : ℝ :=
  (c.map fun (p : ℝ × ℂ × ℂ) => (c'.map fun (p' : ℝ × ℂ × ℂ) => p.1 * p'.1 *
    ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
      Real.exp (-‖(p.2.1 + (s : ℂ) * (p.2.2 - p.2.1)) - (p'.2.1 + (s' : ℂ) * (p'.2.2 - p'.2.1))‖ ^ 2
        / (4 * t ^ 2))).sum).sum

/-- The band covariance (3.5): `∫_a^b exp(-|z-w|²/(4t²)) dt/t`; point variance `log (b/a)`. -/
def bandCov (a b : ℝ) (z w : ℂ) : ℝ :=
  ∫ t in a..b, Real.exp (-‖z - w‖ ^ 2 / (4 * t ^ 2)) / t

/-! ## Layer 0: finite-dimensional Gaussian toolkit

Available already (proved in `LQGDimension.Gaussian.*`): `Blueprint.SudakovFernique`,
`Blueprint.GramBridge`, `Blueprint.GramRepresentation`, `Blueprint.MaxIntegrable`, and the
Gaussian maximal inequality `integral_iSup_inner_le_sqrt` (`E max ≤ σ √(2 log N)`). -/

/-- **(2.1), node `G1`.** Gaussian concentration for a finite maximum of affine functions of a
standard Gaussian vector, in sub-Gaussian mgf form, with a universal constant `κ` (the paper has
`κ = 1` via log-Sobolev; Maurey–Pisier gives `κ = π²/4`, which suffices everywhere). -/
def GaussConcentration : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (ι E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (v : ι → E) (b : ι → ℝ) (σ : ℝ), F.Nonempty → (∀ i ∈ F, ‖v i‖ ≤ σ) →
    HasSubgaussianMGF (fun x => (⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)
      (Real.toNNReal (κ * σ ^ 2)) (stdGaussian E)

/-- **Node `G4` (Dudley entropy bound, minimal form).**  Chaining on a box: if the Gram vectors
have a Hölder-`1/2` canonical metric in `d`-dimensional parameters of sup-diameter `a`, then the
expected maximum of the increments is `O(L √(d a))`, for *every* finite family. -/
def ChainingBox : Prop :=
  ∃ C : ℝ, ∀ (ι E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (F : Finset ι) (p : ι → (Fin d → ℝ)) (v : ι → E) (L a : ℝ), 0 ≤ L →
    (∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a) →
    (∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) →
    ∀ i₀ ∈ F, vecExpectedMax F (fun i => v i - v i₀) 0 ≤ C * L * Real.sqrt ((d + 1) * a)

/-- **Node `G6` (Chatterjee's error bound in Sudakov–Fernique, ref. [2]).**  Expected maxima
are `2√(2γ log N)`-Lipschitz in the covariance, `γ` bounding entrywise differences. -/
def ExpectedMaxCovLipschitz : Prop :=
  ∀ (ι : Type) (F : Finset ι) (C₁ C₂ : ι → ι → ℝ) (b : ι → ℝ) (γ : ℝ),
    PSDOn F C₁ → PSDOn F C₂ → (∀ i ∈ F, ∀ j ∈ F, |C₁ i j - C₂ i j| ≤ γ) →
    |gaussianExpectedMax F C₁ b - gaussianExpectedMax F C₂ b| ≤
      2 * Real.sqrt (2 * γ * Real.log F.card)

/-! ## Layer 1: the circle-average field on finite families (Section 3) -/

/-- **Node `P1`.**  Under `IsGFFCircleAverage`, any finite family of segment functionals of
`h_ε` is a centered Gaussian vector with covariance `circCov ε`.  (Riemann sums of the continuous
field, Fubini for the covariance, and closure of Gaussian laws under a.s. limits via
characteristic functions.) -/
def SegCombLaw : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P → ∀ ε > 0, ∀ (ι : Type) (F : Finset ι) (c : ι → SegComb),
      HasLaw (fun ω (i : F) => (c i).avg (fun z => h ε z ω))
        (gaussVecLaw F fun i j => (c i).circCov ε (c j)) P

/-- **Node `HK` (heat-kernel/Frullani representation, used in Lemmas 3.1, 3.4, 5.1).**
On zero-mass combinations, `∫∫ log|z-w|⁻¹ = ∫₀^∞ ∫∫ e^{-|z-w|²/(4t²)} dt/t`. -/
def LogCovHeatRep : Prop :=
  ∀ c c' : SegComb, c.mass = 0 → c'.mass = 0 → c.Nondeg → c'.Nondeg →
    c.logCov c' = ∫ t in Ioi (0 : ℝ), gaussPair t c c' / t

/-- **Node `L31d` (last assertion of Lemma 3.1).**  Circle averaging decreases the Gaussian
covariance of zero-mass combinations; and the log kernel is positive semidefinite on them.
With `SudakovFernique` this is "taking the full field only enlarges mean suprema" in (4.6). -/
def CircCovDominated : Prop :=
  (∀ ε > 0, ∀ c : SegComb, c.mass = 0 → c.Nondeg → c.circCov ε c ≤ c.logCov c) ∧
  ∀ (ι : Type) (F : Finset ι) (c : ι → SegComb), (∀ i ∈ F, (c i).mass = 0 ∧ (c i).Nondeg) →
    PSDOn F (fun i j => (c i).logCov (c j))

/-- **Node `L31` (Lemma 3.1, (3.1)).**  Two-scale covariance bound, for the log kernel and for
every circle-average regularization.  Only the growth of the coarse pair is needed (the paper's
`L_R L_r` can be replaced by `L_R`). -/
def TwoScaleCovBound : Prop :=
  ∃ C : ℝ, ∀ (μR νR μr νr : SegComb) (L R u v : ℝ),
    μR.IsProb → νR.IsProb → μr.IsProb → νr.IsProb → 0 < R → 0 ≤ u → 0 ≤ v →
    GrowthBound μR.toMeasure L R → GrowthBound νR.toMeasure L R →
    CoupledWithin μR.toMeasure νR.toMeasure u → CoupledWithin μr.toMeasure νr.toMeasure v →
    |(μR.sub νR).logCov (μr.sub νr)| ≤ C * L * Real.sqrt (u * v) / R ∧
    ∀ ε > 0, |(μR.sub νR).circCov ε (μr.sub νr)| ≤ C * L * Real.sqrt (u * v) / R

/-- **Node `SIM`.**  Similarity covariance: the log kernel is invariant and the circle-average
covariance rescales its radius, on zero-mass combinations. -/
def SimilarityCov : Prop :=
  ∀ α β : ℂ, α ≠ 0 → ∀ c c' : SegComb, c.mass = 0 → c'.mass = 0 → c.Nondeg → c'.Nondeg →
    (c.image (simMap (α, β))).logCov (c'.image (simMap (α, β))) = c.logCov c' ∧
    ∀ ε > 0, (c.image (simMap (α, β))).circCov ε (c'.image (simMap (α, β))) =
      c.circCov (ε / ‖α‖) c'

/-- **Node `L32g` (Lemma 3.2, graph form, `g = 0`).**  Used in Lemma 5.1:
`δ⁻¹ Cov(⟨h, μ_{δ,f} - μ_{δ,0}⟩, ⟨h, μ_{δ,f'} - μ_{δ,0}⟩) → Cov(Z_f, Z_{f'})`. -/
def GraphCovLimit : Prop :=
  ∀ (n : ℕ) (f f' : ℝ → ℝ), f ∈ V n → f' ∈ V n →
    Tendsto (fun δ => δ⁻¹ * ((graphComb (16 ^ n) δ f).sub (graphComb (16 ^ n) δ 0)).logCov
        ((graphComb (16 ^ n) δ f').sub (graphComb (16 ^ n) δ 0))) (𝓝[>] 0) (𝓝 (zCov f f'))

/-- The constrained polygon of Lemma 3.2 (third parametrization): vertices `z₀ = x`,
`z_i = x + e (h_i + i δ R f(i/M))` for `1 ≤ i ≤ M-1` with `e = (y-x)/R`, `R = |y-x|` and
horizontal increments `(R/M)√(1 - δ²M²(f(i/M) - f((i-1)/M))²)`, and last vertex `y`. -/
def constrPoly (M : ℕ) (δ : ℝ) (x y : ℂ) (f : ℝ → ℝ) : List ℂ :=
  let R := ‖y - x‖
  let e : ℂ := (y - x) / (R : ℂ)
  let step : ℕ → ℝ := fun j =>
    (R / M) * Real.sqrt (1 - (δ * M * (f ((j : ℝ) / M) - f (((j : ℝ) - 1) / M))) ^ 2)
  let hor : ℕ → ℝ := fun i => ∑ j ∈ Finset.Icc 1 i, step j
  (List.range M).map (fun i => x + e * ((hor i : ℂ) + ((δ * R * f ((i : ℝ) / M) : ℝ) : ℂ) *
    Complex.I)) ++ [y]

/-- Local configuration of Lemma 3.2 in reference coordinates: chord `[x,y]` with
`x = δ p₀`, `y = 1 + δ p₁`, and the constrained polygon with profile `f`. -/
def constrCfg (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) : Config :=
  ([(δ : ℂ) * p₀, 1 + (δ : ℂ) * p₁], constrPoly M δ ((δ : ℂ) * p₀) (1 + (δ : ℂ) * p₁) f)

/-- **Node `L32c` (Lemma 3.2, third parametrization, and (3.3)).**  Uniformly on compact
parameter sets: covariance convergence to `Cov(Z_{f+g} - Z_g, Z_{f'+g'} - Z_{g'})` with
`g` the affine function of the vertical endpoint offsets, the energy expansion (3.3), and a
uniform Hölder-`1/2` modulus in the parameters. -/
def ConstrainedCovLimit : Prop :=
  ∀ (n : ℕ) (B A : ℝ), ∃ Lmod : ℝ, ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
    ∀ f ∈ V n, ∀ f' ∈ V n, ∀ p₀ p₁ p₀' p₁' : ℂ,
      (∀ x, |f x| ≤ B) → (∀ x, |f' x| ≤ B) → ‖p₀‖ ≤ A → ‖p₁‖ ≤ A → ‖p₀'‖ ≤ A → ‖p₁'‖ ≤ A →
      |δ⁻¹ * (cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).logCov
          (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁')) -
        zDiffCov f (affineFn p₀.im p₁.im) f' (affineFn p₀'.im p₁'.im)| ≤ θ ∧
      |δ ^ (-2 : ℤ) * Real.log (polyLen (constrCfg (16 ^ n) δ f p₀ p₁).2 / ‖(1 + (δ : ℂ) * p₁) -
          (δ : ℂ) * p₀‖) - energy f| ≤ θ ∧
      δ⁻¹ * ((cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).sub
          (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁'))).logCov
        ((cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).sub
          (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁'))) ≤
        Lmod * ((⨆ x ∈ Icc (0 : ℝ) 1, |f x - f' x|) + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖)

/-- **Node `ESL` (process convergence ⇒ convergence of expected suprema, the part of Lemma 3.2
used downstream).**  Stated for finite subfamilies of a compact parameter set. -/
def ExpectedSupLimit : Prop :=
  ∀ (d : ℕ) (K : Set (Fin d → ℝ)), IsCompact K →
    ∀ (Cδ : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (C : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
      (bδ : ℝ → (Fin d → ℝ) → ℝ) (b : (Fin d → ℝ) → ℝ) (L : ℝ),
    (∀ δ > 0, ∀ F : Finset (Fin d → ℝ), ↑F ⊆ K → PSDOn F (Cδ δ)) →
    (∀ F : Finset (Fin d → ℝ), ↑F ⊆ K → PSDOn F C) →
    (∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ p ∈ K, ∀ q ∈ K, |Cδ δ p q - C p q| ≤ θ ∧ |bδ δ p - b p| ≤ θ) →
    (∀ᶠ δ in 𝓝[>] 0, ∀ p ∈ K, ∀ q ∈ K, Cδ δ p p - 2 * Cδ δ p q + Cδ δ q q ≤ L * ‖p - q‖) →
    ContinuousOn b K →
    ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ F : Finset (Fin d → ℝ), ↑F ⊆ K →
      ∃ G : Finset (Fin d → ℝ), ↑G ⊆ K ∧
        gaussianExpectedMax F (Cδ δ) (bδ δ) ≤ gaussianExpectedMax G C b + θ

/-! ## Section 2 inputs used by Sections 3–5 -/

/-- **Node `E22` ((2.2)).**  `E sup_{E(f) ≤ R} Z_f ≤ C n^{3/4} R^{1/4}` (from `a_n ≤ n a_1`
and vertical dilation). -/
def EnergyBallSup : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ R > 0, ∀ F : Finset (V n), (∀ f ∈ F, energy f.1 ≤ R) →
    gaussianExpectedMax F (fun f g => zCov f g) 0 ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ)

/-- **Node `L23` (Lemma 2.3).**  A finite near-optimal family with energy, sup-norm and
cardinality control. -/
def Lemma23 : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset (ℝ → ℝ),
    (∀ f ∈ F, f ∈ V n) ∧ (0 : ℝ → ℝ) ∈ F ∧
    (∀ f ∈ F, energy f ≤ C * n) ∧ (∀ f ∈ F, ∀ x, |f x| ≤ C * Real.sqrt n) ∧
    Real.log F.card ≤ C * (16 : ℝ) ^ n * Real.log ((16 : ℝ) ^ n) ∧
    a n - 1 ≤ gaussianExpectedMax F zCov (fun f => -energy f)

/-- **Node `L33` (Lemma 3.3, (3.4)).**  For every endpoint constant `C₀` there is `C` with:
for `f ∈ V_n`, `E(f) ≤ k + 2` (one unit of slack for the `o(1)` in (4.6)) and `g` affine with
endpoint values at most `C₀ η`, `η = M⁻²`,
`E sup {Z_{f+g} - Z_g - k} ≤ min{a_n + C, C n^{3/4} (k+1)^{1/4} - k + C}`. -/
def Lemma33 : Prop :=
  ∀ C₀ : ℝ, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
    ∀ F : Finset ((ℝ → ℝ) × ℝ × ℝ),
      F.Nonempty → (∀ q ∈ F, q.1 ∈ V n ∧ energy q.1 ≤ k + 2 ∧
        |q.2.1| ≤ C₀ / (16 : ℝ) ^ (2 * n) ∧ |q.2.2| ≤ C₀ / (16 : ℝ) ^ (2 * n)) →
      gaussianExpectedMax F
          (fun q q' => zDiffCov q.1 (affineFn q.2.1 q.2.2) q'.1 (affineFn q'.2.1 q'.2.2))
          (fun _ => -(k : ℝ)) ≤
        min (a n + C) (C * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C)


/-! ## Section 4: local families, records, and the upper bound -/

/-- Oscillation of `φ` at scale `r` on the closed disc of radius `3` (which contains `U`);
this is `ω_ε` of (3.7) with `r = 8ε`. -/
def osc (φ : ℂ → ℝ) (r : ℝ) : ℝ :=
  sSup {x | ∃ z w : ℂ, ‖z‖ ≤ 3 ∧ ‖w‖ ≤ 3 ∧ ‖z - w‖ ≤ r ∧ x = |φ z - φ w|}

/-- **Node `L37` ((3.7), minimal form).**  `ω_ε = o_P(log 1/ε)` (the paper proves
`O_P(√log 1/ε)`; only `o_P(log 1/ε)` is used), and `⟨h_ε, ν_{[0,1]}⟩ = O_P(1)`. -/
def Oscillation37 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    (∀ κ > 0, Tendsto (fun ε => P {ω | κ * Real.log (1 / ε) < osc (fun z => h ε z ω) (8 * ε)})
      (𝓝[>] 0) (𝓝 0)) ∧
    ∀ θ > 0, ∃ K : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | K < |segAvg (fun z => h ε z ω) 0 1|} ≤ ENNReal.ofReal θ

/-- Normalized endpoint-cell radius `4η`, `η = M⁻²` (cells of side `ηδL`, normalized by the
segment joining the two cell centres). -/
def cellRad (M : ℕ) : ℝ := 4 / (M : ℝ) ^ 2

/-- Normalized small-excess local family with bin `k` (records with `A ≤ 1`): chord `[x,y]`
with endpoints in the normalized cells, child polygon `z` from `x` to `y` with `m ≤ 3M` edges,
all but the last of length `|y-x|/M`, the last in `[|y-x|/(2M), 3|y-x|/(2M)]`, and excess
`A = log(len z / |y-x|) ∈ [kδ², (k+1)δ²) ∩ [0,1]`. -/
def smallFamily (M : ℕ) (δ : ℝ) (k : ℕ) : Set Config :=
  {c | ∃ (x y : ℂ) (z : List ℂ), c = ([x, y], z) ∧ z.head? = some x ∧ z.getLast? = some y ∧
    ‖x‖ ≤ cellRad M * δ ∧ ‖y - 1‖ ≤ cellRad M * δ ∧ 2 ≤ z.length ∧ z.length ≤ 3 * M + 1 ∧
    (∀ e ∈ (edges z).dropLast, ‖e.2 - e.1‖ = ‖y - x‖ / M) ∧
    (∀ e ∈ (edges z).getLast?, ‖y - x‖ / (2 * M) ≤ ‖e.2 - e.1‖ ∧
      ‖e.2 - e.1‖ ≤ 3 * ‖y - x‖ / (2 * M)) ∧
    (k : ℝ) * δ ^ 2 ≤ Real.log (polyLen z / ‖y - x‖) ∧
    Real.log (polyLen z / ‖y - x‖) < ((k : ℝ) + 1) * δ ^ 2 ∧
    Real.log (polyLen z / ‖y - x‖) ≤ 1}

/-- Normalized large-excess local family (records with `A > 1`): the parent chord and an
adverse child chord in `B(x, 4R)` of length in `[R/(2M), 3R/(2M)]`. -/
def largeFamily (M : ℕ) (δ : ℝ) : Set Config :=
  {c | ∃ x y x' y' : ℂ, c = ([x, y], [x', y']) ∧
    ‖x‖ ≤ cellRad M * δ ∧ ‖y - 1‖ ≤ cellRad M * δ ∧
    ‖x' - x‖ ≤ 4 * ‖y - x‖ ∧ ‖y' - x‖ ≤ 4 * ‖y - x‖ ∧
    ‖y - x‖ / (2 * M) ≤ ‖y' - x'‖ ∧ ‖y' - x'‖ ≤ 3 * ‖y - x‖ / (2 * M)}

/-- The normalized local family of a record of kind `large` and bin `k`. -/
def localFamily (M : ℕ) (δ : ℝ) (large : Bool) (k : ℕ) : Set Config :=
  if large then largeFamily M δ else smallFamily M δ k

/-- **Node `M45` ((4.5)).**  Crude mean bound, uniform in `δ`; the constant may depend on `n`
(the manuscript's `Cn` is not justified by its entropy argument, but only finiteness for
fixed `n` is used). -/
def RecordMeanCrude : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ Cn : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ (large : Bool) (k : ℕ),
    (large = true → k = ⌊δ ^ (-2 : ℤ)⌋₊) →
    ∀ F : Finset Config, F.Nonempty → ↑F ⊆ localFamily (16 ^ n) δ large k →
      gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
          (fun _ => -(k : ℝ)) ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k

/-- **Node `M46` ((4.6)).**  For fixed `n, k`, the limiting mean bound for small-excess records,
with a universal `C`.  (Uses `L32c`, `ESL`, `L33`.) -/
def RecordMeanLimit : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
    ∀ F : Finset Config, F.Nonempty → ↑F ⊆ smallFamily (16 ^ n) δ k →
      gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
          (fun _ => -(k : ℝ)) ≤
        min (a n + C) (C * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C) + θ

/-- The growth factor `g_{δ,n}(k)` of (4.7): `1` when `δ²(k+1) ≤ c₀/M`, `M` otherwise. -/
def gFactor (M : ℕ) (δ c₀ : ℝ) (k : ℕ) : ℝ :=
  if δ ^ 2 * ((k : ℝ) + 1) ≤ c₀ / M then 1 else M

/-- The concatenated (summed) test combination of the first `l` configurations. -/
def sumComb (c : ℕ → Config) (l : ℕ) : SegComb :=
  ((List.range l).map fun i => cfgComb (c i)).flatten

/-- **Node `V47` ((4.7)).**  Variance along a chain of configurations whose similarity scales
decrease by a factor at least `M/4` per step, for every regularization radius. -/
def RecordVariance : Prop :=
  ∃ C c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 1 ≤ n → ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ε > 0, ∀ l : ℕ,
    ∀ (s : ℕ → ℂ × ℂ) (large : ℕ → Bool) (k : ℕ → ℕ) (c : ℕ → Config),
      (∀ i < l, (s i).1 ≠ 0) →
      (∀ i, i + 1 < l → ‖(s (i + 1)).1‖ ≤ 4 / (16 : ℝ) ^ n * ‖(s i).1‖) →
      (∀ i < l, large i = true → k i = ⌊δ ^ (-2 : ℤ)⌋₊) →
      (∀ i < l, c i ∈ cfgMap (s i) '' localFamily (16 ^ n) δ (large i) (k i)) →
      δ⁻¹ * (sumComb c l).circCov ε (sumComb c l) ≤
        C * ∑ i ∈ Finset.range l, gFactor (16 ^ n) δ c₀ (k i) ^ 2 * Real.sqrt ((k i : ℝ) + 1)

/-- **Node `MT` (mean transfer).**  The mean of a record's local supremum under `h_ε` is bounded
by the normalized log-kernel expected maximum (similarity + `L31d` + Sudakov–Fernique + `P1`). -/
def RecordMeanTransfer : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P → ∀ ε > 0, ∀ δ > 0, ∀ s : ℂ × ℂ, s.1 ≠ 0 → ∀ (k : ℕ)
      (F₀ : Finset Config), (∀ c ∈ F₀, 0 < polyLen c.1 ∧ 0 < polyLen c.2) →
      ∫ ω, (⨆ c : F₀.image (cfgMap s), cfgVal (fun z => h ε z ω) δ k c) ∂P ≤
        gaussianExpectedMax F₀ (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
          (fun _ => -(k : ℝ))

/-! ### The partition tree of Section 4.1 -/

/-- A finite tree of consecutive subpaths of a path: nodes are addresses (root `[]`, children
`u ++ [i]`), node `u` is the subpath on the time interval `[t₀ u, t₁ u]` and has `nch u`
children (`0` for leaves). -/
structure CutTree where
  nodes : Finset (List ℕ)
  t₀ : List ℕ → ℝ
  t₁ : List ℕ → ℝ
  nch : List ℕ → ℕ

namespace CutTree

variable (T : CutTree) (γ : ℝ → ℂ)

/-- Chord endpoints and chord length `R_u`. -/
def x (u : List ℕ) : ℂ := γ (T.t₀ u)
def y (u : List ℕ) : ℂ := γ (T.t₁ u)
def R (u : List ℕ) : ℝ := ‖T.y γ u - T.x γ u‖

/-- `S_u = Σ_v R_v` over the children. -/
def S (u : List ℕ) : ℝ := ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i])

/-- Excess `A_u = log(S_u / R_u)`. -/
def A (u : List ℕ) : ℝ := Real.log (T.S γ u / T.R γ u)

/-- The unit flow `θ(v) = Π q_{uv}` with `q_{uv} = R_v / S_u` along the ancestry of `v`. -/
def flow (v : List ℕ) : ℝ :=
  ∏ j ∈ Finset.range v.length, T.R γ (v.take (j + 1)) / T.S γ (v.take j)

/-- `H_u = ⟨φ, ν_{[x_u,y_u]}⟩`. -/
def H (φ : ℂ → ℝ) (u : List ℕ) : ℝ := segAvg φ (T.x γ u) (T.y γ u)

/-- `G_u` of (4.3): `-Δ_u` if `A_u ≤ 1`, and `max_v (H_u - H_v)` over children otherwise. -/
def G (φ : ℂ → ℝ) (u : List ℕ) : ℝ :=
  if T.A γ u ≤ 1 then
    T.H γ φ u - ∑ i ∈ Finset.range (T.nch u), (T.R γ (u ++ [i]) / T.S γ u) * T.H γ φ (u ++ [i])
  else ⨆ i : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)]))

/-- The bin `k_u = ⌊min(A_u, 1) / δ²⌋`. -/
def kbin (δ : ℝ) (u : List ℕ) : ℕ := ⌊min (T.A γ u) 1 / δ ^ 2⌋₊

/-- Leaves. -/
def leaves : Finset (List ℕ) := T.nodes.filter fun u => T.nch u = 0

/-- Well-formedness: the partition of Section 4.1 at ratio `M` and cutoff `ε`. -/
structure WF (M : ℕ) (ε : ℝ) : Prop where
  root_mem : [] ∈ T.nodes
  root_time : T.t₀ [] = 0 ∧ T.t₁ [] = 1
  child_mem : ∀ u ∈ T.nodes, ∀ i < T.nch u, u ++ [i] ∈ T.nodes
  is_child : ∀ v ∈ T.nodes, v = [] ∨ ∃ u ∈ T.nodes, ∃ i < T.nch u, v = u ++ [i]
  time_le : ∀ u ∈ T.nodes, T.t₀ u ≤ T.t₁ u
  consecutive : ∀ u ∈ T.nodes, 0 < T.nch u →
    T.t₀ (u ++ [0]) = T.t₀ u ∧ T.t₁ (u ++ [T.nch u - 1]) = T.t₁ u ∧
    ∀ i, i + 1 < T.nch u → T.t₁ (u ++ [i]) = T.t₀ (u ++ [i + 1])
  internal_iff : ∀ u ∈ T.nodes, 0 < T.nch u ↔ ε < T.R γ u
  scale : ∀ u ∈ T.nodes, ∀ i < T.nch u,
    T.R γ u / (2 * M) ≤ T.R γ (u ++ [i]) ∧ T.R γ (u ++ [i]) ≤ 3 * T.R γ u / (2 * M)
  regular : ∀ u ∈ T.nodes, ∀ i, i + 1 < T.nch u → T.R γ (u ++ [i]) = T.R γ u / M
  ball : ∀ u ∈ T.nodes, ∀ t ∈ Icc (T.t₀ u) (T.t₁ u), ‖γ t - T.x γ u‖ ≤ 4 * T.R γ u

end CutTree

/-- **Node `T41` ((4.1)).**  Every admissible path has a partition tree (successive first
displacements of length `R_u/M`, terminal residual merged when its chord is `≤ r/2`). -/
def PathTreeExists : Prop :=
  ∀ γ : ℝ → ℂ, IsAdmissiblePath γ → ∀ M : ℕ, 16 ≤ M → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∃ T : CutTree, T.WF γ M ε

/-- **Node `CL` (chain lengths).**  Every leaf has depth between `log(1/ε)/log(2M)` and
`log(1/ε)/log(2M/3) + 1`. -/
def ChainLengthBounds : Prop :=
  ∀ γ : ℝ → ℂ, IsAdmissiblePath γ → ∀ M : ℕ, 16 ≤ M → ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ T : CutTree, T.WF γ M ε →
    ∀ v ∈ T.leaves, Real.log (1 / ε) / Real.log (2 * M) ≤ v.length ∧
      (v.length : ℝ) ≤ Real.log (1 / ε) / Real.log (2 * M / 3) + 1

/-- **Node `J42` ((4.2) + (4.3) + flow averaging).**  Deterministic lower bound on the LFPP
length of a path, for every continuous field, in terms of the chain sums of the local
variables `δ^{-1/2} G_u - k_u`. -/
def TreeInequality : Prop :=
  ∀ γ : ℝ → ℂ, IsAdmissiblePath γ → ∀ M : ℕ, 16 ≤ M → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ T : CutTree, T.WF γ M ε → ∀ φ : ℂ → ℝ, Continuous φ → ∀ δ > 0,
      0 < lfppLength (δ ^ (3 / 2 : ℝ)) φ γ ∧
      δ ^ (3 / 2 : ℝ) * T.H γ φ [] - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
            (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j)) ≤
        Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) ∧
      (∀ v ∈ T.leaves, 0 ≤ T.flow γ v) ∧ ∑ v ∈ T.leaves, T.flow γ v = 1

/-! ### Record systems (Section 4.2) -/

/-- An abstract system of chain records: finitely many local records, each with a kind, a bin,
a normalizing similarity, and a family of configurations; `next` is the transition relation
of chain records. -/
structure RecordSystem where
  Rec : Type
  fintype : Fintype Rec
  large : Rec → Bool
  bin : Rec → ℕ
  sim : Rec → ℂ × ℂ
  isRoot : Rec → Prop
  next : Rec → Rec → Prop
  family : Rec → Set Config

namespace RecordSystem

variable (RS : RecordSystem)

/-- A chain record of length `l`. -/
def IsChain (r : ℕ → RS.Rec) (l : ℕ) : Prop :=
  (0 < l → RS.isRoot (r 0)) ∧ ∀ i, i + 1 < l → RS.next (r i) (r (i + 1))

/-- The properties of the paper's record system at `M`, `δ`: normalization by similarities,
scale separation, large-excess bin, and the counting bound (4.4) with constants `C`, `D`. -/
def Good (M : ℕ) (δ C D : ℝ) : Prop :=
  (∀ r, (RS.sim r).1 ≠ 0) ∧
  (∀ r, RS.family r ⊆ cfgMap (RS.sim r) '' localFamily M δ (RS.large r) (RS.bin r)) ∧
  (∀ r, RS.large r = true → RS.bin r = ⌊δ ^ (-2 : ℤ)⌋₊) ∧
  (∀ r r', RS.next r r' → ‖(RS.sim r').1‖ ≤ 4 / M * ‖(RS.sim r).1‖) ∧
  (∀ k : ℕ, (Set.ncard {r | RS.isRoot r ∧ RS.bin r = k} : ℝ) ≤
    C * (M : ℝ) ^ D * ((k : ℝ) + 1) ^ D) ∧
  (∀ r (k : ℕ), (Set.ncard {r' | RS.next r r' ∧ RS.bin r' = k} : ℝ) ≤
    C * (M : ℝ) ^ D * ((k : ℝ) + 1) ^ D)

end RecordSystem

/-- **Node `R44` (records and (4.4)).**  There is a record system with the counting bound such
that along every root-to-leaf chain of every partition tree, the local variables are dominated
by (in fact equal to) values of configurations in the records' families. -/
def RecordAssignment : Prop :=
  ∃ C D : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
    ∃ RS : RecordSystem, RS.Good (16 ^ n) δ C D ∧
      ∀ γ : ℝ → ℂ, IsAdmissiblePath γ → ∀ T : CutTree, T.WF γ (16 ^ n) ε →
      ∀ φ : ℂ → ℝ, Continuous φ → ∀ v ∈ T.leaves,
        ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r v.length ∧
          ∀ j < v.length, c j ∈ RS.family (r j) ∧ RS.bin (r j) = T.kbin γ δ (v.take j) ∧
            δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j) ≤
              cfgVal φ δ (RS.bin (r j)) (c j)

/-- The generating function (4.8): `Z(t) = Σ_k N(k) exp(t m(k) + κ t² v(k))`. -/
def chainZ (N m v : ℕ → ℝ) (κ t : ℝ) : ℝ :=
  ∑' k : ℕ, N k * Real.exp (t * m k + κ * t ^ 2 * v k)

/-- **Node `U49` (chain union bound of Section 4.3).**  Abstract: given counts `N`, mean bounds
`m` and variance bounds `v` for a record system, with `B = (log Z(t) + 1)/t`, the probability
that some chain record of length `l` has local-supremum sum above `B l` is at most `e^{-l}`.
(`P` of a possibly non-measurable set is its outer measure; separability comes from the
continuity of `cfgVal` in the vertices of nondegenerate polygons.) -/
def ChainUnionBound : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P → ∀ ε > 0, ∀ δ > 0, ∀ (RS : RecordSystem) (N m v : ℕ → ℝ),
    (∀ k, (Set.ncard {r | RS.isRoot r ∧ RS.bin r = k} : ℝ) ≤ N k) →
    (∀ r k, (Set.ncard {r' | RS.next r r' ∧ RS.bin r' = k} : ℝ) ≤ N k) →
    (∀ r, ∀ c ∈ RS.family r, 0 < polyLen c.1 ∧ 0 < polyLen c.2) →
    (∀ r, ∀ F : Finset Config, F.Nonempty → ↑F ⊆ RS.family r →
      ∫ ω, (⨆ c : F, cfgVal (fun z => h ε z ω) δ (RS.bin r) c) ∂P ≤ m (RS.bin r)) →
    (∀ (l : ℕ) (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l →
      (∀ i < l, c i ∈ RS.family (r i)) →
      Var[fun ω => ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i); P] ≤
        ∑ i ∈ Finset.range l, v (RS.bin (r i))) →
    ∀ t > 0, Summable (fun k => N k * Real.exp (t * m k + κ * t ^ 2 * v k)) →
    ∀ l : ℕ, P {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l ∧
        (∀ i < l, c i ∈ RS.family (r i)) ∧
        (Real.log (chainZ N m v κ t) + 1) / t * l <
          ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)} ≤
      ENNReal.ofReal (Real.exp (-(l : ℝ)))

/-- **Node `ZL` ((4.8)–(4.9) limit, real analysis).**  With `t = n^{1/4}`, counts
`C₂ M^D (k+1)^D`, variance bounds `C₃ g(k)² √(k+1)`, the crude bound (4.5) and the limiting
bound (4.6), `limsup_{δ↓0} (log Z + 1)/t ≤ A + C n^{3/4}` with `C` independent of `n`. -/
def ZLimitBound : Prop :=
  ∀ (κ C₁ C₂ C₃ D c₀ : ℝ), 0 < κ → 0 < C₂ → 0 ≤ C₃ → 0 ≤ D → 0 < c₀ →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ (A Cn : ℝ), 0 ≤ A → ∀ mδ : ℝ → ℕ → ℝ,
      (∀ δ ∈ Ioo (0 : ℝ) 1, ∀ k : ℕ, mδ δ k ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k) →
      (∀ k : ℕ, ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, mδ δ k ≤
        min (A + C₁) (C₁ * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C₁) + θ) →
      ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
        (Real.log (chainZ (fun k => C₂ * ((16 : ℝ) ^ n) ^ D * ((k : ℝ) + 1) ^ D) (mδ δ)
            (fun k => C₃ * gFactor (16 ^ n) δ c₀ k ^ 2 * Real.sqrt ((k : ℝ) + 1)) κ
            ((n : ℝ) ^ (1 / 4 : ℝ))) + 1) / (n : ℝ) ^ (1 / 4 : ℝ) ≤
          A + C * (n : ℝ) ^ (3 / 4 : ℝ) + θ

/-- **Node `EX` (from probability bounds to exponent bounds).**  Convergence in probability
along the full filter implies it along any sequence `ε_j ↓ 0`. -/
def ExponentFromProb : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ) (ξ lam Λ : ℝ),
    IsProbabilityMeasure P → IsLFPPExponent h P ξ lam →
    ((∀ θ > 0, ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝[>] 0) ∧
      Tendsto (fun j => P {ω | Λ + θ <
        Real.log (lfppDistance ξ (fun z => h (u j) z ω)) / Real.log (u j)}) atTop (𝓝 0)) →
      lam ≤ Λ) ∧
    ((∀ θ > 0, ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝[>] 0) ∧
      Tendsto (fun j => P {ω |
        Real.log (lfppDistance ξ (fun z => h (u j) z ω)) / Real.log (u j) < Λ - θ}) atTop (𝓝 0)) →
      Λ ≤ lam)

/-! ## Section 5: the lower bound, in finite dimensions -/

/-- The tube `T_δ = {z : dist(z, [0,1]) ≤ 2δK}` of Section 5. -/
def tube (δ K : ℝ) : Set ℂ := {z | ∃ s ∈ Icc (0 : ℝ) 1, ‖z - (s : ℂ)‖ ≤ 2 * δ * K}

/-- Vertex `p_i = i/M + i δ f(i/M)` of the polygon `P_f`. -/
def pVert (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : ℂ :=
  ((i : ℝ) / M : ℂ) + (δ * f ((i : ℝ) / M) : ℝ) * Complex.I

/-- The orientation-preserving similarity `T^f_i` from `[0,1]` onto the `i`-th edge
`[p_i, p_{i+1}]` of `P_f` (`0 ≤ i < M`). -/
def edgeSim (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) (z : ℂ) : ℂ :=
  pVert M δ f i + z * (pVert M δ f (i + 1) - pVert M δ f i)

/-- `C_f(μ)` of (5.2) for a finitely supported probability `μ = Σ_{z ∈ S} w_z δ_z` and a field
`X`: `Σ_i r^f_i ∫ e^{ξ X(T^f_i z)} μ(dz)`. -/
def blockCost (ξ : ℝ) (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (S : Finset ℂ) (w : ℂ → ℝ)
    (X : ℂ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ‖pVert M δ f (i + 1) - pVert M δ f i‖ *
    ∑ z ∈ S, w z * Real.exp (ξ * X (edgeSim M δ f i z))

/-- The points `T^f_i z` at which `C_f(μ)` evaluates the field. -/
def blockPts (M : ℕ) (δ : ℝ) (Fn : Finset (ℝ → ℝ)) (S : Finset ℂ) : Set ℂ :=
  {p | ∃ f ∈ Fn, ∃ i < M, ∃ z ∈ S, p = edgeSim M δ f i z}

/-- **Node `L51` (Lemma 5.1, (5.3)), Gram form.**  For a Lemma-2.3 family (constant `C₀`), with
`δ = ξ^{2/3}`, `ρ = δ n^{3/4}` and the root band `X = G_{4ρ/M, ρ}` realised by *any* Gram
vectors on the evaluation points, uniformly over all finitely supported probabilities on the
tube: `E min_f C_f(μ) ≤ 1 - δ²(a_n - C n^{7/8}) + θ δ²` for all small `ξ`. -/
def Lemma51 : Prop :=
  ∀ C₀ : ℝ, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ Fn : Finset (ℝ → ℝ),
    (∀ f ∈ Fn, f ∈ V n) → (0 : ℝ → ℝ) ∈ Fn → (∀ f ∈ Fn, energy f ≤ C₀ * n) →
    (∀ f ∈ Fn, ∀ x, |f x| ≤ C₀ * Real.sqrt n) →
    Real.log Fn.card ≤ C₀ * (16 : ℝ) ^ n * Real.log ((16 : ℝ) ^ n) →
    a n - 1 ≤ gaussianExpectedMax Fn zCov (fun f => -energy f) →
    ∀ θ > 0, ∀ᶠ ξ in 𝓝[>] 0,
      ∀ (S : Finset ℂ) (w : ℂ → ℝ), ↑S ⊆ tube (ξ ^ (2 / 3 : ℝ)) (C₀ * Real.sqrt n) →
      (∀ z ∈ S, 0 ≤ w z) → ∑ z ∈ S, w z = 1 →
      ∀ (d : ℕ) (u : ℂ → EuclideanSpace ℝ (Fin d)),
        (∀ p ∈ blockPts (16 ^ n) (ξ ^ (2 / 3 : ℝ)) Fn S,
          ∀ p' ∈ blockPts (16 ^ n) (ξ ^ (2 / 3 : ℝ)) Fn S,
          ⟪u p, u p'⟫ = bandCov (4 * (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) / 16 ^ n)
            (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) p p') →
        ∫ x, (⨅ f : Fn, blockCost ξ (16 ^ n) (ξ ^ (2 / 3 : ℝ)) f S w (fun z => ⟪u z, x⟫))
            ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤
          1 - (ξ ^ (2 / 3 : ℝ)) ^ 2 * (a n - C * (n : ℝ) ^ (7 / 8 : ℝ)) +
            θ * (ξ ^ (2 / 3 : ℝ)) ^ 2

/-- Riemann-sum LFPP cost of a polygon with `N` equally spaced points per edge:
`Σ_e |e| (1/N) Σ_{q<N} exp(ξ φ(e(q/N)))`. -/
def riemannCost (ξ : ℝ) (N : ℕ) (z : List ℂ) (φ : ℂ → ℝ) : ℝ :=
  ((edges z).map fun (e : ℂ × ℂ) => ‖e.2 - e.1‖ * ((1 : ℝ) / N) *
    ∑ q ∈ Finset.range N, Real.exp (ξ * φ (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1)))).sum

/-- The Riemann points used by `riemannCost`. -/
def riemannPts (N : ℕ) (z : List ℂ) : Set ℂ :=
  {p | ∃ e ∈ edges z, ∃ q < N, p = e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1)}

/-- **Node `B57` (Section 5.2: the iterated block construction, the exact recursion (5.7) and
Lemma 5.1 iterated), in finite dimensions.**  For every depth `j`, a finite set of polygons from
`0` to `1` in `U`, a random choice among them driven by band-field Gram vectors realising
`G_{ε_j, ρ}` on a finite point set of at most exponential size, with expected Riemann cost at
most `b^j`, `b = 4^{ξ²/2}(1 - δ²(a_n - C n^{7/8}) + θδ²)`.  (Proof: finitely many band
intervals at each depth; similarity invariance and additivity of `bandCov`; independence of
disjoint bands from block-diagonal covariances; exact recursion via linearity; `L51`.) -/
def DiscreteBlockConstruction : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ θ > 0, ∀ᶠ ξ in 𝓝[>] 0, ∃ Agr : ℝ, ∀ j : ℕ, 1 ≤ j →
    ∃ (m : ℕ) (poly : Fin m → List ℂ) (S : Finset ℂ) (Nr d : ℕ)
      (u : ℂ → EuclideanSpace ℝ (Fin d)) (sel : EuclideanSpace ℝ (Fin d) → Fin m),
      (∀ i, (poly i).head? = some 0 ∧ (poly i).getLast? = some 1 ∧ (∀ p ∈ poly i, p ∈ U) ∧
        (∀ e ∈ edges (poly i), ‖e.2 - e.1‖ ≤
          Nr * (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * ((16 : ℝ) ^ n)⁻¹ ^ j)) ∧
        riemannPts Nr (poly i) ⊆ ↑S) ∧
      1 ≤ Nr ∧ (∀ s ∈ S, ‖s‖ ≤ 3) ∧ (S.card : ℝ) ≤ Real.exp (Agr * j) ∧
      (∀ s ∈ S, ∀ s' ∈ S, ⟪u s, u s'⟫ =
        bandCov (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * ((16 : ℝ) ^ n)⁻¹ ^ j)
          (ξ ^ (2 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) s s') ∧
      Measurable sel ∧
      Integrable (fun x => riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫)
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤
        ((4 : ℝ) ^ (ξ ^ 2 / 2) * (1 - (ξ ^ (2 / 3 : ℝ)) ^ 2 * (a n - C * (n : ℝ) ^ (7 / 8 : ℝ)) +
          θ * (ξ ^ (2 / 3 : ℝ)) ^ 2)) ^ j

/-- **Node `C36` ((3.6), minimal finite form, glued).**  For fixed `ρ`, every Gram realisation
`w` of the band field `G_{ε,ρ}` on finitely many points of the disc of radius `3` extends
(through an isometric embedding) to a realisation `U` of the circle-average covariance with
`‖U s - ι(w s)‖² ≤ C_ρ` uniformly in `ε`.  (Heat-kernel/white-noise computation in
`L²(ℝ² × (0,∞))`, then Gram gluing.) -/
def CouplingAtPoints : Prop :=
  ∀ ρ > 0, ∃ Cρ : ℝ, ∀ ε ∈ Ioo (0 : ℝ) ρ, ∀ S : Finset ℂ, (∀ s ∈ S, ‖s‖ ≤ 3) →
    ∀ (d₁ : ℕ) (w : ℂ → EuclideanSpace ℝ (Fin d₁)),
      (∀ s ∈ S, ∀ s' ∈ S, ⟪w s, w s'⟫ = bandCov ε ρ s s') →
      ∃ (d : ℕ) (ι : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
        (V : ℂ → EuclideanSpace ℝ (Fin d)),
        (∀ s ∈ S, ∀ s' ∈ S, ⟪V s, V s'⟫ = gffCircleCov ε s ε s') ∧
        ∀ s ∈ S, ‖V s - ι (w s)‖ ^ 2 ≤ Cρ

/-- **Node `PR` (polygonal paths and Riemann sums).**  A polygon from `0` to `1` in `U` is an
admissible path, and its LFPP length is at most `e^{ξ ω}` times its Riemann cost, `ω` the
oscillation at the Riemann spacing. -/
def PolygonRiemannBound : Prop :=
  ∀ ξ > 0, ∀ (z : List ℂ) (N : ℕ) (r : ℝ), 1 ≤ N → z.head? = some 0 → z.getLast? = some 1 →
    (∀ p ∈ z, p ∈ U) → (∀ e ∈ edges z, ‖e.2 - e.1‖ ≤ N * r) → ∀ φ : ℂ → ℝ, Continuous φ →
      lfppDistance ξ φ ≤ Real.exp (ξ * osc φ r) * riemannCost ξ N z φ

/-! ## Conditional assembly -/

/-- **Assembly of (1.7).** -/
def UpperAssembly : Prop :=
  AOneFinite → ASubadditiveE → SegCombLaw → Oscillation37 → RecordMeanCrude →
    RecordMeanLimit → RecordVariance → RecordMeanTransfer → PathTreeExists →
    ChainLengthBounds → TreeInequality → RecordAssignment → ChainUnionBound → ZLimitBound →
    ExponentFromProb → Prop12Upper

/-- **Assembly of (1.8).** -/
def LowerAssembly : Prop :=
  AOneFinite → ASubadditiveE → SegCombLaw → Oscillation37 → DiscreteBlockConstruction →
    CouplingAtPoints → PolygonRiemannBound → ExponentFromProb → Prop12Lower

/-- Inputs of `M46` (for its proving agent). -/
def RecordMeanLimitInputs : Prop :=
  SudakovFernique → ZCovPSD → AOneFinite → ASubadditiveE → CircCovDominated →
    ConstrainedCovLimit → ExpectedSupLimit → Lemma33 → RecordMeanLimit

/-- Inputs of `B57`. -/
def DiscreteBlockInputs : Prop :=
  Lemma23 → Lemma51 → DiscreteBlockConstruction

/-- Inputs of `L51`. -/
def Lemma51Inputs : Prop :=
  SudakovFernique → ZCovPSD → LogCovHeatRep → GraphCovLimit → Lemma51

end LQGDimension.Blueprint.Draft
