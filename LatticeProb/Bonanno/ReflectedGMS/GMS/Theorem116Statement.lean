/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.Theorem116Statement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Code
import LatticeProb.Bonanno.ReflectedGMS.Environment.Similarity
import LatticeProb.Bonanno.ReflectedGMS.Process.QuenchedLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gwynne–Miller–Sheffield, Theorem 1.16 — the statement, with GMS's own setup

Source: E. Gwynne, J. Miller, S. Sheffield, *An invariance principle for ergodic scale-free random
environments*, arXiv:1807.07515v3 (LaTeX source in `work/gms/src/lqg-walks-final.tex`).  Theorem 1.16
is `thm-general-clt` (source lines 608–619); its setup is Definition 1.15 (`def-cell-config`, lines
565–573), the metric `d^CC` (1.15) (`eqn-cell-metric`, lines 591–596), translation invariance modulo
scaling in its mass-transport form, Definition 1.2(4) (lines 260–268), ergodicity modulo scaling,
Definition 1.3 (lines 289–291), the finite-expectation hypothesis (1.5) (`eqn-hyp-moment`, lines
364–368), and connectedness along lines (line 612).

Everything here is GMS's own setup, independent of the reflected-walk development:

* a **cell configuration** is an *unlabelled* set of compact cells with adjacency and conductances;
* random cell configurations are laws on the **Borel σ-algebra of GMS's metric `d^CC`**;
* translation invariance modulo scaling is taken in GMS's **mass-transport form**, Definition
  1.2(4) (GMS prove its equivalence with their other three forms in their Appendix B; the user
  asked for this form);
* the walk is GMS's **continuous-time simple random walk with deterministic holding times**
  `Area(H)/π(H)`, composed with an **arbitrary** point of each cell and linearly interpolated, and
  the convergence is weak convergence in `C([0,∞), ℂ)` with uniform convergence on compacts.

Encoding choices (each checked against the source):

* Adjacency `H ∼ H'` is `0 < c H H'`; this is a bijective encoding of GMS's relation together with
  its conductance function `{(H,H') : H ∼ H'} → (0,∞)`.
* GMS's `H_0` is "the cell containing 0, chosen in some arbitrary manner if there is more than
  one"; the finite-expectation hypothesis is stated for **some** such choice (the weakest reading).
* "Line segment" in connectedness along lines is taken nondegenerate (`a < b`), the weakest
  reading.
* The walk starts from an arbitrary cell `K₀` (GMS leave the start implicit; the limit starts at
  `0` from any fixed start), and the conclusion holds for every starting cell.
* The walk is specified by the law of its jump chain: `IsSRWLaw H K₀ Q` says `Q` has the
  finite-dimensional distributions of the Markov chain with transition probabilities
  `c(H,H')/π(H)` started at `K₀`.  The continuous-time walk is a deterministic function of the jump
  chain (holding time `Area(H)/π(H)` in each cell).
* **Interpolated walk (a deliberate, user-directed choice).** GMS's Theorem 1.16 composes `X` with a
  point of each cell — a step path — and asserts convergence "with respect to the local uniform
  topology".  At the user's direction the Lean statement uses instead the **linear interpolation**
  of that path through the points `(T_n, p(Y_n))`, and **weak convergence of laws on
  `C([0,∞), ℂ)`** with the topology of uniform convergence on compact sets (the compact-open
  topology of `C(ℝ≥0, ℂ)`).  The two formulations are equivalent here because the rescaled jumps
  vanish; that equivalence is not formalized.
* In the statement of Theorem 1.16, `φ₀(H) := ∫_H z dz` is a typo: GMS's proof (source line 993) and
  the face version (Theorem 1.5, line 404) use the centroid `Area(H)⁻¹ ∫_H z dz`, which is what
  `centroid` is.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS

/-- A cell of a cell configuration: a nonempty compact subset of the plane. -/
abbrev Cell := TopologicalSpace.NonemptyCompacts Plane

/-- The data of a cell configuration on `ℂ` (GMS Definition 1.15): an unlabelled set of cells and a
conductance function; `H ∼ H'` means `c H H' > 0`. -/
structure CellConfig where
  /-- The cells. -/
  cells : Set Cell
  /-- The conductance of a pair of cells, `0` exactly when they are not adjacent. -/
  c : Cell → Cell → ℝ

namespace CellConfig

variable (H : CellConfig)

/-- Adjacency `K ∼ K'`. -/
def Adj (K K' : Cell) : Prop := 0 < H.c K K'

/-- `H(A)`: the cells meeting `A`. -/
def restrict (A : Set Plane) : Set Cell := {K | K ∈ H.cells ∧ ((K : Set Plane) ∩ A).Nonempty}

/-- **GMS Definition 1.15** (with `D = ℂ`).
1. A locally finite collection of compact connected sets with nonempty interiors whose union is
   `ℂ`, any two of which meet in a set of zero Lebesgue measure;
2. a symmetric adjacency relation with `H ∼ H' ⇒ H ∩ H' ≠ ∅` and `H ≠ H'`;
3. a symmetric conductance function from adjacent pairs to `(0,∞)`. -/
structure IsCellConfiguration : Prop where
  locallyFinite : ∀ z : Plane, ∃ U ∈ 𝓝 z, (H.restrict U).Finite
  isConnected : ∀ K ∈ H.cells, IsConnected (K : Set Plane)
  interior_nonempty : ∀ K ∈ H.cells, (interior (K : Set Plane)).Nonempty
  iUnion_eq_univ : (⋃ K ∈ H.cells, (K : Set Plane)) = univ
  volume_inter : ∀ K ∈ H.cells, ∀ K' ∈ H.cells, K ≠ K' → volume ((K : Set Plane) ∩ K') = 0
  c_nonneg : ∀ K K', 0 ≤ H.c K K'
  c_symm : ∀ K K', H.c K K' = H.c K' K
  adj_mem : ∀ K K', H.Adj K K' → K ∈ H.cells ∧ K' ∈ H.cells
  adj_ne : ∀ K K', H.Adj K K' → K ≠ K'
  adj_inter : ∀ K K', H.Adj K K' → ((K : Set Plane) ∩ K').Nonempty

/-- The image of a cell under a homeomorphism of the plane. -/
def mapCell (f : Plane ≃ₜ Plane) (K : Cell) : Cell := K.map f f.continuous

/-- The homeomorphisms admissible at radius `r` in `d^CC`: `f` takes each cell of `H(B_r(0))` to a
cell of `H'(B_r(0))` and preserves adjacency, and `f⁻¹` does the same with `H` and `H'` reversed. -/
def AdmissibleAt (H H' : CellConfig) (r : ℝ) (f : Plane ≃ₜ Plane) : Prop :=
  (∀ K ∈ H.restrict (Metric.ball 0 r), mapCell f K ∈ H'.restrict (Metric.ball 0 r)) ∧
    (∀ K ∈ H'.restrict (Metric.ball 0 r), mapCell f.symm K ∈ H.restrict (Metric.ball 0 r)) ∧
    (∀ K ∈ H.restrict (Metric.ball 0 r), ∀ K' ∈ H.restrict (Metric.ball 0 r),
      H.Adj K K' → H'.Adj (mapCell f K) (mapCell f K')) ∧
    (∀ K ∈ H'.restrict (Metric.ball 0 r), ∀ K' ∈ H'.restrict (Metric.ball 0 r),
      H'.Adj K K' → H.Adj (mapCell f.symm K) (mapCell f.symm K'))

/-- The quantity minimised in `d^CC` at radius `r`:
`sup_z |z − f(z)| + max_{{H₁,H₂} ∈ E(H(B_r(0)))} |c(H₁,H₂) − c'(f(H₁), f(H₂))|`. -/
noncomputable def distortion (H H' : CellConfig) (r : ℝ) (f : Plane ≃ₜ Plane) : ℝ≥0∞ :=
  (⨆ z : Plane, edist z (f z)) +
    ⨆ (K ∈ H.restrict (Metric.ball 0 r)) (K' ∈ H.restrict (Metric.ball 0 r)) (_ : H.Adj K K'),
      ENNReal.ofReal |H.c K K' - H'.c (mapCell f K) (mapCell f K')|

/-- **GMS's metric (1.15) on cell configurations**:
`d^CC(H,H') = ∫₀^∞ e^{-r} ∧ inf_{f_r} {…} dr`, the infimum over admissible homeomorphisms (the
integrand is `e^{-r}` when there is none). -/
noncomputable def dCC (H H' : CellConfig) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ),
    min (ENNReal.ofReal (Real.exp (-r))) (⨅ (f : Plane ≃ₜ Plane) (_ : AdmissibleAt H H' r f),
      distortion H H' r f)

/-- The cell configuration `C(H − z)`: cells mapped by `w ↦ C(w − z)`, adjacency and conductances
unchanged. -/
noncomputable def similarity (s : ℝ) (u : Plane) (hs : 0 < s) : CellConfig where
  cells := transformCell s u hs '' H.cells
  c K K' := H.c (mapCell (positiveSimilarityHomeomorph s u hs).symm K)
    (mapCell (positiveSimilarityHomeomorph s u hs).symm K')

/-- `π(H) = Σ_{H' ∼ H} c(H,H')`. -/
noncomputable def pi (K : Cell) : ℝ := ∑' K' : H.cells, H.c K K'

/-- `π*(H) = Σ_{H' ∼ H} c(H,H')⁻¹` (non-neighbours contribute `0⁻¹ = 0`). -/
noncomputable def piStar (K : Cell) : ℝ := ∑' K' : H.cells, (H.c K K')⁻¹

/-- `Area(H)`. -/
noncomputable def area (K : Cell) : ℝ := (volume (K : Set Plane)).toReal

/-- The Lebesgue centre of mass `φ₀(H) = Area(H)⁻¹ ∫_H z dz`. -/
noncomputable def centroid (K : Cell) : Plane :=
  (volume (K : Set Plane)).toReal⁻¹ • ∫ z in (K : Set Plane), z

/-- The weighted graph of a cell configuration, on its cells. -/
def graph : SimpleGraph H.cells where
  Adj K K' := K ≠ K' ∧ H.Adj K K' ∧ H.Adj K' K
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The subgraph of cells meeting `A`, with the edges joining them. -/
def inducedGraph (A : Set Plane) : SimpleGraph {K : H.cells | ((K : Set Plane) ∩ A).Nonempty} :=
  H.graph.induce {K : H.cells | ((K : Set Plane) ∩ A).Nonempty}

end CellConfig

/-- **The space of cell configurations** (GMS Definition 1.15). -/
abbrev GMSSpace : Type := {H : CellConfig // H.IsCellConfiguration}

/-- The topology defined by `d^CC`: generated by its open balls. -/
instance : TopologicalSpace GMSSpace :=
  TopologicalSpace.generateFrom
    {S | ∃ (H : GMSSpace) (ε : ℝ≥0∞), 0 < ε ∧ S = {H' | CellConfig.dCC H.1 H'.1 < ε}}

/-- "When we speak of random [cell configurations], we implicitly assume that their laws are
defined w.r.t. the Borel σ-algebra associated to the topology defined by [`d^CC`]." -/
instance : MeasurableSpace GMSSpace := borel GMSSpace

instance : BorelSpace GMSSpace := ⟨rfl⟩

/-- `H'` is `C(H − z)`. -/
def IsSimilar (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace) : Prop :=
  H'.1 = H.1.similarity s u hs

/-- **GMS Definition 1.2(4), mass transport.**  For every nonnegative measurable
`F : 𝕄 × ℂ² → [0,∞)` with `F(C(H−z), C(w₀−z), C(w₁−z)) = C⁻² F(H,w₀,w₁)`,
`E ∫ F(H,0,w) dw = E ∫ F(H,w,0) dw`. -/
def MassTransport (μ : Measure GMSSpace) : Prop :=
  ∀ F : GMSSpace × Plane × Plane → ℝ≥0, Measurable F →
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ w₀ w₁ : Plane,
        F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) = (s ^ 2)⁻¹ * F (H, w₀, w₁))
      →
    (∫⁻ H, ∫⁻ w : Plane, (F (H, 0, w) : ℝ≥0∞) ∂volume ∂μ) =
      ∫⁻ H, ∫⁻ w : Plane, (F (H, w, 0) : ℝ≥0∞) ∂volume ∂μ

/-- **GMS Definition 1.3, ergodic modulo scaling**: every Borel event invariant under
`H ↦ C(H − z)` has probability `0` or `1`.  (Translation invariance modulo scaling is the separate
hypothesis `MassTransport`.) -/
def ErgodicModuloScaling (μ : Measure GMSSpace) : Prop :=
  ∀ A : Set GMSSpace, MeasurableSet A →
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      (H ∈ A ↔ H' ∈ A)) →
    μ A = 0 ∨ μ A = 1

/-- **GMS finite-expectation hypothesis (1.5)**: with `H₀` the cell containing `0` (chosen in some
arbitrary manner if there is more than one),
`E[diam(H₀)²/Area(H₀) · π(H₀)] < ∞` and `E[diam(H₀)²/Area(H₀) · π*(H₀)] < ∞`. -/
def FiniteExpectation (μ : Measure GMSSpace) : Prop :=
  ∃ H₀ : GMSSpace → Cell, (∀ H, H₀ H ∈ H.1.cells ∧ (0 : Plane) ∈ (H₀ H : Set Plane)) ∧
    (∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 / CellConfig.area (H₀ H) *
      H.1.pi (H₀ H)) ∂μ) < ∞ ∧
    (∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 / CellConfig.area (H₀ H) *
      H.1.piStar (H₀ H)) ∂μ) < ∞

/-- **GMS hypothesis 3, connectedness along lines**: almost surely, for each horizontal or vertical
line segment `L`, the subgraph of cells meeting `L`, with the edges joining them, is connected. -/
def ConnectedAlongLines (μ : Measure GMSSpace) : Prop :=
  ∀ᵐ H ∂μ,
    (∀ a b y : ℝ, a < b → (H.1.inducedGraph (horizontal a b y)).Connected) ∧
    ∀ x a b : ℝ, a < b → (H.1.inducedGraph (vertical x a b)).Connected

namespace CellConfig

variable (H : CellConfig)

/-- The transition probability `c(H,H')/π(H)` of the simple random walk on the cells. -/
noncomputable def transition (K K' : H.cells) : ℝ := H.c K K' / H.pi K

/-- **The simple random walk's jump chain**: `Q` is a probability law on cell sequences with the
finite-dimensional distributions of the Markov chain with transitions `c(H,H')/π(H)` started at
`K₀`. -/
def IsSRWLaw (K₀ : H.cells) (Q : Measure (ℕ → H.cells)) : Prop :=
  open Classical in
  IsProbabilityMeasure Q ∧
    ∀ (n : ℕ) (x : Fin (n + 1) → H.cells),
      Q {ω | ∀ i : Fin (n + 1), ω i = x i} =
        (if x 0 = K₀ then 1 else 0) *
          ∏ i : Fin n, ENNReal.ofReal (H.transition (x i.castSucc) (x i.succ))

/-- The deterministic holding time `Area(H)/π(H)` in a cell. -/
noncomputable def holding (K : H.cells) : ℝ := area K / H.pi K

/-- The time of the `n`-th jump, `T_n = Σ_{k<n} Area(Y_k)/π(Y_k)`. -/
noncomputable def jumpTime (ω : ℕ → H.cells) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, H.holding (ω k)

/-- The number of jumps completed by time `t`. -/
noncomputable def jumpCount (ω : ℕ → H.cells) (t : ℝ) : ℕ := sSup {n | H.jumpTime ω n ≤ t}

/-- **GMS's continuous-time simple random walk** `X_t`, which spends `Area(H)/π(H)` units of time
at each cell before jumping to the next. -/
noncomputable def walk (ω : ℕ → H.cells) (t : ℝ) : H.cells := ω (H.jumpCount ω t)

/-- The linear interpolation of GMS's walk through the points `(T_n, p(Y_n))`: during the holding
interval `[T_n, T_{n+1}]` in the cell `Y_n` it moves at constant speed from `p(Y_n)` to
`p(Y_{n+1})`. -/
noncomputable def interpolatedPath (p : H.cells → Plane) (ω : ℕ → H.cells) (s : ℝ) : Plane :=
  p (ω (H.jumpCount ω s)) +
    ((s - H.jumpTime ω (H.jumpCount ω s)) / H.holding (ω (H.jumpCount ω s))) •
      (p (ω (H.jumpCount ω s + 1)) - p (ω (H.jumpCount ω s)))

/-- The rescaled interpolated walk `t ↦ ε X̃_{t/ε²}` as an element of `C([0,∞), ℂ)`.  (It is
continuous whenever the walk does not explode, which is almost sure; the value `0` is only a
placeholder on the remaining null set of paths.) -/
noncomputable def interpolatedWalk (p : H.cells → Plane) (ε : ℝ≥0) (ω : ℕ → H.cells) :
    BouRabeeGwynne.BrownianPath 2 :=
  open Classical in
  if h : Continuous (fun t : ℝ≥0 => (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2))
  then ⟨fun t => (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2), h⟩ else 0

/-- The simple random walk is recurrent: from every start it returns to the start infinitely
often almost surely. -/
def Recurrent : Prop :=
  ∀ (K₀ : H.cells) (Q : Measure (ℕ → H.cells)), H.IsSRWLaw K₀ Q →
    ∀ᵐ ω ∂Q, {n | ω n = K₀}.Infinite

/-- `φ` is `c`-discrete harmonic at every cell. -/
def DiscreteHarmonic (φ : H.cells → Plane) : Prop :=
  ∀ K : H.cells, ∑' K' : H.cells, H.c K K' • (φ K' - φ K) = 0

/-- `lim_{r→∞} r⁻¹ max_{H ∈ H(B_r(0))} |φ(H) − φ₀(H)| = 0` (the maximum taken in `[0,∞]`, so no
junk value can arise). -/
def SublinearToCentroid (φ : H.cells → Plane) : Prop :=
  Tendsto (fun r : ℝ => ENNReal.ofReal r⁻¹ *
      ⨆ (K : H.cells) (_ : (K : Cell) ∈ H.restrict (Metric.ball 0 r)),
        (‖φ K - centroid K‖₊ : ℝ≥0∞)) atTop (𝓝 0)

end CellConfig

/-- **Weak convergence in `C([0,∞), ℂ)`** (topology of uniform convergence on compact sets) of the
laws of the paths `Y ε` under `Q` to the Brownian law of `target`, as `ε ↓ 0`: for every bounded
continuous `G : C([0,∞), ℂ) → ℝ`, `E_Q[G(Y ε)] → E[G(B)]`. -/
def ConvergesWeaklyInC {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2)
    (target : StatementIngredients.AnisotropicBrownianTarget) : Prop :=
  ∀ G : BouRabeeGwynne.BrownianPath 2 → ℝ, Continuous G → (∃ C, ∀ f, |G f| ≤ C) →
    Tendsto (fun ε => ∫ ω, G (Y ε ω) ∂Q) (𝓝[>] 0)
      (𝓝 (∫ f, G f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))))

open CellConfig in
/-- **Gwynne–Miller–Sheffield, Theorem 1.16.**  Let `H` be a random cell configuration which is
ergodic modulo scaling (translation invariant modulo scaling in the mass-transport form, and
ergodic), satisfies the finite-expectation hypothesis, and satisfies connectedness along lines.
Then there is a deterministic covariance matrix `Σ` with `det Σ ≠ 0` (here: symmetric positive
definite) such that almost surely, as `ε → 0`, the conditional law given `H` of the rescaled walk
`t ↦ ε X̃_{t/ε²}` converges weakly in `C([0,∞), ℂ)` (uniform convergence on compacts) to planar
Brownian motion from `0` with covariance `Σ` — `X` the continuous-time simple random walk with
holding times `Area/π`, and `X̃` the linear interpolation, over each holding interval, of its
composition with an arbitrary point of each cell.  Furthermore the simple random walk is almost
surely recurrent, and there is a discrete harmonic `φ_∞` with
`r⁻¹ max_{H ∈ H(B_r(0))} |φ_∞(H) − φ₀(H)| → 0` almost surely.

This declaration states a proposition; it does not assert that it has been proved. -/
def Theorem1_16 : Prop :=
  ∀ (μ : Measure GMSSpace) [IsProbabilityMeasure μ],
    MassTransport μ → ErgodicModuloScaling μ → FiniteExpectation μ → ConnectedAlongLines μ →
    ∃ target : StatementIngredients.AnisotropicBrownianTarget,
      (∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      (∀ᵐ H ∂μ, H.1.Recurrent) ∧
      (∀ᵐ H ∂μ, ∃ φ : H.1.cells → Plane, H.1.DiscreteHarmonic φ ∧ H.1.SublinearToCentroid φ)

end ReflectedGMS.GMS
