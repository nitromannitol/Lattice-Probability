import LatticeProb.Prob.CellConfigMassTransport

/-!
# The capped-square σ-algebras of a cell configuration with a dyadic system

Let `H` be a random cell configuration and `D` an independent uniform dyadic system of the plane,
with coordinates `q ∈ DyadicCoord`, and let `S_m^0 = S_m^0(H, D)` be the capped square of cell mass
`m` around the origin. Gwynne, Miller and Sheffield (*An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, Definition 2.5) let `𝓕_m` be the σ-algebra of
events of `(H, D)` that are unchanged under `(H, D) ↦ (C(H - z), C(D - z))` for `z ∈ S_m^0` and
`C > 0`: the pair `(H, D)` seen modulo scaling and modulo translation of the origin inside `S_m^0`.

We encode an event `A` of `𝓕_m` through a *rooted* witness: a measurable set `B` of triples
`(H, D, w)` (the configuration seen from the root `w`), invariant under the joint similarity
`(H, D, w) ↦ (C(H - u), C(D - u), C(w - u))`, with `A = {(H, D) | (H, D, 0) ∈ B}`, and such that for
every `H` and almost every `D` the membership `(H, D, z) ∈ B` does not depend on `z ∈ S_m^0`. For
`B = {(H, D, w) | (C(H - w), C(D - w)) ∈ A}` this is the condition of Definition 2.5; the rooted
form needs no measurability of the re-rooting map.

## Main results
* `cappedSquareSigma m`: the σ-algebra `𝓕_m`, and `cappedSquareSigma_le`: it is a sub-σ-algebra.
* `cappedSquareAverage m G H q`: the uniform average `|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz`.
* `lintegral_indicator_mul_cappedSquareAverage`: under the mass-transport principle, for every
  measurable similarity-invariant `G ≥ 0` and every `A ∈ 𝓕_m`,
  `E[1_A |S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz] = E[1_A G(H, D, 0)]`.
  This is the set-integral identity behind `|S_m^0|⁻¹ ∫_{S_m^0} F(H - z, D - z) dz = E[F | 𝓕_m]`
  in the proof of Lemma 2.7 of arXiv 1807.07515, from the re-sampling property (Lemma 2.3).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- The law of the coordinates of the uniform dyadic system: scale coordinate uniform on `[0, 1)`
and two independent offset sequences. -/
noncomputable abbrev dyadicLaw : Measure DyadicCoord :=
  (unifIco 1).prod (offsetLaw.prod offsetLaw)

/-- The capped square `S_m^0(H, D)` of cell mass `m` around the origin. -/
noncomputable abbrev originCappedSquare (m : ℝ≥0∞) (H : GMSSpace) (q : DyadicCoord) : Set ℂ :=
  cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume (complexCells H.1)) m 0

/-- A rooted witness for an event of `𝓕_m`: a measurable set of triples `(H, D, w)`, invariant
under the joint similarity `(H, D, w) ↦ (C(H - u), C(D - u), C(w - u))`, whose membership is, for
every `H` and almost every `D`, constant in the root `z ∈ S_m^0(H, D)`. -/
def IsCappedSquareWitness (m : ℝ≥0∞) (B : Set (GMSSpace × DyadicCoord × ℂ)) : Prop :=
  MeasurableSet B ∧
    (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ (q : DyadicCoord) (w : ℂ),
        ((H', similarityCoord s u q, s • w + similarityOffset s u) ∈ B ↔ (H, q, w) ∈ B)) ∧
    ∀ H : GMSSpace, ∀ᵐ q ∂dyadicLaw, ∀ z ∈ originCappedSquare m H q,
      ((H, q, z) ∈ B ↔ (H, q, 0) ∈ B)

theorem isCappedSquareWitness_compl {m : ℝ≥0∞} {B : Set (GMSSpace × DyadicCoord × ℂ)}
    (hB : IsCappedSquareWitness m B) : IsCappedSquareWitness m Bᶜ :=
  ⟨hB.1.compl, fun s u hs H H' h q w => not_congr (hB.2.1 s u hs H H' h q w),
    fun H => (hB.2.2 H).mono fun _ hq z hz => not_congr (hq z hz)⟩

theorem isCappedSquareWitness_iUnion {m : ℝ≥0∞} {B : ℕ → Set (GMSSpace × DyadicCoord × ℂ)}
    (hB : ∀ i, IsCappedSquareWitness m (B i)) : IsCappedSquareWitness m (⋃ i, B i) := by
  refine ⟨MeasurableSet.iUnion fun i => (hB i).1, fun s u hs H H' h q w => ?_, fun H => ?_⟩
  · simp only [mem_iUnion]
    exact exists_congr fun i => (hB i).2.1 s u hs H H' h q w
  · filter_upwards [ae_all_iff.2 fun i => (hB i).2.2 H] with q hq z hz
    simp only [mem_iUnion]
    exact exists_congr fun i => hq i z hz

/-- **The σ-algebra `𝓕_m`** of arXiv 1807.07515, Definition 2.5: the events of `(H, D)` that are
unchanged by scaling and by translating a point of `S_m^0(H, D)` to the origin, in the rooted form
`A = {(H, D) | (H, D, 0) ∈ B}` with `B` a witness. -/
@[instance_reducible]
def cappedSquareSigma (m : ℝ≥0∞) : MeasurableSpace (GMSSpace × DyadicCoord) where
  MeasurableSet' A := ∃ B, IsCappedSquareWitness m B ∧ A = {p | (p.1, p.2, (0 : ℂ)) ∈ B}
  measurableSet_empty :=
    ⟨∅, ⟨MeasurableSet.empty, fun _ _ _ _ _ _ _ _ => Iff.rfl,
      fun _ => Filter.Eventually.of_forall fun _ _ _ => Iff.rfl⟩, Set.ext fun _ => Iff.rfl⟩
  measurableSet_compl A := by
    rintro ⟨B, hB, rfl⟩
    exact ⟨Bᶜ, isCappedSquareWitness_compl hB, Set.ext fun _ => Iff.rfl⟩
  measurableSet_iUnion f hf := by
    choose B hB hfB using hf
    refine ⟨⋃ i, B i, isCappedSquareWitness_iUnion hB, Set.ext fun p => ?_⟩
    rw [mem_iUnion]
    exact (exists_congr fun i => by rw [hfB i]; exact Iff.rfl).trans mem_iUnion.symm

/-- `𝓕_m` is a sub-σ-algebra of the product σ-algebra. -/
theorem cappedSquareSigma_le (m : ℝ≥0∞) :
    cappedSquareSigma m ≤ (inferInstance : MeasurableSpace (GMSSpace × DyadicCoord)) := by
  rintro A ⟨B, hB, rfl⟩
  exact (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)) hB.1

/-- The uniform average `|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz` of a function of the rooted
configuration over the capped square around the origin. -/
noncomputable def cappedSquareAverage (m : ℝ≥0∞) (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    (H : GMSSpace) (q : DyadicCoord) : ℝ≥0∞ :=
  ∫⁻ z, (volume (originCappedSquare m H q))⁻¹ *
    (originCappedSquare m H q).indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z)

/-- **Set-integral form of `avg_m F = E[F | 𝓕_m]`**: under the mass-transport principle, for every
cell mass `m ∈ (0, ∞)`, every measurable `G(H, D, w) ≥ 0` invariant under the joint similarity and
every event `A ∈ 𝓕_m`,
`E[1_A |S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz] = E[1_A G(H, D, 0)]`
(arXiv 1807.07515, proof of Lemma 2.7, from the re-sampling property of Lemma 2.3). -/
theorem lintegral_indicator_mul_cappedSquareAverage {μ : Measure GMSSpace}
    (hMT : MassTransport μ) {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ (q : DyadicCoord) (w : ℂ),
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    {A : Set (GMSSpace × DyadicCoord)} (hA : MeasurableSet[cappedSquareSigma m] A) :
    ∫⁻ H, ∫⁻ q, A.indicator (fun _ => (1 : ℝ≥0∞)) (H, q) * cappedSquareAverage m G H q
        ∂dyadicLaw ∂μ =
      ∫⁻ H, ∫⁻ q, A.indicator (fun _ => (1 : ℝ≥0∞)) (H, q) * G (H, q, 0) ∂dyadicLaw ∂μ := by
  obtain ⟨B, ⟨hBm, hBcov, hBc⟩, rfl⟩ := hA
  have hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ (q : DyadicCoord) (w : ℂ),
        B.indicator (fun _ => (1 : ℝ≥0∞)) (H', similarityCoord s u q,
            s • w + similarityOffset s u) *
          G (H', similarityCoord s u q, s • w + similarityOffset s u) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) (H, q, w) * G (H, q, w) := by
    intro s u hs H H' hHH' q w
    rw [hinv s u hs H H' hHH' q w]
    by_cases hw : (H, q, w) ∈ B
    · rw [indicator_of_mem ((hBcov s u hs H H' hHH' q w).2 hw), indicator_of_mem hw]
    · rw [indicator_of_notMem (fun h => hw ((hBcov s u hs H H' hHH' q w).1 h)),
        indicator_of_notMem hw]
  have key := lintegral_cappedSquare_average_eq_joint hMT hm0 hmtop
    (G := fun p => B.indicator (fun _ => (1 : ℝ≥0∞)) p * G p)
    ((measurable_const.indicator hBm).mul hG) hcov
  refine Eq.trans ?_ (key.trans rfl)
  refine lintegral_congr fun H => lintegral_congr_ae ?_
  filter_upwards [hBc H] with q hq
  by_cases hB0 : (H, q, (0 : ℂ)) ∈ B
  · have hA : (H, q) ∈ {p : GMSSpace × DyadicCoord | (p.1, p.2, (0 : ℂ)) ∈ B} := hB0
    rw [indicator_of_mem hA, one_mul, cappedSquareAverage]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ originCappedSquare m H q
    · simp only [indicator_of_mem hz, indicator_of_mem ((hq z hz).2 hB0), one_mul]
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]
  · have hA : (H, q) ∉ {p : GMSSpace × DyadicCoord | (p.1, p.2, (0 : ℂ)) ∈ B} := hB0
    rw [indicator_of_notMem hA, zero_mul]
    refine (lintegral_zero.symm.trans (lintegral_congr fun z => ?_))
    by_cases hz : z ∈ originCappedSquare m H q
    · simp only [indicator_of_notMem (fun h => hB0 ((hq z hz).1 h)), zero_mul, mul_zero]
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]

end LatticeProb.CellConfigCappedSquare
