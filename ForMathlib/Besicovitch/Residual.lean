/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Besicovitch.Closed
import ForMathlib.Besicovitch.Density
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# The comeagre residual and the measure-zero member

Intersecting the thin-cover conditions over all rational window centres in `[0,1]` and all
scales `1/(m+1)` yields a dense `Gδ` subset of `kornerCompacts` all of whose members have
Lebesgue-null height slices, hence (by Fubini) Lebesgue measure zero.  Since
`kornerCompacts` is a nonempty complete space, such a member exists.  This is Körner's
Theorem 2.3/2.5.

## Main results

* `not_isMeagre_nullVolume` : the measure-zero members form a non-meagre family (`n ≥ 1`).
* `exists_kornerCompacts_volume_zero` : there is a member of the Körner family of Lebesgue
  measure zero.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Topology Metric Bornology TopologicalSpace MeasureTheory NNReal Filter

namespace Besicovitch

variable {n : ℕ}

/-! ## The comeagre residual and measure-zero member -/

/-- The residual set: members of `kornerCompacts` admitting thin covers at every rational
height in `[0,1]` and every scale `1/(m+1)`.  A countable intersection of dense open sets. -/
def kornerResidual : Set (kornerCompacts (n := n)) :=
  ⋂ i : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) 1} × ℕ,
    thinCoverSet ((i.1 : ℚ) : ℝ) ((1 : ℝ) / ((i.2 : ℝ) + 1))

/-- Membership in `kornerResidual` is having a thin cover at every rational height and scale. -/
@[simp] lemma mem_kornerResidual {P : kornerCompacts (n := n)} :
    P ∈ kornerResidual ↔
      ∀ i : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) 1} × ℕ,
        HasThinCover (P : Set (Fin (n + 1) → ℝ)) ((i.1 : ℚ) : ℝ) (1 / ((i.2 : ℝ) + 1)) := by
  simp only [kornerResidual, mem_iInter]; rfl

/-- The residual set `kornerResidual` is a `Gδ` set. -/
lemma isGδ_kornerResidual : IsGδ (kornerResidual (n := n)) :=
  IsGδ.iInter_of_isOpen fun _ => isOpen_thinCoverSet _ _

/-- The subset of `kornerCompacts` whose every height slice is Lebesgue-null. -/
def nullSlices : Set (kornerCompacts (n := n)) :=
  {P | ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin (n + 1) → ℝ)) u) = 0}

/-- Membership in `nullSlices` is having every height slice Lebesgue-null. -/
@[simp] lemma mem_nullSlices {P : kornerCompacts (n := n)} :
    P ∈ nullSlices ↔
      ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin (n + 1) → ℝ)) u) = 0 := Iff.rfl

/-- The subset of `kornerCompacts` of total Lebesgue measure zero. -/
def nullVolume : Set (kornerCompacts (n := n)) :=
  {P | volume (P : Set (Fin (n + 1) → ℝ)) = 0}

/-- Membership in `nullVolume` is having measure-zero carrier. -/
@[simp] lemma mem_nullVolume {P : kornerCompacts (n := n)} :
    P ∈ nullVolume ↔ volume (P : Set (Fin (n + 1) → ℝ)) = 0 := Iff.rfl

/-- Members of the residual set have all height slices Lebesgue-null. -/
lemma kornerResidual_subset_nullSlices : kornerResidual (n := n) ⊆ nullSlices := by
  intro P hP u hu
  have bound : ∀ m : ℕ, (volume (hSlice (P : Set (Fin (n + 1) → ℝ)) u)).toReal
      ≤ 100 * 4 ^ n * ((1 : ℝ) / ((m : ℝ) + 1)) := by
    intro m
    have he : (0 : ℝ) < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    obtain ⟨q, hq01, hqu⟩ :
        ∃ q : ℚ, ((q : ℝ) ∈ Icc (0 : ℝ) 1) ∧ |u - (q : ℝ)| ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
      rcases le_or_gt u ((1 : ℝ) / ((m : ℝ) + 1)) with hcase | hcase
      · refine ⟨0, by norm_num, ?_⟩
        rwa [Rat.cast_zero, sub_zero, abs_of_nonneg hu.1]
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self u he)
        refine ⟨q, ⟨by linarith, by linarith [hu.2]⟩, ?_⟩
        rw [abs_le]; constructor <;> linarith
    exact HasThinCover.toReal_volume_hSlice_le (mem_iInter.1 hP ⟨⟨q, hq01⟩, m⟩) hqu
  have hlimR : Tendsto (fun m : ℕ => (100 * 4 ^ n : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (100 * 4 ^ n : ℝ)
  have hfin : volume (hSlice (P : Set (Fin (n + 1) → ℝ)) u) < ⊤ :=
    lt_of_le_of_lt
      (measure_mono fun x hx => mem_closedBall_zero_iff.2
        (by simpa using (mem_strip_iff.1 (kornerFamily_subset_strip P.prop hx)).1))
      (isCompact_closedBall (0 : Fin n → ℝ) 1).measure_lt_top
  exact ((ENNReal.toReal_eq_zero_iff _).1
    ((ge_of_tendsto' hlimR bound).antisymm ENNReal.toReal_nonneg)).resolve_right hfin.ne

/-- A member all of whose height slices are null has total Lebesgue measure zero. -/
theorem nullSlices_subset_nullVolume : nullSlices (n := n) ⊆ nullVolume := by
  intro P hP
  -- carrier is measurable
  have hP_meas : MeasurableSet (↑↑P : Set (Fin (n+1) → ℝ)) :=
    (↑P : NonemptyCompacts (Fin (n+1) → ℝ)).isCompact.isClosed.measurableSet
  -- the measure preserving equivalence splitting off the last coordinate
  let e : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)
  have hMP :
      MeasurePreserving e (volume : Measure (Fin (n+1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    have h := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
    rwa [Measure.volume_eq_prod] at h
  -- e.symm (u, x) = stripPoint x u
  have hesymm : ∀ (u : ℝ) (x : Fin n → ℝ),
      e.symm (u, x) = stripPoint x u := by
    intro u x
    funext j
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last,
      Fin.snocEquiv_apply, stripPoint_eq_snoc]
  set S : Set (ℝ × (Fin n → ℝ)) := e.symm ⁻¹' (↑↑P : Set (Fin (n+1) → ℝ)) with hS
  have hS_meas : MeasurableSet S := hP_meas.preimage e.symm.measurable
  -- volume P = prod S
  have hVolP : volume (↑↑P : Set (Fin (n+1) → ℝ))
      = ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S :=
    ((hMP.symm _).measure_preimage_equiv _).symm
  -- each section has measure zero
  have hsec0 : ∀ u : ℝ, volume (Prod.mk u ⁻¹' S) = 0 := by
    intro u
    have hsec : Prod.mk u ⁻¹' S = hSlice (↑↑P : Set (Fin (n+1) → ℝ)) u := by
      ext x
      simp only [hS, Set.mem_preimage, mem_hSlice]
      rw [hesymm]
    rw [hsec]
    by_cases hu : u ∈ Icc (0 : ℝ) 1
    · exact hP u hu
    · -- slice empty since the last coordinate is forced into [0,1]
      refine measure_mono_null (fun x hx => absurd ?_ hu) measure_empty
      have := (mem_strip_iff.1 (kornerFamily_subset_strip P.prop hx)).2
      rwa [stripPoint_last] at this
  rw [mem_nullVolume, hVolP]
  exact Measure.measure_prod_null_of_ae_null hS_meas (Filter.Eventually.of_forall hsec0)

/-! ## Comeagreness and the measure-zero member -/

/-- `P⋆` is dense (`n ≥ 1`): a countable intersection of dense open sets in a complete space. -/
lemma dense_kornerResidual [NeZero n] : Dense (kornerResidual (n := n)) :=
  dense_iInter_of_isOpen (fun _ => isOpen_thinCoverSet _ _)
    fun i => dense_thinCoverSet i.1.2.1 i.1.2.2 (by positivity)

/-- For `n ≥ 1`, the residual set is not meagre. -/
theorem not_isMeagre_kornerResidual [NeZero n] : ¬ IsMeagre (kornerResidual (n := n)) :=
  have := nonempty_kornerCompacts (n := n) |>.to_subtype
  not_isMeagre_of_isGδ_of_dense isGδ_kornerResidual dense_kornerResidual

/-- For `n ≥ 1`, the set of members with all height slices null is not meagre. -/
theorem not_isMeagre_nullSlices [NeZero n] : ¬ IsMeagre (nullSlices (n := n)) :=
  mt (IsMeagre.mono kornerResidual_subset_nullSlices) not_isMeagre_kornerResidual

/-- For `n ≥ 1`, the set of measure-zero members is not meagre. -/
theorem not_isMeagre_nullVolume [NeZero n] : ¬ IsMeagre (nullVolume (n := n)) :=
  mt (IsMeagre.mono nullSlices_subset_nullVolume) not_isMeagre_nullSlices

/-- For `n ≥ 1`, there exists a measure-zero member of `kornerCompacts`. -/
theorem nonempty_nullVolume [NeZero n] : (nullVolume (n := n)).Nonempty :=
  nonempty_of_not_isMeagre not_isMeagre_nullVolume

/-- **Körner's measure-zero seed** (`n ≥ 1`): there is a member of the Körner family of
Lebesgue measure zero. -/
theorem exists_kornerCompacts_volume_zero [NeZero n] :
    ∃ P : kornerCompacts (n := n), volume (P : Set (Fin (n + 1) → ℝ)) = 0 :=
  nonempty_nullVolume

end Besicovitch
