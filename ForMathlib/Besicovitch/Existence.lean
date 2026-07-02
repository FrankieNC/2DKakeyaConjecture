/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Besicovitch.Residual
import ForMathlib.Kakeya.DirectionCover
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Existence of a Besicovitch set in `ℝⁿ`

Assembling the pieces: Körner's Baire argument (`exists_kornerCompacts_volume_zero`) produces a
measure-zero member `P₀` of the Körner family, containing a fibre segment in the direction
`slopeVector v` for every cross-displacement `v` with `‖v‖ ≤ 1/2`.  The direction-cover lemma
(`exists_reflectScale_smul_slopeVector`) shows that finitely many linear images of these slope
directions exhaust the whole sphere.  Taking the union of the linear images of `P₀` therefore
yields a compact set of measure zero containing a unit segment in every direction — a
**Besicovitch set** in `ℝⁿ` (`n ≥ 1`, i.e. ambient dimension `≥ 2`).

## Main results

* `exists_isBesicovitch_fin`: for `n ≥ 1` there is a compact `IsBesicovitch` set in
  `Fin (n+1) → ℝ`.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Topology Metric Bornology TopologicalSpace MeasureTheory NNReal Filter

namespace Besicovitch

variable {n : ℕ}

/-- A rescaled sub-segment: if `w = t • d` with `|t| ≤ 1`, some translate of the segment from
`0` to `w` lies inside the segment from `p` to `p + d`. -/
lemma exists_segment_subset_of_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {d w : E} {t : ℝ} (ht : |t| ≤ 1) (hw : w = t • d) (p : E) :
    ∃ x, segment ℝ x (x + w) ⊆ segment ℝ p (p + d) := by
  have habs := abs_le.1 ht
  have hmem : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → p + θ • d ∈ segment ℝ p (p + d) := by
    intro θ h0 h1
    rw [segment_eq_image']
    exact ⟨θ, ⟨h0, h1⟩, by simp⟩
  refine ⟨p + max (-t) 0 • d, (convex_segment p (p + d)).segment_subset ?_ ?_⟩
  · exact hmem _ (le_max_right _ _) (max_le (by linarith) zero_le_one)
  · have hx : p + max (-t) 0 • d + w = p + max 0 t • d := by
      rw [hw, add_assoc, ← add_smul, ← max_add_add_right]
      simp
    rw [hx]
    exact hmem _ (le_max_left _ _) (max_le zero_le_one (by linarith))

/-- The direction of a fibre segment is the slope vector of its cross-displacement:
`stripPoint x₂ 1 - stripPoint x₁ 0 = slopeVector (x₂ - x₁)`. -/
lemma stripPoint_sub_eq_slopeVector (x₁ x₂ : Fin n → ℝ) :
    stripPoint x₂ 1 - stripPoint x₁ 0 = slopeVector (x₂ - x₁) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [stripPoint_last, slopeVector_last]
  | cast k => simp [stripPoint_castSucc, slopeVector_castSucc, Pi.sub_apply]

/-- **Existence of a Besicovitch set in `ℝⁿ`** (Körner, Section 2), for ambient dimension
`n + 1 ≥ 2`.  There is a compact subset of `Fin (n+1) → ℝ` of Lebesgue measure zero containing
a unit segment in every direction (with respect to the supremum norm). -/
theorem exists_isBesicovitch_fin [NeZero n] :
    ∃ s : Set (Fin (n + 1) → ℝ), IsCompact s ∧ IsBesicovitch s := by
  obtain ⟨P, hPvol⟩ := exists_kornerCompacts_volume_zero (n := n)
  refine ⟨⋃ i : Fin (n + 1), reflectScale i '' (P : Set (Fin (n + 1) → ℝ)), ?_, ?_, ?_⟩
  · -- compactness: finite union of continuous images of a compact
    exact isCompact_iUnion fun i =>
      (P : NonemptyCompacts (Fin (n + 1) → ℝ)).isCompact.image
        (reflectScale i).continuous_of_finiteDimensional
  · -- the Kakeya property
    intro w hw
    obtain ⟨i, v, t, hv, ht, hwt⟩ := exists_reflectScale_smul_slopeVector hw
    obtain ⟨x₁, x₂, -, -, hdiff, hsub⟩ := kornerFamily_exists_fibreSegment P.2 hv
    -- the fibre segment of `P` of slope `v`, as `segment ℝ (endpoint) (endpoint + slopeVector v)`
    have hseg : fibreSegment x₁ x₂
        = segment ℝ (stripPoint x₁ 0) (stripPoint x₁ 0 + slopeVector v) := by
      rw [fibreSegment, ← hdiff, ← stripPoint_sub_eq_slopeVector, add_sub_cancel]
    have himg : reflectScale i '' fibreSegment x₁ x₂
        = segment ℝ (reflectScale i (stripPoint x₁ 0))
            (reflectScale i (stripPoint x₁ 0) + reflectScale i (slopeVector v)) := by
      rw [hseg]
      simpa [map_add] using image_segment ℝ (reflectScale (n := n) i).toAffineMap
        (stripPoint x₁ 0) (stripPoint x₁ 0 + slopeVector v)
    obtain ⟨x, hx⟩ := exists_segment_subset_of_smul ht hwt (reflectScale i (stripPoint x₁ 0))
    refine ⟨x, hx.trans ?_⟩
    rw [← himg]
    exact subset_iUnion_of_subset i (Set.image_mono hsub)
  · -- measure zero: each linear image of a null set is null
    exact measure_iUnion_null fun i => by
      rw [Measure.addHaar_image_linearMap, hPvol, mul_zero]

end Besicovitch
