/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Kakeya and Besicovitch sets

This file defines **Kakeya sets** and **Besicovitch sets** in a real normed vector space,
and records their most basic stability properties.

A *Kakeya set* is a set that contains a unit line segment in every direction; a *Besicovitch
set* is a Kakeya set of Lebesgue measure zero.  The existence of a Besicovitch set in `ℝⁿ`
(`n ≥ 2`) is a classical result of Besicovitch; see `ForMathlib.Besicovitch.Existence`.

## Main definitions

* `IsKakeya s` : the set `s` contains a segment `[x, x + v]` for every unit vector `v`.
* `IsBesicovitch s` : `s` is a Kakeya set of Lebesgue measure zero.

## Main results

* `IsKakeya.mono` : Kakeya sets are upward closed under inclusion.
* `isKakeya_univ` : the whole space is a Kakeya set.
* `isKakeya_closedBall` : the closed unit ball is a Kakeya set.
* `IsKakeya.nonempty` : in a nontrivial space, a Kakeya set is nonempty.
* `isKakeya_iff_norm_le_one` : it suffices to check directions of norm at most one.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A subset `s` of a real normed vector space is a **Kakeya set** if it contains a segment
of unit length in every direction, i.e. for every unit vector `v` there is a base point `x`
with `[x, x + v] ⊆ s`. -/
def IsKakeya (s : Set E) : Prop :=
  ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

/-- The universal set is a Kakeya set. -/
theorem isKakeya_univ : IsKakeya (univ : Set E) := fun _ _ ↦ ⟨0, subset_univ _⟩

/-- Kakeya sets are upward closed under inclusion. -/
theorem IsKakeya.mono {s t : Set E} (h : IsKakeya s) (hst : s ⊆ t) : IsKakeya t :=
  fun v hv ↦ (h v hv).imp fun _ hx ↦ hx.trans hst

/-- The closed unit ball is a Kakeya set. -/
theorem isKakeya_closedBall : IsKakeya (Metric.closedBall (0 : E) 1) := by
  intro v hv
  refine ⟨-v, ?_⟩
  rw [neg_add_cancel]
  exact (convex_closedBall (0 : E) 1).segment_subset (by simp [hv])
    (Metric.mem_closedBall_self zero_le_one)

/-- In a nontrivial normed space, a Kakeya set is nonempty. -/
theorem IsKakeya.nonempty [Nontrivial E] {s : Set E} (h : IsKakeya s) : s.Nonempty := by
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  obtain ⟨x, hx⟩ := h v hv
  exact ⟨x, hx (left_mem_segment ..)⟩

/-- To check the Kakeya property it suffices to produce a segment for every vector of norm
at most `1` (rather than exactly `1`). -/
theorem isKakeya_iff_norm_le_one [Nontrivial E] {s : Set E} :
    IsKakeya s ↔ ∀ v : E, ‖v‖ ≤ 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s := by
  refine ⟨fun h v hv ↦ ?_, fun h v hv ↦ h v hv.le⟩
  by_cases h₀ : v = 0
  · obtain ⟨x, hx⟩ := h.nonempty
    exact ⟨x, by simpa [h₀] using hx⟩
  · obtain ⟨x, hx⟩ := h (‖v‖⁻¹ • v) (norm_smul_inv_norm h₀)
    refine ⟨x, subset_trans ?_ hx⟩
    apply (convex_segment _ _).segment_subset (left_mem_segment _ _ _)
    rw [segment_eq_image']
    exact ⟨‖v‖, ⟨norm_nonneg v, hv⟩, by simp [smul_inv_smul₀ (norm_ne_zero_iff.mpr h₀)]⟩

/-- A **Besicovitch set** is a Kakeya set which is `volume`-null.  In the intended instances
(such as `EuclideanSpace ℝ (Fin n)` with its Lebesgue / additive Haar measure) this is the
classical notion. -/
def IsBesicovitch [MeasureTheory.MeasureSpace E] (s : Set E) : Prop :=
  IsKakeya s ∧ MeasureTheory.volume s = 0
