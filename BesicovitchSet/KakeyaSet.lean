/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.MulAction
-- import Mathlib.Analysis.NormedSpace.Real

/-!
# Kakeya sets

This file defines **Kakeya sets** in real normed vector spaces.

## Main definitions

* `IsKakeya s` : the predicate asserting that `s` is a Kakeya set.

## Main results

* `univ_isKakeya` : the whole space is a Kakeya set.
* `IsKakeya_subset` : Kakeya sets are upward-closed with respect to set inclusion.
* `IsKakeya_ball` : the closed unit ball is Kakeya.
* `IsKakeya.nonempty` : in a nontrivial space, any Kakeya set is nonempty.
* `isKakeya_iff_sub_unit` : it suffices to check the condition for vectors of norm ≤ 1.

-/

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A subset of a normed real vector space `E` is Kakeya if it contains a segment of unit length in
every direction. -/
def IsKakeya {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) : Prop :=
    ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

/-- The universal set is Kakeya. -/
lemma univ_isKakeya : IsKakeya (Set.univ : Set E) := by simp [IsKakeya]

/-- If `s` is Kakeya and `s ⊆ t`, then `t` is Kakeya. -/
theorem IsKakeya.mono {s t : Set E} (h : IsKakeya s) (hs : s ⊆ t) : IsKakeya t := by
   -- To show `t` is Kakeya, fix an arbitrary unit direction `v`.
  intro v hv
  -- From the Kakeya property of `s`, get a base point `x` such that the unit segment
  -- in direction `v` starting at `x` is contained in `s`.
  rcases h v hv with ⟨x, hx⟩
  -- Since `s ⊆ t`, that same segment is also contained in `t`.
  exact ⟨x, hx.trans hs⟩

/-- The closed unit ball is Kakeya. -/
theorem IsKakeya_ball : IsKakeya (closedBall (0 : E) 1) := by
  -- Fix a unit direction `v`.
  intro v hv
  -- Choose the base point `x := -v`, so the segment is from `-v` to `0`.
  use -v
  -- Let `y` be any point on the segment; we must show `y ∈ closedBall 0 1`.
  intro y hy
  calc
    -- Turn distance into a norm difference.
    dist y 0 = ‖y - 0‖ := by simp
    -- A point on the segment from `0` to `-v` cannot be farther from `0`
    -- than the endpoint `-v` is. We massage `hy` to that exact form:
    --   1) simplify `(-v) + v = 0` so `hy : y ∈ segment ℝ (-v) 0`
    --   2) use symmetry to view `hy : y ∈ segment ℝ 0 (-v)`
    _ ≤ ‖(-v) - 0‖ := by
      apply norm_sub_le_of_mem_segment
      simp only [neg_add_cancel] at hy
      rw [segment_symm]
      exact hy
    _ = ‖v‖ := by simp
    _ = 1 := hv

/-- In a nontrivial normed space, any Kakeya set is nonempty. -/
theorem IsKakeya.nonempty [Nontrivial E] {s : Set E} (h : IsKakeya s) : s.Nonempty := by
  -- Choose a unit vector `v` (possible since the space is nontrivial).
  obtain ⟨v, hv_norm⟩ := exists_norm_eq E zero_le_one
  -- By the Kakeya property of `s`, there exists a base point `y` such that
  -- the segment from `y` to `y + v` is contained in `s`.
  rcases h v hv_norm with ⟨y, hy⟩
  -- The left endpoint `y` belongs to that segment, hence `y ∈ s`.
  exact ⟨y, hy (left_mem_segment ..)⟩

/--
A reformulation of the Kakeya condition: it suffices to check the existence of
a segment for all vectors with norm at most 1, rather than exactly 1.
-/
theorem isKakeya_iff_sub_unit [Nontrivial E] {s : Set E} :
    IsKakeya s ↔ ∀ v : E, ‖v‖ ≤ 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s := by
  constructor
  -- First, we prove: `IsKakeya s → ∀ v, ‖v‖ ≤ 1 → ∃ x, segment x x + v ⊆ s`
  · intro h_kakeya v hv
    -- Case: `v = 0`
    by_cases h₀ : v = 0
    · obtain ⟨x, hx⟩ := h_kakeya.nonempty
      refine ⟨x, ?_⟩
      simp only [h₀, add_zero, segment_same, Set.singleton_subset_iff]
      exact hx
    -- Case: `v ≠ 0`
    · set u := ‖v‖⁻¹ • v with hu -- rescale `v` to a unit vector `u`
      have h₁ : ‖v‖ ≠ 0 := by
        contrapose! h₀
        rw [norm_eq_zero] at h₀
        exact h₀
      -- Now `u` has norm 1
      have h₂ : ‖u‖ = 1 := by
        simp [hu, norm_smul, inv_mul_cancel₀ h₁]
      -- By IsKakeya, `s` contains segment in direction `u`
      obtain ⟨x, hx⟩ := h_kakeya u h₂
      use x
      -- We want to show: `segment x x + v ⊆ segment x x + u`
      -- Since `v` is a scalar multiple of `u`, both segments lie along same ray
      have h₃ : segment ℝ x (x + v) ⊆ segment ℝ x (x + u) := by
        apply (convex_segment _ _).segment_subset (left_mem_segment _ _ _)
        rw [segment_eq_image']
        exact ⟨‖v‖, by simp [*]⟩
      -- Apply inclusion of segments to conclude result
      exact h₃.trans hx
  -- Converse: `∀ v, ‖v‖ ≤ 1 → ... ⇒ IsKakeya s`
  · intro h_segment v hv
    exact h_segment v hv.le

#lint
