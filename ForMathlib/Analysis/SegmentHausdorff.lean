/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Hausdorff distance between segments

Elementary estimates for the Hausdorff distance between segments in a seminormed real module
with bounded scalar action: moving an endpoint moves the segment by at most the distance
between the endpoints, and segments converge in Hausdorff distance when their endpoints
converge.

## Main results

* `isCompact_segment` : a segment in a topological module over a linearly ordered field is
  compact.
* `hausdorffDist_segment_le_endpoints` : the Hausdorff distance between two segments is at
  most the sum of the distances between corresponding endpoints.
* `tendsto_hausdorffDist_segment_of_tendsto_endpoints` : segments converge in Hausdorff
  distance when their endpoints converge.
-/

open Metric Filter Topology Bornology

/-! ## Compactness and boundedness of segments -/

/-- A segment in a topological module over a linearly ordered field with the order topology
is compact. -/
theorem isCompact_segment {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] (x y : E) : IsCompact (segment 𝕜 x y) := by
  rw [← convexHull_pair]
  exact ((Set.finite_singleton y).insert x).isCompact_convexHull 𝕜

/-- A segment is bounded. -/
lemma isBounded_segment {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [IsBoundedSMul ℝ E] (x y : E) : IsBounded (segment ℝ x y) :=
  (isCompact_segment x y).isBounded

/-! ## General segment Hausdorff-distance lemmas -/

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [IsBoundedSMul ℝ E]

/-- Moving the left endpoint of a segment changes it by at most the endpoint distance in
Hausdorff distance. -/
lemma hausdorffDist_segment_left_le_dist {x y z : E} :
    hausdorffDist (segment ℝ x z) (segment ℝ y z) ≤ dist x y := by
  have key : ∀ u v : E, ∀ p ∈ segment ℝ u z, ∃ q ∈ segment ℝ v z, dist p q ≤ dist u v := by
    rintro u v _ ⟨b, c, hb, hc, hbc, rfl⟩
    refine ⟨b • v + c • z, ⟨b, c, hb, hc, hbc, rfl⟩, ?_⟩
    rw [dist_add_right]
    exact (dist_smul_le b u v).trans <| mul_le_of_le_one_left dist_nonneg <| by
      rw [Real.norm_of_nonneg hb]; linarith
  exact hausdorffDist_le_of_mem_dist dist_nonneg (key x y)
    fun p hp ↦ by simpa [dist_comm] using key y x p hp

/-- Moving the right endpoint of a segment changes it by at most the endpoint distance in
Hausdorff distance. -/
lemma hausdorffDist_segment_right_le_dist {z x y : E} :
    hausdorffDist (segment ℝ z x) (segment ℝ z y) ≤ dist x y := by
  simpa [segment_symm, hausdorffDist_comm, dist_comm]
    using hausdorffDist_segment_left_le_dist (x := x) (y := y) (z := z)

/-- The Hausdorff extended distance between two segments is finite. -/
lemma hausdorffEDist_segment_ne_top (a b c d : E) :
    hausdorffEDist (segment ℝ a b) (segment ℝ c d) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨a, left_mem_segment ℝ a b⟩
    ⟨c, left_mem_segment ℝ c d⟩ (isBounded_segment a b) (isBounded_segment c d)

/-- Triangle inequality for Hausdorff distance between segments, routed through `segment ℝ a d`. -/
lemma hausdorffDist_segment_triangle (a b c d : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ c d)
      ≤ hausdorffDist (segment ℝ a b) (segment ℝ a d)
        + hausdorffDist (segment ℝ a d) (segment ℝ c d) :=
  hausdorffDist_triangle (hausdorffEDist_segment_ne_top a b a d)

/-- The Hausdorff distance between two segments is bounded by the sum of the endpoint
distances. -/
theorem hausdorffDist_segment_le_endpoints (a b a' b' : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ a' b') ≤ dist a a' + dist b b' :=
  (hausdorffDist_segment_triangle a b a' b').trans <|
    (add_le_add hausdorffDist_segment_right_le_dist
      hausdorffDist_segment_left_le_dist).trans_eq (add_comm _ _)

/-- Segments converge in Hausdorff distance when their endpoints converge (general `E`). -/
theorem tendsto_hausdorffDist_segment_of_tendsto_endpoints
    {ι : Type*} {xn yn : ι → E} {x y : E} {l : Filter ι}
    (hx : Tendsto xn l (𝓝 x)) (hy : Tendsto yn l (𝓝 y)) :
    Tendsto (fun i ↦ hausdorffDist (segment ℝ (xn i) (yn i)) (segment ℝ x y)) l (𝓝 0) := by
  refine squeeze_zero (fun _ ↦ hausdorffDist_nonneg)
    (fun i ↦ hausdorffDist_segment_le_endpoints (xn i) (yn i) x y) ?_
  simpa using (tendsto_iff_dist_tendsto_zero.1 hx).add (tendsto_iff_dist_tendsto_zero.1 hy)
