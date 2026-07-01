/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import BesicovitchSet.KakeyaSet
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Closeds

/-!
# Besicovitch–Kakeya sets via Baire category (after Körner)

This file develops the Baire category construction of a planar Besicovitch set,
following Körner’s paper "Besicovitch via Baire".


## Main definitions

* `IsBesicovitch s` : a Kakeya set in `ℝⁿ` of Lebesgue measure zero.
* `rectangle : Set (Fin 2 → ℝ)` : the closed strip `[-1,1] × [0,1]`.
* `segment01 (x₁ x₂ : ℝ) : Set (Fin 2 → ℝ)` : the segment from `(x₁,0)` to `(x₂,1)`.
* `kornerCollection` : subsets `P ⊆ rectangle` which are (i) unions of such segments and
  (ii) “span” all horizontal differences `v` with `|v| ≤ 1/2`.
* `kornerCompacts` : the same class, viewed as a subset of `NonemptyCompacts (Fin 2 → ℝ)`.
* `HasThinCover P v ε` : Körner’s “thin cover” condition at height `v` and thickness `ε`.
* `thinCoverSet v ε` : elements of `kornerCompacts` admitting a thin cover at `(v, ε)`.
* `kornerResidual` : the countable intersection of the `thinCoverSet q (1/(m+1))` over rational
  window centres `q ∈ [0,1]` and scales `1/(m+1)`.

## Main results

* `isClosed_kornerCompacts : IsClosed kornerCompacts`.
  In particular, `(kornerCompacts, dist)` is a complete Baire space.
* Openness/density of thin-cover conditions: `IsOpen (thinCoverSet v ε)` and `Dense (thinCoverSet v ε)`.
* `isGδ_kornerResidual` and `dense_kornerResidual` : `kornerResidual` is a dense `Gδ` subset of `kornerCompacts`.
* Slicing estimates imply `kornerResidual ⊆ nullSlices`, where `nullSlices` consists of those
  `P ∈ kornerCompacts` whose every horizontal slice has Lebesgue measure `0`.
  Consequently there exists `P ∈ kornerCompacts` with `volume (P : Set _) = 0`
  (`exists_kornerCompacts_volume_zero`).
* `exists_isBesicovitch` : there is a compact subset of `ℝ²` of Lebesgue measure zero
  containing a unit segment in every direction — a **Besicovitch set**, obtained by
  transforming a measure-zero member of `𝒫` by four integer matrices covering the four
  cones of the sup-norm unit sphere.

The metric/compactness part relies on Hausdorff convergence in `NonemptyCompacts`,
together with quantitative control of segments by their endpoints.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
  [EuDML link](http://eudml.org/doc/284499)

-/

open Set Topology Metric Bornology TopologicalSpace MeasureTheory NNReal Filter

/-- A Besicovitch set in `ℝⁿ` is a Kakeya set of Lebesgue measure zero. -/
def IsBesicovitch {n : ℕ} (s : Set (Fin n → ℝ)) : Prop := IsKakeya s ∧ volume s = 0

/-- The closed rectangle `[-1,1] × [0,1] ⊆ ℝ²`, written in coordinates for `Fin 2 → ℝ`. -/
def rectangle : Set (Fin 2 → ℝ) := Icc ![-1, 0] ![1,1]

lemma isBounded_rectangle : IsBounded rectangle := by simp [rectangle, isBounded_Icc]

lemma isClosed_rectangle : IsClosed rectangle := by
  simpa [rectangle] using (isClosed_Icc : IsClosed (Icc ![(-1 : ℝ), 0] ![1, 1]))

lemma convex_rectangle : Convex ℝ rectangle := by simp [rectangle, convex_Icc]

/-- `rectangle` is nonempty. We use `![0,0]` as the witness. -/
lemma nonempty_rectangle : (rectangle : Set (Fin 2 → ℝ)).Nonempty := by
  refine ⟨![0,0], ?_⟩
  simp [rectangle, Pi.le_def, Fin.forall_fin_two]

/-- The line segment in `ℝ²` from `(x₁, 0)` to `(x₂, 1)`. -/
def segment01 (x₁ x₂ : ℝ) : Set (Fin 2 → ℝ) :=
  segment ℝ ![x₁, 0] ![x₂, 1]

/-- The collection `𝒫` of subsets `P ⊆ rectangle` satisfying
    (i) “union of those segments’’ and (ii) the spanning condition. -/
def kornerCollection : Set (Set (Fin 2 → ℝ)) :=
  { P | IsClosed P ∧ P ⊆ rectangle ∧
      -- (i)  P is a union of segments of the form `segment01 x₁ x₂`
      (∃ A : Set (Fin 2 → ℝ), A ⊆ Icc ![-1, -1] ![1, 1] ∧
        P = ⋃ (p ∈ A), segment01 (p 0) (p 1)) ∧
      -- (ii) for every |v| ≤ 1/2 there is a segment with horizontal length v lying in P
      (∀ v : ℝ, |v| ≤ (1 / 2 : ℝ) →
        ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧
          x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

/-- The same collection, but viewed inside the type of non-empty compact
    subsets of `Fin 2 → ℝ`. -/
def kornerCompacts : Set (NonemptyCompacts (Fin 2 → ℝ)) :=
  { P | IsClosed (P : Set (Fin 2 → ℝ)) ∧ (P : Set (Fin 2 → ℝ)) ⊆ rectangle ∧
      (∃ A : Set (Fin 2 → ℝ), A ⊆ Icc ![-1, -1] ![1, 1] ∧
        (P : Set (Fin 2 → ℝ)) = ⋃ (p ∈ A), segment01 (p 0) (p 1)) ∧
      (∀ v : ℝ, |v| ≤ (1 / 2 : ℝ) →
        ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧
          x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

/-- A convenient compact witness in `𝒫'`: the whole rectangle as a
`NonemptyCompacts` together with the obvious interior point `(0,0)`. -/
def rectangleCompacts : NonemptyCompacts (Fin 2 → ℝ) :=
  ⟨⟨rectangle, by
    -- `rectangle` is a product of closed intervals, hence compact.
    simpa [rectangle] using (isCompact_Icc : IsCompact (Icc ![(-1 : ℝ), 0] ![1, 1]))⟩,
    -- The point `(0,0)` lies in the rectangle.
    by exact nonempty_rectangle⟩

/-- Endpoints `![a,0]` and `![b,1]` of our standard segments lie in `rectangle`
whenever `a,b ∈ [-1,1]`. -/
lemma endpoints_mem_rectangle {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ![a, 0] ∈ rectangle ∧ ![b, 1] ∈ rectangle := by
  simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]

/-- Every point of the rectangle lies on some segment of the form
`segment01 (p 0) (p 1)` with `p ∈ [-1,1]×[-1,1]`.  (We take the vertical
segment through the `x`–coordinate.) -/
lemma rectangle_subset_iUnion_segment01 :
    rectangle ⊆ ⋃ (p ∈ Icc ![-1,-1] ![1,1]), segment01 (p 0) (p 1) := by
  intro x hx
  -- Take the vertical segment at `x 0`, i.e. `p := ![x 0, x 0]`.
  refine mem_iUnion.2 ?_
  refine ⟨![x 0, x 0], ?_⟩
  refine mem_iUnion.2 ?_
  refine ⟨?px_mem, ?x_on_segment⟩
  · -- `p` is in the parameter rectangle `[-1,1] × [-1,1]`.
    have hx0 : x 0 ∈ Icc (-1 : ℝ) 1 := by
      change x ∈ rectangle at hx
      simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]
    simpa [Pi.le_def, Fin.forall_fin_two] using hx0
  · -- Write `x` as a convex combination of the endpoints with weights `1 - x 1` and `x 1`.
    have hx1 : x 1 ∈ Icc (0 : ℝ) 1 := by
      change x ∈ rectangle at hx
      simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]
    rcases hx1 with ⟨h0, h1⟩
    refine ?_  -- show: `x ∈ segment01 (x 0) (x 0)`
    -- With coefficients `b = 1 - x 1`, `c = x 1`.
    refine ⟨1 - x 1, x 1, by linarith, by linarith, by ring, ?_⟩
    -- Evaluate the affine combination equals `x`.
    ext i
    fin_cases i <;> simp
    linarith

/-- Each such segment is contained in the rectangle: the parameter
points are in `[-1,1]×[-1,1]`, the rectangle is convex. -/
lemma iUnion_segment01_subset_rectangle :
    (⋃ (p ∈ Icc ![-1,-1] ![1,1]), segment01 (p 0) (p 1)) ⊆ rectangle := by
  intro x hx
  rcases mem_iUnion.1 hx with ⟨p, hp⟩
  rcases mem_iUnion.1 hp with ⟨hpA, hxSeg⟩
  -- From `p ∈ Icc ![-1,-1] ![1,1]` get coordinatewise bounds on `p 0` and `p 1`.
  have hp_bounds : ((![(-1 : ℝ), -1] : Fin 2 → ℝ) ≤ p) ∧ (p ≤ ![1, 1]) := by
    simpa [Icc, Pi.le_def, Fin.forall_fin_two] using hpA
  have ha : p 0 ∈ Icc (-1 : ℝ) 1 :=
    ⟨by simpa using hp_bounds.1 0, by simpa using hp_bounds.2 0⟩
  have hb : p 1 ∈ Icc (-1 : ℝ) 1 :=
    ⟨by simpa using hp_bounds.1 1, by simpa using hp_bounds.2 1⟩
  -- Endpoints belong to the rectangle; convexity gives the whole segment.
  obtain ⟨hL, hR⟩ := endpoints_mem_rectangle ha hb
  exact convex_rectangle.segment_subset hL hR hxSeg

/-- The rectangle is exactly the union of all standard segments `segment01 (p 0) (p 1)`
with `p ∈ [-1,1]×[-1,1]`. -/
lemma rectangle_eq_iUnion_segment01 :
    rectangle = ⋃ (p ∈ Icc ![-1,-1] ![1,1]), segment01 (p 0) (p 1) := by
  ext x
  constructor
  all_goals intro hx
  · -- `x ∈ rectangle` implies `x` belongs to the union of segments.
    exact rectangle_subset_iUnion_segment01 hx
  · -- `x` in the union of segments implies `x ∈ rectangle`.
    exact iUnion_segment01_subset_rectangle hx

/-- Spanning property (ii) for the rectangle: for any `|v| ≤ 1/2`, the segment
from `(0,0)` to `(v,1)` lies inside the rectangle. -/
lemma exists_segment01_subset_rectangle :
    ∀ v : ℝ, |v| ≤ (1/2 : ℝ) →
      ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧
        x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ (rectangle : Set (Fin 2 → ℝ)) := by
  intro v hv
  refine ⟨0, v, ?x1, ?x2, by ring_nf, ?incl⟩
  · -- `0 ∈ [-1,1]`
    simp
  · -- `|v| ≤ 1/2` implies `v ∈ [-1,1]`.
    have : |v| ≤ (1 : ℝ) := (le_trans hv (by norm_num : (1/2 : ℝ) ≤ 1))
    simpa [Icc, abs_le] using this
  · -- The segment from `(0,0)` to `(v,1)` is inside the rectangle by convexity.
    have hL : ![0, 0] ∈ rectangle := by
      simp [rectangle, Pi.le_def, Fin.forall_fin_two]
    have hR : ![v, 1] ∈ rectangle := by
      -- `x = v` is in `[-1,1]` by the bound above.
      have hv' : v ∈ Icc (-1 : ℝ) 1 := by
        have : |v| ≤ (1 : ℝ) := (le_trans hv (by norm_num : (1/2 : ℝ) ≤ 1))
        simpa [Icc, abs_le] using this
      simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]
    exact convex_rectangle.segment_subset hL hR

@[simp] lemma rectangleCompacts_coe :
    (rectangleCompacts : Set (Fin 2 → ℝ)) = rectangle := rfl

/-- `𝒫` is nonempty: the rectangle itself (as a compact nonempty set) satisfies
all clauses of the definition. -/
theorem nonempty_kornerCompacts : (kornerCompacts).Nonempty := by
  refine ⟨rectangleCompacts, ?_⟩
  split_ands
  · -- (closedness)
    rw [rectangleCompacts_coe]; exact isClosed_rectangle
  · -- (contained in the rectangle: trivial for the rectangle itself)
    rw [rectangleCompacts_coe]
  · -- (i) union-of-segments representation
    refine ⟨Icc ![-1,-1] ![1,1], ?_, ?_⟩
    · intro p hp
      exact hp
    · -- equality from the two inclusions above
      rw [rectangleCompacts_coe]; exact rectangle_eq_iUnion_segment01
  · -- (ii) spanning property for all `|v| ≤ 1/2`
    intro v hv
    rw [rectangleCompacts_coe]
    exact exists_segment01_subset_rectangle v hv

/-- Any set in `kornerCollection` is non‑empty: the segment guaranteed by the
definition already gives a point. -/
theorem nonempty_of_mem_kornerCollection {P : Set (Fin 2 → ℝ)} (hP : P ∈ kornerCollection) :
    P.Nonempty := by
  rcases hP with ⟨-, -, -, h⟩
  rcases h 0 (by norm_num) with ⟨x₁, x₂, -, -, -, hPseg⟩
  exact ⟨![x₁, 0], hPseg <| left_mem_segment _ _ _⟩

/-- A set in `kornerCollection` is bounded since it lies inside the ambient rectangle. -/
theorem isBounded_of_mem_kornerCollection {P : Set (Fin 2 → ℝ)} (hP : P ∈ kornerCollection) :
    IsBounded P := by
  rcases hP with ⟨-, hS, -⟩
  exact isBounded_rectangle.subset hS

/-- A set in `kornerCollection` is compact: it is closed and bounded. -/
theorem isCompact_of_mem_kornerCollection {P : Set (Fin 2 → ℝ)} (hP : P ∈ kornerCollection) :
    IsCompact P := by
  simpa [isCompact_iff_isClosed_bounded] using ⟨hP.1, isBounded_of_mem_kornerCollection hP⟩

/-- The carrier image of `kornerCompacts` recovers the original set-level collection `kornerCollection`. -/
theorem image_coe_kornerCompacts : (↑) '' kornerCompacts = kornerCollection := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨⟨P, isCompact_of_mem_kornerCollection hP⟩, nonempty_of_mem_kornerCollection  hP⟩, hP, rfl⟩

/-- Equivalent formulation of the second defining property of `𝒫`. -/
lemma exists_segment01_pair_iff {P : Set (Fin 2 → ℝ)} :
    (∀ (v : ℝ), |v| ≤ (1/2 : ℝ) → ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1
      ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P)
    ↔
    (∀ (v : ℝ), |v| ≤ (1/2 : ℝ) → ∃ x : Fin 2 → ℝ, x ∈ Icc ![-1, -1] ![1, 1] ∧ (x 1) - (x 0) = v
      ∧ segment01 (x 0) (x 1) ⊆ P) := by
  refine ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · rcases h v hv with ⟨x₁, x₂, hx₁, hx₂, hdiff, hP⟩
    let x : Fin 2 → ℝ := ![x₁, x₂]
    have : x ∈ Icc ![-1, -1] ![1, 1] := by simp_all [x, Pi.le_def, Fin.forall_fin_two]
    exact ⟨x, this, hdiff, hP⟩
  · rcases h v hv with ⟨x, ⟨hx₀, hx₁⟩, hdiff, hP⟩
    exact ⟨x 0, x 1, by all_goals simp_all [Pi.le_def, Fin.forall_fin_two]⟩

/--
By Aaron Liu (from Zulip)
The Hausdorff distance between two line segments with the same endpoint
is at most the distance between the other two endpoints. -/
theorem hausdorffDist_segment_left_le_dist
  {E : Type*} {x y z : E}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    hausdorffDist (segment ℝ x z) (segment ℝ y z) ≤ dist x y := by
  apply hausdorffDist_le_of_mem_dist
  · apply dist_nonneg
  · rintro _ ⟨b, c, hb, hc, hbc, rfl⟩
    refine ⟨b • y + c • z, ⟨b, c, hb, hc, hbc, rfl⟩, ?_⟩
    rw [dist_add_right]
    apply (dist_smul_le b x y).trans
    apply mul_le_of_le_one_left
    · apply dist_nonneg
    · rw [Real.norm_eq_abs, abs_of_nonneg hb]
      linarith
  · rintro _ ⟨b, c, hb, hc, hbc, rfl⟩
    refine ⟨b • x + c • z, ⟨b, c, hb, hc, hbc, rfl⟩, ?_⟩
    rw [dist_add_right, dist_comm]
    apply (dist_smul_le b x y).trans
    apply mul_le_of_le_one_left
    · apply dist_nonneg
    · rw [Real.norm_eq_abs, abs_of_nonneg hb]
      linarith

/-- Moving the right endpoint by distance `d` moves the segment by at most `d` in Hausdorff distance. -/
lemma hausdorffDist_segment_right_le_dist
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {z x y : E} :
    hausdorffDist (segment ℝ z x) (segment ℝ z y) ≤ dist x y := by
  simpa [segment_symm, hausdorffDist_comm, dist_comm]
    using (hausdorffDist_segment_left_le_dist (E := E) (x := x) (y := y) (z := z))

/-- In a real normed vector space, every segment is bounded. -/
lemma isBounded_segment {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    IsBounded (segment ℝ x y) := by
  -- The segment is the continuous image of the compact interval `[0,1]`.
  have hcont : Continuous fun t : ℝ ↦ (1 - t) • x + t • y := by
    continuity
  have hcomp : IsCompact ((fun t : ℝ ↦ (1 - t) • x + t • y) '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image hcont)
  -- Use the standard representation of the segment as that image.
  simpa [segment_eq_image] using hcomp.isBounded

/-- Triangle control for segments: compare `(a,b)` to `(c,d)` via the intermediate `(a,d)`. -/
lemma hausdorffDist_segment_triangle
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ c d)
      ≤ hausdorffDist (segment ℝ a b) (segment ℝ a d)
        + hausdorffDist (segment ℝ a d) (segment ℝ c d) := by
  -- Hausdorff triangle inequality; segments are nonempty and bounded.
  refine hausdorffDist_triangle ?_
  refine hausdorffEDist_ne_top_of_nonempty_of_bounded ?_ ?_ ?_ ?_ <;>
  first
  | exact ⟨_, left_mem_segment _ _ _⟩
  | exact isBounded_segment _ _

/-- Endpoint-wise control: the Hausdorff distance between segments is bounded by
the sum of the distances between corresponding endpoints. -/
lemma hausdorffDist_segment_le_endpoints
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b a' b' : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ a' b') ≤ dist a a' + dist b b' := by
  -- Triangle via `(a, b')`.
  have htri := hausdorffDist_segment_triangle (a) (b) (a') (b')
  -- First leg: move **right** endpoint `b → b'` with left fixed `a`.
  have h₁ : hausdorffDist (segment ℝ a b) (segment ℝ a b') ≤ dist b b' :=
    hausdorffDist_segment_right_le_dist (z := a) (x := b) (y := b')
  -- Second leg: move **left** endpoint `a → a'` with right fixed `b'`.
  have h₂ : hausdorffDist (segment ℝ a b') (segment ℝ a' b') ≤ dist a a' :=
    hausdorffDist_segment_left_le_dist (x := a) (y := a') (z := b')
  -- Combine and commute the sum to match the target order.
  exact htri.trans <| by simpa [add_comm] using add_le_add h₁ h₂

/-- If `xn → x` and `yn → y`, then `dist (xn i) x + dist (yn i) y → 0`. -/
lemma tendsto_dist_add_dist_nhds_zero
    {ι : Type*} {X : Type*} [PseudoMetricSpace X] {l : Filter ι}
    {xn yn : ι → X} {x y : X}
    (hx : Tendsto xn l (𝓝 x)) (hy : Tendsto yn l (𝓝 y)) :
    Tendsto (fun i ↦ dist (xn i) x + dist (yn i) y) l (𝓝 0) := by
  have hx0 : Tendsto (fun i ↦ dist (xn i) x) l (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hx
  have hy0 : Tendsto (fun i ↦ dist (yn i) y) l (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hy
  simpa using hx0.add hy0

/-- Segments converge in Hausdorff distance when their endpoints converge. -/
theorem tendsto_hausdorffDist_segment_of_tendsto_endpoints
    {ι : Type*} {xn yn : ι → Fin 2 → ℝ} {x y : Fin 2 → ℝ} {l : Filter ι}
    (hx : Tendsto xn l (𝓝 x)) (hy : Tendsto yn l (𝓝 y)) :
    Tendsto (fun i ↦ hausdorffDist (segment ℝ (xn i) (yn i)) (segment ℝ x y)) l (𝓝 0) := by
  -- Pointwise bound by the sum of endpoint distances.
  have hbound : ∀ i, hausdorffDist (segment ℝ (xn i) (yn i)) (segment ℝ x y) ≤ dist (xn i) x + dist (yn i) y := by
    intro i
    simpa using (hausdorffDist_segment_le_endpoints (a := xn i) (b := yn i) (a' := x) (b' := y))
  -- The upper bound tends to `0`, hence the Hausdorff distance does by squeezing.
  refine squeeze_zero (fun _ ↦ hausdorffDist_nonneg) hbound ?_
  simpa using tendsto_dist_add_dist_nhds_zero hx hy

/-- The segment `segment01 a b` in `ℝ²` is compact.
This follows since it is the continuous image of the compact interval `[0,1]`. -/
lemma isCompact_segment01 (a b : ℝ) :
    IsCompact (segment01 a b) := by
  -- identify the segment with the image of `[0,1]` under the line map
  have : segment ℝ ![a, 0] ![b, 1] = AffineMap.lineMap ![a, 0] ![b, 1] '' Icc (0 : ℝ) 1 := by
    simp [segment_eq_image_lineMap]
  -- the line map is continuous
  have hcont : Continuous fun t : ℝ ↦ AffineMap.lineMap ![a, 0] ![b, 1] t := by
    continuity
  -- compactness transfers under continuous images
  simpa [segment01, this] using (isCompact_Icc.image hcont)

/-- The Hausdorff extended distance between two `segment01`s is finite. -/
lemma hausdorffEDist_segment01_ne_top (a b a' b' : ℝ) :
    hausdorffEDist (segment01 a b) (segment01 a' b') ≠ ⊤ := by
  -- Each `segment01` is nonempty: it contains its left endpoint.
  have Lne : (segment01 a  b).Nonempty :=
    ⟨![a, 0], by simpa [segment01] using left_mem_segment ℝ ![a,0] ![b,1]⟩
  have Rne : (segment01 a' b').Nonempty :=
    ⟨![a',0], by simpa [segment01] using left_mem_segment ℝ ![a',0] ![b',1]⟩
  -- Each `segment01` is bounded (indeed compact): use the compact image of `[0,1]`.
  have Lbd : IsBounded (segment01 a b) := (isCompact_segment01 a b).isBounded
  have Rbd : IsBounded (segment01 a' b') := (isCompact_segment01 a' b').isBounded
  -- Finite Hausdorff *e-distance* holds for nonempty, bounded sets.
  exact hausdorffEDist_ne_top_of_nonempty_of_bounded Lne Rne Lbd Rbd

/-- If `L,T` are `segment01`s, any `y ∈ L` has a point on `T` within the Hausdorff distance. -/
lemma exists_mem_segment01_dist_le
    {a b a' b' : ℝ} {y : Fin 2 → ℝ}
    (hy : y ∈ (segment01 a b)) :
    ∃ t ∈ (segment01 a' b'), dist t y ≤ hausdorffDist (segment01 a b) (segment01 a' b') := by
  -- choose a minimiser on the compact target segment
  obtain ⟨t, ht_mem, ht_eq⟩ := (isCompact_segment01 a' b').exists_infDist_eq_dist
    (by refine ⟨![a',0], ?_⟩; simpa [segment01] using left_mem_segment ℝ ![a',0] ![b',1]) y
  -- compare infDist with HD (finiteness from the previous lemma)
  have hfin : hausdorffEDist (segment01 a b) (segment01 a' b') ≠ ⊤ :=
    hausdorffEDist_segment01_ne_top a b a' b'
  have h_le : infDist y (segment01 a' b' : Set (Fin 2 → ℝ)) ≤ hausdorffDist (segment01 a b) (segment01 a' b') :=
    infDist_le_hausdorffDist_of_mem (x := y) (s := segment01 a b) (t := segment01 a' b') hy hfin
  -- turn infDist into a genuine distance via the minimiser `t`
  have : dist t y = infDist y (segment01 a' b') := by
    simpa [dist_comm, eq_comm] using ht_eq
  exact ⟨t, ht_mem, by simpa [this] using h_le⟩

/-- A point of `K` lying outside the closed `rectangle` has strictly positive
distance to `rectangle`. -/
theorem infDist_rectangle_pos_of_notMem {k' : Fin 2 → ℝ} (h_notin : k' ∉ rectangle) :
    0 < infDist k' rectangle := by
  by_contra h
  -- if not `> 0`, then `infDist = 0` (by nonnegativity)
  have h0 : infDist k' (rectangle : Set _) = 0 := le_antisymm (le_of_not_gt h) infDist_nonneg
  -- hence `k' ∈ closure rectangle`
  have hk_cl : k' ∈ closure (rectangle : Set (Fin 2 → ℝ)) := by
    simpa [mem_closure_iff_infDist_zero, nonempty_rectangle] using h0
  -- but `rectangle` is closed, contradiction
  have : k' ∈ rectangle := by simpa [isClosed_rectangle.closure_eq] using hk_cl
  exact h_notin this

/-- **Stability of the ambient rectangle under limits**.
If each `Pₙ ⊆ rectangle` and `Pₙ → K` in `NonemptyCompacts`, then `K ⊆ rectangle`. -/
theorem limit_subset_rectangle
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ kornerCompacts) (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (fin_dist : ∀ (n : ℕ), hausdorffEDist (K : Set (Fin 2 → ℝ)) (Pₙ n) ≠ ⊤) :
    ↑K ⊆ rectangle := by
  have hP_sub : ∀ n, ↑(Pₙ n) ⊆ rectangle := fun n ↦ (h_mem n).2.1
  intro k' hk'
  by_contra h_notin
  -- positive distance from `k'` to rectangle
  set d := infDist k' rectangle with hd
  have hd_pos : 0 < d := infDist_rectangle_pos_of_notMem h_notin
  -- pick index `N` so that `Pₙ N` is within `d/2` of `K`
  obtain ⟨N, hN⟩ := h_lim (d/2) (half_pos hd_pos)
  have hhd : hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ N) < d/2 :=
    by simpa [Metric.NonemptyCompacts.dist_eq, dist_comm] using hN N le_rfl
  -- apply Hausdorff → pointwise lemma
  obtain ⟨y, hyP, hy_lt⟩ := exists_dist_lt_of_hausdorffDist_lt hk' hhd (fin_dist N)
  -- but `y ∈ rectangle`, so `d ≤ dist k' y`, contradiction with `dist k' y < d/2`
  have hd_le : d ≤ dist k' y := by simpa [hd] using infDist_le_dist_of_mem (x := k') (hP_sub N hyP)
  exact (not_lt_of_ge hd_le) (lt_of_lt_of_le hy_lt (by linarith [hd_pos]))

/--
If each `Pₙ` is in `kornerCompacts`, then every point of `Pₙ n` lies on a segment
`segment01 (x 0) (x 1)` for some `x ∈ [-1,1] × [-1,1]`, and that whole segment is
contained in `Pₙ n`.
-/
theorem exists_segment01_of_mem_kornerCompacts {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ kornerCompacts)
    (pₙ : (k : Fin 2 → ℝ) → k ∈ K → ℕ → Fin 2 → ℝ)
    (hpₙ_mem : ∀ (k : Fin 2 → ℝ) (a : k ∈ K) (n : ℕ), pₙ k a n ∈ Pₙ n)
    (k : Fin 2 → ℝ) (hk : k ∈ ↑K) (n : ℕ) :
    ∃ x ∈ Icc ![-1, -1] ![1, 1], pₙ k hk n ∈ segment01 (x 0) (x 1) ∧ segment01 (x 0) (x 1) ⊆ ↑(Pₙ n) := by
  rcases h_mem n with ⟨_, _, ⟨A, hA_sub, hA_eq⟩, _⟩
  have : pₙ k hk n ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
    rw [←hA_eq]
    exact hpₙ_mem k hk n
  rcases mem_iUnion₂.1 this with ⟨p, hpA, hp_seg⟩
  let x : Fin 2 → ℝ := ![p 0, p 1]
  have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
    simpa [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, x] using hA_sub hpA
  have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
    intro y hy
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      x] at hy
    have : y ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
      apply mem_iUnion₂.2
      use p
    rwa [←hA_eq] at this
  exact ⟨x, hx, hp_seg, hsub⟩

theorem mem_iUnion_segment_of_limit {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ kornerCompacts) (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (h_closed : IsClosed ↑(K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), hausdorffEDist ↑(Pₙ n : Set (Fin 2 → ℝ)) ↑K ≠ ⊤) (pₙ : (k : Fin 2 → ℝ) → k ∈ K → ℕ → Fin 2 → ℝ)
    (hpₙ_mem : ∀ (k : Fin 2 → ℝ) (a : k ∈ K) (n : ℕ), pₙ k a n ∈ Pₙ n)
    (h_tendsto : ∀ (k : Fin 2 → ℝ) (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k)) :
    let A := {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K};
    A = {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K} →
      A ⊆ Icc ![-1, -1] ![1, 1] → ∀ k ∈ ↑K, k ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
  intro A hA hAsub k hk
  choose x hx h_pn_in_seg_n h_seg_subset_n using exists_segment01_of_mem_kornerCompacts
  obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq (hx h_mem pₙ hpₙ_mem k hk)
  set L := segment01 (x_lim 0) (x_lim 1) with hL

  have h_seg_j_P : ∀ j, segment01 (x h_mem pₙ hpₙ_mem k hk (φ j) 0) (x h_mem pₙ hpₙ_mem k hk (φ j) 1) ⊆ Pₙ (φ j) := by
    intro j y hy
    apply h_seg_subset_n
    exact hy

  have h_seg_HD0 : Tendsto (fun j ↦
    hausdorffDist (segment01 (x h_mem pₙ hpₙ_mem k hk (φ j) 0) (x h_mem pₙ hpₙ_mem  k hk (φ j) 1)) L) atTop (𝓝 0) := by
    apply tendsto_hausdorffDist_segment_of_tendsto_endpoints
    all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]
  observe h_L_compact : IsCompact L
  refine mem_iUnion.2 ?_
  refine ⟨x_lim, ?_⟩
  refine mem_iUnion.2 ?_
  refine ⟨?hxlim_in_A, ?k_in_L⟩
  have hLsubK : L ⊆ (K : Set _) := by
    intro y hyL
    set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x h_mem pₙ hpₙ_mem k hk (φ j) 0) (x h_mem pₙ hpₙ_mem  k hk (φ j) 1) with hS
    have h_exist :
        ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
      intro j
      have := exists_mem_segment01_dist_le
        (a := x_lim 0) (b := x_lim 1)
        (a' := x h_mem pₙ hpₙ_mem  k hk (φ j) 0) (b' := x h_mem pₙ hpₙ_mem  k hk (φ j) 1)
        (y := y) (hy := by simpa [hL] using hyL)
      rcases this with ⟨q, hqS, hq_le⟩
      exact ⟨q, hqS, by simpa [hL] using hq_le⟩

    choose q hqS hq_le using h_exist

    have hqP : ∀ j, q j ∈ (Pₙ (φ j) : Set (Fin 2 → ℝ)) := by
      intro j
      exact h_seg_j_P j (hqS j)

    have hHD_LS :
        Tendsto (fun j ↦ hausdorffDist L (S j)) atTop (𝓝 0) := by
      simpa [hausdorffDist_comm] using h_seg_HD0
    have hdist_qy :
        Tendsto (fun j ↦ dist (q j) y) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ hq_le j) hHD_LS

    have hq_tendsto : Tendsto q atTop (𝓝 y) :=
      (tendsto_iff_dist_tendsto_zero).2 hdist_qy

    have hHD_PK_all : Tendsto (fun n ↦ hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
      have : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0) := by
        refine Metric.tendsto_atTop.2 ?_
        simpa [dist_comm] using h_lim
      simpa [Metric.NonemptyCompacts.dist_eq] using this

    have hHD_PK_subseq : Tendsto (fun j ↦ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
      have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
      exact hHD_PK_all.comp hφ_tendsto

    have hr_exists : ∀ j, ∃ r ∈ (K : Set (Fin 2 → ℝ)), dist (q j) r = Metric.infDist (q j) (K : Set (Fin 2 → ℝ)) := by
      intro j
      obtain ⟨r, hrK, hr_eq⟩ := (K.toCompacts.isCompact).exists_infDist_eq_dist K.nonempty (q j)
      exact ⟨r, hrK, by simpa [comm] using hr_eq⟩

    choose r hrK hr_eq using hr_exists

    have hr_le_HD : ∀ j, dist (q j) (r j) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) := by
      intro j
      have hfin : hausdorffEDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
        simpa [hausdorffEDist_comm] using fin_dist (φ j)
      have h_le : Metric.infDist (q j) (K : Set (Fin 2 → ℝ)) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) := by
        apply Metric.infDist_le_hausdorffDist_of_mem
        · exact h_seg_subset_n h_mem pₙ hpₙ_mem k hk (φ j) (hqS j)
        · exact fin_dist (φ j)
      simpa [hr_eq j] using h_le

    have hdist_y_r :Tendsto (fun j ↦ dist y (r j)) atTop (𝓝 0) := by
      have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
        intro j
        simpa [dist_comm] using dist_triangle_right y (r j) (q j)

      have hsum_to0 : Tendsto (fun j ↦ dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
        simpa using hdist_qy.add hHD_PK_subseq

      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hsum_to0
      exact (htri j).trans (add_le_add (by simp [dist_comm]) (hr_le_HD j))

    have hr_tendsto : Tendsto r atTop (𝓝 y) := by
      refine tendsto_iff_dist_tendsto_zero.2 ?_
      simpa [dist_comm] using hdist_y_r

    exact h_closed.mem_of_tendsto hr_tendsto (Eventually.of_forall hrK)

  · exact ⟨hx_lim_mem, by simpa [hL] using hLsubK⟩
  · observe hL_compact : IsCompact L
    observe hL_closed : IsClosed L
    have h_inf_to_zero : Tendsto (fun j ↦ infDist (pₙ k hk (φ j)) L) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_seg_HD0 ?lower ?upper
      · intro i
        exact infDist_nonneg
      · intro i
        apply infDist_le_hausdorffDist_of_mem
        · exact h_pn_in_seg_n h_mem pₙ hpₙ_mem  k hk (φ i)
        · exact hausdorffEDist_segment01_ne_top (x h_mem pₙ hpₙ_mem k hk (φ i) 0) (x h_mem pₙ hpₙ_mem  k hk (φ i) 1) (x_lim 0) (x_lim 1)
    have h_inf_to_k : Tendsto (fun j ↦ infDist (pₙ k hk (φ j)) L) atTop (𝓝 (infDist k L)) := by
      have hcont : Continuous (fun x ↦ infDist x L) := by
        simpa using (Metric.continuous_infDist_pt (s := L))
      apply (hcont.tendsto k).comp
      have : Tendsto (fun j ↦ pₙ k hk (φ j)) atTop (𝓝 k) := by
        have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
        exact (h_tendsto k hk).comp hφ_tendsto
      exact this
    have h_k_zero : infDist k L = 0 := tendsto_nhds_unique h_inf_to_k h_inf_to_zero
    have hk_closure : k ∈ closure L := by
      rw [mem_closure_iff_infDist_zero]
      · exact h_k_zero
      · rw [hL]
        simpa [segment01] using
          (show (segment ℝ ![x_lim 0, 0] ![x_lim 1, 1]).Nonempty from
            ⟨![x_lim 0, 0], left_mem_segment _ _ _⟩)
    simpa [hL_closed.closure_eq] using hk_closure

/--  If `Pₙ ∈ kornerCompacts`, then for every slope `v` with `|v| ≤ 1/2`,
there is a horizontal segment of length `v` contained in `Pₙ n`. -/
theorem exists_segment01_slope_of_mem_kornerCompacts
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)}
    (v : ℝ) (hv : |v| ≤ 1 / 2)
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ kornerCompacts)  :
    ∀ n, ∃ x ∈ Icc ![-1, -1] ![1, 1], x 1 - x 0 = v ∧ segment01 (x 0) (x 1) ⊆ ↑(Pₙ n) := by
  intro n
  rcases h_mem n with ⟨-, -, -, h_prop₂⟩
  rcases h_prop₂ v hv with ⟨x₁, x₂, hx₁, hx₂, hdiffn, hsegPn⟩
  set x : Fin 2 → ℝ := ![x₁, x₂] with h
  have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
    simp_all [Fin.forall_fin_two, Pi.le_def]
  have hdiff : (x 1) - (x 0) = v := by simp [x, hdiffn]
  have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
    intro y hy
    convert hsegPn hy
  exact ⟨x, hx, hdiff, hsub⟩

/-- For each point `k ∈ K`, there is a point `p ∈ Pₙ n`
at distance at most `dist K (Pₙ n)`. -/
theorem exists_mem_dist_le_dist
  {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
  (fin_dist : ∀ (n : ℕ), hausdorffEDist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) :
    ∀ k ∈ K, ∀ (n : ℕ), ∃ p ∈ Pₙ n, dist p k ≤ dist K (Pₙ n) := by
  intro k hk n
  obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
  have hpk : dist p k = Metric.infDist k (Pₙ n : Set _) := by
    simpa [eq_comm, dist_comm] using hp_eq
  have fin : hausdorffEDist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) ≠ ⊤ := by
    simpa [hausdorffEDist_comm] using fin_dist n
  have h_le : Metric.infDist k (Pₙ n : Set _) ≤ Metric.hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) := by
    apply Metric.infDist_le_hausdorffDist_of_mem (x := k) (s := (K : Set _)) (t := (Pₙ n : Set _)) hk fin
  have h_dist : dist p k ≤ dist K (Pₙ n) := by
    simpa [Metric.NonemptyCompacts.dist_eq, hpk] using h_le
  exact ⟨p, hp_mem, h_dist⟩

/-- If each `Pₙ` converges to `K` in the Hausdorff metric,
then the selected points `pₙ` in `Pₙ n`that stay within `dist K (Pₙ n)` of `k`
converge to `k` as `n → ∞`. -/

theorem tendsto_select_points
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε) :
  ∀ (pₙ : (k : Fin 2 → ℝ) → k ∈ K → ℕ → Fin 2 → ℝ),
      (∀ k (hk : k ∈ K) n, dist (pₙ k hk n) k ≤ dist K (Pₙ n)) →
      ∀ k (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k) := by
  intro pₙ hle k hk
  -- Use the metric characterization of `Tendsto`:
  -- `dist (pₙ k hk n) k → 0`.
  refine (tendsto_iff_dist_tendsto_zero).2 ?_
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := h_lim ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have h_le' : dist (dist (pₙ k hk n) k) 0 ≤ dist K (Pₙ n) := by
    simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg)] using hle k hk n
  have h_small : dist K (Pₙ n) < ε := by
    simpa [dist_comm] using hN n hn
  exact lt_of_le_of_lt h_le' h_small

/--
If `Pₙ ∈ kornerCompacts` and `Pₙ → K` in the Hausdorff metric, then `K` also satisfies
the segment property: for every `|v| ≤ 1/2` there exist `x₁, x₂ ∈ [-1,1]` with
`x₂ - x₁ = v` and `segment01 x₁ x₂ ⊆ K`.
-/
theorem exists_segment_subset_K_of_diff_le_half {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ kornerCompacts) (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (h_closed : IsClosed (K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), hausdorffEDist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) :
    ∀ v, |v| ≤ 1 / 2 → ∃ x₁ x₂, x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ ↑K := by
  intro v hv
  have h_exists : ∀ n, ∃ x : Fin 2 → ℝ, x ∈ Icc ![-1, -1] ![1, 1] ∧ (x 1) - (x 0) = v ∧ segment01 (x 0) (x 1) ⊆ Pₙ n := by
      intro n
      rcases h_mem n with ⟨_, _, _, h_prop₂⟩
      rcases h_prop₂ v hv with ⟨x₁, x₂, hx₁, hx₂, hdiffn, hsegPn⟩
      set x : Fin 2 → ℝ := ![x₁, x₂] with h
      have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
        simp_all [Fin.forall_fin_two, Pi.le_def]
      have hdiff : (x 1) - (x 0) = v := by simp [x, hdiffn]
      have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
        intro y hy
        convert hsegPn hy
      exact ⟨x, hx, hdiff, hsub⟩

  choose! x hx hdiff h_segP using h_exists

  obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hx

  have h_seg_n_P : ∀ j, segment01 (x (φ j) 0) (x (φ j) 1) ⊆ Pₙ (φ j) := by
    intro n y hy
    apply h_segP
    exact hy

  set L := segment01 (x_lim 0) (x_lim 1) with hL
  -- set L : NonemptyCompacts (Fin 2 → ℝ) := ⟨⟨segment01 (x_lim 0) (x_lim 1), isCompact_segment01 _ _⟩, by
  --     simpa [segment01] using (show (segment ℝ ![x_lim 0, 0] ![x_lim 1, 1]).Nonempty from ⟨![x_lim 0, 0], left_mem_segment _ _ _⟩)⟩
  --   with hL

  refine ⟨x_lim 0, x_lim 1, ?hx0, ?hx1, ?hdiff_lim, ?hLsubK⟩
  · exact (by simp_all [Pi.le_def, Fin.forall_fin_two])
  · exact (by simp_all [Pi.le_def, Fin.forall_fin_two])
  · have h0 : Tendsto (fun j ↦ (x (φ j)) 0) atTop (𝓝 (x_lim 0)) := ((continuous_apply 0).tendsto _).comp hφ_lim
    have h1 : Tendsto (fun j ↦ (x (φ j)) 1) atTop (𝓝 (x_lim 1)) := ((continuous_apply 1).tendsto _).comp hφ_lim
    have hsub : Tendsto (fun j ↦ (x (φ j) 1 - x (φ j) 0)) atTop (𝓝 (x_lim 1 - x_lim 0)) := h1.sub h0
    have hconst : Tendsto (fun _ : ℕ ↦ v) atTop (𝓝 v) := tendsto_const_nhds
    have : Tendsto (fun j ↦ (x (φ j) 1 - x (φ j) 0)) atTop (𝓝 v) := by simp [hdiff]
    exact tendsto_nhds_unique hsub this
  · show L ⊆ K
    intro y hyL
    set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x (φ j) 0) (x (φ j) 1)
    have h_exist : ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
      intro j
      have := exists_mem_segment01_dist_le
        (a := x_lim 0) (b := x_lim 1)
        (a' := x (φ j) 0) (b' := x (φ j) 1)
        (y := y) (hy := by simpa [hL] using hyL)
      rcases this with ⟨q, hqS, hq_le⟩
      exact ⟨q, hqS, by simpa [hL] using hq_le⟩
    choose q hqS hq_le using h_exist

    have hqP : ∀ j, q j ∈ (Pₙ (φ j) : Set (Fin 2 → ℝ)) := by
      intro j
      exact h_seg_n_P j (hqS j)
    have h_seg_HD0 : Tendsto (fun j ↦ hausdorffDist (segment01 (x (φ j) 0) (x (φ j) 1)) L) atTop (𝓝 0) := by
      apply tendsto_hausdorffDist_segment_of_tendsto_endpoints
      all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]

    have hHD_LS : Tendsto (fun j ↦ hausdorffDist L (S j)) atTop (𝓝 0) := by
      simpa [hausdorffDist_comm] using h_seg_HD0

    have hdist_qy : Tendsto (fun j ↦ dist (q j) y) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ hq_le j) hHD_LS

    have hHD_PK_all : Tendsto (fun n ↦ hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
      have : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0) := by
        refine Metric.tendsto_atTop.2 ?_
        simpa [dist_comm] using h_lim
      simpa [Metric.NonemptyCompacts.dist_eq] using this

    have hHD_PK_subseq : Tendsto (fun j ↦ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
      have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
      exact hHD_PK_all.comp hφ_tendsto

    have hr_exists : ∀ j, ∃ r ∈ (K : Set (Fin 2 → ℝ)), dist (q j) r = infDist (q j) (K : Set (Fin 2 → ℝ)) := by
      intro j
      obtain ⟨r, hrK, hr_eq⟩ := (K.toCompacts.isCompact).exists_infDist_eq_dist K.nonempty (q j)
      exact ⟨r, hrK, by simpa [comm] using hr_eq⟩

    choose r hrK hr_eq using hr_exists

    have hr_le_HD : ∀ j, dist (q j) (r j) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _) := by
      intro j
      have hfin :
          hausdorffEDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
        simpa [hausdorffEDist_comm] using fin_dist (φ j)
      have h_le :=
        Metric.infDist_le_hausdorffDist_of_mem (hqP j) hfin
      simpa [hr_eq j] using h_le

    have hdist_y_r : Tendsto (fun j ↦ dist y (r j)) atTop (𝓝 0) := by
      have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
        intro j
        simpa [dist_comm] using dist_triangle_right y (r j) (q j)

      have hsum_to0 : Tendsto (fun j ↦ dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
        simpa using hdist_qy.add hHD_PK_subseq

      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hsum_to0
      exact (htri j).trans (add_le_add (by simp [dist_comm]) (hr_le_HD j))
    have hr_tendsto : Tendsto r atTop (𝓝 y) := (tendsto_iff_dist_tendsto_zero.2 (by simpa [dist_comm] using hdist_y_r))

    exact h_closed.mem_of_tendsto hr_tendsto (Eventually.of_forall hrK)

theorem isClosed_kornerCompacts : IsClosed kornerCompacts := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := isBounded_of_mem_kornerCollection (h_mem n)
  have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : hausdorffEDist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (Pₙ n).nonempty K.nonempty (hPn_bdd n) hK_bdd
  split_ands
  · exact h_closed
  · apply limit_subset_rectangle h_mem h_lim
    · intro n
      simpa [hausdorffEDist_comm] using fin_dist n
  · set A : Set (Fin 2 → ℝ) := { p | p ∈ Icc ![-1,-1] ![1,1] ∧ segment01 (p 0) (p 1) ⊆ (K : Set (Fin 2 → ℝ)) } with hA
    use A
    split_ands
    · rintro _ ⟨h, -⟩
      exact h
    · ext k
      constructor
      all_goals intro hk
      · choose pₙ hpₙ_mem hpₙ_lt using exists_mem_dist_le_dist fin_dist
        refine mem_iUnion_segment_of_limit h_mem h_lim h_closed fin_dist pₙ hpₙ_mem ?_ hA ?_ ?_ ?_
        · apply tendsto_select_points h_lim pₙ hpₙ_lt
        · exact sep_subset (Icc ![-1, -1] ![1, 1]) fun x ↦ segment01 (x 0) (x 1) ⊆ ↑K
        · exact hk
      · rcases mem_iUnion₂.1 hk with ⟨_, hpA, hk_seg⟩
        rw [hA] at hpA
        rcases hpA with ⟨-, hseg_sub⟩
        exact hseg_sub hk_seg
  · exact exists_segment_subset_K_of_diff_le_half h_mem h_lim h_closed fin_dist

-- The version below is the unrefactored proof.
-- It is much heavier, and Lean may require an increased heartbeat limit to compile it.

-- theorem P_col'_IsClosed : IsClosed kornerCompacts := by
--   rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
--   intro Pₙ K h_mem h_lim
--   have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
--   rw [Metric.tendsto_atTop] at h_lim
--   -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
--   have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := isBounded_of_mem_kornerCollection (h_mem n)
--   have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
--   have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ :=
--     hausdorffEdist_ne_top_of_nonempty_of_bounded (Pₙ n).nonempty K.nonempty (hPn_bdd n) hK_bdd

--   have : ∀ k ∈ K, ∀ n, ∃ p ∈ Pₙ n, dist p k ≤ dist K (Pₙ n) := by
--     intro k hk n
--     simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
--     obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
--     have hpk : dist p k = Metric.infDist k (Pₙ n : Set _) := by
--       simpa [eq_comm, dist_comm] using hp_eq
--     have fin : EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) ≠ ⊤ := by
--       simpa [EMetric.hausdorffEdist_comm] using fin_dist n
--     have h_le : Metric.infDist k (Pₙ n : Set _) ≤ Metric.hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) := by
--       apply Metric.infDist_le_hausdorffDist_of_mem (x := k) (s := (K : Set _)) (t := (Pₙ n : Set _)) hk fin
--     have h_dist : dist p k ≤ dist K (Pₙ n) := by
--       simpa [Metric.NonemptyCompacts.dist_eq, hpk] using h_le
--     exact ⟨p, hp_mem, h_dist⟩

--   choose pₙ hpₙ_mem hpₙ_lt using this

--   -- extract_goal
--   have h_tendsto : ∀ (k : Fin 2 → ℝ) (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k) := by
--     intro k hk
--     rw [NormedAddCommGroup.tendsto_atTop']
--     intro ε hε
--     obtain ⟨N, hN⟩ := h_lim ε hε
--     refine ⟨N, fun n hn ↦ ?_⟩
--     have h_le : dist (pₙ k hk n) k ≤ dist K (Pₙ n) := hpₙ_lt k hk n
--     have h_small : dist K (Pₙ n) < ε := by
--       simpa [dist_comm] using hN n (Nat.le_of_lt hn)
--     exact lt_of_le_of_lt h_le h_small

--   have h_sub : (K : Set _) ⊆ rectangle := by
--     have hP_sub : ∀ n, (Pₙ n : Set _) ⊆ rectangle := by
--       intro n
--       rcases h_mem n with ⟨_, h_subset, _, _⟩
--       exact h_subset
--     have rect_closed : IsClosed rectangle := by
--       rw [rectangle]
--       exact isClosed_Icc

--     -- Main argument
--     intro k' hk'
--     by_contra h_notin

--     have h_pos : 0 < Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) := by
--       have h_ne : Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) ≠ 0 := by
--         intro h_eq
--         have h_cl : k' ∈ closure (rectangle : Set (Fin 2 → ℝ)) := by
--           rw [Metric.mem_closure_iff_infDist_zero]
--           · exact h_eq
--           · dsimp [rectangle]
--             refine ⟨![0, 0], by simp [Pi.le_def, Fin.forall_fin_two]⟩
--         have : k' ∈ rectangle := by
--           simpa [rect_closed.closure_eq] using h_cl
--         exact h_notin this
--       exact lt_of_le_of_ne Metric.infDist_nonneg h_ne.symm

--     set d : ℝ := Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) with hd
--     have h_half_pos : 0 < d / 2 := by linarith
--     obtain ⟨N, hN⟩ := h_lim (d / 2) h_half_pos

--     have h_haus : hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ N : Set _) < d / 2 := by
--       have : dist (Pₙ N) K < d / 2 := hN N (le_rfl)
--       simpa [Metric.NonemptyCompacts.dist_eq, dist_comm] using this

--     have h_edist_ne : EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ N : Set _) ≠ ⊤ := by
--       simpa [EMetric.hausdorffEdist_comm] using fin_dist N

--     obtain ⟨y, hyP, hy_lt⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hk' h_haus h_edist_ne

--     have hy_rect : y ∈ rectangle := (hP_sub N) hyP

--     have hd_le : d ≤ dist k' y := by
--       have h_le := Metric.infDist_le_dist_of_mem (x := k') hy_rect
--       simpa [hd] using h_le

--     have : dist k' y < d := by
--       have : dist k' y < d / 2 := hy_lt
--       exact lt_of_lt_of_le this (by linarith)
--     exact (not_lt_of_ge hd_le) this

--   have h_union : ∃ A ⊆ Icc ![-1, -1] ![1, 1], K = ⋃ p ∈ A, segment01 (p 0) (p 1) := by
--     have h_seg_exists : ∀ (k : Fin 2 → ℝ) (hk : k ∈ (K : Set (Fin 2 → ℝ))) (n : ℕ), ∃ (x : Fin 2 → ℝ), x ∈ Icc ![-1,-1] ![1,1] ∧ pₙ k hk n ∈ segment01 (x 0) (x 1) ∧ segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
--       intro k hk n
--       rcases h_mem n with ⟨_, _, ⟨A, hA_sub, hA_eq⟩, _⟩
--       have : pₙ k hk n ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
--         rw [←hA_eq]
--         exact hpₙ_mem k hk n
--       rcases mem_iUnion₂.1 this with ⟨p, hpA, hp_seg⟩
--       let x : Fin 2 → ℝ := ![p 0, p 1]
--       have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
--         simpa [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, x] using hA_sub hpA
--       have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
--         intro y hy
--         simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
--           x] at hy
--         have : y ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
--           apply mem_iUnion₂.2
--           use p
--         rwa [←hA_eq] at this
--       exact ⟨x, hx, hp_seg, hsub⟩

--     choose x hx h_pn_in_seg_n h_seg_subset_n using h_seg_exists

--     set A : Set (Fin 2 → ℝ) := { p | p ∈ Icc ![-1,-1] ![1,1] ∧ segment01 (p 0) (p 1) ⊆ (K : Set (Fin 2 → ℝ)) } with hA

--     have hA_sub : A ⊆ Icc ![-1, -1] ![1, 1] := by
--       rintro p ⟨hp_in, _⟩
--       exact hp_in

--     refine ⟨A, hA_sub, ?_⟩
--     ext k
--     constructor
--     · intro hk
--       obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq (hx k hk)
--       set L := segment01 (x_lim 0) (x_lim 1) with hL

--       have h_seg_j_P : ∀ j, segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) ⊆ Pₙ (φ j) := by
--         intro j y hy
--         apply h_seg_subset_n
--         exact hy

--       have h_seg_HD0 : Tendsto (fun j ↦ hausdorffDist (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) L) atTop (𝓝 0) := by
--         apply tendsto_hausdorffDist_segment_of_tendsto_endpoints
--         all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]
--       observe h_L_compact : IsCompact L
--       refine mem_iUnion.2 ?_
--       refine ⟨x_lim, ?_⟩
--       refine mem_iUnion.2 ?_
--       refine ⟨?hxlim_in_A, ?k_in_L⟩
--       have hLsubK : L ⊆ (K : Set _) := by
--         intro y hyL
--         set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) with hS
--         have h_exist :
--             ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
--           intro j
--           have := exists_mem_segment01_dist_le
--             (a := x_lim 0) (b := x_lim 1)
--             (a' := x k hk (φ j) 0) (b' := x k hk (φ j) 1)
--             (y := y) (hy := by simpa [hL] using hyL)
--           rcases this with ⟨q, hqS, hq_le⟩
--           exact ⟨q, hqS, by simpa [hL] using hq_le⟩

--         choose q hqS hq_le using h_exist

--         have hqP : ∀ j, q j ∈ (Pₙ (φ j) : Set (Fin 2 → ℝ)) := by
--           intro j
--           exact h_seg_j_P j (hqS j)

--         have hHD_LS :
--             Tendsto (fun j ↦ hausdorffDist L (S j)) atTop (𝓝 0) := by
--           simpa [hausdorffDist_comm] using h_seg_HD0
--         have hdist_qy :
--             Tendsto (fun j ↦ dist (q j) y) atTop (𝓝 0) := by
--           refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ hq_le j) hHD_LS

--         have hq_tendsto : Tendsto q atTop (𝓝 y) :=
--           (tendsto_iff_dist_tendsto_zero).2 hdist_qy

--         have hHD_PK_all : Tendsto (fun n ↦ hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--           have : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0) := by
--             refine Metric.tendsto_atTop.2 ?_
--             simpa [dist_comm] using h_lim
--           simpa [Metric.NonemptyCompacts.dist_eq] using this

--         have hHD_PK_subseq : Tendsto (fun j ↦ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--           have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
--           exact hHD_PK_all.comp hφ_tendsto

--         have hr_exists : ∀ j, ∃ r ∈ (K : Set (Fin 2 → ℝ)), dist (q j) r = Metric.infDist (q j) (K : Set (Fin 2 → ℝ)) := by
--           intro j
--           obtain ⟨r, hrK, hr_eq⟩ := (K.toCompacts.isCompact).exists_infDist_eq_dist K.nonempty (q j)
--           exact ⟨r, hrK, by simpa [comm] using hr_eq⟩

--         choose r hrK hr_eq using hr_exists

--         have hr_le_HD : ∀ j, dist (q j) (r j) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) := by
--           intro j
--           have hfin : EMetric.hausdorffEdist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
--             simpa [EMetric.hausdorffEdist_comm] using fin_dist (φ j)
--           have h_le : Metric.infDist (q j) (K : Set (Fin 2 → ℝ)) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) := by
--             apply Metric.infDist_le_hausdorffDist_of_mem
--             · exact h_seg_subset_n k hk (φ j) (hqS j)
--             · exact fin_dist (φ j)
--           simpa [hr_eq j] using h_le

--         have hdist_y_r :Tendsto (fun j ↦ dist y (r j)) atTop (𝓝 0) := by
--           have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
--             intro j
--             simpa [dist_comm] using dist_triangle_right y (r j) (q j)

--           have hsum_to0 : Tendsto (fun j ↦ dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--             simpa using hdist_qy.add hHD_PK_subseq

--           refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hsum_to0
--           exact (htri j).trans (add_le_add (by simp [dist_comm]) (hr_le_HD j))

--         have hr_tendsto : Tendsto r atTop (𝓝 y) := by
--           refine tendsto_iff_dist_tendsto_zero.2 ?_
--           simpa [dist_comm] using hdist_y_r

--         exact h_closed.mem_of_tendsto hr_tendsto (Eventually.of_forall hrK)

--       · exact ⟨hx_lim_mem, by simpa [hL] using hLsubK⟩
--       · observe hL_compact : IsCompact L
--         observe hL_closed : IsClosed L
--         have h_inf_to_zero : Tendsto (fun j ↦ infDist (pₙ k hk (φ j)) L) atTop (𝓝 0) := by
--           refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_seg_HD0 ?lower ?upper
--           · intro i
--             exact infDist_nonneg
--           · intro i
--             apply infDist_le_hausdorffDist_of_mem
--             · exact h_pn_in_seg_n k hk (φ i)
--             · exact hausdorffEDist_segment01_ne_top (x k hk (φ i) 0) (x k hk (φ i) 1) (x_lim 0) (x_lim 1)
--         have h_inf_to_k : Tendsto (fun j ↦ infDist (pₙ k hk (φ j)) L) atTop (𝓝 (infDist k L)) := by
--           have hcont : Continuous (fun x ↦ infDist x L) := by
--             simpa using (Metric.continuous_infDist_pt (s := L))
--           apply (hcont.tendsto k).comp
--           have : Tendsto (fun j ↦ pₙ k hk (φ j)) atTop (𝓝 k) := by
--             have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
--             exact (h_tendsto k hk).comp hφ_tendsto
--           exact this
--         have h_k_zero : infDist k L = 0 := tendsto_nhds_unique h_inf_to_k h_inf_to_zero
--         have hk_closure : k ∈ closure L := by
--           rw [mem_closure_iff_infDist_zero]
--           · exact h_k_zero
--           · simpa [segment01] using (show (segment ℝ ![x_lim 0, 0] ![x_lim 1, 1]).Nonempty from ⟨![x_lim 0, 0], left_mem_segment _ _ _⟩)
--         simpa [hL_closed.closure_eq] using hk_closure
--     · intro hk_union
--       rcases mem_iUnion₂.1 hk_union with ⟨p, hpA, hk_seg⟩
--       rw [hA] at hpA
--       rcases hpA with ⟨_, hseg_sub⟩
--       exact hseg_sub hk_seg

--   -- PROPERTY 2

--   have h_forall : ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂, x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ K := by
--     intro v hv
--     have h_exists : ∀ n, ∃ x : Fin 2 → ℝ, x ∈ Icc ![-1, -1] ![1, 1] ∧ (x 1) - (x 0) = v ∧ segment01 (x 0) (x 1) ⊆ Pₙ n := by
--       intro n
--       rcases h_mem n with ⟨_, _, _, h_prop₂⟩
--       rcases h_prop₂ v hv with ⟨x₁, x₂, hx₁, hx₂, hdiffn, hsegPn⟩
--       set x : Fin 2 → ℝ := ![x₁, x₂] with h
--       have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
--         simp_all [Fin.forall_fin_two, Pi.le_def]
--       have hdiff : (x 1) - (x 0) = v := by simp [x, hdiffn]
--       have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
--         intro y hy
--         convert hsegPn hy
--       exact ⟨x, hx, hdiff, hsub⟩

--     choose! x hx hdiff h_segP using h_exists

--     obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hx

--     have h_seg_n_P : ∀ j, segment01 (x (φ j) 0) (x (φ j) 1) ⊆ Pₙ (φ j) := by
--       intro n y hy
--       apply h_segP
--       exact hy

--     set L := segment01 (x_lim 0) (x_lim 1) with hL
--     -- set L : NonemptyCompacts (Fin 2 → ℝ) := ⟨⟨segment01 (x_lim 0) (x_lim 1), isCompact_segment01 _ _⟩, by
--     --     simpa [segment01] using (show (segment ℝ ![x_lim 0, 0] ![x_lim 1, 1]).Nonempty from ⟨![x_lim 0, 0], left_mem_segment _ _ _⟩)⟩
--     --   with hL

--     refine ⟨x_lim 0, x_lim 1, ?hx0, ?hx1, ?hdiff_lim, ?hLsubK⟩
--     · exact (by simp_all [Pi.le_def, Fin.forall_fin_two])
--     · exact (by simp_all [Pi.le_def, Fin.forall_fin_two])
--     · have h0 : Tendsto (fun j ↦ (x (φ j)) 0) atTop (𝓝 (x_lim 0)) := ((continuous_apply 0).tendsto _).comp hφ_lim
--       have h1 : Tendsto (fun j ↦ (x (φ j)) 1) atTop (𝓝 (x_lim 1)) := ((continuous_apply 1).tendsto _).comp hφ_lim
--       have hsub : Tendsto (fun j ↦ (x (φ j) 1 - x (φ j) 0)) atTop (𝓝 (x_lim 1 - x_lim 0)) := h1.sub h0
--       have hconst : Tendsto (fun _ : ℕ ↦ v) atTop (𝓝 v) := tendsto_const_nhds
--       have : Tendsto (fun j ↦ (x (φ j) 1 - x (φ j) 0)) atTop (𝓝 v) := by simp [hdiff]
--       exact tendsto_nhds_unique hsub this
--     · show L ⊆ K
--       intro y hyL
--       set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x (φ j) 0) (x (φ j) 1)
--       have h_exist : ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
--         intro j
--         have := exists_mem_segment01_dist_le
--           (a := x_lim 0) (b := x_lim 1)
--           (a' := x (φ j) 0) (b' := x (φ j) 1)
--           (y := y) (hy := by simpa [hL] using hyL)
--         rcases this with ⟨q, hqS, hq_le⟩
--         exact ⟨q, hqS, by simpa [hL] using hq_le⟩
--       choose q hqS hq_le using h_exist

--       have hqP : ∀ j, q j ∈ (Pₙ (φ j) : Set (Fin 2 → ℝ)) := by
--         intro j
--         exact h_seg_n_P j (hqS j)
--       have h_seg_HD0 : Tendsto (fun j ↦ hausdorffDist (segment01 (x (φ j) 0) (x (φ j) 1)) L) atTop (𝓝 0) := by
--         apply tendsto_hausdorffDist_segment_of_tendsto_endpoints
--         all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]

--       have hHD_LS : Tendsto (fun j ↦ hausdorffDist L (S j)) atTop (𝓝 0) := by
--         simpa [hausdorffDist_comm] using h_seg_HD0

--       have hdist_qy : Tendsto (fun j ↦ dist (q j) y) atTop (𝓝 0) := by
--         refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ hq_le j) hHD_LS

--       have hHD_PK_all : Tendsto (fun n ↦ hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--         have : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0) := by
--           refine Metric.tendsto_atTop.2 ?_
--           simpa [dist_comm] using h_lim
--         simpa [Metric.NonemptyCompacts.dist_eq] using this

--       have hHD_PK_subseq : Tendsto (fun j ↦ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--         have hφ_tendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
--         exact hHD_PK_all.comp hφ_tendsto

--       have hr_exists : ∀ j, ∃ r ∈ (K : Set (Fin 2 → ℝ)), dist (q j) r = infDist (q j) (K : Set (Fin 2 → ℝ)) := by
--         intro j
--         obtain ⟨r, hrK, hr_eq⟩ := (K.toCompacts.isCompact).exists_infDist_eq_dist K.nonempty (q j)
--         exact ⟨r, hrK, by simpa [comm] using hr_eq⟩

--       choose r hrK hr_eq using hr_exists

--       have hr_le_HD : ∀ j, dist (q j) (r j) ≤ hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _) := by
--         intro j
--         have hfin :
--             EMetric.hausdorffEdist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
--           simpa [EMetric.hausdorffEdist_comm] using fin_dist (φ j)
--         have h_le :=
--           Metric.infDist_le_hausdorffDist_of_mem (hqP j) hfin
--         simpa [hr_eq j] using h_le

--       have hdist_y_r : Tendsto (fun j ↦ dist y (r j)) atTop (𝓝 0) := by
--         have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
--           intro j
--           simpa [dist_comm] using dist_triangle_right y (r j) (q j)

--         have hsum_to0 : Tendsto (fun j ↦ dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
--           simpa using hdist_qy.add hHD_PK_subseq

--         refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hsum_to0
--         exact (htri j).trans (add_le_add (by simp [dist_comm]) (hr_le_HD j))
--       have hr_tendsto : Tendsto r atTop (𝓝 y) := (tendsto_iff_dist_tendsto_zero.2 (by simpa [dist_comm] using hdist_y_r))

--       exact h_closed.mem_of_tendsto hr_tendsto (Eventually.of_forall hrK)

--   exact ⟨h_closed, h_sub, h_union, h_forall⟩

/-- The space `kornerCompacts` is complete. -/
instance : CompleteSpace kornerCompacts :=
  isClosed_kornerCompacts.completeSpace_coe

/-- The space `kornerCompacts` has the Baire property. -/
-- Maybe this can be deprecated
instance : BaireSpace kornerCompacts :=
  inferInstance

noncomputable section

/-- Horizontal slice of a planar set at height `y`. -/
def hSlice (S : Set (Fin 2 → ℝ)) (y : ℝ) : Set ℝ :=
  {x | (![x, y] : Fin 2 → ℝ) ∈ S}

/-- Monotonicity of slices under inclusion. -/
lemma hSlice_mono {S T : Set (Fin 2 → ℝ)} (hST : S ⊆ T) (y : ℝ) :
    hSlice S y ⊆ hSlice T y := by
  intro x hx
  exact hST hx

/-- An open axis-parallel rectangle `(a,b) × (c,d)` in the `Fin 2 → ℝ` model of `ℝ²`. -/
def openRect (a b c d : ℝ) : Set (Fin 2 → ℝ) :=
  {p | p 0 ∈ Ioo a b ∧ p 1 ∈ Ioo c d}

lemma isOpen_openRect {a b c d : ℝ} : IsOpen (openRect a b c d) := by
  have : openRect a b c d
      = (fun p : Fin 2 → ℝ ↦ p 0) ⁻¹' Ioo a b ∩ (fun p : Fin 2 → ℝ ↦ p 1) ⁻¹' Ioo c d := rfl
  rw [this]
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage (continuous_apply 1))

/-- Körner's "thin cover" condition at height `v` and thickness `ε` (Lemma 2.4): there are
finitely many open axis-parallel rectangles covering the part of `P` lying in the horizontal
band `|y - v| ≤ ε`, such that at every height `y` of the band the rectangles present at
height `y` have total width strictly less than `100 ε`. -/
def HasThinCover (P : Set (Fin 2 → ℝ)) (v ε : ℝ) : Prop :=
  ∃ (N : ℕ) (a b c d : Fin N → ℝ),
    (∀ j, a j ≤ b j) ∧
    (∀ p ∈ P, |p 1 - v| ≤ ε → ∃ j, p ∈ openRect (a j) (b j) (c j) (d j)) ∧
    (∀ y : ℝ, |y - v| ≤ ε →
      ∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) y < 100 * ε)

/-- `𝒫(v, ε)` as a subset of `NonemptyCompacts (Fin 2 → ℝ)`. -/
def thinCoverSet (v ε : ℝ) : Set kornerCompacts :=
  {P | HasThinCover (P : Set _) v ε}

/-- The thin-cover condition is open in the Hausdorff metric: the witnessing open rectangles
cover the compact band-part of `P` together with the open "outside the band" region, and a
compact set contained in an open set stays inside it under small Hausdorff perturbations. -/
lemma isOpen_setOf_hasThinCover (v ε : ℝ) :
    IsOpen {K : NonemptyCompacts (Fin 2 → ℝ) | HasThinCover (K : Set (Fin 2 → ℝ)) v ε} := by
  rw [Metric.isOpen_iff]
  rintro K ⟨N, a, b, c, d, hab, hcov, hthin⟩
  set W : Set (Fin 2 → ℝ) :=
    (⋃ j, openRect (a j) (b j) (c j) (d j)) ∪ {p | ε < |p 1 - v|} with hW
  have hWopen : IsOpen W := by
    apply IsOpen.union (isOpen_iUnion fun j ↦ isOpen_openRect)
    exact isOpen_lt continuous_const (((continuous_apply 1).sub continuous_const).abs)
  have hKW : (K : Set (Fin 2 → ℝ)) ⊆ W := by
    intro p hp
    by_cases hpv : |p 1 - v| ≤ ε
    · rcases hcov p hp hpv with ⟨j, hj⟩
      exact Or.inl (mem_iUnion.2 ⟨j, hj⟩)
    · exact Or.inr (lt_of_not_ge hpv)
  obtain ⟨δ, hδ, hsub⟩ := K.isCompact.exists_thickening_subset_open hWopen hKW
  refine ⟨δ, hδ, fun K' hK' ↦ ?_⟩
  have hlt : hausdorffDist (K' : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) < δ := by
    rw [← NonemptyCompacts.dist_eq]
    exact Metric.mem_ball.1 hK'
  have hK'W : (K' : Set (Fin 2 → ℝ)) ⊆ W := by
    refine subset_trans (fun x hx ↦ ?_) hsub
    rw [mem_thickening_iff_infDist_lt K.nonempty]
    have hfin : hausdorffEDist (K' : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded K'.nonempty K.nonempty
        K'.isCompact.isBounded K.isCompact.isBounded
    exact lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem hx hfin) hlt
  refine ⟨N, a, b, c, d, hab, fun p hp hpv ↦ ?_, hthin⟩
  rcases hK'W hp with h | h
  · exact mem_iUnion.1 h
  · exact absurd hpv (not_le.2 h)

theorem isOpen_thinCoverSet (v ε : ℝ) : IsOpen (thinCoverSet v ε) := by
  have : thinCoverSet v ε = Subtype.val ⁻¹'
      {K : NonemptyCompacts (Fin 2 → ℝ) | HasThinCover (K : Set (Fin 2 → ℝ)) v ε} := rfl
  rw [this]
  exact (isOpen_setOf_hasThinCover v ε).preimage continuous_subtype_val

/-! ### Density of the thin-cover condition (Körner, Lemma 2.4, density half)

Following the paper, one approximates `P ∈ 𝒫` within `δ` by a set `P'` of the form
`P' = Q' ∪ Q''` where `Q''` is a finite union of segments of `P` (a `δ`-net, by
compactness) and `Q'` is a finite union of *fans*: one-parameter families of segments
pivoting at height `v` around finitely many segments of (a slightly shrunk copy of) `P`
whose slopes form a grid covering `[-1/2, 1/2]`.  Near height `v` a fan is squeezed into
a bowtie of width proportional to `|y - v|`, so `P'` admits a thin cover by a staircase
of rectangles. -/

/-- The parametrisation of `segment01 x₁ x₂` by height. -/
lemma segment01_eq_image (x₁ x₂ : ℝ) :
    segment01 x₁ x₂ = (fun y : ℝ ↦ ![x₁ + y * (x₂ - x₁), y]) '' Icc (0 : ℝ) 1 := by
  rw [segment01, segment_eq_image']
  ext p
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨θ, hθ, ?_⟩
    ext i
    fin_cases i <;> simp
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext i
    fin_cases i <;> simp

/-- The fan pivoting at `(c, v)` with slopes `t ∈ [s - ρ, s + ρ]`: the union of the
segments `segment01 (c - v * t) (c + (1 - v) * t)`, each of which passes through
`(c, v)` with slope `t`. -/
def fan (c s ρ v : ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ t ∈ Icc (s - ρ) (s + ρ), segment01 (c - v * t) (c + (1 - v) * t)

/-- Membership in a fan, in coordinates. -/
lemma mem_fan {c s ρ v : ℝ} {p : Fin 2 → ℝ} :
    p ∈ fan c s ρ v ↔
      ∃ t ∈ Icc (s - ρ) (s + ρ), ∃ y ∈ Icc (0 : ℝ) 1, p = ![c + (y - v) * t, y] := by
  simp only [fan, mem_iUnion, segment01_eq_image, mem_image]
  constructor
  · rintro ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, y, hy, ?_⟩
    congr 1
    ring
  · rintro ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, y, hy, ?_⟩
    congr 1
    ring

/-- Fans are compact. -/
lemma isCompact_fan (c s ρ v : ℝ) : IsCompact (fan c s ρ v) := by
  have himage : fan c s ρ v =
      (fun q : ℝ × ℝ ↦ ![c + (q.2 - v) * q.1, q.2]) ''
        (Icc (s - ρ) (s + ρ) ×ˢ Icc (0 : ℝ) 1) := by
    ext p
    rw [mem_fan]
    constructor
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨(t, y), ⟨ht, hy⟩, rfl⟩
    · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
      exact ⟨t, ht, y, hy, rfl⟩
  rw [himage]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  refine continuous_pi ?_
  intro i
  fin_cases i
  · simpa using ((continuous_snd.sub continuous_const).mul continuous_fst).const_add c
  · simpa using continuous_snd

/-- For every `P ∈ 𝒫'` and `δ > 0` there is a finite family of segments contained in `P`
(with endpoint abscissae in `[-1, 1]`) forming a `δ`-net for `P`. -/
theorem exists_segment_net (P : kornerCompacts) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset (ℝ × ℝ),
      (∀ q ∈ s, q.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2 ∈ Icc (-1 : ℝ) 1 ∧
        segment01 q.1 q.2 ⊆ (P : Set (Fin 2 → ℝ))) ∧
      (∀ p ∈ (P : Set (Fin 2 → ℝ)), ∃ q ∈ s, ∃ p' ∈ segment01 q.1 q.2, dist p p' ≤ δ) := by
  obtain ⟨-, -, ⟨A, hA, hPA⟩, -⟩ := P.2
  -- `P` is compact, so it admits a finite `δ`-net `t` of centres lying in `P`.
  obtain ⟨t, htP, htfin, htcover⟩ :=
    (P : NonemptyCompacts (Fin 2 → ℝ)).isCompact.finite_cover_balls hδ
  lift t to Finset (Fin 2 → ℝ) using htfin
  -- Each centre lies on one of the segments constituting `P`; choose one for each.
  have hchoice : ∀ x ∈ t, ∃ p, p ∈ A ∧ x ∈ segment01 (p 0) (p 1) := by
    intro x hx
    have hxP : x ∈ (P : Set (Fin 2 → ℝ)) := htP hx
    rw [hPA] at hxP
    simpa using hxP
  choose f hfA hfx using hchoice
  refine ⟨t.attach.image fun x ↦ (f x.1 x.2 0, f x.1 x.2 1), ?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hp := hA (hfA x hx)
    rw [mem_Icc, Pi.le_def, Pi.le_def] at hp
    refine ⟨⟨by simpa using hp.1 0, by simpa using hp.2 0⟩,
      ⟨by simpa using hp.1 1, by simpa using hp.2 1⟩, ?_⟩
    rw [hPA]
    exact subset_biUnion_of_mem (u := fun p ↦ segment01 (p 0) (p 1)) (hfA x hx)
  · intro p hp
    obtain ⟨x, hxt, hdist⟩ := mem_iUnion₂.1 (htcover hp)
    have hxt' : x ∈ t := hxt
    exact ⟨(f x hxt' 0, f x hxt' 1),
      Finset.mem_image.2 ⟨⟨x, hxt'⟩, Finset.mem_attach _ _, rfl⟩,
      x, hfx x hxt', (mem_ball.1 hdist).le⟩

/-- The horizontal sub-bands `(v - ε + h j - σ, v - ε + h (j+1) + σ)`, `j : Fin K`, that
contain a fixed height `y` are at most two, provided the overlap `σ` is small (`2σ ≤ h`).
This is the counting heart of the staircase estimate. -/
lemma staircase_band_card_le {K : ℕ} {h σ v ε y : ℝ} (hh0 : 0 < h) (hσh : 2 * σ ≤ h)
    (F : Finset (Fin K))
    (hF : F = Finset.univ.filter
      (fun j : Fin K ↦ y ∈ Ioo (v - ε + h * (j : ℝ) - σ) (v - ε + h * ((j : ℝ) + 1) + σ))) :
    F.card ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty F with hFe | hFne
  · simp [hFe]
  · have hmem : ∀ j ∈ F,
        v - ε + h * (j : ℝ) - σ < y ∧ y < v - ε + h * ((j : ℝ) + 1) + σ := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      exact hj.2
    have hpair : ∀ j ∈ F, ∀ j' ∈ F, (j : ℕ) ≤ (j' : ℕ) + 1 := by
      intro j hj j' hj'
      have h1 := (hmem j hj).1
      have h2 := (hmem j' hj').2
      have hlt : h * (j : ℝ) < h * ((j' : ℝ) + 1) + 2 * σ := by linarith
      have hjj' : (j : ℝ) < (j' : ℝ) + 2 := by nlinarith
      have : ((j : ℕ) : ℝ) < ((j' : ℕ) : ℝ) + 2 := by exact_mod_cast hjj'
      have : (j : ℕ) < (j' : ℕ) + 2 := by exact_mod_cast this
      omega
    have hne : (F.image Fin.val).Nonempty := hFne.image _
    set m := (F.image Fin.val).min' hne with hm
    clear_value m
    obtain ⟨jm, hjm, hjmv⟩ := Finset.mem_image.1 ((F.image Fin.val).min'_mem hne)
    have himg : F.image Fin.val ⊆ Finset.Icc m (m + 1) := by
      intro nn hnn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hnn
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · rw [hm]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)
      · rw [hm, ← hjmv]
        exact hpair j hj jm hjm
    calc F.card = (F.image Fin.val).card :=
          (Finset.card_image_of_injective F Fin.val_injective).symm
      _ ≤ (Finset.Icc m (m + 1)).card := Finset.card_le_card himg
      _ ≤ 2 := by rw [Nat.card_Icc]; omega

/-- Given a height `y` in the band `|y - v| ≤ ε`, the clamped floor index
`n = min ⌊(y - (v-ε))/h⌋ (K-1)` locates the sub-band of height `h = 2ε/K` containing `y`. -/
lemma staircase_mem_band {K : ℕ} (hK : 0 < K) {h v ε y : ℝ} (hh0 : 0 < h)
    (hKh : (K : ℝ) * h = 2 * ε) (hy : |y - v| ≤ ε) :
    let n := min ⌊(y - (v - ε)) / h⌋₊ (K - 1)
    n < K ∧ v - ε + h * (n : ℝ) ≤ y ∧ y ≤ v - ε + h * ((n : ℝ) + 1) := by
  intro n
  have habs := abs_le.1 hy
  have hz0 : 0 ≤ (y - (v - ε)) / h := div_nonneg (by linarith [habs.1]) hh0.le
  have hzK : y - (v - ε) ≤ (K : ℝ) * h := by rw [hKh]; linarith [habs.2]
  have hfl1 : (⌊(y - (v - ε)) / h⌋₊ : ℝ) * h ≤ y - (v - ε) := by
    have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le hz0) hh0.le
    rwa [div_mul_cancel₀ _ hh0.ne'] at h1
  have hfl2 : y - (v - ε) < ((⌊(y - (v - ε)) / h⌋₊ : ℝ) + 1) * h := by
    have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one ((y - (v - ε)) / h)) hh0
    rwa [div_mul_cancel₀ _ hh0.ne'] at h2
  have hnK : n < K := by
    have : n ≤ K - 1 := min_le_right _ _
    omega
  refine ⟨hnK, ?_⟩
  rcases le_or_gt ⌊(y - (v - ε)) / h⌋₊ (K - 1) with hc | hc
  · have hne : (n : ℝ) = (⌊(y - (v - ε)) / h⌋₊ : ℝ) := by
      simp only [n, min_eq_left hc]
    rw [hne]
    constructor <;> nlinarith
  · have hge : (K : ℝ) ≤ (⌊(y - (v - ε)) / h⌋₊ : ℝ) := by
      have : K ≤ ⌊(y - (v - ε)) / h⌋₊ := by omega
      exact_mod_cast this
    have hyt : (K : ℝ) * h ≤ y - (v - ε) := by nlinarith
    have hcast : (n : ℝ) = (K : ℝ) - 1 := by
      have hne : n = K - 1 := min_eq_right (by omega)
      rw [hne]
      push_cast [Nat.cast_sub hK]
      ring
    rw [hcast]
    constructor <;> nlinarith

/-- **Staircase covering of a fan near its pivot height.**  The part of `fan c s ρ v` lying
in the band `|y - v| ≤ ε` can be covered by `K` open rectangles, one for each horizontal
sub-band of height `2ε/K`, in such a way that at any height the rectangles present have
total width at most `6 * (2ε/K + ε ρ + σ)`. -/
theorem exists_staircase_fan (c s ρ v ε : ℝ) (K : ℕ) {σ : ℝ}
    (hρ : 0 ≤ ρ) (hs : |s| + ρ ≤ 2) (hε : 0 < ε) (hK : 0 < K)
    (hσ : 0 < σ) (hσK : σ ≤ ε / K) :
    ∃ a b cc dd : Fin K → ℝ,
      (∀ j, a j ≤ b j) ∧
      (∀ p ∈ fan c s ρ v, |p 1 - v| ≤ ε → ∃ j, p ∈ openRect (a j) (b j) (cc j) (dd j)) ∧
      (∀ y : ℝ, ∑ j, (Ioo (cc j) (dd j)).indicator (fun _ ↦ b j - a j) y
          ≤ 6 * (2 * ε / K + ε * ρ + σ)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set h : ℝ := 2 * ε / K with hh
  have hh0 : 0 < h := by rw [hh]; positivity
  have hKh : (K : ℝ) * h = 2 * ε := by
    rw [hh]
    field_simp
  have hσh : 2 * σ ≤ h := by
    have h1 : ε / K = h / 2 := by rw [hh]; ring
    linarith [hσK.trans_eq h1]
  clear_value h
  set w : ℝ := 2 * ε / K + ε * ρ + σ with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  clear_value w
  -- centre of the `j`-th horizontal strip and of the corresponding rectangle
  set μ : Fin K → ℝ := fun j ↦ v - ε + ((j : ℝ) + 1 / 2) * h with hμ
  set γ : Fin K → ℝ := fun j ↦ c + (μ j - v) * s with hγ
  have hμv : ∀ j : Fin K, |μ j - v| ≤ ε := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast j.2
    simp only [hμ]
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨fun j ↦ γ j - w, fun j ↦ γ j + w,
    fun j ↦ v - ε + h * (j : ℝ) - σ, fun j ↦ v - ε + h * ((j : ℝ) + 1) + σ, ?_, ?_, ?_⟩
  · intro j
    linarith
  · -- the covering property
    rintro p hp hp1
    rw [mem_fan] at hp
    obtain ⟨t, ht, y, hy, rfl⟩ := hp
    have hy1 : (![c + (y - v) * t, y] : Fin 2 → ℝ) 1 = y := by simp
    rw [hy1] at hp1
    have ht' : |t - s| ≤ ρ := by
      rw [mem_Icc] at ht
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have htabs : |t| ≤ 2 := by
      calc |t| = |s + (t - s)| := by ring_nf
        _ ≤ |s| + |t - s| := abs_add_le _ _
        _ ≤ 2 := by linarith
    -- locate the sub-band containing `y`
    obtain ⟨hnK, hband⟩ := staircase_mem_band hK hh0 hKh hp1
    set n : ℕ := min ⌊(y - (v - ε)) / h⌋₊ (K - 1) with hn
    clear_value n
    have hyn : |y - μ ⟨n, hnK⟩| ≤ ε / K := by
      have hεK : ε / K = h / 2 := by rw [hh]; ring
      have hμn : μ ⟨n, hnK⟩ = v - ε + ((n : ℝ) + 1 / 2) * h := by simp [hμ]
      rw [hμn, hεK, abs_le]
      constructor <;> nlinarith [hband.1, hband.2]
    refine ⟨⟨n, hnK⟩, ?_, ?_⟩
    · -- horizontal membership
      have hx : (![c + (y - v) * t, y] : Fin 2 → ℝ) 0 = c + (y - v) * t := by simp
      have hkey : |(c + (y - v) * t) - γ ⟨n, hnK⟩| < w := by
        have hexp : (c + (y - v) * t) - γ ⟨n, hnK⟩
            = (y - μ ⟨n, hnK⟩) * t + (μ ⟨n, hnK⟩ - v) * (t - s) := by
          simp only [hγ]
          ring
        rw [hexp]
        calc |(y - μ ⟨n, hnK⟩) * t + (μ ⟨n, hnK⟩ - v) * (t - s)|
            ≤ |(y - μ ⟨n, hnK⟩) * t| + |(μ ⟨n, hnK⟩ - v) * (t - s)| := abs_add_le _ _
          _ = |y - μ ⟨n, hnK⟩| * |t| + |μ ⟨n, hnK⟩ - v| * |t - s| := by
              rw [abs_mul, abs_mul]
          _ ≤ (ε / K) * 2 + ε * ρ := by
              have h1 : |y - μ ⟨n, hnK⟩| * |t| ≤ (ε / K) * 2 :=
                mul_le_mul hyn htabs (abs_nonneg _) (by positivity)
              have h2 : |μ ⟨n, hnK⟩ - v| * |t - s| ≤ ε * ρ :=
                mul_le_mul (hμv _) ht' (abs_nonneg _) hε.le
              linarith
          _ < w := by
              have h3 : (ε / K) * 2 = 2 * ε / K := by ring
              rw [hw, h3]
              linarith
      rw [abs_lt] at hkey
      exact ⟨by rw [hx]; linarith [hkey.1], by rw [hx]; linarith [hkey.2]⟩
    · -- vertical membership
      rw [hy1]
      exact ⟨by linarith [hband.1], by linarith [hband.2]⟩
  · -- thinness: at any height at most two rectangles are present
    intro y
    classical
    rw [Finset.sum_indicator_eq_sum_filter]
    set F := Finset.univ.filter
      (fun j : Fin K ↦ y ∈ Ioo (v - ε + h * (j : ℝ) - σ) (v - ε + h * ((j : ℝ) + 1) + σ)) with hF
    have hcard : F.card ≤ 2 := staircase_band_card_le hh0 hσh F hF
    clear_value F
    have hterm : ∀ j ∈ F, (γ j + w) - (γ j - w) = 2 * w := fun j _ ↦ by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard' : (F.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    rw [hw]
    nlinarith

/-- The first-coordinate estimate behind the `3η`-closeness of fan points to `P`:
if the anchor slope `s'` and shrink factor satisfy `σ' = (1-η) s'`, `|x₁| ≤ 1`, `|s'| ≤ 1/2`,
`|t - σ'| ≤ η`, `|y - v| ≤ 1`, `0 ≤ v ≤ 1`, then the horizontal displacement is at most `3η`. -/
lemma fan_anchor_horizontal_bound {η v x₁ s' t y σ' : ℝ} (hη : 0 < η)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hx₁ : |x₁| ≤ 1) (hs'half : |s'| ≤ 1/2)
    (hσs' : σ' = (1 - η) * s') (htσ : |t - σ'| ≤ η) (hyv : |y - v| ≤ 1) :
    |(1 - η) * x₁ + v * σ' + (y - v) * t - (x₁ + y * s')| ≤ 3 * η := by
  have hexp : (1 - η) * x₁ + v * σ' + (y - v) * t - (x₁ + y * s')
      = -(η * x₁) + (y - v) * (t - s') - v * η * s' := by
    rw [hσs']; ring
  rw [hexp]
  have hts' : |t - s'| ≤ 3 * η / 2 := by
    have h1 : |σ' - s'| = η * |s'| := by
      rw [hσs', show (1 - η) * s' - s' = -(η * s') by ring, abs_neg, abs_mul, abs_of_pos hη]
    have h2 : |t - s'| ≤ |t - σ'| + |σ' - s'| := by
      calc |t - s'| = |(t - σ') + (σ' - s')| := by congr 1; ring
        _ ≤ |t - σ'| + |σ' - s'| := abs_add_le _ _
    rw [h1] at h2
    nlinarith [abs_nonneg s']
  have htri : |(-(η * x₁) + (y - v) * (t - s') - v * η * s')|
      ≤ |η * x₁| + |(y - v) * (t - s')| + |v * η * s'| := by
    calc |(-(η * x₁) + (y - v) * (t - s') - v * η * s')|
        = |(-(η * x₁)) + ((y - v) * (t - s') + (-(v * η * s')))| := by congr 1; ring
      _ ≤ |(-(η * x₁))| + |(y - v) * (t - s') + (-(v * η * s'))| := abs_add_le _ _
      _ ≤ |(-(η * x₁))| + (|(y - v) * (t - s')| + |(-(v * η * s'))|) := by
          linarith [abs_add_le ((y - v) * (t - s')) (-(v * η * s'))]
      _ = |η * x₁| + |(y - v) * (t - s')| + |v * η * s'| := by rw [abs_neg, abs_neg]; ring
  have e1 : |η * x₁| ≤ η := by
    rw [abs_mul, abs_of_pos hη]
    nlinarith [abs_nonneg x₁]
  have e2 : |(y - v) * (t - s')| ≤ 3 * η / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (y - v), abs_nonneg (t - s')]
  have e3 : |v * η * s'| ≤ η / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hv₀, abs_of_pos hη]
    have h1 : v * η * |s'| ≤ 1 * η * (1/2) :=
      mul_le_mul (mul_le_mul hv₁ le_rfl hη.le zero_le_one) hs'half (abs_nonneg s') (by positivity)
    linarith
  linarith

/-- **Grid covering.**  The `M` midpoints `σ' m = -1/2 + (m + 1/2)/M` of the equal
subdivisions of `[-1/2, 1/2]` approximate every `w ∈ [-1/2, 1/2]` to within `1/(2M)`,
via the clamped floor index. -/
lemma exists_grid_point_dist_le {M : ℕ} (hM0 : 0 < M) {w : ℝ} (hw : |w| ≤ 1 / 2) :
    ∃ n : Fin M, |w - (-(1/2) + ((n : ℝ) + 1/2) / M)| ≤ 1 / (2 * (M : ℝ)) := by
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hw' := abs_le.1 hw
  have hz0 : 0 ≤ (w + 1/2) * M := by nlinarith
  have hzM : (w + 1/2) * M ≤ M := by nlinarith
  set n : ℕ := min ⌊(w + 1/2) * M⌋₊ (M - 1) with hn
  have hnM : n < M := by
    have : n ≤ M - 1 := min_le_right _ _
    omega
  have hfl1 : (⌊(w + 1/2) * M⌋₊ : ℝ) ≤ (w + 1/2) * M := Nat.floor_le hz0
  have hfl2 : (w + 1/2) * M < (⌊(w + 1/2) * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨⟨n, hnM⟩, ?_⟩
  have hval : (((⟨n, hnM⟩ : Fin M) : ℝ)) = (n : ℝ) := rfl
  rw [hval]
  rcases le_or_gt ⌊(w + 1/2) * M⌋₊ (M - 1) with hc | hc
  · have hne : (n : ℝ) = (⌊(w + 1/2) * M⌋₊ : ℝ) := by rw [hn, min_eq_left hc]
    have hexp : w - (-(1/2) + ((n : ℝ) + 1/2) / M)
        = ((w + 1/2) * M - ((⌊(w + 1/2) * M⌋₊ : ℝ) + 1/2)) / M := by
      rw [hne]
      field_simp
      ring
    rw [hexp, abs_div, abs_of_pos hM0',
      div_le_div_iff₀ hM0' (by positivity : (0:ℝ) < 2 * M)]
    have hnum : |(w + 1/2) * M - ((⌊(w + 1/2) * M⌋₊ : ℝ) + 1/2)| ≤ 1/2 := by
      rw [abs_le]
      constructor <;> nlinarith
    nlinarith
  · have hge : (M : ℝ) ≤ (⌊(w + 1/2) * M⌋₊ : ℝ) := by
      have : M ≤ ⌊(w + 1/2) * M⌋₊ := by omega
      exact_mod_cast this
    have hwM : (w + 1/2) * M = M := le_antisymm hzM (by nlinarith)
    have hw12 : w = 1/2 := by
      have hcancel : (w + 1/2) * M = 1 * M := by rw [hwM, one_mul]
      have := mul_right_cancel₀ hM0'.ne' hcancel
      linarith
    have hcast : (n : ℝ) = (M : ℝ) - 1 := by
      have hne : n = M - 1 := min_eq_right (by omega)
      rw [hne]
      push_cast [Nat.cast_sub hM0]
      ring
    have hexp : w - (-(1/2) + ((n : ℝ) + 1/2) / M) = (1/2) / M := by
      rw [hcast, hw12]
      field_simp
      ring
    rw [hexp, abs_of_nonneg (by positivity),
      div_le_div_iff₀ hM0' (by positivity : (0:ℝ) < 2 * M)]
    nlinarith

/-- **Fan anchors.**  Given `P ∈ 𝒫` and `0 < η ≤ 1/2`, there are finitely many fans, each
pivoting at height `v` around (a slightly shrunk copy of) a segment of `P`, whose slope
ranges cover `[-1/2, 1/2]`, whose segments stay inside the ambient rectangle, and whose
points all lie within `3η` of `P`.  Moreover the number of fans satisfies `M * η ≤ 1`. -/
theorem exists_fan_anchors (P : kornerCompacts) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/2)
    (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ∃ (M : ℕ) (c s : Fin M → ℝ),
      (∀ m, |s m| + η ≤ 1) ∧
      (∀ m, ∀ t ∈ Icc (s m - η) (s m + η),
        (c m - v * t) ∈ Icc (-1 : ℝ) 1 ∧ (c m + (1 - v) * t) ∈ Icc (-1 : ℝ) 1) ∧
      (∀ m, ∀ p ∈ fan (c m) (s m) η v, ∃ p' ∈ (P : Set (Fin 2 → ℝ)), dist p p' ≤ 3 * η) ∧
      (∀ w : ℝ, |w| ≤ (1/2 : ℝ) → ∃ m, w ∈ Icc (s m - η) (s m + η)) ∧
      ((M : ℝ) * η ≤ 1) := by
  have hη1 : η < 1 := lt_of_le_of_lt hη' (by norm_num)
  have h1η : 0 < 1 - η := by linarith
  -- the number of fans
  set M : ℕ := ⌈1 / (2 * η)⌉₊ with hM
  have hM0 : 0 < M := by rw [hM]; exact Nat.ceil_pos.2 (by positivity)
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hM1 : 1 / (2 * η) ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil _
  have hM2 : (M : ℝ) < 1 / (2 * η) + 1 := by rw [hM]; exact Nat.ceil_lt_add_one (by positivity)
  clear_value M
  have hinv : 1 / (2 * η) * η = 1 / 2 := by
    field_simp
  have hMη : (M : ℝ) * η ≤ 1 := by nlinarith
  have hMη' : 1 / (2 * (M : ℝ)) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηM : η / 2 ≤ 1 / (2 * (M : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  -- the grid of slopes
  set σ' : Fin M → ℝ := fun m ↦ -(1/2) + ((m : ℝ) + 1/2) / M with hσ'
  clear_value σ'
  have hσ'abs : ∀ m : Fin M, |σ' m| ≤ 1/2 - 1 / (2 * (M : ℝ)) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1 : (m : ℝ) + 1 ≤ M := by exact_mod_cast m.2
    have hlo : 1 / (2 * (M : ℝ)) ≤ ((m : ℝ) + 1/2) / M := by
      rw [div_le_div_iff₀ (by positivity) hM0']
      nlinarith
    have hhi : ((m : ℝ) + 1/2) / M ≤ 1 - 1 / (2 * (M : ℝ)) := by
      rw [div_le_iff₀ hM0']
      have hexp : (1 - 1 / (2 * (M : ℝ))) * M = M - 1/2 := by
        field_simp
      rw [hexp]
      linarith
    simp only [hσ']
    rw [abs_le]
    constructor <;> linarith
  have hσ'half : ∀ m : Fin M, |σ' m| ≤ (1 - η) / 2 := by
    intro m
    have h1 := hσ'abs m
    have h2 := hηM
    linarith
  -- anchor segments of `P` for each grid slope
  have hanchor : ∀ m : Fin M, ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧
      x₂ - x₁ = σ' m / (1 - η) ∧ segment01 x₁ x₂ ⊆ (P : Set (Fin 2 → ℝ)) := by
    intro m
    apply P.2.2.2.2
    rw [abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
    have := hσ'half m
    nlinarith
  choose x₁ x₂ hx₁ hx₂ hslope hseg using hanchor
  have hx2eq : ∀ m, (1 - η) * x₂ m = (1 - η) * x₁ m + σ' m := by
    intro m
    have h := hslope m
    rw [eq_div_iff h1η.ne'] at h
    nlinarith [h]
  refine ⟨M, fun m ↦ (1 - η) * x₁ m + v * σ' m, σ', ?_, ?_, ?_, ?_, hMη⟩
  · -- slopes bounded away from 1
    intro m
    have := hσ'half m
    linarith
  · -- fan segments stay in the ambient rectangle
    intro m t ht
    rw [mem_Icc] at ht
    have htσ : |t - σ' m| ≤ η := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    constructor
    · have hexp : (1 - η) * x₁ m + v * σ' m - v * t = (1 - η) * x₁ m + v * (σ' m - t) := by
        ring
      rw [hexp, mem_Icc]
      have h1 : |(1 - η) * x₁ m| ≤ 1 - η := by
        rw [abs_mul, abs_of_pos h1η]
        nlinarith [abs_le.2 ⟨(hx₁ m).1, (hx₁ m).2⟩, abs_nonneg (x₁ m)]
      have h2 : |v * (σ' m - t)| ≤ η := by
        rw [abs_mul, abs_of_nonneg hv₀, abs_sub_comm]
        nlinarith [abs_nonneg (t - σ' m)]
      constructor <;> nlinarith [abs_le.1 h1, abs_le.1 h2]
    · have hexp : (1 - η) * x₁ m + v * σ' m + (1 - v) * t
          = (1 - η) * x₂ m + (1 - v) * (t - σ' m) := by
        rw [hx2eq]
        ring
      rw [hexp, mem_Icc]
      have h1 : |(1 - η) * x₂ m| ≤ 1 - η := by
        rw [abs_mul, abs_of_pos h1η]
        nlinarith [abs_le.2 ⟨(hx₂ m).1, (hx₂ m).2⟩, abs_nonneg (x₂ m)]
      have h2 : |(1 - v) * (t - σ' m)| ≤ η := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - v)]
        nlinarith [abs_nonneg (t - σ' m)]
      constructor <;> nlinarith [abs_le.1 h1, abs_le.1 h2]
  · -- fan points lie within `3η` of `P`
    intro m p hp
    rw [mem_fan] at hp
    obtain ⟨t, ht, y, hy, rfl⟩ := hp
    rw [mem_Icc] at ht hy
    have htσ : |t - σ' m| ≤ η := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    set s' : ℝ := σ' m / (1 - η) with hs'
    clear_value s'
    have hs'half : |s'| ≤ 1/2 := by
      rw [hs', abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
      have := hσ'half m
      nlinarith
    have hσs' : σ' m = (1 - η) * s' := by
      rw [hs']
      field_simp
    refine ⟨![x₁ m + y * s', y], ?_, ?_⟩
    · apply hseg m
      rw [segment01_eq_image]
      refine ⟨y, mem_Icc.2 hy, ?_⟩
      rw [hslope m, ← hs']
    · -- coordinatewise distance bound
      have hyv : |y - v| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      have hx₁abs : |x₁ m| ≤ 1 := abs_le.2 ⟨(hx₁ m).1, (hx₁ m).2⟩
      rw [dist_pi_le_iff (by positivity)]
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        rw [Real.dist_eq]
        exact fan_anchor_horizontal_bound hη hv₀ hv₁ hx₁abs hs'half hσs' htσ hyv
      · simp only [Fin.mk_one, Matrix.cons_val_one]
        rw [dist_self]
        positivity
  · -- the slope ranges cover `[-1/2, 1/2]`
    intro w hw
    obtain ⟨n, hn⟩ := exists_grid_point_dist_le hM0 hw
    have hσn : σ' n = -(1/2) + ((n : ℝ) + 1/2) / M := by simp [hσ']
    rw [← hσn] at hn
    refine ⟨n, ?_⟩
    rw [mem_Icc]
    have hk := abs_le.1 hn
    constructor <;> nlinarith [hMη', hk.1, hk.2]

/-- Every `segment01` is a degenerate fan (with zero opening angle), pivoting at height `v`. -/
lemma segment01_eq_fan (x₁ x₂ v : ℝ) :
    segment01 x₁ x₂ = fan (x₁ + v * (x₂ - x₁)) (x₂ - x₁) 0 v := by
  rw [fan, sub_zero, add_zero, Icc_self]
  simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
  rw [show x₁ + v * (x₂ - x₁) - v * (x₂ - x₁) = x₁ by ring,
    show x₁ + v * (x₂ - x₁) + (1 - v) * (x₂ - x₁) = x₂ by ring]

/-- Segments with endpoint abscissae in `[-1,1]` lie in the ambient rectangle. -/
lemma segment01_subset_rectangle {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Icc (-1 : ℝ) 1)
    (h₂ : x₂ ∈ Icc (-1 : ℝ) 1) :
    segment01 x₁ x₂ ⊆ rectangle := by
  obtain ⟨hL, hR⟩ := endpoints_mem_rectangle h₁ h₂
  intro p hp
  exact convex_rectangle.segment_subset hL hR hp

/-- Points of the parameter square, from coordinatewise bounds. -/
lemma pair_mem_Icc {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (![a, b] : Fin 2 → ℝ) ∈ Icc ![-1, -1] ![1, 1] := by
  rw [mem_Icc] at ha hb ⊢
  refine ⟨?_, ?_⟩ <;> rw [Pi.le_def] <;> intro i <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    linarith [ha.1, ha.2, hb.1, hb.2]

/-- Thin covers of finitely many pieces combine into a thin cover of their union,
provided the total of the individual width bounds is less than `100 ε`. -/
lemma hasThinCover_iUnion {ι : Type*} [Fintype ι] {S : ι → Set (Fin 2 → ℝ)} {v ε : ℝ}
    (B : ι → ℝ)
    (h : ∀ i, ∃ (K : ℕ) (a b c d : Fin K → ℝ),
      (∀ j, a j ≤ b j) ∧
      (∀ p ∈ S i, |p 1 - v| ≤ ε → ∃ j, p ∈ openRect (a j) (b j) (c j) (d j)) ∧
      (∀ y : ℝ, ∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) y ≤ B i))
    (hB : ∑ i, B i < 100 * ε) :
    HasThinCover (⋃ i, S i) v ε := by
  choose K a b c d hab hcov hthin using h
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ((i : ι) × Fin (K i))) ≃ (i : ι) × Fin (K i)) :=
    ⟨(Fintype.equivFin _).symm⟩
  refine ⟨Fintype.card ((i : ι) × Fin (K i)),
    fun j ↦ a (e j).1 (e j).2, fun j ↦ b (e j).1 (e j).2,
    fun j ↦ c (e j).1 (e j).2, fun j ↦ d (e j).1 (e j).2,
    fun j ↦ hab _ _, ?_, ?_⟩
  · intro p hp hpv
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj⟩ := hcov i p hi hpv
    obtain ⟨j', hj'⟩ : ∃ j', e j' = ⟨i, j⟩ := ⟨e.symm ⟨i, j⟩, e.apply_symm_apply _⟩
    refine ⟨j', ?_⟩
    beta_reduce
    rw [hj']
    exact hj
  · intro y _
    have hsum : (∑ j, (Ioo (c (e j).1 (e j).2) (d (e j).1 (e j).2)).indicator
          (fun _ ↦ b (e j).1 (e j).2 - a (e j).1 (e j).2) y)
        = ∑ q : (i : ι) × Fin (K i),
            (Ioo (c q.1 q.2) (d q.1 q.2)).indicator (fun _ ↦ b q.1 q.2 - a q.1 q.2) y :=
      Fintype.sum_equiv e _ _ fun j ↦ rfl
    rw [hsum, Fintype.sum_sigma]
    calc (∑ i, ∑ j, (Ioo (c i j) (d i j)).indicator (fun _ ↦ b i j - a i j) y)
        ≤ ∑ i, B i := Finset.sum_le_sum fun i _ ↦ hthin i y
      _ < 100 * ε := hB

/-- The approximant `Q = (⋃ fans) ∪ (net segments)` admits a thin cover at `(v, ε)`:
each fan and each net segment (a degenerate fan) is covered by an `N`-step staircase with
`N = 24(M + #nt) + 1`, and the widths sum to `< 100 ε`. -/
lemma hasThinCover_fans_union_net {M : ℕ} {cM sM : Fin M → ℝ} {η v ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hMη : (M : ℝ) * η ≤ 1)
    (hs1 : ∀ m, |sM m| + η ≤ 1) (nt : Finset (ℝ × ℝ))
    (hntP : ∀ q ∈ nt, q.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2 ∈ Icc (-1 : ℝ) 1 ∧
      segment01 q.1 q.2 ⊆ (⋃ m : Fin M, fan (cM m) (sM m) η v) ∪ (⋃ q ∈ nt, segment01 q.1 q.2)) :
    HasThinCover ((⋃ m : Fin M, fan (cM m) (sM m) η v) ∪ (⋃ q ∈ nt, segment01 q.1 q.2)) v ε := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 24 * (M + nt.card) + 1 := ⟨_, rfl⟩
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hσ0 : 0 < ε / N := by positivity
  have hQU : (⋃ m : Fin M, fan (cM m) (sM m) η v) ∪ (⋃ q ∈ nt, segment01 q.1 q.2)
      = ⋃ i : Fin M ⊕ {q : ℝ × ℝ // q ∈ nt},
        Sum.elim (fun m ↦ fan (cM m) (sM m) η v)
          (fun q ↦ segment01 q.1.1 q.1.2) i := by
    rw [iUnion_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    exact (iUnion_subtype (fun q ↦ q ∈ nt)
      (fun q : {q : ℝ × ℝ // q ∈ nt} ↦ segment01 q.1.1 q.1.2)).symm
  rw [hQU]
  refine hasThinCover_iUnion
    (Sum.elim (fun _ ↦ 6 * (2 * ε / N + ε * η + ε / N))
      (fun _ ↦ 6 * (2 * ε / N + ε * 0 + ε / N))) ?_ ?_
  · rintro (m | q)
    · refine ⟨N, ?_⟩
      exact exists_staircase_fan (cM m) (sM m) η v ε N (σ := ε / N) hη.le
        (by linarith [hs1 m]) hε hN0 hσ0 le_rfl
    · have hq1 := (hntP q.1 q.2).1
      have hq2 := (hntP q.1 q.2).2.1
      rw [mem_Icc] at hq1 hq2
      have hs2 : |q.1.2 - q.1.1| + 0 ≤ 2 := by
        rw [add_zero, abs_le]
        constructor <;> linarith
      obtain ⟨a, b, cc, dd, h1, h2, h3⟩ :=
        exists_staircase_fan (q.1.1 + v * (q.1.2 - q.1.1)) (q.1.2 - q.1.1) 0 v ε N
          (σ := ε / N) le_rfl hs2 hε hN0 hσ0 le_rfl
      refine ⟨N, a, b, cc, dd, h1, ?_, h3⟩
      intro p hp hpv
      rw [Sum.elim_inr, segment01_eq_fan q.1.1 q.1.2 v] at hp
      exact h2 p hp hpv
  · -- the numeric bound
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
    have hNval : (N : ℝ) = 24 * ((M : ℝ) + nt.card) + 1 := by
      rw [hN]; push_cast; ring
    have hMc0 : (0 : ℝ) ≤ (M : ℝ) + nt.card := by positivity
    have h18 : 18 * ((M : ℝ) + nt.card) < N := by rw [hNval]; linarith
    have hX : 18 * ((M : ℝ) + nt.card) * (ε / N) < ε := by
      have h1 : 18 * ((M : ℝ) + nt.card) * (ε / N) < (N : ℝ) * (ε / N) :=
        mul_lt_mul_of_pos_right h18 hσ0
      rwa [mul_div_cancel₀ _ hNR.ne'] at h1
    have h6 : 6 * ε * ((M : ℝ) * η) ≤ 6 * ε := by nlinarith [hMη, hε]
    have hexp : (M : ℝ) * (6 * (2 * ε / N + ε * η + ε / N))
          + (nt.card : ℝ) * (6 * (2 * ε / N + ε * 0 + ε / N))
        = 18 * ((M : ℝ) + nt.card) * (ε / N) + 6 * ε * ((M : ℝ) * η) := by ring
    rw [hexp]
    linarith [hX, h6, hε]

theorem dense_thinCoverSet {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (thinCoverSet v ε) := by
  rw [Metric.dense_iff]
  intro P δ hδ
  -- parameters
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min (δ / 4) (1 / 2) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hη_def]
    exact lt_min (by positivity) (by norm_num)
  have hη' : η ≤ 1 / 2 := hη_def.trans_le (min_le_right _ _)
  have hηδ : η ≤ δ / 4 := hη_def.trans_le (min_le_left _ _)
  -- the fans and the net
  obtain ⟨M, cM, sM, hs1, hends, hnear, hcovs, hMη⟩ := exists_fan_anchors P hη hη' v hv₀ hv₁
  obtain ⟨nt, hntP, hntnet⟩ := exists_segment_net P (show (0:ℝ) < δ / 2 by positivity)
  -- the approximating set
  obtain ⟨Q, hQ⟩ : ∃ Q : Set (Fin 2 → ℝ),
      Q = (⋃ m : Fin M, fan (cM m) (sM m) η v) ∪ (⋃ q ∈ nt, segment01 q.1 q.2) := ⟨_, rfl⟩
  have hfan_sub : ∀ m : Fin M, fan (cM m) (sM m) η v ⊆ Q := by
    intro m
    rw [hQ]
    exact (subset_iUnion (fun m ↦ fan (cM m) (sM m) η v) m).trans subset_union_left
  have hseg_sub : ∀ q ∈ nt, segment01 q.1 q.2 ⊆ Q := by
    intro q hq y hy
    rw [hQ]
    exact Or.inr (mem_iUnion₂.2 ⟨q, hq, hy⟩)
  -- `Q` is nonempty
  obtain ⟨m₀, -⟩ := hcovs 0 (by norm_num)
  have hQne : Q.Nonempty := by
    refine ⟨![cM m₀ - v * sM m₀, 0], hfan_sub m₀ ?_⟩
    rw [mem_fan]
    refine ⟨sM m₀, ?_, 0, ?_, ?_⟩
    · rw [mem_Icc]
      constructor <;> linarith
    · rw [mem_Icc]
      norm_num
    · ext i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        ring
      · simp
  -- `Q` is compact
  have hQcomp : IsCompact Q := by
    rw [hQ]
    apply IsCompact.union
    · exact isCompact_iUnion fun m ↦ isCompact_fan _ _ _ _
    · exact nt.finite_toSet.isCompact_biUnion fun q _ ↦ isCompact_segment01 _ _
  -- `Q` lies in the ambient rectangle
  have hQrect : Q ⊆ rectangle := by
    rw [hQ]
    apply union_subset
    · refine iUnion_subset fun m ↦ ?_
      rw [fan]
      refine iUnion₂_subset fun t ht ↦ ?_
      exact segment01_subset_rectangle (hends m t ht).1 (hends m t ht).2
    · refine iUnion₂_subset fun q hq ↦ ?_
      exact segment01_subset_rectangle (hntP q hq).1 (hntP q hq).2.1
  -- `Q` is a union of segments
  have hQdecomp : ∃ A : Set (Fin 2 → ℝ), A ⊆ Icc ![-1, -1] ![1, 1] ∧
      Q = ⋃ (p ∈ A), segment01 (p 0) (p 1) := by
    refine ⟨(⋃ m : Fin M, (fun t ↦ ![cM m - v * t, cM m + (1 - v) * t]) ''
        Icc (sM m - η) (sM m + η)) ∪ ((fun q : ℝ × ℝ ↦ ![q.1, q.2]) '' ↑nt), ?_, ?_⟩
    · apply union_subset
      · refine iUnion_subset fun m ↦ ?_
        rintro - ⟨t, ht, rfl⟩
        exact pair_mem_Icc (hends m t ht).1 (hends m t ht).2
      · rintro - ⟨q, hq, rfl⟩
        exact pair_mem_Icc (hntP q hq).1 (hntP q hq).2.1
    · apply Subset.antisymm
      · rw [hQ]
        apply union_subset
        · refine iUnion_subset fun m ↦ ?_
          rw [fan]
          refine iUnion₂_subset fun t ht ↦ ?_
          have hpA : (![cM m - v * t, cM m + (1 - v) * t] : Fin 2 → ℝ) ∈
              (⋃ m : Fin M, (fun t ↦ ![cM m - v * t, cM m + (1 - v) * t]) ''
                Icc (sM m - η) (sM m + η)) ∪ ((fun q : ℝ × ℝ ↦ ![q.1, q.2]) '' ↑nt) :=
            mem_union_left _ (mem_iUnion.2 ⟨m, mem_image_of_mem _ ht⟩)
          have hsub := subset_biUnion_of_mem
            (u := fun p : Fin 2 → ℝ ↦ segment01 (p 0) (p 1)) hpA
          simpa using hsub
        · refine iUnion₂_subset fun q hq ↦ ?_
          have hpA : (![q.1, q.2] : Fin 2 → ℝ) ∈
              (⋃ m : Fin M, (fun t ↦ ![cM m - v * t, cM m + (1 - v) * t]) ''
                Icc (sM m - η) (sM m + η)) ∪ ((fun q : ℝ × ℝ ↦ ![q.1, q.2]) '' ↑nt) :=
            mem_union_right _ (mem_image_of_mem _ (Finset.mem_coe.2 hq))
          have hsub := subset_biUnion_of_mem
            (u := fun p : Fin 2 → ℝ ↦ segment01 (p 0) (p 1)) hpA
          simpa using hsub
      · refine iUnion₂_subset fun p hpA ↦ ?_
        rcases hpA with hpA | hpA
        · obtain ⟨m, hm⟩ := mem_iUnion.1 hpA
          obtain ⟨t, ht, rfl⟩ := hm
          refine subset_trans ?_ (hfan_sub m)
          rw [fan]
          have hsub := subset_biUnion_of_mem
            (u := fun t ↦ segment01 (cM m - v * t) (cM m + (1 - v) * t)) ht
          simpa using hsub
        · obtain ⟨q, hq, rfl⟩ := hpA
          have hsub := hseg_sub q (Finset.mem_coe.1 hq)
          simpa using hsub
  -- `Q` contains segments of every admissible slope
  have hQslopes : ∀ w : ℝ, |w| ≤ (1/2 : ℝ) → ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧
      x₂ ∈ Icc (-1 : ℝ) 1 ∧ x₂ - x₁ = w ∧ segment01 x₁ x₂ ⊆ Q := by
    intro w hw
    obtain ⟨m, hm⟩ := hcovs w hw
    refine ⟨cM m - v * w, cM m + (1 - v) * w, (hends m w hm).1, (hends m w hm).2,
      by ring, ?_⟩
    refine subset_trans ?_ (hfan_sub m)
    rw [fan]
    exact subset_biUnion_of_mem
      (u := fun t ↦ segment01 (cM m - v * t) (cM m + (1 - v) * t)) hm
  -- the staircase thin cover of `Q`
  have hQthin : HasThinCover Q v ε := by
    rw [hQ]
    refine hasThinCover_fans_union_net hη hε hMη hs1 nt (fun q hq ↦ ⟨(hntP q hq).1,
      (hntP q hq).2.1, ?_⟩)
    rw [← hQ]
    exact hseg_sub q hq
  -- assemble the element of `𝒫` and conclude
  have hQP : (⟨⟨Q, hQcomp⟩, hQne⟩ : NonemptyCompacts (Fin 2 → ℝ)) ∈ kornerCompacts :=
    ⟨hQcomp.isClosed, hQrect, hQdecomp, hQslopes⟩
  refine ⟨⟨⟨⟨Q, hQcomp⟩, hQne⟩, hQP⟩, ?_, ?_⟩
  · -- the new set is `δ`-close to `P`
    rw [mem_ball, Subtype.dist_eq, NonemptyCompacts.dist_eq]
    have hd1 : ∀ x ∈ Q, ∃ y ∈ (P : Set (Fin 2 → ℝ)), dist x y ≤ 3 * (δ / 4) := by
      intro x hx
      rw [hQ] at hx
      rcases hx with hx | hx
      · obtain ⟨m, hm⟩ := mem_iUnion.1 hx
        obtain ⟨y, hyP, hyd⟩ := hnear m x hm
        exact ⟨y, hyP, hyd.trans (by linarith)⟩
      · obtain ⟨q, hq⟩ := mem_iUnion.1 hx
        obtain ⟨hqnt, hxq⟩ := mem_iUnion.1 hq
        exact ⟨x, (hntP q hqnt).2.2 hxq, by simp; positivity⟩
    have hd2 : ∀ x ∈ (P : Set (Fin 2 → ℝ)), ∃ y ∈ Q, dist x y ≤ 3 * (δ / 4) := by
      intro x hx
      obtain ⟨q, hq, y, hyq, hyd⟩ := hntnet x hx
      exact ⟨y, hseg_sub q hq hyq, hyd.trans (by linarith)⟩
    have hHD : hausdorffDist Q (P : Set (Fin 2 → ℝ)) ≤ 3 * (δ / 4) :=
      hausdorffDist_le_of_mem_dist (by positivity) hd1 hd2
    calc hausdorffDist Q (P : Set (Fin 2 → ℝ)) ≤ 3 * (δ / 4) := hHD
      _ < δ := by linarith
  · exact hQthin

theorem isNowhereDense_compl_thinCoverSet {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsClosed (thinCoverSet v ε)ᶜ ∧ IsNowhereDense (thinCoverSet v ε)ᶜ := by
  simp_rw [isClosed_isNowhereDense_iff_compl, compl_compl]
  exact ⟨isOpen_thinCoverSet v ε, dense_thinCoverSet hv₀ hv₁ hε⟩

/-- **Körner's slicing estimate** (the core of Theorem 2.5): if `P` admits a thin cover at a
window `(v, ε)` and `u` lies in that window, then the horizontal slice of `P` at height `u`
has Lebesgue measure at most `100 ε`. -/
lemma HasThinCover.toReal_volume_hSlice_le {P : Set (Fin 2 → ℝ)} {v ε u : ℝ}
    (h : HasThinCover P v ε) (hu : |u - v| ≤ ε) :
    (volume (hSlice P u)).toReal ≤ 100 * ε := by
  obtain ⟨N, a, b, c, d, hab, hcov, hthin⟩ := h
  have hind : ∀ j : Fin N, (0 : ℝ) ≤ (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u :=
    fun j ↦ Set.indicator_nonneg (fun _ _ ↦ sub_nonneg.2 (hab j)) _
  -- The slice at height `u` is covered by the slices of the rectangles.
  have hsub : hSlice P u ⊆
      ⋃ j, {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)} := by
    intro x hx
    obtain ⟨j, hj⟩ := hcov ![x, u] hx (by simpa using hu)
    exact mem_iUnion.2 ⟨j, hj⟩
  have hvol_each : ∀ j : Fin N,
      volume {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)}
        ≤ ENNReal.ofReal ((Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u) := by
    intro j
    by_cases hj : u ∈ Ioo (c j) (d j)
    · have hset : {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)}
          = Ioo (a j) (b j) := by
        ext x
        constructor
        · rintro ⟨h0, -⟩
          simpa using h0
        · intro hx
          exact ⟨by simpa using hx, by simpa using hj⟩
      rw [hset, Real.volume_Ioo, Set.indicator_of_mem hj]
    · have hset : {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)}
          = (∅ : Set ℝ) := by
        ext x
        simp only [mem_empty_iff_false, iff_false, mem_setOf_eq]
        rintro ⟨-, h1⟩
        exact hj (by simpa using h1)
      rw [hset]
      simp
  have hbound : volume (hSlice P u)
      ≤ ENNReal.ofReal (∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u) := by
    calc volume (hSlice P u)
        ≤ volume (⋃ j, {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)}) :=
          measure_mono hsub
      _ ≤ ∑ j, volume {x : ℝ | (![x, u] : Fin 2 → ℝ) ∈ openRect (a j) (b j) (c j) (d j)} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, ENNReal.ofReal ((Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u) :=
          Finset.sum_le_sum fun j _ ↦ hvol_each j
      _ = ENNReal.ofReal (∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hind j).symm
  have h0 : (0 : ℝ) ≤ ∑ j, (Ioo (c j) (d j)).indicator (fun _ ↦ b j - a j) u :=
    Finset.sum_nonneg fun j _ ↦ hind j
  exact (ENNReal.toReal_le_of_le_ofReal h0 hbound).trans (hthin u hu).le

/-- Körner's residual set `P⋆`: the members of `𝒫` admitting thin covers at every rational
height in `[0,1]` and at every scale `1/(m+1)`.

Indexing the windows by rational centres keeps the family countable, while the density of
`ℚ` provides a window around every `u ∈ [0,1]` at arbitrarily small scales.  This replaces
(and generalises) the grid of centres `r/n`, `0 ≤ r ≤ n`, used in the paper, which is one
particular countable family with this property. -/
def kornerResidual : Set kornerCompacts :=
  ⋂ i : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) 1} × ℕ,
    thinCoverSet ((i.1 : ℚ) : ℝ) ((1 : ℝ) / ((i.2 : ℝ) + 1))

/-- `P⋆` is a Gδ set: a countable intersection of open sets. -/
lemma isGδ_kornerResidual : IsGδ kornerResidual :=
  IsGδ.iInter_of_isOpen fun _ ↦ isOpen_thinCoverSet _ _

/-- `P⋆` is dense: a countable intersection of dense open sets in a complete space. -/
lemma dense_kornerResidual : Dense kornerResidual := by
  apply dense_iInter_of_isOpen
  all_goals intro i
  · exact isOpen_thinCoverSet _ _
  · exact dense_thinCoverSet i.1.2.1 i.1.2.2 (by positivity)

theorem not_isMeagre_kornerResidual : ¬ IsMeagre kornerResidual := by
  haveI : Nonempty kornerCompacts := by
    rcases nonempty_kornerCompacts with ⟨P, hP⟩
    exact ⟨P, hP⟩
  exact not_isMeagre_of_isGδ_of_dense isGδ_kornerResidual dense_kornerResidual

/-- The subset of `kornerCompacts` consisting of sets whose every
horizontal slice has Lebesgue measure zero. -/
def nullSlices : Set kornerCompacts := {P | ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin 2 → ℝ)) u) = 0}

lemma kornerResidual_subset_nullSlices : kornerResidual ⊆ nullSlices := by
  intro P hP u hu
  -- For every scale `1/(m+1)`, density of `ℚ` provides a window centre near `u`, so the
  -- slice at `u` has measure at most `100/(m+1)`.
  have bound : ∀ m : ℕ, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal
      ≤ 100 * ((1 : ℝ) / ((m : ℝ) + 1)) := by
    intro m
    have he : (0 : ℝ) < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    obtain ⟨q, hq01, hqu⟩ :
        ∃ q : ℚ, ((q : ℝ) ∈ Icc (0 : ℝ) 1) ∧ |u - (q : ℝ)| ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
      rcases le_or_gt u ((1 : ℝ) / ((m : ℝ) + 1)) with hcase | hcase
      · refine ⟨0, by norm_num, ?_⟩
        rw [Rat.cast_zero, sub_zero, abs_of_nonneg hu.1]
        exact hcase
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self u he)
        refine ⟨q, ⟨by linarith, by linarith [hu.2]⟩, ?_⟩
        rw [abs_le]
        constructor <;> linarith
    have hthin : HasThinCover (P : Set (Fin 2 → ℝ)) (q : ℝ) ((1 : ℝ) / ((m : ℝ) + 1)) :=
      mem_iInter.1 hP ⟨⟨q, hq01⟩, m⟩
    exact HasThinCover.toReal_volume_hSlice_le hthin hqu
  have hlimR : Tendsto (fun m : ℕ ↦ (100 : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (100 : ℝ)
  have hfin : volume (hSlice (P : Set (Fin 2 → ℝ)) u) < ⊤ := by
    have hsub : hSlice (P : Set (Fin 2 → ℝ)) u ⊆ Icc (-1 : ℝ) 1 := by
      intro x hx
      have hRect : (↑↑P : Set (Fin 2 → ℝ)) ⊆ Icc ![-1, 0] ![1, 1] := (P.prop).2.1
      have hxRect : (![x, u] : Fin 2 → ℝ) ∈ Icc ![-1, 0] ![1, 1] := hRect hx
      rcases hxRect with ⟨hlo, hhi⟩
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Pi.le_def, Fin.forall_fin_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hlo hhi
      exact ⟨hlo.1, hhi.1⟩
    have : volume (hSlice (P : Set (Fin 2 → ℝ)) u) ≤ volume (Icc (-1 : ℝ) 1) := measure_mono hsub
    exact lt_of_le_of_lt this (by simp)
  have hle0 : (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
    rcases (Metric.tendsto_atTop.1 hlimR) ε hε with ⟨N, hN⟩
    have hN' := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN'
    exact (bound N).trans (by linarith)
  set μ := volume (hSlice (↑↑P) u) with hμ
  have htr0 : μ.toReal = 0 := le_antisymm hle0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff μ).1 htr0 with h | h
  · exact h
  · aesop

theorem not_isMeagre_nullSlices : ¬ IsMeagre nullSlices := by
  intro hM
  exact not_isMeagre_kornerResidual (IsMeagre.mono kornerResidual_subset_nullSlices hM)

/-- The subset of `kornerCompacts` consisting of sets of total
Lebesgue volume zero. -/
def nullVolume : Set kornerCompacts := {P | volume (P : Set (Fin 2 → ℝ)) = 0}

theorem nullSlices_subset_nullVolume : nullSlices ⊆ nullVolume := by
  intro P hP
  have hSlices :
      ∀ y ∈ Icc (0 : ℝ) 1, volume (hSlice (↑↑P : Set (Fin 2 → ℝ)) y) = 0 := by
    simpa [nullSlices, mem_setOf_eq] using hP
  simp_rw [nullVolume, mem_setOf_eq, ← MeasureTheory.setLIntegral_one]
  have hMP := (MeasureTheory.measurePreserving_finTwoArrow (volume : Measure ℝ))
  rw [← MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.volume_pi] at hMP
  rw [← hMP.symm.setLIntegral_comp_preimage_emb]
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  set S : Set (ℝ × ℝ) := e.symm ⁻¹' (↑↑P : Set (Fin 2 → ℝ)) with hS
  · have hP_meas : MeasurableSet (P : Set (Fin 2 → ℝ)) := by
      simpa using ((↑P : NonemptyCompacts (Fin 2 → ℝ)).isCompact.isClosed.measurableSet)
    have hS_meas : MeasurableSet S := by
      simpa [hS] using (MeasurableEquiv.measurableSet_preimage e.symm).mpr hP_meas
    have hFubiniS :
        volume S = ∫⁻ y : ℝ, volume {x | (x, y) ∈ S} := by
      have hvol :
          (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := by
        simpa using Measure.volume_eq_prod ℝ ℝ
      simpa [hvol, Set.preimage, Set.mem_setOf_eq] using
        (Measure.prod_apply_symm
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (s := S) hS_meas)
    have hRect : (↑↑P : Set (Fin 2 → ℝ)) ⊆ Icc ![-1,0] ![1,1] := (P.prop).2.1
    have sec0 : ∀ y : ℝ, volume {x | (x, y) ∈ S} = 0 := by
      intro y
      by_cases hy : y ∈ Icc (0 : ℝ) 1
      · have hsubset :
            {x | (x, y) ∈ S}
              ⊆ {x ∈ Icc (-1 : ℝ) 1 | (![x,y] : Fin 2 → ℝ) ∈ (P : Set _)} := by
          intro x hx
          have hxP : ((![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _)) := by
            simpa [S, hS, e] using hx
          have hxI : x ∈ Icc (-1 : ℝ) 1 := by
            have hxRect : (![x,y] : Fin 2 → ℝ) ∈ Icc ![-1,0] ![1,1] := hRect hxP
            rcases hxRect with ⟨hlo, hhi⟩
            simp [Pi.le_def, Fin.forall_fin_two] at hlo hhi
            exact ⟨hlo.1, hhi.1⟩
          exact ⟨hxI, by simpa⟩
        have aux1 : volume {x : ℝ | (![x, y] : Fin 2 → ℝ) ∈ (↑↑P : Set _)} = 0 := by
          simpa [hSlice] using hSlices y hy
        have aux2 : {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ (![x, y] : Fin 2 → ℝ) ∈ (↑↑P : Set _)}
          ⊆ {x : ℝ | (![x, y] : Fin 2 → ℝ) ∈ (↑↑P : Set _)} := by
          intro x hx
          exact hx.2
        have : volume {x ∈ Icc (-1 : ℝ) 1 | (![x,y] : Fin 2 → ℝ) ∈ (P : Set _)} = 0 :=
          measure_mono_null aux2 aux1
        exact measure_mono_null hsubset this
      · have : {x | (x, y) ∈ S} = (∅ : Set ℝ) := by
          ext x
          constructor
          · intro hx
            have hxP : ((![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _)) := by
              simpa [S, hS, e] using hx
            have hyI : y ∈ Icc (0 : ℝ) 1 := by
              have hxRect : (![x,y] : Fin 2 → ℝ) ∈ Icc ![-1,0] ![1,1] := hRect hxP
              rcases hxRect with ⟨hlo, hhi⟩
              simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Pi.le_def, Fin.forall_fin_two,
                Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_fin_one] at hlo hhi
              exact ⟨hlo.2, hhi.2⟩
            exact (hy hyI).elim
          · intro hx
            cases hx
        simp [this]
    have : ∫⁻ y, volume {x | (x, y) ∈ S} = 0 := by simp [sec0]
    simpa [hFubiniS, S, hS]
  · exact MeasurableEquiv.measurableEmbedding MeasurableEquiv.finTwoArrow.symm

/-- The set of `P ∈ 𝒫` with Lebesgue measure zero is of second category in `(𝒫, d)`.
This is **Körner, Theorem 2.3**. -/
theorem not_isMeagre_nullVolume : ¬ IsMeagre nullVolume := by
  intro h
  exact not_isMeagre_nullSlices (IsMeagre.mono nullSlices_subset_nullVolume h)

/-- There exists at least one `P ∈ 𝒫` whose Lebesgue measure is zero. -/
theorem nonempty_nullVolume : nullVolume.Nonempty :=
  nonempty_of_not_isMeagre not_isMeagre_nullVolume

/-- **Körner, Theorem 2.3 (existence form).**  There is a member of `𝒫`
of Lebesgue measure zero: a compact union of segments joining the two horizontal
sides of the rectangle `[-1,1] × [0,1]`, containing a segment of every slope
`v` with `|v| ≤ 1/2`, and having planar Lebesgue measure zero. -/
theorem exists_kornerCompacts_volume_zero :
    ∃ P : kornerCompacts, volume (P : Set (Fin 2 → ℝ)) = 0 := by
  obtain ⟨P, hP⟩ := nonempty_nullVolume
  exact ⟨P, hP⟩

/-! ### Assembly of a Besicovitch set (Körner, end of §2)

A member of `𝒫` of measure zero contains unit segments in all directions `![v, 1]` with
`|v| ≤ 1/2` — the "vertical cone" of directions.  Four copies of it, transformed by the
integer matrices `1`, `!![1,-1;1,1]`, `!![0,1;-1,0]` and `!![1,1;-1,1]`, cover the four
cones (vertical, both diagonals, horizontal) into which the sup-norm unit sphere of `ℝ²`
splits, yielding a Besicovitch set.  (The paper suggests three rotations by `π/3`, which
does not quite work: the directions of `𝒫`-segments span an arc of half-width
`arctan (1/2) < π/6` only.) -/

/-- The four linear transformations assembling a Besicovitch set from a member of `𝒫`. -/
def besicovitchMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![1, !![1, -1; 1, 1], !![0, 1; -1, 0], !![1, 1; -1, 1]]

lemma mulVec_fin_two (a b c d x y : ℝ) :
    (!![a, b; c, d]).mulVec ![x, y] = ![a * x + b * y, c * x + d * y] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Cone decomposition of the unit sphere.**  Every vector of sup-norm `1` is, up to a
scalar of absolute value at most `1`, the image of a direction `![v, 1]` with `|v| ≤ 1/2`
under one of the four matrices `besicovitchMatrix k`. -/
lemma exists_besicovitchMatrix_smul {w : Fin 2 → ℝ} (hw : ‖w‖ = 1) :
    ∃ (k : Fin 4) (v t : ℝ), |v| ≤ 1 / 2 ∧ |t| ≤ 1 ∧
      w = t • (besicovitchMatrix k).mulVec ![v, 1] := by
  set a := w 0 with ha_def
  set b := w 1 with hb_def
  have ha1 : |a| ≤ 1 := by
    simpa [Real.norm_eq_abs, hw] using norm_le_pi_norm w 0
  have hb1 : |b| ≤ 1 := by
    simpa [Real.norm_eq_abs, hw] using norm_le_pi_norm w 1
  have hmax : 1 ≤ max |a| |b| := by
    have h : ‖w‖ ≤ max |a| |b| := by
      refine (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg a) (le_max_left _ _))).2 ?_
      intro i
      fin_cases i
      · show ‖w 0‖ ≤ max |a| |b|
        rw [Real.norm_eq_abs, ← ha_def]
        exact le_max_left _ _
      · show ‖w 1‖ ≤ max |a| |b|
        rw [Real.norm_eq_abs, ← hb_def]
        exact le_max_right _ _
    linarith [hw ▸ h]
  have hw_eq : w = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rcases le_or_gt |a| (|b| / 2) with h1 | h1
  · -- vertical cone: `w = b • ![a/b, 1]`
    have hb : |b| = 1 := by
      have hmab : max |a| |b| = |b| := max_eq_right (by linarith [abs_nonneg b])
      rw [hmab] at hmax
      exact le_antisymm hb1 hmax
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hb
      norm_num at hb
    refine ⟨0, a / b, b, ?_, hb.le, ?_⟩
    · rw [abs_div, hb, div_one]
      linarith [hb ▸ h1]
    · rw [hw_eq]
      show ![a, b] = b • (besicovitchMatrix 0).mulVec ![a / b, 1]
      have h0 : besicovitchMatrix 0 = 1 := rfl
      rw [h0, Matrix.one_mulVec]
      funext i
      fin_cases i
      · show a = b * (a / b)
        field_simp
      · show b = b * 1
        rw [mul_one]
  rcases le_or_gt |b| (|a| / 2) with h2 | h2
  · -- horizontal cone: `w = a • ![1, -v]` with `v = -b/a`
    have ha : |a| = 1 := by
      have hmab : max |a| |b| = |a| := max_eq_left (by linarith [abs_nonneg a])
      rw [hmab] at hmax
      exact le_antisymm ha1 hmax
    have ha0 : a ≠ 0 := by
      intro h
      rw [h] at ha
      norm_num at ha
    refine ⟨2, -b / a, a, ?_, ha.le, ?_⟩
    · rw [abs_div, abs_neg, ha, div_one]
      linarith [ha ▸ h2]
    · rw [hw_eq]
      show ![a, b] = a • (besicovitchMatrix 2).mulVec ![-b / a, 1]
      have h2' : besicovitchMatrix 2 = !![0, 1; -1, 0] := rfl
      rw [h2', mulVec_fin_two]
      funext i
      fin_cases i
      · show a = a * (0 * (-b / a) + 1 * 1)
        ring
      · show b = a * (-1 * (-b / a) + 0 * 1)
        field_simp
        ring
  -- diagonal cones: both coordinates have absolute value in `(1/2, 1]`
  have hkey : 2 * (a ^ 2 + b ^ 2) < 5 * (|a| * |b|) := by
    nlinarith [mul_pos (show 0 < 2 * |a| - |b| by linarith) (show 0 < 2 * |b| - |a| by linarith),
      sq_abs a, sq_abs b]
  rcases le_or_gt 0 (a * b) with hab | hab
  · -- first/third-quadrant diagonal: matrix `!![1,1;-1,1]`
    have habs : |a| * |b| = a * b := by
      rw [← abs_mul, abs_of_nonneg hab]
    have hs : a + b ≠ 0 := by
      intro h
      have ha0 : a = -b := by linarith [h]
      have hb0 : b = 0 := by nlinarith [hkey, habs, ha0]
      have ha0' : a = 0 := by rw [ha0, hb0]; ring
      rw [ha0', hb0] at hmax
      norm_num at hmax
    refine ⟨3, (a - b) / (a + b), (a + b) / 2, ?_, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hs)]
      have hsq : |a - b| ^ 2 ≤ (1 / 2 * |a + b|) ^ 2 := by
        rw [sq_abs, mul_pow, sq_abs]
        nlinarith [hkey, habs]
      have h2 : (0 : ℝ) ≤ 1 / 2 * |a + b| := by positivity
      nlinarith [abs_nonneg (a - b), hsq, h2]
    · rw [abs_div, abs_two]
      rw [div_le_one (by norm_num : (0:ℝ) < 2)]
      calc |a + b| ≤ |a| + |b| := abs_add_le a b
        _ ≤ 2 := by linarith
    · rw [hw_eq]
      show ![a, b] = ((a + b) / 2) • (besicovitchMatrix 3).mulVec ![(a - b) / (a + b), 1]
      have h3 : besicovitchMatrix 3 = !![1, 1; -1, 1] := rfl
      rw [h3, mulVec_fin_two]
      funext i
      fin_cases i
      · show a = (a + b) / 2 * (1 * ((a - b) / (a + b)) + 1 * 1)
        field_simp
        ring
      · show b = (a + b) / 2 * (-1 * ((a - b) / (a + b)) + 1 * 1)
        field_simp
        ring
  · -- second/fourth-quadrant diagonal: matrix `!![1,-1;1,1]`
    have habs : |a| * |b| = -(a * b) := by
      rw [← abs_mul, abs_of_neg hab]
    have hs : b - a ≠ 0 := by
      intro h
      have : a = b := by linarith [sub_eq_zero.1 h]
      nlinarith [hab, this]
    refine ⟨1, (a + b) / (b - a), (b - a) / 2, ?_, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hs)]
      have hsq : |a + b| ^ 2 ≤ (1 / 2 * |b - a|) ^ 2 := by
        rw [sq_abs, mul_pow, sq_abs]
        nlinarith [hkey, habs]
      have h2 : (0 : ℝ) ≤ 1 / 2 * |b - a| := by positivity
      nlinarith [abs_nonneg (a + b), hsq, h2]
    · rw [abs_div, abs_two]
      rw [div_le_one (by norm_num : (0:ℝ) < 2)]
      calc |b - a| ≤ |b| + |a| := by
            rw [sub_eq_add_neg]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ 2 := by linarith
    · rw [hw_eq]
      show ![a, b] = ((b - a) / 2) • (besicovitchMatrix 1).mulVec ![(a + b) / (b - a), 1]
      have h1' : besicovitchMatrix 1 = !![1, -1; 1, 1] := rfl
      rw [h1', mulVec_fin_two]
      funext i
      fin_cases i
      · show a = (b - a) / 2 * (1 * ((a + b) / (b - a)) + -1 * 1)
        field_simp
        ring
      · show b = (b - a) / 2 * (1 * ((a + b) / (b - a)) + 1 * 1)
        field_simp
        ring

/-- A rescaled sub-segment: if `w = t • d` with `|t| ≤ 1`, then some translate of the
segment from `0` to `w` is contained in the segment from `p` to `p + d`. -/
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

/-- **Existence of a Besicovitch set in the plane** (Körner, Section 2): there is a
compact `s ⊆ ℝ²` of Lebesgue measure zero containing a unit segment in every direction,
i.e. `IsBesicovitch s`.

The ambient space is modelled as `Fin 2 → ℝ` with its supremum norm (so `‖v‖ = 1`
in `IsKakeya` ranges over the sup-norm unit sphere) and `volume` the planar (product
Lebesgue) measure. This is equivalent to the usual Euclidean formulation: the sup and
Euclidean norms are equivalent, so quantifying directions over the sup-norm sphere gives
the same Kakeya property, while `volume` is unchanged. The `Fin 2 → ℝ` model keeps
coordinates, slicing and the linear-image computations definitionally clean. -/
theorem exists_isBesicovitch : ∃ s : Set (Fin 2 → ℝ), IsCompact s ∧ IsBesicovitch s := by
  obtain ⟨P, hPvol⟩ := exists_kornerCompacts_volume_zero
  refine ⟨⋃ k : Fin 4, Matrix.toLin' (besicovitchMatrix k) '' (P : Set (Fin 2 → ℝ)),
    ?_, ?_, ?_⟩
  · -- compactness
    exact isCompact_iUnion fun k ↦
      ((P : NonemptyCompacts (Fin 2 → ℝ)).isCompact).image
        (Matrix.toLin' (besicovitchMatrix k)).continuous_of_finiteDimensional
  · -- the Kakeya property
    intro w hw
    obtain ⟨k, v, t, hv, ht, hwt⟩ := exists_besicovitchMatrix_smul hw
    obtain ⟨x₁, x₂, -, -, hdiff, hsub⟩ := P.2.2.2.2 v hv
    -- the segment of `P` of slope `v`, written with endpoint and direction
    have hseg : segment01 x₁ x₂ = segment ℝ ![x₁, 0] (![x₁, 0] + ![v, 1]) := by
      rw [segment01]
      congr 1
      funext i
      fin_cases i
      · show x₂ = x₁ + v
        linarith [hdiff]
      · simp
    -- its image is a segment in direction `(besicovitchMatrix k).mulVec ![v, 1]`
    set L := Matrix.toLin' (besicovitchMatrix k) with hL
    have hmulVec : (besicovitchMatrix k).mulVec ![v, 1] = L ![v, 1] :=
      (Matrix.toLin'_apply _ _).symm
    have himg : L '' segment01 x₁ x₂
        = segment ℝ (L ![x₁, 0]) (L ![x₁, 0] + (besicovitchMatrix k).mulVec ![v, 1]) := by
      rw [hseg, hmulVec]
      have h := image_segment ℝ L.toAffineMap ![x₁, 0] (![x₁, 0] + ![v, 1])
      rw [LinearMap.coe_toAffineMap, map_add] at h
      simpa using h
    obtain ⟨x, hx⟩ := exists_segment_subset_of_smul ht hwt (L ![x₁, 0])
    refine ⟨x, hx.trans ?_⟩
    rw [← himg, hL]
    exact (Set.image_mono hsub).trans
      (subset_iUnion (fun k ↦ Matrix.toLin' (besicovitchMatrix k) '' (P : Set (Fin 2 → ℝ))) k)
  · -- measure zero
    rw [measure_iUnion_null_iff]
    intro k
    rw [_root_.MeasureTheory.Measure.addHaar_image_linearMap volume, hPvol, mul_zero]

#lint
