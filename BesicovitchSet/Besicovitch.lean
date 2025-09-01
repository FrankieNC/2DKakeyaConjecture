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
import Mathlib.Topology.MetricSpace.Closeds

/-!
# Besicovitch–Kakeya sets via Baire category (after Körner)

This file develops the Baire category construction of a planar Besicovitch set,
following Körner’s paper "Besicovitch via Baire".


## Main definitions

* `IsBesicovitch s` : a Kakeya set in `ℝⁿ` of Lebesgue measure zero.
* `rectangle : Set (Fin 2 → ℝ)` : the closed strip `[-1,1] × [0,1]`.
* `segment01 (x₁ x₂ : ℝ) : Set (Fin 2 → ℝ)` : the segment from `(x₁,0)` to `(x₂,1)`.
* `P_collection` : subsets `P ⊆ rectangle` which are (i) unions of such segments and
  (ii) “span” all horizontal differences `v` with `|v| ≤ 1/2`.
* `P_collection'` : the same class, viewed as a subset of `NonemptyCompacts (Fin 2 → ℝ)`.
* `hasThinCover P v ε` : Körner’s “thin cover” condition at slope `v` and thickness `ε`.
* `P_v_eps' v ε` : elements of `P_collection'` admitting a thin cover at `(v, ε)`.
* `Pn φ n`, `Pstar φ` : intersections of `P_v_eps'` along a decreasing scale `φ : ℕ → ℝ≥0`.

## Main results

* `P_collection'_IsClosed : IsClosed P_collection'`.
  In particular, `(P_collection', dist)` is a complete Baire space.
* Openness/density of thin-cover conditions: `IsOpen (P_v_eps' v ε)` and `Dense (P_v_eps' v ε)`.
* `IsGδ_Pstar` and `Dense_Pstar` : `Pstar φ` is a dense `Gδ` subset of `P_collection'`.
* Slicing estimates imply `Pstar φ ⊆ E_set`, where `E_set` consists of those
  `P ∈ P_collection'` whose every horizontal slice has Lebesgue measure `0`.
  Consequently there exists `P ∈ P_collection'` with `volume (P : Set _) = 0`.

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

lemma rectangle_isBounded : IsBounded rectangle := by simp [rectangle, isBounded_Icc]

lemma rectangle_isClosed : IsClosed rectangle := by
  simpa [rectangle] using (isClosed_Icc : IsClosed (Icc ![(-1 : ℝ), 0] ![1, 1]))

lemma rectangle.convex : Convex ℝ rectangle := by simp [rectangle, convex_Icc]

/-- `rectangle` is nonempty. We use `![0,0]` as the witness. -/
lemma rectangle.nonempty : (rectangle : Set (Fin 2 → ℝ)).Nonempty := by
  refine ⟨![0,0], ?_⟩
  simp [rectangle, Pi.le_def, Fin.forall_fin_two]

/-- The line segment in `ℝ²` from `(x₁, 0)` to `(x₂, 1)`. -/
def segment01 (x₁ x₂ : ℝ) : Set (Fin 2 → ℝ) :=
  segment ℝ ![x₁, 0] ![x₂, 1]

/-- The collection `𝒫` of subsets `P ⊆ rectangle` satisfying
    (i) “union of those segments’’ and (ii) the spanning condition. -/
def P_collection : Set (Set (Fin 2 → ℝ)) :=
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
def P_collection' : Set (NonemptyCompacts (Fin 2 → ℝ)) :=
  { P | IsClosed (P : Set (Fin 2 → ℝ)) ∧ (P : Set (Fin 2 → ℝ)) ⊆ rectangle ∧
      (∃ A : Set (Fin 2 → ℝ), A ⊆ Icc ![-1, -1] ![1, 1] ∧
        (P : Set (Fin 2 → ℝ)) = ⋃ (p ∈ A), segment01 (p 0) (p 1)) ∧
      (∀ v : ℝ, |v| ≤ (1 / 2 : ℝ) →
        ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧
          x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

/-- A convenient compact witness in `𝒫'`: the whole rectangle as a
`NonemptyCompacts` together with the obvious interior point `(0,0)`. -/
def Krect : NonemptyCompacts (Fin 2 → ℝ) :=
  ⟨⟨rectangle, by
    -- `rectangle` is a product of closed intervals, hence compact.
    simpa [rectangle] using (isCompact_Icc : IsCompact (Icc ![(-1 : ℝ), 0] ![1, 1]))⟩,
    -- The point `(0,0)` lies in the rectangle.
    by exact rectangle.nonempty⟩

/-- Endpoints `![a,0]` and `![b,1]` of our standard segments lie in `rectangle`
whenever `a,b ∈ [-1,1]`. -/
lemma endpoints_mem_rectangle {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ![a, 0] ∈ rectangle ∧ ![b, 1] ∈ rectangle := by
  simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]

/-- Every point of the rectangle lies on some segment of the form
`segment01 (p 0) (p 1)` with `p ∈ [-1,1]×[-1,1]`.  (We take the vertical
segment through the `x`–coordinate.) -/
lemma rectangle_subset_Union_segments :
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
    simpa [Pi.le_def, Fin.forall_fin_two] using And.intro hx0 hx0
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
lemma Union_segments_subset_rectangle :
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
  exact rectangle.convex.segment_subset hL hR hxSeg

/-- The rectangle is exactly the union of all standard segments `segment01 (p 0) (p 1)`
with `p ∈ [-1,1]×[-1,1]`. -/
lemma rectangle_Union_segments :
    rectangle = ⋃ (p ∈ Icc ![-1,-1] ![1,1]), segment01 (p 0) (p 1) := by
  ext x
  constructor
  all_goals intro hx
  · -- `x ∈ rectangle` implies `x` belongs to the union of segments.
    exact rectangle_subset_Union_segments hx
  · -- `x` in the union of segments implies `x ∈ rectangle`.
    exact Union_segments_subset_rectangle hx

/-- Spanning property (ii) for the rectangle: for any `|v| ≤ 1/2`, the segment
from `(0,0)` to `(v,1)` lies inside the rectangle. -/
lemma rectangle_property_ii :
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
    exact rectangle.convex.segment_subset hL hR

/-- `𝒫` is nonempty: the rectangle itself (as a compact nonempty set) satisfies
all clauses of the definition. -/
theorem P_collection'_nonempty : (P_collection').Nonempty := by
  refine ⟨Krect, ?_⟩
  split_ands
  · -- (closedness)
    simpa using rectangle_isClosed
  · -- (contained in the rectangle: trivial for the rectangle itself)
    intro x hx
    simpa using hx
  · -- (i) union-of-segments representation
    refine ⟨Icc ![-1,-1] ![1,1], ?_, ?_⟩
    · intro p hp
      exact hp
    · -- equality from the two inclusions above
      simpa using rectangle_Union_segments
  · -- (ii) spanning property for all `|v| ≤ 1/2`
    intro v hv
    simpa using rectangle_property_ii v hv

/-- Any set in `P_collection` is non‑empty: the segment guaranteed by the
definition already gives a point. -/
theorem P_collection.nonempty {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    P.Nonempty := by
  rcases hP with ⟨-, -, -, h⟩
  rcases h 0 (by norm_num) with ⟨x₁, x₂, -, -, -, hPseg⟩
  exact ⟨![x₁, 0], hPseg <| left_mem_segment _ _ _⟩

/-- A set in `P_collection` is bounded since it lies inside the ambient rectangle. -/
theorem P_collection.isBounded {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsBounded P := by
  rcases hP with ⟨-, hS, -⟩
  exact rectangle_isBounded.subset hS

/-- A set in `P_collection` is compact: it is closed and bounded. -/
theorem P_collection.isCompact {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsCompact P := by
  simpa [isCompact_iff_isClosed_bounded] using ⟨hP.1, P_collection.isBounded hP⟩

/-- The carrier image of `P_collection'` recovers the original set-level collection `P_collection`. -/
theorem P_collection'_image_eq : (↑) '' P_collection' = P_collection := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨⟨P, P_collection.isCompact hP⟩, P_collection.nonempty  hP⟩, hP, rfl⟩

/-- Equivalent formulation of the second defining property of `𝒫`. -/
lemma prop_ii_equiv {P : Set (Fin 2 → ℝ)} :
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
lemma hausdorffDist_segments_triangle
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ c d)
      ≤ hausdorffDist (segment ℝ a b) (segment ℝ a d)
        + hausdorffDist (segment ℝ a d) (segment ℝ c d) := by
  -- Hausdorff triangle inequality; segments are nonempty and bounded.
  refine hausdorffDist_triangle ?_
  refine hausdorffEdist_ne_top_of_nonempty_of_bounded ?_ ?_ ?_ ?_ <;>
  first
  | exact ⟨_, left_mem_segment _ _ _⟩
  | exact isBounded_segment _ _

/-- Endpoint-wise control: the Hausdorff distance between segments is bounded by
the sum of the distances between corresponding endpoints. -/
lemma hausdorffDist_segments_le_endpoints
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b a' b' : E) :
    hausdorffDist (segment ℝ a b) (segment ℝ a' b') ≤ dist a a' + dist b b' := by
  -- Triangle via `(a, b')`.
  have htri := hausdorffDist_segments_triangle (a) (b) (a') (b')
  -- First leg: move **right** endpoint `b → b'` with left fixed `a`.
  have h₁ : hausdorffDist (segment ℝ a b) (segment ℝ a b') ≤ dist b b' :=
    hausdorffDist_segment_right_le_dist (z := a) (x := b) (y := b')
  -- Second leg: move **left** endpoint `a → a'` with right fixed `b'`.
  have h₂ : hausdorffDist (segment ℝ a b') (segment ℝ a' b') ≤ dist a a' :=
    hausdorffDist_segment_left_le_dist (x := a) (y := a') (z := b')
  -- Combine and commute the sum to match the target order.
  exact htri.trans <| by simpa [add_comm] using add_le_add h₁ h₂

/-- If `xn → x` and `yn → y`, then `dist (xn i) x + dist (yn i) y → 0`. -/
lemma tendsto_sum_of_tendsto_dists_to_zero
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
theorem tendsto_hausdorffDist_segments_of_tendsto_endpoints
    {ι : Type*} {xn yn : ι → Fin 2 → ℝ} {x y : Fin 2 → ℝ} {l : Filter ι}
    (hx : Tendsto xn l (𝓝 x)) (hy : Tendsto yn l (𝓝 y)) :
    Tendsto (fun i ↦ hausdorffDist (segment ℝ (xn i) (yn i)) (segment ℝ x y)) l (𝓝 0) := by
  -- Pointwise bound by the sum of endpoint distances.
  have hbound : ∀ i, hausdorffDist (segment ℝ (xn i) (yn i)) (segment ℝ x y) ≤ dist (xn i) x + dist (yn i) y := by
    intro i
    simpa using (hausdorffDist_segments_le_endpoints (a := xn i) (b := yn i) (a' := x) (b' := y))
  -- The upper bound tends to `0`, hence the Hausdorff distance does by squeezing.
  refine squeeze_zero (fun _ ↦ hausdorffDist_nonneg) hbound ?_
  simpa using tendsto_sum_of_tendsto_dists_to_zero hx hy

/-- The segment `segment01 a b` in `ℝ²` is compact.
This follows since it is the continuous image of the compact interval `[0,1]`. -/
lemma segment01_isCompact (a b : ℝ) :
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
lemma hausdorffEdist_ne_top_segment01 (a b a' b' : ℝ) :
    EMetric.hausdorffEdist (segment01 a b) (segment01 a' b') ≠ ⊤ := by
  -- Each `segment01` is nonempty: it contains its left endpoint.
  have Lne : (segment01 a  b).Nonempty :=
    ⟨![a, 0], by simpa [segment01] using left_mem_segment ℝ ![a,0] ![b,1]⟩
  have Rne : (segment01 a' b').Nonempty :=
    ⟨![a',0], by simpa [segment01] using left_mem_segment ℝ ![a',0] ![b',1]⟩
  -- Each `segment01` is bounded (indeed compact): use the compact image of `[0,1]`.
  have Lbd : IsBounded (segment01 a b) := (segment01_isCompact a b).isBounded
  have Rbd : IsBounded (segment01 a' b') := (segment01_isCompact a' b').isBounded
  -- Finite Hausdorff *e-distance* holds for nonempty, bounded sets.
  exact hausdorffEdist_ne_top_of_nonempty_of_bounded Lne Rne Lbd Rbd

/-- If `L,T` are `segment01`s, any `y ∈ L` has a point on `T` within the Hausdorff distance. -/
lemma exists_point_on_segment01_within_HD
    {a b a' b' : ℝ} {y : Fin 2 → ℝ}
    (hy : y ∈ (segment01 a b)) :
    ∃ t ∈ (segment01 a' b'), dist t y ≤ hausdorffDist (segment01 a b) (segment01 a' b') := by
  -- choose a minimiser on the compact target segment
  obtain ⟨t, ht_mem, ht_eq⟩ := (segment01_isCompact a' b').exists_infDist_eq_dist
    (by refine ⟨![a',0], ?_⟩; simpa [segment01] using left_mem_segment ℝ ![a',0] ![b',1]) y
  -- compare infDist with HD (finiteness from the previous lemma)
  have hfin : EMetric.hausdorffEdist (segment01 a b) (segment01 a' b') ≠ ⊤ :=
    hausdorffEdist_ne_top_segment01 a b a' b'
  have h_le : infDist y (segment01 a' b' : Set (Fin 2 → ℝ)) ≤ hausdorffDist (segment01 a b) (segment01 a' b') :=
    infDist_le_hausdorffDist_of_mem (x := y) (s := segment01 a b) (t := segment01 a' b') hy hfin
  -- turn infDist into a genuine distance via the minimiser `t`
  have : dist t y = infDist y (segment01 a' b') := by
    simpa [dist_comm, eq_comm] using ht_eq
  exact ⟨t, ht_mem, by simpa [this] using h_le⟩

/-- **Choice of close points from the limit**.
If `Pₙ → K` in `NonemptyCompacts` and `k ∈ K`, then for every `n` there exists
`p ∈ Pₙ n` with `dist p k ≤ dist K (Pₙ n)`. -/
theorem close_points_in_approx {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)} :
    ∀ k ∈ K, ∀ (n : ℕ), ∃ p ∈ Pₙ n, dist p k ≤ dist K (Pₙ n) := by
  intro k hk n
  -- On each compact `Pₙ n`, pick a minimiser of the distance to `k`.
  obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
  -- Turn `infDist` into `dist` and compare with the Hausdorff distance between carriers.
  have hpk : dist p k = infDist k (Pₙ n : Set _) := by
    simpa [eq_comm, dist_comm] using hp_eq
  -- Finiteness of the Hausdorff edistance (nonempty + bounded).
  have hfin :
      EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ n) ≠ ⊤ := by
    refine hausdorffEdist_ne_top_of_nonempty_of_bounded
      K.nonempty (Pₙ n).nonempty (K.toCompacts.isCompact.isBounded) ((Pₙ n).toCompacts.isCompact.isBounded)
  -- `infDist ≤ HD ≤ dist of NonemptyCompacts`
  have h_le : infDist k (Pₙ n) ≤ hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ n) := by
    apply infDist_le_hausdorffDist_of_mem hk hfin
  -- Re-express `hausdorffDist` by the metric on `NonemptyCompacts`.
  have h_dist : dist p k ≤ dist K (Pₙ n) := by
    simpa [NonemptyCompacts.dist_eq, hpk] using h_le
  exact ⟨p, hp_mem, h_dist⟩

/-- If the compacts `Pₙ` converge to `K` in Hausdorff distance
and the points `pₙ n` stay within `dist K (Pₙ n)` of `k`, then `pₙ → k`. -/
lemma tendsto_chosen_points
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_lim : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0)) :
    ∀ k pₙ, (∀ n, dist (pₙ n) k ≤ dist K (Pₙ n)) → Tendsto pₙ atTop (𝓝 (k : Fin 2 → ℝ)) := by
  intro k pₙ hle
  -- Reformulate convergence in terms of `dist (pₙ n) k → 0`.
  refine (tendsto_iff_dist_tendsto_zero).2 ?_
  -- Squeeze: `0 ≤ dist (pₙ n) k ≤ dist K (Pₙ n)`, and RHS → 0.
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hle n) ?_
  simpa [dist_comm] using h_lim

/-- A point of `K` lying outside the closed `rectangle` has strictly positive
distance to `rectangle`. -/
theorem infDist_pos_of_mem_limit_notin_rectangle {k' : Fin 2 → ℝ} (h_notin : k' ∉ rectangle) :
    0 < infDist k' rectangle := by
  by_contra h
  -- if not `> 0`, then `infDist = 0` (by nonnegativity)
  have h0 : infDist k' (rectangle : Set _) = 0 := le_antisymm (le_of_not_gt h) infDist_nonneg
  -- hence `k' ∈ closure rectangle`
  have hk_cl : k' ∈ closure (rectangle : Set (Fin 2 → ℝ)) := by
    simpa [mem_closure_iff_infDist_zero, rectangle.nonempty] using h0
  -- but `rectangle` is closed, contradiction
  have : k' ∈ rectangle := by simpa [rectangle_isClosed.closure_eq] using hk_cl
  exact h_notin this

/-- **Stability of the ambient rectangle under limits**.
If each `Pₙ ⊆ rectangle` and `Pₙ → K` in `NonemptyCompacts`, then `K ⊆ rectangle`. -/
theorem limit_subset_rectangle
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection') (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ n) ≠ ⊤) :
    ↑K ⊆ rectangle := by
  have hP_sub : ∀ n, ↑(Pₙ n) ⊆ rectangle := fun n ↦ (h_mem n).2.1
  intro k' hk'
  by_contra h_notin
  -- positive distance from `k'` to rectangle
  set d := infDist k' rectangle with hd
  have hd_pos : 0 < d := infDist_pos_of_mem_limit_notin_rectangle h_notin
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
If each `Pₙ` is in `P_collection'`, then every point of `Pₙ n` lies on a segment
`segment01 (x 0) (x 1)` for some `x ∈ [-1,1] × [-1,1]`, and that whole segment is
contained in `Pₙ n`.
-/
theorem exists_segment_in_P_collection' {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection')
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
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection') (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (h_closed : IsClosed ↑(K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n : Set (Fin 2 → ℝ)) ↑K ≠ ⊤) (pₙ : (k : Fin 2 → ℝ) → k ∈ K → ℕ → Fin 2 → ℝ)
    (hpₙ_mem : ∀ (k : Fin 2 → ℝ) (a : k ∈ K) (n : ℕ), pₙ k a n ∈ Pₙ n)
    (h_tendsto : ∀ (k : Fin 2 → ℝ) (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k)) :
    let A := {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K};
    A = {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K} →
      A ⊆ Icc ![-1, -1] ![1, 1] → ∀ k ∈ ↑K, k ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
  intro A hA hAsub k hk
  choose x hx h_pn_in_seg_n h_seg_subset_n using exists_segment_in_P_collection'
  obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq (hx h_mem pₙ hpₙ_mem k hk)
  set L := segment01 (x_lim 0) (x_lim 1) with hL

  have h_seg_j_P : ∀ j, segment01 (x h_mem pₙ hpₙ_mem k hk (φ j) 0) (x h_mem pₙ hpₙ_mem k hk (φ j) 1) ⊆ Pₙ (φ j) := by
    intro j y hy
    apply h_seg_subset_n
    exact hy

  have h_seg_HD0 : Tendsto (fun j ↦
    hausdorffDist (segment01 (x h_mem pₙ hpₙ_mem k hk (φ j) 0) (x h_mem pₙ hpₙ_mem  k hk (φ j) 1)) L) atTop (𝓝 0) := by
    apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
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
      have := exists_point_on_segment01_within_HD
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
      have hfin : EMetric.hausdorffEdist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
        simpa [EMetric.hausdorffEdist_comm] using fin_dist (φ j)
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
        · exact hausdorffEdist_ne_top_segment01 (x h_mem pₙ hpₙ_mem k hk (φ i) 0) (x h_mem pₙ hpₙ_mem  k hk (φ i) 1) (x_lim 0) (x_lim 1)
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
      · simpa [segment01] using (show (segment ℝ ![x_lim 0, 0] ![x_lim 1, 1]).Nonempty from ⟨![x_lim 0, 0], left_mem_segment _ _ _⟩)
    simpa [hL_closed.closure_eq] using hk_closure

/--  If `Pₙ ∈ P_collection'`, then for every slope `v` with `|v| ≤ 1/2`,
there is a horizontal segment of length `v` contained in `Pₙ n`. -/
theorem P_collection'_exists_segment_of_diff
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)}
    (v : ℝ) (hv : |v| ≤ 1 / 2)
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection')  :
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
theorem exists_mem_Pn_close_to
  {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
  (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) :
    ∀ k ∈ K, ∀ (n : ℕ), ∃ p ∈ Pₙ n, dist p k ≤ dist K (Pₙ n) := by
  intro k hk n
  obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
  have hpk : dist p k = Metric.infDist k (Pₙ n : Set _) := by
    simpa [eq_comm, dist_comm] using hp_eq
  have fin : EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) ≠ ⊤ := by
    simpa [EMetric.hausdorffEdist_comm] using fin_dist n
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
If `Pₙ ∈ P_collection'` and `Pₙ → K` in the Hausdorff metric, then `K` also satisfies
the segment property: for every `|v| ≤ 1/2` there exist `x₁, x₂ ∈ [-1,1]` with
`x₂ - x₁ = v` and `segment01 x₁ x₂ ⊆ K`.
-/
theorem exists_segment_subset_K_of_diff_le_half {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection') (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε)
    (h_closed : IsClosed (K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) :
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
  -- set L : NonemptyCompacts (Fin 2 → ℝ) := ⟨⟨segment01 (x_lim 0) (x_lim 1), segment01_isCompact _ _⟩, by
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
      have := exists_point_on_segment01_within_HD
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
      apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
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
          EMetric.hausdorffEdist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
        simpa [EMetric.hausdorffEdist_comm] using fin_dist (φ j)
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

theorem P_collection'_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := P_collection.isBounded (h_mem n)
  have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ :=
    hausdorffEdist_ne_top_of_nonempty_of_bounded (Pₙ n).nonempty K.nonempty (hPn_bdd n) hK_bdd
  split_ands
  · exact h_closed
  · apply limit_subset_rectangle h_mem h_lim
    · intro n
      simpa [EMetric.hausdorffEdist_comm] using fin_dist n
  · set A : Set (Fin 2 → ℝ) := { p | p ∈ Icc ![-1,-1] ![1,1] ∧ segment01 (p 0) (p 1) ⊆ (K : Set (Fin 2 → ℝ)) } with hA
    use A
    split_ands
    · rintro _ ⟨h, -⟩
      exact h
    · ext k
      constructor
      all_goals intro hk
      · choose pₙ hpₙ_mem hpₙ_lt using exists_mem_Pn_close_to fin_dist
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

-- theorem P_col'_IsClosed : IsClosed P_collection' := by
--   rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
--   intro Pₙ K h_mem h_lim
--   have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
--   rw [Metric.tendsto_atTop] at h_lim
--   -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
--   have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := P_collection.isBounded (h_mem n)
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
--         apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
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
--           have := exists_point_on_segment01_within_HD
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
--             · exact hausdorffEdist_ne_top_segment01 (x k hk (φ i) 0) (x k hk (φ i) 1) (x_lim 0) (x_lim 1)
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
--     -- set L : NonemptyCompacts (Fin 2 → ℝ) := ⟨⟨segment01 (x_lim 0) (x_lim 1), segment01_isCompact _ _⟩, by
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
--         have := exists_point_on_segment01_within_HD
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
--         apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
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

/-- The space `P_collection'` is complete. -/
instance CompleteSpace_P_collection' : CompleteSpace P_collection' :=
  IsClosed.completeSpace_coe P_collection'_IsClosed

/-- The space `P_collection'` has the Baire property. -/
instance BaireSpace_P_collection' : BaireSpace P_collection' :=
  BaireSpace.of_pseudoEMetricSpace_completeSpace

noncomputable section

/-- A closed, axis–aligned rectangle `[x₁,x₂] × [y₁,y₂]`
    written in the `Fin 2 → ℝ` model of `ℝ²`. -/
def axisRect (x₁ x₂ y₁ y₂ : ℝ) : Set (Fin 2 → ℝ) :=
  {p | p 0 ∈ Icc x₁ x₂ ∧ p 1 ∈ Icc y₁ y₂}

/-- Horizontal slice of a planar set at height `y`. -/
def hSlice (S : Set (Fin 2 → ℝ)) (y : ℝ) : Set ℝ :=
  {x | (![x, y] : Fin 2 → ℝ) ∈ S}

/-- The vertical window `W v ε := [0,1] ∩ [v - ε,v + ε]`. -/
def window (v ε : ℝ) : Set ℝ :=
  Icc 0 1 ∩ Icc (v - ε) (v + ε)

/-- The "good cover" condition appearing in Lemma 2.4. -/
def hasThinCover (P : Set (Fin 2 → ℝ)) (v ε : ℝ) : Prop :=
  ∃ (R : Finset (Set (Fin 2 → ℝ))),
      -- every element of `R` is an axis–aligned rectangle
      (∀ r ∈ R, ∃ a b c d, r = axisRect a b c d) ∧
      -- each slice of `P` in the window is covered by `⋃ R`
      (∀ y, y ∈ window v ε →
        hSlice P y ⊆ hSlice (⋃ r ∈ R, (r : Set _)) y) ∧
      -- and the total horizontal length is < 100 ε
      (∀ y, y ∈ window v ε → (volume (hSlice (⋃ r ∈ R, (r : Set _)) y)).toReal < 100 * ε)

/-- A singleton has a thin cover given by its degenerate rectangle. -/
lemma hasThinCover_singleton (v ε : ℝ) (x : Fin 2 → ℝ) (hε : 0 < ε) :
    hasThinCover ({x} : Set (Fin 2 → ℝ)) v ε := by
  -- one degenerate rectangle around `x`
  let R : Finset (Set (Fin 2 → ℝ)) := {axisRect (x 0) (x 0) (x 1) (x 1)}
  refine ⟨R, ?rects, ?cover, ?length⟩
  · -- every member of `R` is an axis-rectangle
    intro r hr
    rcases Finset.mem_singleton.mp hr with rfl
    exact ⟨x 0, x 0, x 1, x 1, rfl⟩
  · -- each slice of `{x}` is covered by `⋃ R`
    intro y _ t ht
    -- `![t,y] = x`, hence it lies in the (degenerate) rectangle at `x`
    have hx : (![t,y] : Fin 2 → ℝ) = x := by simpa [hSlice] using ht
    have : (![t,y] : Fin 2 → ℝ) ∈ axisRect (x 0) (x 0) (x 1) (x 1) := by
      simp [hx, axisRect]
    simpa [R]
  · -- the slice of the union is either `∅` or `{x 0}`, so `volume = 0 < 100 ε`
    intro y _
    have : hSlice (⋃ r ∈ R, (r : Set _)) y = (if y = x 1 then {x 0} else (∅ : Set ℝ)) := by
      split_ifs
      all_goals simp [R, hSlice, axisRect, *]
    have hvol : (volume (hSlice (⋃ r ∈ R, r) y)).toReal = 0 := by
      split_ifs at this
      all_goals simp [this]
    simpa [hvol] using (by simp [hε])

/-- `𝒫(v, ε)` as a subset of `NonemptyCompacts (Fin 2 → ℝ)`. -/
def P_v_eps' (v ε : ℝ) : Set P_collection' :=
  {P | hasThinCover (P : Set _) v ε}

/-- helper: expand an axis-aligned rectangle by `η` in both directions -/
def axisRectExpand (η a b c d : ℝ) : Set (Fin 2 → ℝ) :=
  axisRect (a - η) (b + η) (c - η) (d + η)

/-- Structural fact: slices commute with finite unions of rectangles. -/
lemma hSlice_iUnion_finset {R : Finset (Set (Fin 2 → ℝ))} {y : ℝ} :
    hSlice (⋃ r ∈ R, (r : Set _)) y = ⋃ r ∈ R, {x : ℝ | (![x, y] : Fin 2 → ℝ) ∈ r} := by
  ext x
  simp [hSlice]

/-- Slice of a rectangle is a rectangle in 1D: an interval if the `y`-constraint is satisfied,
otherwise empty. -/
lemma hSlice_axisRect (a b c d y : ℝ) :
    hSlice (axisRect a b c d) y = (if y ∈ Icc c d then {x : ℝ | x ∈ Icc a b} else (∅ : Set ℝ)) := by
  ext x
  by_cases hy : y ∈ Icc c d
  all_goals simp_rw [hSlice, axisRect, hy]
  all_goals aesop

/-- Monotonicity of slices under inclusion. -/
lemma hSlice_mono {S T : Set (Fin 2 → ℝ)} (hST : S ⊆ T) (y : ℝ) :
    hSlice S y ⊆ hSlice T y := by
  intro x hx
  exact hST hx

/-- `rectangle ⊆` its `η`-expansion. -/
lemma axisRect_subset_expand {a b c d : ℝ} {η : ℝ} (hη : 0 ≤ η) :
    axisRect a b c d ⊆ axisRectExpand η a b c d := by
  intro p hp
  rcases hp with ⟨hx, hy⟩
  dsimp [axisRectExpand, axisRect] at *
  constructor
  · exact Icc_subset_Icc (sub_le_self _ hη) (le_add_of_nonneg_right hη) hx
  · exact Icc_subset_Icc (sub_le_self _ hη) (le_add_of_nonneg_right hη) hy

/-- If a point is `η`-close to a point inside a rectangle, it lies in the `η`-expansion
of that rectangle. -/
lemma mem_expand_of_close {a b c d η : ℝ} {p q : Fin 2 → ℝ}
    (hq : q ∈ axisRect a b c d) (hpq : dist p q ≤ η) :
    p ∈ axisRectExpand η a b c d := by
  rcases hq with ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
  have h0 : |p 0 - q 0| ≤ η := by simpa [Real.dist_eq] using le_of_max_le_left hpq
  have h1 : |p 1 - q 1| ≤ η := by simpa [Real.dist_eq] using le_of_max_le_right hpq
  rw [abs_le] at h0 h1
  simp only [axisRectExpand, axisRect, Fin.isValue, mem_Icc, tsub_le_iff_right, mem_setOf_eq]
  split_ands
  all_goals linarith

theorem isOpen_P_v_eps' {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsOpen (P_v_eps' v ε) := by
  rw [Metric.isOpen_iff]
  intro P hP
  rcases hP with ⟨R, h_rects, h_cover, h_len⟩
  sorry

theorem dense_P_v_eps' {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (P_v_eps' v ε) := by
  sorry

theorem P_v_eps_compl_nowhereDense {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsClosed (P_v_eps' v ε)ᶜ ∧ IsNowhereDense (P_v_eps' v ε)ᶜ := by
  simp_rw [isClosed_isNowhereDense_iff_compl, compl_compl]
  exact ⟨isOpen_P_v_eps' hv₀ hv₁ hε, dense_P_v_eps' hv₀ hv₁ hε⟩

/-- A simple auxiliary sequence `φ n = 1 / (n+2)` in `ℝ≥0`.
This sequence is used as a witness in existence proofs: it is strictly decreasing, tends to `0`,
and stays in `(0,1)`. -/
def phi (n : ℕ) : ℝ≥0 := 1 / (n + 2 : ℝ≥0)

/-- `phi` is strictly decreasing. -/
lemma phi_strictAnti : StrictAnti phi := by
  intro a b hlt
  -- Prove on ℝ and cast back
  have : (1 : ℝ) / (b + 2) < 1 / (a + 2) := by
    have pos : (0 : ℝ) < a + 2 := by exact_mod_cast Nat.succ_pos (a + 1)
    have lt' : (a + 2 : ℝ) < (b + 2 : ℝ) := by exact_mod_cast add_lt_add_right hlt 2
    simpa using one_div_lt_one_div_of_lt pos lt'
  exact this

/-- Each term of `phi` lies in `(0,1)`. -/
lemma phi_mem_Ioo (n : ℕ) : phi n ∈ Set.Ioo 0 1 := by
  simp only [phi, one_div, mem_Ioo, inv_pos, add_pos_iff, Nat.cast_pos, Nat.ofNat_pos, or_true,
    true_and]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n))

/-- `phi n → 0`. -/
lemma tendsto_phi_zero : Tendsto phi atTop (𝓝 (0 : ℝ≥0)) := by
  -- Prove on `ℝ` and pull back
  have h : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 2)) atTop (𝓝 0) := by
    simpa using (tendsto_add_atTop_iff_nat 2).2 h
  simpa using (NNReal.tendsto_coe.1 this)

lemma mul_nonneg_range (n r : ℕ) :
    (0 : ℝ≥0) ≤ (r : ℝ≥0) * phi n := by
  simp [phi]

/-- For `r < n`, we have `r * phi n ≤ 1`. -/
lemma mul_le_one_on_range (n r : ℕ) (hr : r ∈ Finset.range n) :
    (r : ℝ≥0) * phi n ≤ 1 := by
  -- `r ≤ n ≤ n+2`, then multiply by the positive `phi n = 1/(n+2)`
  have hr' : (r : ℝ≥0) ≤ n := by exact_mod_cast (Finset.mem_range.1 hr).le
  have pos : 0 < phi n := (phi_mem_Ioo n).1
  have step1 : (r : ℝ≥0) * phi n ≤ (n : ℝ≥0) * phi n :=
    mul_le_mul_of_nonneg_right hr' (le_of_lt pos)
  have step2 : (n : ℝ≥0) * phi n ≤ ((n + 2 : ℕ) : ℝ≥0) * phi n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n 2) (le_of_lt pos)
  have hne : ((n + 2 : ℕ) : ℝ≥0) ≠ 0 := by simp
  have : ((n + 2 : ℕ) : ℝ≥0) * phi n = 1 := by simp [phi]
  exact (step1.trans (step2.trans (by aesop)))

theorem exists_strictAnti_seq_Ioo_tendsto_zero_with_range_mul_le_one :
  ∃ φ : ℕ → ℝ≥0,
    StrictAnti φ
    ∧ (∀ n, φ n ∈ Set.Ioo 0 1)
    ∧ Tendsto φ atTop (𝓝 0)
    ∧ (∀ n r, r ∈ Finset.range n → 0 ≤ (r : ℝ≥0) * φ n)
    ∧ (∀ n r, r ∈ Finset.range n → (r : ℝ≥0) * φ n ≤ 1) := by
  refine ⟨phi, phi_strictAnti, (fun n ↦ phi_mem_Ioo n), tendsto_phi_zero, ?_, ?_⟩
  · exact fun n r a ↦ mul_nonneg_range n r
  · exact fun n r hr ↦ mul_le_one_on_range n r hr

/-- The set of configurations in `P_collection'` satisfying the
`P_v_eps'` constraints for all `r < n` at scale `φ n`. -/
def Pn (φ : ℕ → ℝ≥0) (n : ℕ) : Set P_collection' :=
  ⋂ r ∈ Finset.range n, P_v_eps' ((r : ℝ) * (φ n : ℝ)) (φ n : ℝ)

variable (φ : ℕ → ℝ≥0)

/-- Expand membership in `Pn` to the finset form. -/
@[simp]
lemma mem_Pn (n : ℕ) {x : P_collection'} :
    x ∈ Pn φ n ↔ ∀ r ∈ Finset.range n, x ∈ P_v_eps' ((r : ℝ) * (φ n : ℝ)) (φ n) := by
  simp [Pn]

lemma isOpen_Pn (n : ℕ)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    IsOpen (Pn φ n) := by
  rw [Pn]
  refine isOpen_biInter_finset ?_
  intro r hr
  exact isOpen_P_v_eps' (hv0 n r hr) (hv1 n r hr) ((hφ n).1)

lemma measure_Pn
    (n : ℕ) (P : P_collection') (hP : P ∈ Pn φ n)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ∀ u ∈ Icc (0 : ℝ) 1, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal ≤ 100 * φ n := by
  intro u hu
  simp_rw [Pn, Finset.mem_range, mem_iInter, P_v_eps', hasThinCover, hSlice, window] at hP
  sorry

/-- The intersection of all `Pn φ n`. It collects the sets in
`P_collection'` satisfying all the constraints as `n → ∞`. -/
def Pstar (φ : ℕ → ℝ≥0) : Set P_collection' := ⋂ n : ℕ, Pn φ n

@[simp]
lemma mem_Pstar {x : P_collection'} :
    x ∈ Pstar φ ↔ ∀ n, x ∈ Pn φ n := by
  simp [Pstar]

/-- `P⋆ ⊆ Pₙ` for every `n`. -/
lemma Pstar_subset_Pn (n : ℕ) : Pstar φ ⊆ Pn φ n := by
  intro x hx
  simp only [Pstar, mem_iInter, mem_Pn, Finset.mem_range] at hx
  simp only [mem_Pn, Finset.mem_range]
  intro r hr
  exact hx n r hr

/-- `Pstar(φ)` is a Gδ set: countable intersection of open sets. -/
lemma IsGδ_Pstar
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv1 : ∀ n r, r ∈ Finset.range n → ↑r * φ n ≤ 1) :
    IsGδ (Pstar φ) := by
  apply IsGδ.iInter_of_isOpen
  intro i
  apply isOpen_Pn
  · exact fun n ↦ hφ n
  · exact fun n r a ↦ zero_le (↑r * φ n)
  · exact fun n r a ↦ hv1 n r a

lemma Dense_Pn (n : ℕ)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    Dense (Pn φ n) := by
  rw [Pn]
  apply dense_iInter_of_isOpen
  all_goals intro i
  · apply isOpen_iInter_of_finite
    intro hi
    exact isOpen_P_v_eps' (hv0 n i hi) (hv1 n i hi) ((hφ n).1)
  · apply dense_iInter_of_isOpen
    all_goals intro hi
    · exact isOpen_P_v_eps' (hv0 n i hi) (hv1 n i hi) ((hφ n).1)
    · exact dense_P_v_eps' (hv0 n i hi) (hv1 n i hi) ((hφ n).1)

/-- `Pstar(φ)` is dense: countable intersection of open dense sets. -/
lemma Dense_Pstar
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    Dense (Pstar φ) := by
  apply dense_iInter_of_isOpen
  all_goals intro i
  · apply isOpen_Pn
    · exact hφ
    · exact fun n r a ↦ hv0 n r a
    · exact fun n r a ↦ hv1 n r a
  · apply Dense_Pn
    · exact hφ
    · exact fun n r a ↦ hv0 n r a
    · exact fun n r a ↦ hv1 n r a

theorem Pstar_notMeagre
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ¬ IsMeagre (Pstar φ) := by
  haveI : Nonempty P_collection' := by
    rcases P_collection'_nonempty with ⟨P, hP⟩
    exact ⟨P, hP⟩
  apply not_isMeagre_of_isGδ_of_dense
  · apply IsGδ_Pstar
    · exact fun n ↦ hφ n
    · exact fun n r a ↦ hv1 n r a
  · apply Dense_Pstar
    · exact fun n ↦ hφ n
    · exact fun n r a ↦ hv0 n r a
    · exact fun n r a ↦ hv1 n r a

/-- The subset of `P_collection'` consisting of sets whose every
horizontal slice has Lebesgue measure zero. -/
def E_set : Set P_collection' := {P | ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin 2 → ℝ)) u) = 0}

lemma Pstar_sub_E_set
    (h₃φ : Tendsto φ atTop (𝓝 0))
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n) (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    Pstar φ ⊆ E_set := by
  intro P hP u hu
  have bound : ∀ n, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal ≤ 100 * φ n := by
    intro n
    apply measure_Pn
    · rw [Pstar, mem_iInter] at hP
      exact hP n
    · exact fun n r a ↦ hv0 n r a
    · exact fun n r a ↦ hv1 n r a
    · exact hu
  -- have hlim : Tendsto (fun n ↦ 100 * φ n) atTop (𝓝 0) := by
  --   simpa [zero_mul] using (tendsto_const_nhds.mul h₃φ)
  have hφR : Tendsto (fun n : ℕ ↦ (φ n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (NNReal.tendsto_coe.2 h₃φ)
  have hlimR : Tendsto (fun n : ℕ ↦ (100 : ℝ) * (φ n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [zero_mul] using (tendsto_const_nhds.mul hφR)
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
    have hN' : (100 : ℝ) * (φ N : ℝ) < 0 + ε := by simpa [zero_add] using hN N le_rfl
    exact (bound N).trans (le_of_lt hN')
  set μ := volume (hSlice (↑↑P) u) with hμ
  have htr0 : μ.toReal = 0 := le_antisymm hle0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff μ).1 htr0 with h | h
  · exact h
  · aesop

theorem E_set_not_meagre
    (h : Pstar φ ⊆ E_set)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ¬ IsMeagre E_set := by
  intro hM
  apply IsMeagre.mono at h
  · exact (Pstar_notMeagre φ hφ hv0 hv1) h
  · exact hM

/-- The subset of `P_collection'` consisting of sets of total
Lebesgue volume zero. -/
def P_zero_vol : Set P_collection' := {P | volume (P : Set (Fin 2 → ℝ)) = 0}

theorem E_set_subset_PzeroVol : E_set ⊆ P_zero_vol := by
  intro P hP
  have hSlices :
      ∀ y ∈ Icc (0 : ℝ) 1, volume (hSlice (↑↑P : Set (Fin 2 → ℝ)) y) = 0 := by
    simpa [E_set, mem_setOf_eq] using hP
  simp_rw [P_zero_vol, mem_setOf_eq, ← MeasureTheory.setLIntegral_one]
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

/-- The set of `P ∈ 𝒫` with Lebesgue measure zero is of second category in `(𝒫, d)`. -/
theorem P_zero_vol_not_meagre
    (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n) (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ¬ IsMeagre P_zero_vol := by
  intro h
  exact E_set_not_meagre φ (Pstar_sub_E_set φ h₃φ hv0 hv1) h₂φ hv0 hv1 (h.mono E_set_subset_PzeroVol)

/-- There exists at least one `P ∈ 𝒫` whose Lebesgue measure is zero. -/
theorem exists_P_with_zero_volume
    (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n) (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    P_zero_vol.Nonempty :=
  nonempty_of_not_isMeagre (P_zero_vol_not_meagre φ h₂φ h₃φ hv0 hv1)

#lint
