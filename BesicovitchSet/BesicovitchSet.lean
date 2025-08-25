/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import Mathlib

set_option maxHeartbeats 300000

open Set Real Topology Metric Bornology TopologicalSpace MeasureTheory MetricSpace ENNReal NNReal Filter

namespace Besicovitch

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A subset of a normed real vector space `E` is Kakeya if it contains a segment of unit length in
every direction. -/
def IsKakeya {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) : Prop :=
    ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

/-- The universal set is Kakeya. -/
lemma univ_isKakeya : IsKakeya (Set.univ : Set E) := by simp [IsKakeya]

/-- If `s` is Kakeya and `s ⊆ t`, then `t` is Kakeya. -/
theorem IsKakeya_subset {s t : Set E} (h : IsKakeya s) (hs : s ⊆ t) : IsKakeya t := by
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
    · simpa [h₀] using h_kakeya.nonempty
    -- Case: `v ≠ 0`
    · set u := ‖v‖⁻¹ • v with hu -- rescale `v` to a unit vector `u`
      have h₁ : ‖v‖ ≠ 0 := by
        contrapose! h₀
        rw [norm_eq_zero] at h₀
        exact h₀
      -- Now `u` has norm 1
      have h₂ : ‖u‖ = 1 := by field_simp [hu, norm_smul]
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

/-- A Besicovitch set in `ℝⁿ` is a Kakeya set of Lebesgue measure zero. -/
def IsBesicovitch {n : ℕ} (s : Set (Fin n → ℝ)) : Prop := IsKakeya s ∧ volume s = 0

end

section

/-- The closed rectangle `[-1,1] × [0,1] ⊆ ℝ²`, written in coordinates for `Fin 2 → ℝ`. -/
def rectangle : Set (Fin 2 → ℝ) := Icc ![-1, 0] ![1,1]

lemma rectangle_isBounded : IsBounded rectangle := by simp [rectangle, isBounded_Icc]

lemma rectangle_isClosed : IsClosed rectangle := by
  simpa [rectangle] using (isClosed_Icc : IsClosed (Icc ![(-1 : ℝ), 0] ![1, 1]))

lemma rectangle_convex : Convex ℝ rectangle := by simp [rectangle, convex_Icc]

/-- `rectangle` is nonempty. We use `![0,0]` as the witness. -/
lemma rectangle_nonempty : (rectangle : Set (Fin 2 → ℝ)).Nonempty := by
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
    by exact rectangle_nonempty⟩

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
  exact rectangle_convex.segment_subset hL hR hxSeg


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
    exact rectangle_convex.segment_subset hL hR

/-- `𝒫` is nonempty: the rectangle itself (as a compact nonempty set) satisfies
all clauses of the definition. -/
theorem P_collection'_nonempty : (P_collection').Nonempty := by
  refine ⟨Krect, ?_⟩
  refine And.intro ?closed <| And.intro ?subset <| And.intro ?union ?prop2
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
`p ∈ Pₙ n` with `dist p k ≤ dist K (Pₙ n)`. This is a standard
"nearest point on a compact" argument packaged for later reuse. -/
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

/-- **Convergence of the chosen points**.
With `pₙ k hk n` as in `close_points_in_approx`, we actually have `pₙ k hk n → k`. -/
lemma tendsto_chosen_points
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)} {K : NonemptyCompacts (Fin 2 → ℝ)}
    (h_lim : Tendsto (fun n ↦ dist (Pₙ n) K) atTop (𝓝 0)) :
    ∀ k ∈ K, ∀ pₙ, (∀ n, pₙ n ∈ Pₙ n) → (∀ n, dist (pₙ n) k ≤ dist K (Pₙ n)) → Tendsto pₙ atTop (𝓝 k) := by
  intro k hk pₙ hp_mem hle
  -- Convert to the metric characterization.
  refine (tendsto_iff_dist_tendsto_zero).2 ?_
  -- Squeeze: `0 ≤ dist (pₙ n) k ≤ dist K (Pₙ n) → 0`.
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
    simpa [mem_closure_iff_infDist_zero, rectangle_nonempty] using h0
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

/-- **Pick one segment from the cover of `Pₙ` through a given point.**
If `Pₙ ∈ P_collection'`, every point `q ∈ Pₙ` lies on a segment
`segment01 (x 0) (x 1)` whose endpoint vector `x` is in the unit square, and this
segment is contained in `Pₙ`. -/
lemma pick_segment_of_cover
    {Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)}
    (h_mem : ∀ n, Pₙ n ∈ P_collection')
    {n : ℕ} {q : Fin 2 → ℝ} (hq : q ∈ (Pₙ n : Set (Fin 2 → ℝ))) :
    ∃ x ∈ Icc ![-1,-1] ![1,1], q ∈ segment01 (x 0) (x 1) ∧ segment01 (x 0) (x 1) ⊆ (Pₙ n : Set (Fin 2 → ℝ)) := by
  rcases h_mem n with ⟨_, _, ⟨A, hA_sub, hA_eq⟩, _⟩
  have : q ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by simpa [hA_eq] using hq
  rcases mem_iUnion₂.1 this with ⟨p, hpA, hpq⟩
  refine ⟨![p 0, p 1], ?_, ?_, ?_⟩
  · simpa [Pi.le_def, Fin.forall_fin_two] using hA_sub hpA
  · simpa using hpq
  · intro y hy
    have : y ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) :=
      mem_iUnion₂.2 ⟨p, hpA, by simpa using hy⟩
    simpa [hA_eq] using this

theorem Besicovitch.Besicovitch.P_col'_IsClosed.extracted_1_3.extracted_1_5 ⦃Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)⦄
    ⦃K : NonemptyCompacts (Fin 2 → ℝ)⦄
    (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε) (h_closed : IsClosed ↑(K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n : Set (Fin 2 → ℝ)) ↑K ≠ ⊤)
    (x : (k : Fin 2 → ℝ) → k ∈ ↑K → ℕ → Fin 2 → ℝ)
    (h_seg_subset_n : ∀ (k : Fin 2 → ℝ) (hk : k ∈ ↑K) (n : ℕ), segment01 (x k hk n 0) (x k hk n 1) ⊆ ↑(Pₙ n)) :
    let A := {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K};
    A = {p | p ∈ Icc ![-1, -1] ![1, 1] ∧ segment01 (p 0) (p 1) ⊆ ↑K} →
      A ⊆ Icc ![-1, -1] ![1, 1] →
        ∀ (k : Fin 2 → ℝ) (hk : k ∈ ↑K),
          ∀ x_lim ∈ Icc ![-1, -1] ![1, 1],
            ∀ (φ : ℕ → ℕ),
              StrictMono φ →
                Tendsto (x k hk ∘ φ) atTop (𝓝 x_lim) →
                  let L := segment01 (x_lim 0) (x_lim 1);
                  L = segment01 (x_lim 0) (x_lim 1) →
                    (∀ (j : ℕ), segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) ⊆ ↑(Pₙ (φ j))) →
                      Tendsto (fun j ↦ hausdorffDist (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) L) atTop (𝓝 0)
                        → segment01 (x_lim 0) (x_lim 1) ⊆ ↑K := by
  intro A hA hA_sub k hk x_lim hx_lim_mem φ hφ hφ_lim L hL hS_sub hS_lim
  intro y hyL
  set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) with hS
  have h_exist : ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
    intro j
    have := exists_point_on_segment01_within_HD
      (a := x_lim 0) (b := x_lim 1)
      (a' := x k hk (φ j) 0) (b' := x k hk (φ j) 1)
      (y := y) (hy := by simpa [hL] using hyL)
    rcases this with ⟨q, hqS, hq_le⟩
    exact ⟨q, hqS, by simpa [hL] using hq_le⟩

  choose q hqS hq_le using h_exist

  have hqP : ∀ j, q j ∈ (Pₙ (φ j) : Set (Fin 2 → ℝ)) := by
    intro j
    exact hS_sub j (hqS j)

  have hHD_LS :
      Tendsto (fun j ↦ hausdorffDist L (S j)) atTop (𝓝 0) := by
    simpa [hausdorffDist_comm] using hS_lim
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
      · exact h_seg_subset_n k hk (φ j) (hqS j)
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

theorem Besicovitch.P_col'_IsClosed.extracted_1_3
    ⦃Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)⦄ ⦃K : NonemptyCompacts (Fin 2 → ℝ)⦄
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection')
    (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε) (h_closed : IsClosed (K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) (pₙ : (k : Fin 2 → ℝ) → k ∈ K → ℕ → Fin 2 → ℝ)
    (hpₙ_mem : ∀ (k : Fin 2 → ℝ) (a : k ∈ K) (n : ℕ), pₙ k a n ∈ Pₙ n)
    (h_tendsto : ∀ (k : Fin 2 → ℝ) (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k)) :
    ∃ A ⊆ Icc ![-1, -1] ![1, 1], ↑K = ⋃ p ∈ A, segment01 (p 0) (p 1) := by
  have h_seg_exists : ∀ (k : Fin 2 → ℝ) (hk : k ∈ (K : Set (Fin 2 → ℝ))) (n : ℕ), ∃ (x : Fin 2 → ℝ), x ∈ Icc ![-1,-1] ![1,1] ∧ pₙ k hk n ∈ segment01 (x 0) (x 1) ∧ segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
      intro k hk n
      rcases h_mem n with ⟨_, _, ⟨A, hA_sub, hA_eq⟩, _⟩
      have : pₙ k hk n ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
        rw [←hA_eq]
        exact hpₙ_mem k hk n
      rcases mem_iUnion₂.1 this with ⟨p, hpA, hp_seg⟩
      let x : Fin 2 → ℝ := ![p 0, p 1]
      have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
        simpa [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, x] using hA_sub hpA
      have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
        intro y hy
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          x] at hy
        have : y ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
          apply mem_iUnion₂.2
          use p
        rwa [←hA_eq] at this
      exact ⟨x, hx, hp_seg, hsub⟩

  choose x hx h_pn_in_seg_n h_seg_subset_n using h_seg_exists

  set A : Set (Fin 2 → ℝ) := { p | p ∈ Icc ![-1,-1] ![1,1] ∧ segment01 (p 0) (p 1) ⊆ (K : Set (Fin 2 → ℝ)) } with hA

  have hA_sub : A ⊆  Icc ![-1, -1] ![1, 1] := by
    rintro p ⟨hp_in, _⟩
    exact hp_in

  refine ⟨A, hA_sub, ?_⟩
  ext k
  constructor
  · intro hk
    obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq (hx k hk)
    set L := segment01 (x_lim 0) (x_lim 1) with hL

    have h_seg_j_P : ∀ j, segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) ⊆ Pₙ (φ j) := by
      intro j y hy
      apply h_seg_subset_n
      exact hy

    have h_seg_HD0 : Tendsto (fun j ↦ hausdorffDist (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) L) atTop (𝓝 0) := by
      apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
      all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]

    observe h_L_compact : IsCompact L
    refine mem_iUnion.2 ?_
    refine ⟨x_lim, ?_⟩
    refine mem_iUnion.2 ?_
    refine ⟨?hxlim_in_A, ?k_in_L⟩
    have hLsubK : L ⊆ (K : Set _) := by
      intro y hyL
      set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) with hS
      have h_exist :
          ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
        intro j
        have := exists_point_on_segment01_within_HD
          (a := x_lim 0) (b := x_lim 1)
          (a' := x k hk (φ j) 0) (b' := x k hk (φ j) 1)
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
          · exact h_seg_subset_n k hk (φ j) (hqS j)
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
          · exact h_pn_in_seg_n k hk (φ i)
          · exact hausdorffEdist_ne_top_segment01 (x k hk (φ i) 0) (x k hk (φ i) 1) (x_lim 0) (x_lim 1)
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
  · intro hk_union
    rcases mem_iUnion₂.1 hk_union with ⟨p, hpA, hk_seg⟩
    rw [hA] at hpA
    rcases hpA with ⟨_, hseg_sub⟩
    exact hseg_sub hk_seg

theorem Besicovitch.P_col'_IsClosed.extracted_1_7 ⦃Pₙ : ℕ → NonemptyCompacts (Fin 2 → ℝ)⦄ ⦃K : NonemptyCompacts (Fin 2 → ℝ)⦄
    (h_mem : ∀ (n : ℕ), Pₙ n ∈ P_collection')
    (h_lim : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (Pₙ n) K < ε) (h_closed : IsClosed (K : Set (Fin 2 → ℝ)))
    (fin_dist : ∀ (n : ℕ), EMetric.hausdorffEdist ↑(Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤) :
     ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂, x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ ↑K := by
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

theorem P_col'_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := P_collection.isBounded (h_mem n)
  have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ :=
    hausdorffEdist_ne_top_of_nonempty_of_bounded (Pₙ n).nonempty K.nonempty (hPn_bdd n) hK_bdd

  have : ∀ k ∈ K, ∀ n, ∃ p ∈ Pₙ n, dist p k ≤ dist K (Pₙ n) := by
    intro k hk n
    simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
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

  choose pₙ hpₙ_mem hpₙ_lt using this

  -- extract_goal
  have h_tendsto : ∀ (k : Fin 2 → ℝ) (hk : k ∈ K), Tendsto (fun n ↦ pₙ k hk n) atTop (𝓝 k) := by
    intro k hk
    rw [NormedAddCommGroup.tendsto_atTop']
    intro ε hε
    obtain ⟨N, hN⟩ := h_lim ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h_le : dist (pₙ k hk n) k ≤ dist K (Pₙ n) := hpₙ_lt k hk n
    have h_small : dist K (Pₙ n) < ε := by
      simpa [dist_comm] using hN n (Nat.le_of_lt hn)
    exact lt_of_le_of_lt h_le h_small

  have h_sub : (K : Set _) ⊆ rectangle := by
    have hP_sub : ∀ n, (Pₙ n : Set _) ⊆ rectangle := by
      intro n
      rcases h_mem n with ⟨_, h_subset, _, _⟩
      exact h_subset
    have rect_closed : IsClosed rectangle := by
      rw [rectangle]
      exact isClosed_Icc

    -- Main argument
    intro k' hk'
    by_contra h_notin

    have h_pos : 0 < Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) := by
      have h_ne : Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) ≠ 0 := by
        intro h_eq
        have h_cl : k' ∈ closure (rectangle : Set (Fin 2 → ℝ)) := by
          rw [Metric.mem_closure_iff_infDist_zero]
          · exact h_eq
          · dsimp [rectangle]
            refine ⟨![0, 0], by simp [Pi.le_def, Fin.forall_fin_two]⟩
        have : k' ∈ rectangle := by
          simpa [rect_closed.closure_eq] using h_cl
        exact h_notin this
      exact lt_of_le_of_ne Metric.infDist_nonneg h_ne.symm

    set d : ℝ := Metric.infDist k' (rectangle : Set (Fin 2 → ℝ)) with hd
    have h_half_pos : 0 < d / 2 := by linarith
    obtain ⟨N, hN⟩ := h_lim (d / 2) h_half_pos

    have h_haus : hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ N : Set _) < d / 2 := by
      have : dist (Pₙ N) K < d / 2 := hN N (le_rfl)
      simpa [Metric.NonemptyCompacts.dist_eq, dist_comm] using this

    have h_edist_ne : EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ N : Set _) ≠ ⊤ := by
      simpa [EMetric.hausdorffEdist_comm] using fin_dist N

    obtain ⟨y, hyP, hy_lt⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hk' h_haus h_edist_ne

    have hy_rect : y ∈ rectangle := (hP_sub N) hyP

    have hd_le : d ≤ dist k' y := by
      have h_le := Metric.infDist_le_dist_of_mem (x := k') hy_rect
      simpa [hd] using h_le

    have : dist k' y < d := by
      have : dist k' y < d / 2 := hy_lt
      exact lt_of_lt_of_le this (by linarith)
    exact (not_lt_of_ge hd_le) this

  have h_union : ∃ A ⊆ Icc ![-1, -1] ![1, 1], K = ⋃ p ∈ A, segment01 (p 0) (p 1) := by
    have h_seg_exists : ∀ (k : Fin 2 → ℝ) (hk : k ∈ (K : Set (Fin 2 → ℝ))) (n : ℕ), ∃ (x : Fin 2 → ℝ), x ∈ Icc ![-1,-1] ![1,1] ∧ pₙ k hk n ∈ segment01 (x 0) (x 1) ∧ segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
      intro k hk n
      rcases h_mem n with ⟨_, _, ⟨A, hA_sub, hA_eq⟩, _⟩
      have : pₙ k hk n ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
        rw [←hA_eq]
        exact hpₙ_mem k hk n
      rcases mem_iUnion₂.1 this with ⟨p, hpA, hp_seg⟩
      let x : Fin 2 → ℝ := ![p 0, p 1]
      have hx : x ∈ Icc ![-1, -1] ![1, 1] := by
        simpa [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, x] using hA_sub hpA
      have hsub : segment01 (x 0) (x 1) ⊆ (Pₙ n : Set _) := by
        intro y hy
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          x] at hy
        have : y ∈ ⋃ p ∈ A, segment01 (p 0) (p 1) := by
          apply mem_iUnion₂.2
          use p
        rwa [←hA_eq] at this
      exact ⟨x, hx, hp_seg, hsub⟩

    choose x hx h_pn_in_seg_n h_seg_subset_n using h_seg_exists

    set A : Set (Fin 2 → ℝ) := { p | p ∈ Icc ![-1,-1] ![1,1] ∧ segment01 (p 0) (p 1) ⊆ (K : Set (Fin 2 → ℝ)) } with hA

    have hA_sub : A ⊆  Icc ![-1, -1] ![1, 1] := by
      rintro p ⟨hp_in, _⟩
      exact hp_in

    refine ⟨A, hA_sub, ?_⟩
    ext k
    constructor
    · intro hk
      obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq (hx k hk)
      set L := segment01 (x_lim 0) (x_lim 1) with hL

      have h_seg_j_P : ∀ j, segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) ⊆ Pₙ (φ j) := by
        intro j y hy
        apply h_seg_subset_n
        exact hy

      have h_seg_HD0 : Tendsto (fun j ↦ hausdorffDist (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) L) atTop (𝓝 0) := by
        apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
        all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]
      observe h_L_compact : IsCompact L
      refine mem_iUnion.2 ?_
      refine ⟨x_lim, ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?hxlim_in_A, ?k_in_L⟩
      have hLsubK : L ⊆ (K : Set _) := by
        intro y hyL
        set S : ℕ → Set (Fin 2 → ℝ) := fun j ↦ segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) with hS
        have h_exist :
            ∀ j, ∃ q ∈ S j, dist q y ≤ hausdorffDist L (S j) := by
          intro j
          have := exists_point_on_segment01_within_HD
            (a := x_lim 0) (b := x_lim 1)
            (a' := x k hk (φ j) 0) (b' := x k hk (φ j) 1)
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
            · exact h_seg_subset_n k hk (φ j) (hqS j)
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
            · exact h_pn_in_seg_n k hk (φ i)
            · exact hausdorffEdist_ne_top_segment01 (x k hk (φ i) 0) (x k hk (φ i) 1) (x_lim 0) (x_lim 1)
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
    · intro hk_union
      rcases mem_iUnion₂.1 hk_union with ⟨p, hpA, hk_seg⟩
      rw [hA] at hpA
      rcases hpA with ⟨_, hseg_sub⟩
      exact hseg_sub hk_seg

  -- PROPERTY 2

  have h_forall : ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂, x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ K := by
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

  exact ⟨h_closed, h_sub, h_union, h_forall⟩

-- https://proofwiki.org/wiki/Subspace_of_Complete_Metric_Space_is_Closed_iff_Complete
/-- The space `P_collection'` is complete. -/
theorem CompleteSpace_P_collection' : CompleteSpace P_collection' :=
  IsClosed.completeSpace_coe P_col'_IsClosed

/-- The space `P_collection'` has the Baire property. -/
theorem BaireSpace_P_collection' [CompleteSpace P_collection'] : BaireSpace P_collection' :=
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

-- /-- Nonemptiness of `𝒫(v, ε)` for every `v, ε > 0`. -/
-- theorem P_v_eps'.nonempty {v ε : ℝ} (hε : 0 < ε) :
--     (P_v_eps' v ε).Nonempty := by
--   -- choose the vertical segment at `x = 0`
--   sorry

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

/-- Rectangle ⊆ its `η`-expansion. -/
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

/-- If every `r ∈ R` is an axis rectangle, we can *choose* parameters for each of them. -/
lemma choose_axis_params
    {R : Finset (Set (Fin 2 → ℝ))}
    (h_rects : ∀ r ∈ R, ∃ a b c d : ℝ, r = axisRect a b c d) :
    ∃ (a b c d : ∀ r, r ∈ R → ℝ), ∀ r (hr : r ∈ R), r = axisRect (a r hr) (b r hr) (c r hr) (d r hr) := by
  have H : ∀ r ∈ R, ∃ t : ℝ × ℝ × ℝ × ℝ,
      r = axisRect t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    intro r hr
    rcases h_rects r hr with ⟨a,b,c,d,hr'⟩
    exact ⟨(a,b,c,d), by simp [hr']⟩
  choose t ht using H
  let a : ∀ r, r ∈ R → ℝ := fun r hr => (t r hr).1
  let b : ∀ r, r ∈ R → ℝ := fun r hr => (t r hr).2.1
  let c : ∀ r, r ∈ R → ℝ := fun r hr => (t r hr).2.2.1
  let d : ∀ r, r ∈ R → ℝ := fun r hr => (t r hr).2.2.2
  refine ⟨a,b,c,d,?_⟩
  intro r hr; simpa [a,b,c,d] using ht r hr

theorem P_v_eps_open {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsOpen (P_v_eps' v ε) := by
  rw [Metric.isOpen_iff]
  intro P hP
  rcases hP with ⟨R, h_rects, h_cover, h_len⟩
  rcases choose_axis_params h_rects with ⟨a,b,c,d,hr⟩
  sorry
  -- choose a b c d h_abcd using h_rects
  -- set R' : Finset (Set (Fin 2 → ℝ)) := {axisRectExpand η a b c d} with hR'
  -- refine ⟨R', ?_, ?_, ?_⟩
  -- · sorry
  -- · sorry
  -- · sorry

theorem P_v_eps_dense {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (P_v_eps' v ε) := by
  sorry

theorem P_v_eps_compl_nowhereDense {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsClosed (P_v_eps' v ε)ᶜ ∧ IsNowhereDense (P_v_eps' v ε)ᶜ := by
  simp_rw [isClosed_isNowhereDense_iff_compl, compl_compl]
  exact ⟨P_v_eps_open hv₀ hv₁ hε, P_v_eps_dense hv₀ hv₁ hε⟩

theorem extra_exists_seq_strictAnti_tendsto :
    ∃ φ : ℕ → ℝ≥0,
      StrictAnti φ
      ∧ (∀ n, φ n ∈ Set.Ioo 0 1)
      ∧ Tendsto φ atTop (𝓝 0)
      ∧ (∀ n r, r ∈ Finset.range n → 0 ≤ (r : ℝ≥0) * φ n)
      ∧ (∀ n r, r ∈ Finset.range n → (r : ℝ≥0) * φ n ≤ 1) := by
  -- Start from any strictly decreasing sequence in (0,1) → 0.
  obtain ⟨φ', h₁φ', h₂φ', h₃φ'⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)

  -- helper sequences
  let ψ : ℕ → ℝ≥0 := fun k ↦ min (φ' k) (1 / (k+1 : ℝ≥0))
  let s  : ℕ → ℝ≥0 := fun k ↦ 1 / (k+2 : ℝ≥0)
  let φ  : ℕ → ℝ≥0 := fun k ↦ ψ k * s k

  -- 1) `ψ` is antitone (min of two antitone sequences)
  have h_ant_one_div : Antitone (fun k : ℕ ↦ (1 : ℝ≥0) / (k+1)) := by
    intro a b hle
    -- use ℝ lemma and cast back
    have hle' : (a+1 : ℝ) ≤ (b+1 : ℝ) := by exact_mod_cast add_le_add_right hle 1
    have hpos : (0 : ℝ) < (a+1 : ℝ) := by exact_mod_cast Nat.succ_pos a
    have : 1 / (b+1 : ℝ) ≤ 1 / (a+1 : ℝ) := one_div_le_one_div_of_le hpos hle'
    exact_mod_cast this
  have h_ant_ψ : Antitone ψ := by
    intro a b hle
    have h1 : φ' b ≤ φ' a := (h₁φ'.antitone) hle
    have h2 : (1 : ℝ≥0) / (b+1) ≤ 1 / (a+1) := h_ant_one_div hle
    exact min_le_min h1 h2

  -- 2) `s` is strictly decreasing and positive
  have hs_pos : ∀ k, 0 < s k := by
    intro k
    -- in ℝ: 0 < 1/(k+2), then cast
    have : (0 : ℝ) < 1 / (k+2 : ℝ) := by
      have hk : (0 : ℝ) < (k+2 : ℝ) := by exact_mod_cast Nat.succ_pos (k+1)
      simpa using (one_div_pos.mpr hk)
    exact this
  have h_strict_s : StrictAnti s := by
    intro a b hab
    -- in ℝ: 1/(b+2) < 1/(a+2), then cast
    have : (1 : ℝ) / (b+2 : ℝ) < 1 / (a+2 : ℝ) := by
      have hlt : (a+2 : ℝ) < (b+2 : ℝ) := by exact_mod_cast add_lt_add_right hab 2
      have hpos : (0 : ℝ) < (a+2 : ℝ) := by exact_mod_cast Nat.succ_pos (a+1)
      simpa using one_div_lt_one_div_of_lt hpos hlt
    exact this

  -- 3) `ψ` is strictly positive
  have hψ_pos : ∀ k, 0 < ψ k := by
    intro k
    have hφ'pos : 0 < φ' k := (h₂φ' k).1
    have honepos : 0 < (1 : ℝ) / (k+1 : ℝ) := by
      have hk : (0 : ℝ) < (k+1 : ℝ) := by exact_mod_cast Nat.succ_pos k
      simpa using (one_div_pos.mpr hk)
    -- cast and use `lt_min_iff`
    have : 0 < min (φ' k : ℝ) (1 / (k+1 : ℝ)) := by
      simpa [lt_min_iff] using And.intro (show (0 : ℝ) < φ' k by exact_mod_cast hφ'pos) honepos
    exact this

  -- 4) Put together: φ is strictly decreasing
  have h_strict : StrictAnti φ := by
    intro a b hab
    -- ψ b * s b ≤ ψ a * s b < ψ a * s a
    have step1 :
        ψ b * s b ≤ ψ a * s b :=
      mul_le_mul_of_nonneg_right (h_ant_ψ (le_of_lt hab)) (le_of_lt (hs_pos b))
    have step2 :
        ψ a * s b < ψ a * s a :=
      mul_lt_mul_of_pos_left (h_strict_s hab) (hψ_pos a)
    exact lt_of_le_of_lt step1 step2

  -- 5) φ(n) in (0,1)
  have hψ_le_one : ∀ k, ψ k ≤ 1 := by
    intro k
    -- ψ k ≤ φ' k < 1
    exact (le_trans (min_le_left _ _) (le_of_lt (h₂φ' k).2))
  have hφ_inIoo : ∀ k, φ k ∈ Set.Ioo 0 1 := by
    intro k
    have hlt1 : ψ k * s k ≤ 1 * s k :=
      mul_le_mul_of_nonneg_right (hψ_le_one k) (le_of_lt (hs_pos k))
    have hlt2 : ψ k * s k < 1 := by
      have : ψ k * s k ≤ s k := by simpa [one_mul] using hlt1
      exact lt_of_le_of_lt this (by
        -- s k ≤ 1/2 < 1, so φ k ≤ s k < 1
        have : (s k : ℝ) ≤ (1 / 2 : ℝ) := by
          -- cast and compare 1/(k+2) ≤ 1/2
          have hk : (2 : ℝ) ≤ (k+2 : ℝ) := by exact_mod_cast add_le_add_right (Nat.succ_le_succ (Nat.zero_le k)) 1
          -- have hpos : (0 : ℝ) < (2 : ℝ) := by norm_num
          exact one_div_le_one_div_of_le (by linarith) (hk)
          -- simpa using (one_div_le_one_div_of_le hpos hk)
        have : s k ≤ (1 / (2 : ℝ≥0)) := by exact_mod_cast this
        have : (s k : ℝ≥0) < 1 := lt_of_le_of_lt this (by norm_num)
        simpa using this)
      -- (the previous block shows `s k ≤ 1/2 < 1` hence `φ k ≤ s k < 1`)
    exact ⟨by
             -- 0 < φ k
             have : (0 : ℝ) < (ψ k : ℝ) * (s k : ℝ) := by
               have h1 : (0 : ℝ) < ψ k := by exact_mod_cast (hψ_pos k)
               have h2 : (0 : ℝ) < s k  := by exact_mod_cast (hs_pos k)
               simpa using (mul_pos h1 h2)
             exact_mod_cast this,
           hlt2⟩

  -- 6) Tendsto φ → 0 (squeeze by 0 ≤ φ ≤ s and s → 0)
  have hs_tendsto_real : Tendsto (fun k : ℕ ↦ (s k : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    -- standard lemma on ℝ: 1/(k+2) → 0
    simp_rw [s]
    have hs0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ ↦ 1 / (↑(n + 2) : ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_add_atTop_iff_nat 2).2 (_root_.tendsto_const_div_atTop_nhds_zero_nat 1)
      simpa [Nat.cast_add, Nat.cast_ofNat] using h
    simpa [tendsto_one_div_add_atTop_nhds_zero_nat] using hs0
  have hs_tendsto : Tendsto s atTop (𝓝 (0 : ℝ≥0)) := by
    -- coercion ℝ≥0 → ℝ is an embedding; rewrite via `simp`
    simpa using (NNReal.tendsto_coe.1 hs_tendsto_real)
  have hφ_le_s : ∀ᶠ k in atTop, φ k ≤ s k := by
    filter_upwards [Eventually.of_forall fun k ↦ (mul_le_mul_of_nonneg_right (hψ_le_one k) (le_of_lt (hs_pos k)))]
    intro k hk
    aesop
  have hφ_nonneg : ∀ᶠ k in atTop, (0 : ℝ≥0) ≤ φ k := by
    apply Eventually.of_forall
    intro x
    specialize hφ_inIoo x
    exact zero_le (φ x)
  have htend : Tendsto φ atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0)) atTop (𝓝 0))  -- lower bound g → 0
    hs_tendsto                                                     -- upper bound h = s → 0
    hφ_nonneg                                                      -- eventually 0 ≤ φ
    hφ_le_s                                                        -- eventually φ ≤ s
  · -- derive `0 ≤ φ k` pointwise (used just above)
    refine ?_  -- This is resolved by `le_of_lt (hφ_inIoo _).1` inline, kept above.
  -- 7) hv0 and hv1
    have hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ (r : ℝ≥0) * φ n := by
      intro n r _; simp   -- nonnegativity in ℝ≥0
    have hv1 : ∀ n r, r ∈ Finset.range n → (r : ℝ≥0) * φ n ≤ 1 := by
      intro n r hr
      have hrlt : r < n := Finset.mem_range.1 hr
      have hrle : (r : ℝ≥0) ≤ n := by exact_mod_cast (le_of_lt hrlt)
      -- r*φ ≤ r*s ≤ n*s ≤ (n+2)*s = 1
      have h1 : (r : ℝ≥0) * φ n ≤ (r : ℝ≥0) * s n := by
        -- since ψ n ≤ 1
        have := mul_le_mul_of_nonneg_left (by
          have := (hψ_le_one n)
          exact (mul_le_of_le_one_right (le_of_lt (hs_pos n)) this)) (by simp : (0 : ℝ≥0) ≤ r)
        -- streamline:
        -- simply: (r * (ψ n * s n)) ≤ (r * (1 * s n))
        have : (r : ℝ≥0) * (ψ n * s n) ≤ (r : ℝ≥0) * (1 * s n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hψ_le_one n) (le_of_lt (hs_pos n)))
            (by simp)
        simpa [φ, one_mul, mul_assoc] using this
      have h2 : (r : ℝ≥0) * s n ≤ (n : ℝ≥0) * s n :=
        mul_le_mul_of_nonneg_right hrle (le_of_lt (hs_pos n))
      have h3 : (n : ℝ≥0) * s n ≤ ((n+2 : ℕ) : ℝ≥0) * s n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n 2) (le_of_lt (hs_pos n))
      have h4 : ((n+2 : ℕ) : ℝ≥0) * s n = 1 := by
        -- ((n+2) : ℝ≥0) * (1/(n+2)) = 1
        have hne : ((n+2 : ℕ) : ℝ≥0) ≠ 0 := by simp
        simp [s, one_div]
      exact (le_trans (le_trans h1 h2) (by rw [h4] at h3; exact h3))
    -- Wrap up
    refine ⟨φ, h_strict, (by intro k; exact hφ_inIoo k), htend, hv0, hv1⟩

/-- TO DO -/
def Pn (φ : ℕ → ℝ≥0) (n : ℕ) : Set P_collection' :=
  ⋂ r ∈ Finset.range n, P_v_eps' ((r : ℝ) * (φ n : ℝ)) (φ n : ℝ)

variable (φ : ℕ → ℝ≥0)

lemma isOpen_Pn (n : ℕ)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    IsOpen (Pn φ n) := by
  rw [Pn]
  refine isOpen_biInter_finset ?_
  intro r hr
  exact P_v_eps_open (hv0 n r hr) (hv1 n r hr) ((hφ n).1)

lemma measure_Pn (n : ℕ) (P : P_collection') (hP : P ∈ Pn φ n) (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ∀ u ∈ Icc (0 : ℝ) 1, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal ≤ 100 * φ n := by
  intro u hu
  simp_rw [Pn, Finset.mem_range, mem_iInter, P_v_eps', hasThinCover, hSlice, window] at hP
  simp_rw [hSlice]
  sorry
  -- exact (ENNReal.toReal_mono hμmono).trans_lt.this.le

def Pstar (φ : ℕ → ℝ≥0) : Set P_collection' := ⋂ n : ℕ, Pn φ n

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

variable [BaireSpace P_collection']

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
    exact P_v_eps_open (hv0 n i hi) (hv1 n i hi) ((hφ n).1)
  · apply dense_iInter_of_isOpen
    all_goals intro hi
    · exact P_v_eps_open (hv0 n i hi) (hv1 n i hi) ((hφ n).1)
    · exact P_v_eps_dense (hv0 n i hi) (hv1 n i hi) ((hφ n).1)

--(h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))

-- include h₁φ h₂φ

-- Is this necessary?
-- theorem P_v_eps'_not_meagre {v ε : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (hε : 0 < ε) :
--     ¬ IsMeagre (P_v_eps' v ε) :=
--   not_isMeagre_of_isOpen (P_v_eps_open h0 h1 hε) (P_v_eps'_nonempty h0 h1 hε)

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

def E_set : Set P_collection' := {P | ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin 2 → ℝ)) u) = 0}

lemma Pstar_sub_E_set
    (h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n) (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    Pstar φ ⊆ E_set := by
  intro P hP u hu
  -- refine le_antisymm ?_ (by positivity)
  have bound : ∀ n, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal ≤ 100 * φ n := by
    intro n
    apply measure_Pn
    · rw [Pstar, mem_iInter] at hP
      exact hP n
    · exact fun n r a ↦ hv0 n r a
    · exact fun n r a ↦ hv1 n r a
    · exact hu
  have lim : Tendsto (fun n ↦ 100 * φ n) atTop (𝓝 0) := by
    simpa [zero_mul] using (tendsto_const_nhds.mul h₃φ)
  sorry

theorem thm2_5
    (h : Pstar φ ⊆ E_set)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) : ¬ IsMeagre E_set := by
  intro hM
  apply IsMeagre.mono at h
  · exact (Pstar_notMeagre φ hφ hv0 hv1) h
  · exact hM

def P_zero_vol : Set P_collection' := {P | volume (P : Set (Fin 2 → ℝ)) = 0}

lemma aux {P : Set (ℝ × ℝ)} (hP : P ⊆ Icc (-1, 0) (1, 1))
    (hP' : ∀ y ∈ Icc 0 1, volume {x ∈ Icc (-1) 1 | (x, y) ∈ P} = 0) :
    volume P = 0 := by
  sorry

lemma mem_prod_Icc_of_mem_P {P : P_collection'} {p : ℝ × ℝ}
    (hp : (Fin.cons p.1 (Fin.cons p.2 finZeroElim) : Fin 2 → ℝ) ∈ (P : Set (Fin 2 → ℝ))) :
    p ∈ Icc (-1,0) (1,1) := by
  -- `P ⊆ rectangle`, so this vector lies in `rectangle`
  have hmem := P.property.2.1 hp
  -- rectangle = {q | q 0 ∈ Icc 0 1 ∧ q 1 ∈ Icc 0 1}
  simp only [rectangle, mem_Icc] at hmem
  rcases hmem with ⟨hx, hy⟩
  simp only [Pi.le_def, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.forall_fin_two, Fin.isValue,
    Matrix.cons_val_zero, Fin.cons_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.cons_one] at hx hy
  constructor
  · exact hx
  · exact hy

theorem E_sub_P_zero_vol : E_set ⊆ P_zero_vol := by
  intro P hP
  simp_rw [P_zero_vol, mem_setOf_eq, ← MeasureTheory.setLIntegral_one]
  have := (MeasureTheory.measurePreserving_finTwoArrow (volume : Measure ℝ))
  rw [← MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.volume_pi] at this
  rw [← this.symm.setLIntegral_comp_preimage_emb]
  apply le_antisymm _ (by positivity)
  simp only [MeasurableEquiv.finTwoArrow_symm_apply, lintegral_const, MeasurableSet.univ,
    Measure.restrict_apply, univ_inter, one_mul, nonpos_iff_eq_zero]
  apply aux
  · intro p hp
    exact mem_prod_Icc_of_mem_P hp
  · intro y hy
    have : volume (hSlice (↑↑P) y) = 0 := (hP : ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (↑↑P) u) = 0) y hy
    have hset :
    {x | x ∈ Icc 0 1 ∧ (x, y) ∈ (fun p : ℝ × ℝ ↦ Fin.cons p.1 (Fin.cons p.2 finZeroElim)) ⁻¹' (P : Set (Fin 2 → ℝ)) }
      = {x | x ∈ Icc 0 1 ∧ (![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _) } := by
      ext x
      simp only [mem_Icc, Nat.reduceAdd, mem_preimage, SetLike.mem_coe, mem_setOf_eq,
        Nat.succ_eq_add_one, and_congr_right_iff, and_imp]
      intro hx0 hx1
      constructor
      all_goals
        intro h
        exact h
    have hsubset :
    {x | x ∈ Icc (-1 : ℝ) 1 ∧ (![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _) }
      ⊆ {x | (![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _) } := by
      intro x hx
      exact hx.2
    have hslice_zero : volume {x | (![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _) } = 0 := by
      simpa [hSlice] using this
    -- A subset of a null set is null
    have : volume {x | x ∈ Icc (-1 : ℝ) 1 ∧ (![x,y] : Fin 2 → ℝ) ∈ (↑↑P : Set _) } = 0 :=
      measure_mono_null hsubset hslice_zero
    simpa [hset]
  · exact MeasurableEquiv.measurableEmbedding MeasurableEquiv.finTwoArrow.symm

  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.html#MeasureTheory.lintegral_const
  -- rw [MeasureTheory.Measure.volume_eq_prod]
  -- Fubini argument?


/-- The set of `P ∈ 𝒫` with Lebesgue measure zero is of second category in `(𝒫, d)`. -/
theorem theorem_2_3
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ n r, r ∈ Finset.range n → 0 ≤ r * φ n)
    (hv1 : ∀ n r, r ∈ Finset.range n → r * φ n ≤ 1) :
    ¬ IsMeagre P_zero_vol := by
  intro h

  sorry
  -- exact (thm2_5 φ (Pstar_sub_E_set φ)) (h.mono E_sub_P_zero_vol)

theorem Exists_P0 (φ : ℕ → ℝ≥0) : P_zero_vol.Nonempty := by
  apply nonempty_of_not_isMeagre
  apply theorem_2_3
  all_goals sorry
  -- nonempty_of_not_isMeagre (theorem_2_3 φ)

end

end

end Besicovitch

section

open Besicovitch ENNReal NNReal MeasureTheory Measure Filter Topology EMetric

/-- Any Kakeya set in `ℝ` contains a closed unit‐length interval. -/
lemma kakeya_contains_unit_Icc {K : Set ℝ} (hK : IsKakeya K) :
    ∃ x₀, Icc x₀ (x₀ + 1) ⊆ K := by
  have := hK 1 (by simp)
  -- simp only [segment_eq_Icc, norm_one] at this
  rcases this with ⟨x₀, hseg⟩
  exact ⟨x₀, by simpa using hseg⟩

/-- Any closed interval of length 1 has Hausdorff dimension 1. -/
lemma dimH_Icc_length_one (a : ℝ) :
    dimH (Icc a (a + 1)) = 1 := by
  have h : (interior (Icc a (a + 1))).Nonempty := by simp [interior_Icc]
  calc
    dimH (Icc a (a + 1)) = Module.finrank ℝ ℝ := Real.dimH_of_nonempty_interior h
    _ = 1 := by simp

/-- If a set contains some unit interval, then its `dimH ≥ 1`. -/
lemma dimH_of_contains_Icc {K : Set ℝ} {x₀} (h : Icc x₀ (x₀ + 1) ⊆ K) :
    1 ≤ dimH K := by
  calc
    1 = dimH (Icc x₀ (x₀ + 1)) := (dimH_Icc_length_one x₀).symm
    _ ≤ dimH K := dimH_mono h

/-- Any subset of `ℝ` has `dimH ≤ 1`. -/
lemma dimH_le_one_univ : ∀ (K : Set ℝ), dimH K ≤ 1 := fun K ↦ by
  calc
    dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = Module.finrank ℝ ℝ := by simp [dimH_univ]
    _ = 1 := by simp

/-- Any Kakeya set in `ℝ` has full Hausdorff dimension. -/
theorem isKakeya.dimH_eq_one (K : Set ℝ) (hK : IsKakeya K) :
    dimH K = 1 := by
  rcases kakeya_contains_unit_Icc hK with ⟨x₀, hsub⟩
  exact le_antisymm (dimH_le_one_univ K) (dimH_of_contains_Icc hsub)

-- This result has been formalised by Bhavik Mehta in a private repository,
-- and will soon be added to Mathlib

/-- For any set `E` and any nonnegative `s : ℝ`, there exists a Gδ set `G` containing `E`
with the same `s`-dimensional Hausdorff measure. -/
theorem exists_Gδ_superset_hausdorffMeasure_eq {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    ∃ G : Set X, IsGδ G ∧ E ⊆ G ∧ μH[s] G = μH[s] E := by
  sorry

/-- A subset of `ℝⁿ` has finite Hausdorff dimension. -/
theorem dimH_lt_top {n : ℕ} {A : Set (Fin n → ℝ)} :
    dimH A < ⊤ := by
  calc
    dimH A ≤ dimH (Set.univ : Set (Fin n → ℝ)) := dimH_mono (by simp)
    _ = n := dimH_univ_pi_fin n
    _ < ⊤ := by simp

theorem dimH_ne_top {n : ℕ} {A : Set (Fin n → ℝ)} : dimH A ≠ ⊤ := by
  simpa using (lt_top_iff_ne_top).1 dimH_lt_top

/-- For any subset `A` of `ℝⁿ` there is a G₀‐set `G` with `A ⊆ G` and `dimH G = dimH A`. -/
theorem exists_Gδ_of_dimH {n : ℕ} (A : Set (Fin n → ℝ)) :
    ∃ G : Set (Fin n → ℝ), IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
  observe dimHA_ne_top : dimH A ≠ ⊤
  observe dimHA_nt_top : dimH A < ⊤
  generalize hA : dimH A = DA
  have : DA ≠ ⊤ := Ne.symm (ne_of_ne_of_eq (id (Ne.symm dimHA_ne_top)) hA)
  lift DA to ℝ≥0 using this
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right
      (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  choose G' hG'_Gδ subG' meas_eq' using
    fun k : ℕ ↦ exists_Gδ_superset_hausdorffMeasure_eq (coe_nonneg (DA + φ k)) A
  let G := ⋂ k, G' k
  have iGδ : IsGδ G := IsGδ.iInter fun k ↦ hG'_Gδ k
  have Asub : A ⊆ G := subset_iInter fun k ↦ subG' k
  have hge : dimH A ≤ dimH G := dimH_mono Asub
  have hle : dimH G ≤ dimH A := dimH_le fun d' hd' ↦ by
    by_contra! hgt
    have hd_pos : 0 < (d' : ℝ≥0) - DA := by aesop
    rw [Metric.tendsto_atTop] at h₃φ
    rcases h₃φ _ hd_pos with ⟨k, hφk_lt⟩
    generalize hD : DA + φ k = D
    specialize h₂φ k
    simp only [mem_Ioo] at h₂φ
    cases' h₂φ with hφk_gt_0 hφk_lt_1
    have hlt : DA < D := by
      linear_combination hD + hφk_gt_0
    have hμA : μH[D] A = 0 := by
      apply hausdorffMeasure_of_dimH_lt
      rw [hA]
      norm_cast
    have hμGk : μH[D] (G' k) = 0 := by
      rw [← hD, meas_eq', hD, hμA]
    have hmono : μH[d'] G ≤ μH[D] (G' k) := by
      calc
        μH[d'] G ≤ μH[d'] (G' k) := by
          apply measure_mono
          exact iInter_subset_of_subset k fun ⦃a⦄ a ↦ a
        _ ≤ μH[D] (G' k) := by
          apply hausdorffMeasure_mono
          apply le_of_lt
          rw [← hD]
          simp only [NNReal.coe_add]
          specialize hφk_lt k
          norm_cast
          simp only [ge_iff_le, le_refl, val_eq_coe, dist_lt_coe, nndist_zero_eq_val',
            forall_const] at hφk_lt
          rw [lt_tsub_iff_left] at hφk_lt
          exact hφk_lt
    have h0 : μH[d'] G = 0 := by
      have hbot : μH[d'] G ≤ 0 := by
        apply hmono.trans_eq
        exact hμGk
      exact le_bot_iff.1 hbot
    simp [h0] at hd'
  rw [← hA]
  exact ⟨G, iGδ, Asub, le_antisymm hle hge⟩

/-- If `A ⊆ ℝⁿ` has finite `s`-dimensional Hausdorff measure,
    then for any `k ≤ s` and any `k`-plane `W`, the slices
    `A ∩ (Wᗮ + x)` have finite `(s - k)`-measure for `μH[k]`-almost all `x ∈ W`. -/
theorem hausdorffMeasure_slicing
  (n : ℕ)
  (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
  (s : ℝ) (hs : μH[s] A < ⊤)
  (k : ℕ) (hks : (k : ℝ) ≤ s)
  (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : Module.finrank ℝ W = k)
  (direction : W) (x : W) :
  ∀ᵐ x ∂ (μH[(k : ℝ)]).restrict (W : Set (EuclideanSpace ℝ (Fin n))),
    μH[s - k] (A ∩ (AffineSubspace.mk' x W.orthogonal : Set _)) < ⊤ := by
  sorry

end

section

/--
-/

/-
This section collects the results that were contributed to Mathlib as part of this project.
-/

open Measure

theorem dimH_eq_iInf' {X : Type*}
  [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (s : Set X) :
    dimH s = ⨅ (d : ℝ≥0) (_ : μH[d] s = 0), (d : ℝ≥0∞) := by
  borelize X
  rw [dimH_def]
  apply le_antisymm
  · simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono (le_of_lt hij) s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 : μH[d'] s = 0 := by
      apply hausdorffMeasure_of_dimH_lt
      rw [dimH_def]
      exact hdim_lt
    have hle : (⨅ (d'' : ℝ≥0) (_ : μH[d''] s = 0), (d'' : ℝ≥0∞)) ≤ (d' : ℝ≥0∞) := by
      exact iInf₂_le d' h0
    exact lt_irrefl _ (hlt.trans_le hle)

/--
In a Baire space, every nonempty open set is non‐meagre,
that is, it cannot be written as a countable union of nowhere‐dense sets.
-/
theorem not_isMeagre_of_isOpen' {X : Type*} {s : Set X} [TopologicalSpace X] [BaireSpace X]
  (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ IsMeagre s := by
  intro h
  rcases (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
    with ⟨x, hx, hxc⟩
  exact hxc hx

/-- A set of second category (i.e. non-meagre) is nonempty. -/
lemma nonempty_of_not_IsMeagre' {X : Type*} [TopologicalSpace X] {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using (IsMeagre.empty)

/-- In a nonempty Baire space, any dense `Gδ` set is not meagre. -/
theorem IsGδ_dense_not_meagre' {X : Type*} [Nonempty X] [TopologicalSpace X] [BaireSpace X] {s : Set X} (hs : IsGδ s) (hd : Dense s) : ¬ IsMeagre s := by
  intro h
  rcases (mem_residual).1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact (hts hx₂) hx₁

/-- In a nonempty Baire space, a residual (comeagre) set is not meagre. -/
lemma not_isMeagre_of_mem_residual' {X : Type*} [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] {s : Set X} (hs : s ∈ residual X) :
    ¬ IsMeagre s := by
  -- From `mem_residual`, pick a dense Gδ subset `t ⊆ s`.
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  -- Dense Gδ sets aren’t meagre in a nonempty Baire space.
  -- If `s` were meagre, then so would be `t ⊆ s`, contradiction.
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense htGδ ht_dense (hs_meagre.mono ht_sub)

end
