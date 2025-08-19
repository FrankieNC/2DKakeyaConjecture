/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Bhavik Mehta
-/

import Mathlib

set_option maxHeartbeats 300000

namespace Besicovitch

open Set Real Topology Metric Bornology TopologicalSpace MeasureTheory MetricSpace ENNReal NNReal Filter

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

lemma rectangle_IsBounded : IsBounded rectangle := by simp [rectangle, isBounded_Icc]

lemma rectangle_isClosed : IsClosed rectangle := by
  simpa [rectangle] using (isClosed_Icc : IsClosed (Icc ![(-1 : ℝ), 0] ![1, 1]))

lemma rectangle_convex : Convex ℝ rectangle := by simp [rectangle, convex_Icc]

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
    by refine ⟨![0,0], ?_⟩; simp [rectangle, Pi.le_def, Fin.forall_fin_two]⟩

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
theorem Nonempty_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    P.Nonempty := by
  rcases hP with ⟨-, -, -, h⟩
  rcases h 0 (by norm_num) with ⟨x₁, x₂, -, -, -, hPseg⟩
  exact ⟨![x₁, 0], hPseg <| left_mem_segment _ _ _⟩

theorem IsBounded_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsBounded P := by
  rcases hP with ⟨-, hS, -⟩
  exact rectangle_IsBounded.subset hS

theorem IsCompact_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsCompact P := by
  simpa [isCompact_iff_isClosed_bounded] using ⟨hP.1, IsBounded_P hP⟩

/-- The carrier image of `P_collection'` recovers the original set-level collection `P_collection`. -/
theorem P_collection'_image_eq : (↑) '' P_collection' = P_collection := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨⟨P, IsCompact_P hP⟩, Nonempty_P  hP⟩, hP, rfl⟩

/-- Equivalent formulation of the second defining property of `𝒫`. -/
lemma prop_ii_equiv {P : Set (Fin 2 → ℝ)} :
    (∀ (v : ℝ), |v| ≤ (1/2 : ℝ) → ∃ x₁ x₂ : ℝ, x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P)
    ↔
    (∀ (v : ℝ), |v| ≤ (1/2 : ℝ) → ∃ x : Fin 2 → ℝ, x ∈ Icc ![-1, -1] ![1, 1] ∧ (x 1) - (x 0) = v ∧ segment01 (x 0) (x 1) ⊆ P) := by
  refine ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · rcases h v hv with ⟨x₁, x₂, hx₁, hx₂, hdiff, hP⟩
    let x : Fin 2 → ℝ := ![x₁, x₂]
    have : x ∈ Icc ![-1, -1] ![1, 1] := by simp_all [x, Pi.le_def, Fin.forall_fin_two]
    exact ⟨x, this, hdiff, hP⟩
  · rcases h v hv with ⟨x, ⟨hx₀, hx₁⟩, hdiff, hP⟩
    exact ⟨x 0, x 1, by all_goals simp_all [Pi.le_def, Fin.forall_fin_two]⟩

-- By Aaron Liu (from Zulip)
theorem hausdorffDist_segment_left_le_dist {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {x y z : E} :
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
  have hcont : Continuous fun t : ℝ => (1 - t) • x + t • y := by
    continuity
  have hcomp : IsCompact ((fun t : ℝ => (1 - t) • x + t • y) '' Icc (0 : ℝ) 1) :=
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
  refine squeeze_zero (fun _ => hausdorffDist_nonneg) hbound ?_
  simpa using tendsto_sum_of_tendsto_dists_to_zero hx hy

lemma isCompact_segment01 (a b : ℝ) :
    IsCompact (segment01 a b) := by
  have : segment ℝ ![a, 0] ![b, 1] = AffineMap.lineMap ![a, 0] ![b, 1] '' Icc (0 : ℝ) 1 := by
    simp [segment_eq_image_lineMap]
  have hcont : Continuous fun t : ℝ => AffineMap.lineMap ![a, 0] ![b, 1] t := by
    continuity
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
  have Lbd : IsBounded (segment01 a b) := (isCompact_segment01 a b).isBounded
  have Rbd : IsBounded (segment01 a' b') := (isCompact_segment01 a' b').isBounded
  -- Finite Hausdorff *e-distance* holds for nonempty, bounded sets.
  exact hausdorffEdist_ne_top_of_nonempty_of_bounded Lne Rne Lbd Rbd

/-- If `L,T` are `segment01`s, any `y ∈ L` has a point on `T` within the Hausdorff distance. -/
lemma exists_point_on_segment01_within_HD
    {a b a' b' : ℝ} {y : Fin 2 → ℝ}
    (hy : y ∈ (segment01 a b)) :
    ∃ t ∈ (segment01 a' b'), dist t y ≤ hausdorffDist (segment01 a b) (segment01 a' b') := by
  -- choose a minimiser on the compact target segment
  obtain ⟨t, ht_mem, ht_eq⟩ := (isCompact_segment01 a' b').exists_infDist_eq_dist
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

theorem P_col'_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := IsBounded_P (h_mem n)
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

      have h_seg_HD0 : Tendsto (fun j => hausdorffDist (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) L) atTop (𝓝 0) := by
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
            Tendsto (fun j => hausdorffDist L (S j)) atTop (𝓝 0) := by
          simpa [hausdorffDist_comm] using h_seg_HD0
        have hdist_qy :
            Tendsto (fun j => dist (q j) y) atTop (𝓝 0) := by
          refine squeeze_zero (fun _ => dist_nonneg) (fun j => hq_le j) hHD_LS

        have hq_tendsto : Tendsto q atTop (𝓝 y) :=
          (tendsto_iff_dist_tendsto_zero).2 hdist_qy

        have hHD_PK_all : Tendsto (fun n => hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
          have : Tendsto (fun n => dist (Pₙ n) K) atTop (𝓝 0) := by
            refine Metric.tendsto_atTop.2 ?_
            simpa [dist_comm] using h_lim
          simpa [Metric.NonemptyCompacts.dist_eq] using this

        have hHD_PK_subseq : Tendsto (fun j => hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
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

        have hdist_y_r :Tendsto (fun j => dist y (r j)) atTop (𝓝 0) := by
          have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
            intro j
            simpa [dist_comm] using dist_triangle_right y (r j) (q j)

          have hsum_to0 : Tendsto (fun j => dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
            simpa using hdist_qy.add hHD_PK_subseq

          refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hsum_to0
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
          have hcont : Continuous (fun x => infDist x L) := by
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
      have h_seg_HD0 : Tendsto (fun j => hausdorffDist (segment01 (x (φ j) 0) (x (φ j) 1)) L) atTop (𝓝 0) := by
        apply tendsto_hausdorffDist_segments_of_tendsto_endpoints
        all_goals simp_all [tendsto_pi_nhds, Fin.forall_fin_two]

      have hHD_LS : Tendsto (fun j => hausdorffDist L (S j)) atTop (𝓝 0) := by
        simpa [hausdorffDist_comm] using h_seg_HD0

      have hdist_qy : Tendsto (fun j => dist (q j) y) atTop (𝓝 0) := by
        refine squeeze_zero (fun _ => dist_nonneg) (fun j => hq_le j) hHD_LS

      have hHD_PK_all : Tendsto (fun n => hausdorffDist (Pₙ n : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
        have : Tendsto (fun n => dist (Pₙ n) K) atTop (𝓝 0) := by
          refine Metric.tendsto_atTop.2 ?_
          simpa [dist_comm] using h_lim
        simpa [Metric.NonemptyCompacts.dist_eq] using this

      have hHD_PK_subseq : Tendsto (fun j => hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
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

      have hdist_y_r : Tendsto (fun j => dist y (r j)) atTop (𝓝 0) := by
        have htri : ∀ j, dist y (r j) ≤ dist y (q j) + dist (q j) (r j) := by
          intro j
          simpa [dist_comm] using dist_triangle_right y (r j) (q j)

        have hsum_to0 : Tendsto (fun j => dist (q j) y + hausdorffDist (Pₙ (φ j) : Set (Fin 2 → ℝ)) (K : Set _)) atTop (𝓝 0) := by
          simpa using hdist_qy.add hHD_PK_subseq

        refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hsum_to0
        exact (htri j).trans (add_le_add (by simp [dist_comm]) (hr_le_HD j))
      have hr_tendsto : Tendsto r atTop (𝓝 y) := (tendsto_iff_dist_tendsto_zero.2 (by simpa [dist_comm] using hdist_y_r))

      exact h_closed.mem_of_tendsto hr_tendsto (Eventually.of_forall hrK)

  exact ⟨h_closed, h_sub, h_union, h_forall⟩

#exit

-- https://proofwiki.org/wiki/Subspace_of_Complete_Metric_Space_is_Closed_iff_Complete
theorem P_col'_CompleteSpace : CompleteSpace P_collection' := IsClosed.completeSpace_coe P_col'_IsClosed

theorem P_col'_BaireSpace [CompleteSpace P_collection'] : BaireSpace P_collection' := BaireSpace.of_pseudoEMetricSpace_completeSpace

noncomputable section

/-- A closed, axis–aligned rectangle `[x₁,x₂] × [y₁,y₂]`
    written in the `Fin 2 → ℝ` model of `ℝ²`. -/
def axisRect (x₁ x₂ y₁ y₂ : ℝ) : Set (Fin 2 → ℝ) :=
  {p | p 0 ∈ Icc x₁ x₂ ∧ p 1 ∈ Icc y₁ y₂}

/-- Horizontal slice of a planar set at height `y`. -/
def hSlice (S : Set (Fin 2 → ℝ)) (y : ℝ) : Set ℝ :=
  {x | (![x, y] : Fin 2 → ℝ) ∈ S}

/-- The vertical window `W v ε := [0,1] ∩ [v-ε,v+ε]`. -/
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

lemma hasThinCover_singleton (v ε : ℝ) (x : Fin 2 → ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    hasThinCover ({x} : Set (Fin 2 → ℝ)) v ε := by
  let R : Finset (Set (Fin 2 → ℝ)) :=
    {axisRect (x 0) (x 0) (x 1) (x 1)}
  refine ⟨R, ?rects, ?cover, ?length⟩
  · intro r hr
    rcases Finset.mem_singleton.mp hr with rfl
    exact ⟨x 0, x 0, x 1, x 1, rfl⟩
  · intro y hy t ht
    -- ht: (![t,y]) ∈ {x}  ⇒  t = x 0 and y = x 1
    have hxy : (![t, y] : Fin 2 → ℝ) = x := by
      simpa [hSlice] using ht
    have ht0 : t = x 0 := by simpa using congrArg (fun p => p 0) hxy
    have hy1 : y = x 1 := by simpa using congrArg (fun p => p 1) hxy
    -- show t belongs to the slice of our rectangle at y
    -- the big union over a singleton is just that set
    have : hSlice (⋃ r ∈ R, (r : Set _)) y = hSlice (axisRect (x 0) (x 0) (x 1) (x 1)) y := by
      simp [R]
    -- finish by unfolding `hSlice`/`axisRect`
    -- simpa [this, hSlice, axisRect, ht0, hy1]
    simp only [hSlice, Nat.succ_eq_add_one, Nat.reduceAdd, hy1, Fin.isValue, mem_iUnion,
      exists_prop, ht0, mem_setOf_eq]
    sorry
  · intro y hy
    -- reduce the union over the singleton R
    have : hSlice (⋃ r ∈ R, (r : Set _)) y
          = {t : ℝ | t ∈ Icc (x 0) (x 0) ∧ y ∈ Icc (x 1) (x 1)} := by
      simp [R, hSlice, axisRect]
    -- the slice is either ∅ (if y ≠ x 1) or {x 0}; in both cases volume = 0
    have hvol : volume (hSlice (⋃ r ∈ R, (r : Set _)) y) = 0 := by
      by_cases hy' : y = x 1
      · have : hSlice (⋃ r ∈ R, (r : Set _)) y = {x 0} := by
          ext t
          sorry
        simp [this]
      · have : hSlice (⋃ r ∈ R, (r : Set _)) y = (∅ : Set ℝ) := by
          ext t
          sorry
        simp [this]
    have hpos : 0 < 100 * ε := by simp [hε]
    simpa [hvol] using hpos

/-- The same collection, but as a subset of the Hausdorff–metric
    space `NonemptyCompacts (Fin 2 → ℝ)`. -/
def P_v_eps' (v ε : ℝ) : Set P_collection' :=
  {P | hasThinCover (P : Set _) v ε}

theorem P_v_eps'_nonempty {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    (P_v_eps' v ε).Nonempty := by
  let K : NonemptyCompacts (Fin 2 → ℝ) := ⟨⟨{![1/2, 1/2]}, isCompact_singleton⟩, fun a ↦ v, by sorry⟩
  have K_mem : K ∈ (Set.univ : Set (NonemptyCompacts (Fin 2 → ℝ))) := by simp
  have hcover : hasThinCover ((K : Set (Fin 2 → ℝ))) v ε := by
    sorry
    -- hasThinCover_singleton hv₀ hv₁ hε
  have K_mem_P_col' : K ∈ P_collection' := by
    sorry
  exact ⟨⟨K, K_mem_P_col'⟩, by simpa using hcover⟩

/-- helper: expand an axis-aligned rectangle by η in both directions -/
def axisRectExpand (η : ℝ) (a b c d : ℝ) : Set (Fin 2 → ℝ) :=
  axisRect (a - η) (b + η) (c - η) (d + η)

lemma axisRect_subset_expand {a b c d : ℝ} :
    ∃ η > 0, axisRect a b c d ⊆ axisRectExpand η a b c d := by
  sorry
  -- intro p hp
  -- rcases hp with ⟨hx, hy⟩
  -- simp_rw [axisRectExpand, axisRect]
  -- constructor
  -- · apply Icc_subset_Icc_left (sub_nonpos.mpr (by sorry))
  --   sorry
  -- · apply Icc_subset_Icc_left (sub_nonpos.mpr (by sorry))
  --   sorry
  -- exact ⟨by exact Icc_subset_Icc_left (sub_nonpos.mpr (by linarith)) hx,
    -- by exact Icc_subset_Icc_left (sub_nonpos.mpr (by linarith)) hy⟩

/-- If `q` is inside an axis–aligned rectangle and `p` is within distance `η` of `q`,
then `p` lies in the rectangle thickened by `η` in both axes. -/
lemma mem_thickened_axisRect_of_close {a b c d η : ℝ} {p q : Fin 2 → ℝ} (hq : q ∈ axisRect a b c d) (hpq : dist p q ≤ η) :
    p ∈ axisRectExpand η a b c d := by
  rcases hq with ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · have aux : |p 0 - q 0| ≤ η := by
      sorry
    have hx' : a ≤ q 0 ∧ q 0 ≤ b := hx
    constructor
    · have : a - η ≤ p 0 := by
        sorry
      simpa using this
    · have : p 0 ≤ b + η := by
        sorry
      simpa using this
  · have aux : |p 1 - q 1| ≤ η := by
      sorry
    rcases hy with ⟨hyL, hyU⟩
    constructor
    · have : c - η ≤ p 1 := by sorry
      simpa using this
    · have : p 1 ≤ d + η := by sorry
      simpa using this

theorem P_v_eps_open {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsOpen (P_v_eps' v ε) := by
  rw [Metric.isOpen_iff]
  intro P hP
  rcases hP with ⟨R, h_rects, h_cover, h_le⟩
  dsimp only [ball]
  sorry

theorem P_v_eps_dense {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (P_v_eps' v ε) := by
  sorry

theorem lemma_2_4 {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsClosed (P_v_eps' v ε)ᶜ ∧ IsNowhereDense (P_v_eps' v ε)ᶜ := by
  simp_rw [isClosed_isNowhereDense_iff_compl, compl_compl]
  exact ⟨P_v_eps_open hv₀ hv₁ hε, P_v_eps_dense hv₀ hv₁ hε⟩

------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------

/--
In a Baire space, every nonempty open set is non‐meagre,
that is, it cannot be written as a countable union of nowhere‐dense sets.
-/
theorem not_isMeagre_of_isOpen {X : Type*} {s : Set X} [TopologicalSpace X] [BaireSpace X]
  (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ IsMeagre s := by
  intro h
  rcases (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
    with ⟨x, hx, hxc⟩
  exact hxc hx

/-- A set of second category (i.e. non-meagre) is nonempty. -/
lemma nonempty_of_not_IsMeagre {X : Type*} [TopologicalSpace X] {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using (IsMeagre.empty)

/-- In a nonempty Baire space, any dense `Gδ` set is not meagre. -/
theorem IsGδ_dense_not_meagre {X : Type*} [Nonempty X] [TopologicalSpace X] [BaireSpace X] {s : Set X} (hs : IsGδ s) (hd : Dense s) : ¬ IsMeagre s := by
  intro h
  rcases (mem_residual).1 h with ⟨t, hts, htG, hd'⟩
  rcases (hd.inter_of_Gδ hs htG hd').nonempty with ⟨x, hx₁, hx₂⟩
  exact (hts hx₂) hx₁

/-- In a nonempty Baire space, a residual (comeagre) set is not meagre. -/
lemma not_isMeagre_of_mem_residual {X : Type*} [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] {s : Set X} (hs : s ∈ residual X) :
    ¬ IsMeagre s := by
  -- From `mem_residual`, pick a dense Gδ subset `t ⊆ s`.
  rcases (mem_residual (X := X)).1 hs with ⟨t, ht_sub, htGδ, ht_dense⟩
  -- Dense Gδ sets aren’t meagre in a nonempty Baire space.
  -- If `s` were meagre, then so would be `t ⊆ s`, contradiction.
  intro hs_meagre
  exact not_isMeagre_of_isGδ_of_dense htGδ ht_dense (hs_meagre.mono ht_sub)

------------------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------

/-- TO DO -/
def φ' (φ : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  if n = 0 then φ n else min (1 / (n : ℕ)) (φ n)

-- Junk?
-- lemma φ'_mem_Ioo (φ : ℕ → ℝ≥0) (hφ : ∀ n, φ n ∈ Set.Ioo 0 1) :
--     ∀ n, φ' φ n ∈ Set.Ioo (0 : ℝ≥0) 1 := by
--   intro n
--   by_cases h : n = 0
--   · subst h
--     simpa [φ'] using hφ 0
--   · rcases hφ n with ⟨hpos, hlt1⟩
--     have hpos' : 0 < 1 / (n : ℕ) := by
--       sorry
--     refine ⟨?_, ?_⟩
--     · sorry
--     · simpa [φ', h] using (min_lt_iff.2 (Or.inr hlt1))

lemma extra_exists_seq_strictAnti_tendsto (n r : ℕ) :
    ∃ φ : ℕ → ℝ≥0, StrictAnti φ ∧ (∀ n, φ n ∈ Set.Ioo 0 1) ∧ Tendsto φ atTop (𝓝 0) ∧ (∀ n, r * (φ n) ≤ 1) ∧ (∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n)) :=  by
  obtain ⟨φ', h₁φ', h₂φ', h₃φ'⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0) < 1 by norm_num)
  set φ : ℕ → ℝ≥0 := if n = 0 then φ' else min (1 / n) φ' with hφ
  use φ
  by_cases h : n = 0
  · subst h
    simp only [↓reduceIte] at hφ
    sorry
  · sorry
-- and to prove that existence you can probably just use the same exists_seq_strictAnti_tendsto' to get phi', then use phi n := if n = 0 then 1 else min (1/n) (phi' n)
-- #check exists_seq_strictAnti_tendsto

/-- TO DO -/
def Pn (φ : ℕ → ℝ≥0) (n : ℕ) : Set P_collection' := ⋂ r ∈ Finset.range (n + 1), P_v_eps' ((r : ℝ) * (φ n : ℝ)) (φ n : ℝ)

lemma isOpen_Pn (φ : ℕ → ℝ≥0) (n : ℕ)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n))
    (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1) :
    IsOpen (Pn φ n) := by
  unfold Pn
  refine isOpen_biInter_finset ?_
  intro r hr
  exact P_v_eps_open (hv0 r hr) (hv1 r hr) ((hφ n).1)

def Pstar (φ : ℕ → ℝ≥0) : Set P_collection' := ⋂ n : ℕ, Pn φ (n + 1)

def Pstar' (φ : ℕ → ℝ≥0) : Set P_collection' := ⋂ n ∈ Set.Ici (1 : ℕ), Pn φ n

lemma Pstar_eq_Pstar' (φ : ℕ → ℝ≥0) :
    Pstar φ = Pstar' φ := by
  ext P
  constructor
  · -- from ⋂_{m} Pn (m+1) to ⋂_{n≥1} Pn n
    intro h
    refine mem_iInter₂.2 ?_
    intro n hn
    -- write n = m+1 with m := n-1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    simpa using (mem_iInter.mp h m)
  · -- from ⋂_{n≥1} Pn n to ⋂_{m} Pn (m+1)
    intro h
    refine mem_iInter.2 ?_
    intro m
    have : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le _)
    simpa using (mem_iInter₂.mp h (m + 1) this)

-- φ : ℕ → ℝ≥0
-- h₁φ : StrictAnti φ
-- h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1
-- h₃φ : Tendsto φ atTop (𝓝 0)

variable [BaireSpace P_collection']

lemma Dense_Pn (φ : ℕ → ℝ≥0) (n : ℕ)
    (hφ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1)
    (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n))
    (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1) :
    Dense (Pn φ n) := by
  rw [Pn]
  apply dense_iInter_of_isOpen
  all_goals intro i
  · -- apply P_v_eps_open (v := i * (φ n)) (ε := (φ n)) (hv0 i) (hv1 i)
    sorry
  · sorry

variable (φ : ℕ → ℝ≥0) (n : ℕ) (h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
  (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n)) (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1)

-- Is this necessary?
-- theorem P_v_eps'_not_meagre {v ε : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (hε : 0 < ε) :
--     ¬ IsMeagre (P_v_eps' v ε) :=
--   not_isMeagre_of_isOpen (P_v_eps_open h0 h1 hε) (P_v_eps'_nonempty h0 h1 hε)

/-- `Pstar(φ)` is dense: countable intersection of open dense sets. -/
lemma Dense_Pstar (φ : ℕ → ℝ≥0) (n : ℕ) (h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
  (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n)) (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1)  : Dense (Pstar φ) := by
  apply dense_sInter_of_isOpen
  · intro S hS
    rcases hS with ⟨m, rfl⟩
    apply isOpen_Pn
    · exact fun n ↦ h₂φ n
    · exact fun r a ↦ zero_le (↑r * φ (m + 1))
    · sorry
  · exact countable_range fun n ↦ Pn φ (n + 1)
  · intro S hS
    rcases hS with ⟨m, rfl⟩
    apply Dense_Pn
    · exact fun n ↦ h₂φ n
    · exact fun r a ↦ zero_le (↑r * φ (m + 1))
    · sorry

/-- `Pstar(φ)` is a Gδ: countable intersection of open sets. -/
lemma IsGδ_Pstar (φ : ℕ → ℝ≥0) (n : ℕ) (h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
  (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n)) (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1) : IsGδ (Pstar φ) := by
  -- simp_rw [isGδ_iff_eq_iInter_nat]
  have : ∀ m, IsOpen (Pn φ (m + 1)) := by
    intro m
    apply isOpen_Pn -- φ (m + 1)
    · intro r
      exact h₂φ r
    · intro r hr
      exact zero_le (↑r * φ (m + 1))
    · intro r hr
      have hr_le : r ≤ m+1 := Finset.mem_range_succ_iff.mp hr
      calc
        (r : ℝ) * φ (m+1) ≤ (m+1 : ℝ) * φ (m+1) := by gcongr; exact_mod_cast hr_le
        _ ≤ 1 := sorry
  simpa [Pstar] using IsGδ.iInter_of_isOpen this

theorem Pstar_notMeagre : ¬ IsMeagre (Pstar φ) := by
  haveI : Nonempty P_collection' := by
    rcases P_collection'_nonempty with ⟨P, hP⟩
    exact ⟨P, hP⟩
  -- exact not_isMeagre_of_isGδ_of_dense (IsGδ_Pstar φ) (Dense_Pstar φ)
  sorry

def E_set : Set P_collection' := {P | ∀ u ∈ Icc (0 : ℝ) 1, volume (hSlice (P : Set (Fin 2 → ℝ)) u) = 0}

lemma Pstar_sub_E_set  (φ : ℕ → ℝ≥0) (n : ℕ) (h₁φ : StrictAnti φ) (h₂φ : ∀ (n : ℕ), φ n ∈ Set.Ioo 0 1) (h₃φ : Tendsto φ atTop (𝓝 0))
  (hv0 : ∀ r ∈ Finset.range (n + 1), 0 ≤ r * (φ n)) (hv1 : ∀ r ∈ Finset.range (n + 1), r * (φ n) ≤ 1) :
    Pstar φ ⊆ E_set := by
  intro P hP
  have hmem : ∀ m, P ∈ Pn φ (m+1) := by
    intro m
    simpa [Pstar] using (mem_iInter.mp hP m)
  intro u hu
  have hu01 : u ∈ Icc (0 : ℝ) 1 := by simpa [Icc]
  have hbound : ∀ m, (volume (hSlice (P : Set (Fin 2 → ℝ)) u)).toReal < 100 * (φ (m+1) : ℝ) := by
    sorry
  sorry

theorem thm2_5 (h : Pstar φ ⊆ E_set) : ¬ IsMeagre E_set := by
  intro hM
  apply IsMeagre.mono at h
  · simp [Pstar_notMeagre] at h
  · exact hM

def P_zero_vol : Set P_collection' := {P | volume (P : Set (Fin 2 → ℝ)) = 0}

lemma E_sub_P_zero_vol : E_set ⊆ P_zero_vol := by
  intro P hP
  simp_rw [P_zero_vol, mem_setOf_eq, ← MeasureTheory.setLIntegral_one]
  sorry
  -- simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
  -- have hP_sub_rect : (P : Set (Fin 2 → ℝ)) ⊆ rectangle := (P.property).2.1
  -- have hslice_zero : ∀ y : ℝ, volume (hSlice (P : Set (Fin 2 → ℝ)) y) = 0 := by
  --   intro y
  --   by_cases hy : y ∈ Icc (0 : ℝ) 1
  --   · simpa [E_set, mem_setOf_eq] using hP y hy
  --   · have : hSlice (P : Set (Fin 2 → ℝ)) y = (∅ : Set ℝ) := by
  --       ext x
  --       constructor
  --       · intro hx
  --         have hxP : (![x, y] : Fin 2 → ℝ) ∈ (P : Set (Fin 2 → ℝ)) := by
  --           simpa [hSlice] using hx
  --         have hxRect : (![x, y] : Fin 2 → ℝ) ∈ rectangle := hP_sub_rect hxP
  --         have : y ∈ Icc (0 : ℝ) 1 := by
  --           simpa [rectangle, Pi.le_def, Fin.forall_fin_two] using (show (![x, y] : Fin 2 → ℝ) 1 ∈ Icc (0 : ℝ) 1 from
  --             (by simp_all [rectangle, Pi.le_def, Fin.forall_fin_two]))
  --         exact (hy this).elim
  --       · simp
  --     simp [this]
  -- have h_prod_bound : volume (P : Set (Fin 2 → ℝ)) ≤ ∫⁻ y : ℝ, volume (hSlice (P : Set (Fin 2 → ℝ)) y) := by
  --   sorry
  -- have : ∫⁻ y : ℝ, volume (hSlice (P : Set (Fin 2 → ℝ)) y) = 0 := by
  --   simp [hslice_zero]
  -- have hle : volume (↑↑P : Set (Fin 2 → ℝ)) ≤ 0 := by
  --   simpa [this] using h_prod_bound
  -- exact le_antisymm hle bot_le

  -- #check MeasureTheory.lintegral_prod_le
  -- #check MeasureTheory.measurePreserving_finTwoArrow (volume : Measure ℝ)
  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.html#MeasureTheory.lintegral_const
  -- rw [MeasureTheory.Measure.volume_eq_prod]
  -- Fubini argument?

/-- The set of `P ∈ 𝒫` with Lebesgue measure zero is of second category in `(𝒫, d)`. -/
theorem theorem_2_3 (φ : ℕ → ℝ≥0) : ¬ IsMeagre P_zero_vol := by
  intro h
  exact (thm2_5 φ (Pstar_sub_E_set φ)) (h.mono E_sub_P_zero_vol)

theorem Exists_P0 (φ : ℕ → ℝ≥0) : P_zero_vol.Nonempty := nonempty_of_not_isMeagre (theorem_2_3 φ)

end

end

#exit

section

-- /-- In ℝ, there exists a Kakeya set. -/
theorem one_dim_exists_kakeya : ∃ s : Set ℝ, IsKakeya s := ⟨closedBall (0 : ℝ) 1, IsKakeya_ball⟩

-- /-- Any Kakeya set in `ℝ` contains a closed unit‐length interval. -/
-- lemma kakeya_contains_unit_Icc {K : Set ℝ} (hK : IsKakeya K) :
--     ∃ x₀, Icc x₀ (x₀ + 1) ⊆ K := by
--   have := hK 1 (by simp)
--   -- simp only [segment_eq_Icc, norm_one] at this
--   rcases this with ⟨x₀, hseg⟩
--   exact ⟨x₀, by simpa using hseg⟩

-- /-- Any closed interval of length 1 has Hausdorff dimension 1. -/
-- lemma dimH_Icc_length_one (a : ℝ) :
--     dimH (Icc a (a + 1)) = 1 := by
--   have h : (interior (Icc a (a + 1))).Nonempty := by simp [interior_Icc]
--   calc
--     dimH (Icc a (a + 1)) = Module.finrank ℝ ℝ := Real.dimH_of_nonempty_interior h
--     _ = 1 := by simp

-- /-- If a set contains some unit‐interval, then its dimH ≥ 1. -/
-- lemma dimH_of_contains_Icc {K : Set ℝ} {x₀} (h : Icc x₀ (x₀ + 1) ⊆ K) :
--     1 ≤ dimH K := by
--   calc
--     1 = dimH (Icc x₀ (x₀ + 1)) := (dimH_Icc_length_one x₀).symm
--     _ ≤ dimH K := dimH_mono h

-- /-- Any subset of `ℝ` has dimH ≤ 1. -/
-- lemma dimH_le_one_univ : ∀ (K : Set ℝ), dimH K ≤ 1 := fun K ↦ by
--   calc
--     dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
--     _ = Module.finrank ℝ ℝ := by simp [dimH_univ]
--     _ = 1 := by simp

-- /-- Any Kakeya set in `ℝ` has full Hausdorff dimension. -/
-- theorem dimH_kakeya_eq_one (K : Set ℝ) (hK : IsKakeya K) :
--     dimH K = 1 := by
--   rcases kakeya_contains_unit_Icc hK with ⟨x₀, hsub⟩
--   exact le_antisymm (dimH_le_one_univ K) (dimH_of_contains_Icc hsub)

-- /-- Kakeya conjecture in ℝ: there exists a Kakeya set of Hausdorff dimension 1. -/
-- theorem one_dim_kakeya_conjecture : ∃ s : Set ℝ, IsKakeya s ∧ dimH s = 1 := by
--   refine ⟨closedBall (0 : ℝ) 1, ⟨IsKakeya.ball, dimH_kakeya_eq_one _ IsKakeya.ball⟩⟩


/-- A Kakeya subset of ℝ has full Hausdorff dimension. -/
theorem dimH_kakeya_eq_one (K : Set ℝ)
  (hK : IsKakeya K) :
    dimH K = 1 := by
  rw [IsKakeya] at hK
  specialize hK 1
  simp only [norm_one, le_add_iff_nonneg_right, zero_le_one, segment_eq_Icc, forall_const] at hK
  rcases hK with ⟨x₀, hseg⟩
  have hIcc_sub : Icc x₀ (x₀ + 1) ⊆ K := by
    simpa [segment_eq_Icc (by linarith : x₀ ≤ x₀ + 1)] using hseg
  have hlow : 1 ≤ dimH K := by
    have eq1 : dimH (Icc x₀ (x₀ + 1)) = 1 := by
      have nin : (interior (Icc x₀ (x₀ + 1))).Nonempty := by
        rw [interior_Icc]; simp
      calc
        dimH (Icc x₀ (x₀ + 1)) = Module.finrank ℝ ℝ := Real.dimH_of_nonempty_interior nin
        _ = 1 := by simp
    calc
      1 = dimH (Icc x₀ (x₀ + 1)) := eq1.symm
      _ ≤ dimH K := by apply dimH_mono; exact hseg
  have hup : dimH K ≤ 1 := by
    calc
      dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ K)
      _ = Module.finrank ℝ ℝ := by simp only [Module.finrank_self, Nat.cast_one, dimH_univ]
      _ = 1 := by simp
  exact le_antisymm hup hlow

open ENNReal NNReal MeasureTheory Measure Filter Topology EMetric

/-@b-mehta's formulation of Prop 3.2 of Fox (needs to be PR by BM)-/
theorem asdf {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    ∃ G : Set X, IsGδ G ∧ E ⊆ G ∧ μH[s] G = μH[s] E := by
  sorry

theorem dimH_eq_iInf {X : Type*}
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

/-- A subset of `ℝⁿ` has finite Hausdorff dimension. -/
theorem dimH_lt_top {n : ℕ} {A : Set (Fin n → ℝ)} :
    dimH A < ⊤ := by
  calc
    dimH A ≤ dimH (Set.univ : Set (Fin n → ℝ)) := dimH_mono (by simp)
    _ = n := dimH_univ_pi_fin n
    _ < ⊤ := by simp

theorem dimH_ne_top {n : ℕ} {A : Set (Fin n → ℝ)} : dimH A ≠ ⊤ := by
  simpa using (lt_top_iff_ne_top).1 dimH_lt_top

/- Proposition 3.4 (Fox):
For any subset `A` of `ℝⁿ` there is a G₀‐set `G` with `A ⊆ G` and `dimH G = dimH A`. -/
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
    fun k : ℕ ↦ asdf (coe_nonneg (DA + φ k)) A
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


/-- Proposition 3.7 (slicing): if `A ⊆ ℝⁿ` has finite `s`-dimensional Hausdorff measure,
    then for any `k ≤ s` and any `k`-plane `W`, the slices
    `A ∩ (Wᗮ + x)` have finite `(s - k)`-measure for `μH[k]`-almost all `x ∈ W`. -/
theorem prop_3_7_slicing
  (n : ℕ)
  (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
  (s : ℝ) (hs : μH[s] A < ⊤)
  (k : ℕ) (hks : (k : ℝ) ≤ s)
  (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : Module.finrank ℝ W = k)
  (direction : W) (x : W) :
  ∀ᵐ x ∂ (μH[(k : ℝ)]).restrict (W : Set (EuclideanSpace ℝ (Fin n))),
    μH[s - k] (A ∩ (AffineSubspace.mk' x W.orthogonal : Set _)) < ⊤ := by
  sorry

section

/--
Besicovitch sets have Hausdorff dimension equal to 2.
-/
theorem hausdorff_dim_Besicovitch_eq_2 (B : Set (EuclideanSpace ℝ (Fin 2))) (hB : IsBesicovitch B) :
    dimH B = 2 := by
  sorry

end

end

end Besicovitch

open Metric

-- Aaron Liu (Zulip)
theorem hausdorffDist_segment_left_le_dist {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {x y z : E} :
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

open Set Real Topology Metric Bornology TopologicalSpace MeasureTheory MetricSpace Filter

namespace Minkowski

variable {α : Type*} [PseudoMetricSpace α]

open scoped BigOperators

/-- The set of all finite families of points whose closed r-balls cover `s`. -/
def coveringCandidates (s : Set α) (r : ℝ) : Set (Finset α) :=
  {t | s ⊆ ⋃ x ∈ t, Metric.closedBall x r}

/-- Minimal number of closed `r`-balls to cover `s` (centres in `α`), or `∞` if no finite cover. -/
noncomputable def coveringNumber (s : Set α) (r : ℝ) : WithTop ℕ :=
  sInf { n : WithTop ℕ | ∃ t : Finset α, (t.card : WithTop ℕ) = n ∧ s ⊆ ⋃ x ∈ t, Metric.closedBall x r }

lemma coveringNumber_mono_radius {s : Set α} {r₁ r₂ : ℝ}
    (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
      coveringNumber s r₂ ≤ coveringNumber s r₁ := by
  -- larger radius ⇒ need no more balls
  -- (prove by showing candidate sets transfer)
  dsimp only [coveringNumber]
  apply sInf_le_sInf_of_forall_exists_le
  rintro n ⟨t, rfl, hcov⟩
  have hcov₂ : s ⊆ ⋃ x ∈ t, closedBall x r₂ := by
    simp only [subset_def, mem_iUnion, exists_prop] at hcov
    intro a ha
    rcases hcov a ha with ⟨x, hx, hdist⟩
    sorry
  sorry

lemma coveringNumber_empty (r : ℝ) : coveringNumber (∅ : Set α) r = 0 := by
   dsimp [coveringNumber]
   have h0 : (0 : WithTop ℕ) ∈ { n | ∃ t : Finset α, (t.card : WithTop ℕ) = n ∧ ∅ ⊆ ⋃ x ∈ t, closedBall x r } := ⟨∅, by simp, by simp⟩
   sorry

lemma coveringNumber_singleton {x : α} {r : ℝ} (hr : 0 < r) :
    coveringNumber ({x} : Set α) r = 1 := by
  sorry

-- lemma coveringNumber_eq_coe_nat
--   {s : Set α} {r : ℝ} (hfin : ∃ t, s ⊆ ⋃ x∈t, Metric.closedBall x r) :
--     ∃ n : ℕ, coveringNumber s r = n := by
--   sorry

open ENNReal Filter

noncomputable def N (s : Set α) (r : ℝ) : ℝ≥0∞ :=
  (coveringNumber s r).map (fun (n : ℕ) ↦ (n : ℝ).toNNReal)


noncomputable def ballRatio (s : Set α) (r : ℝ) : ENNReal :=
  if N s r = ⊤ then ⊤ else
  (Real.log (N s r).toReal / (- Real.log r)).toNNReal

noncomputable def upperBoxDim (s : Set α) : ℝ≥0∞ :=
  limsup (fun r ↦ ballRatio s r) (𝓝[>] (0 : ℝ))

-- noncomputable def upper_minkowski_dim (s : Set α) : ℝ :=
--   limsup (𝓝[>] (0 : ℝ)) (fun r ↦ if r > 0 then log ((N s r).toReal) / (- log r) else 0)

-- /-- Upper (box / Minkowski) dimension of a bounded (or totally bounded) set. -/
-- noncomputable def upper (s : Set α) : ℝ≥0∞ :=

-- /-- Lower Minkowski dimension of a set. -/
-- noncomputable def lower (s : Set α) : ℝ≥0∞ := sorry

-- /-- If upper = lower we speak of "the" Minkowski dimension. -/
-- noncomputable def dim (s : Set α) : ℝ≥0∞ :=
--   if h : upper s = lower s then upper s else 0  -- or leave undefined


end Minkowski


/--
In a nonempty Baire space, a countable intersection of dense open sets is not meager.
-/
theorem not_meager_iInter_of_countable {α : Type*} [TopologicalSpace α] [BaireSpace α] [Nonempty α]
  {ι : Type*} [Countable ι] {U : ι → Set α} (hU_Open : ∀ i, IsOpen (U i)) (hU_Dense : ∀ i, Dense (U i)) :
  ¬ IsMeagre (⋂ i, U i) := by
  intro hM
  have aux0 : Dense (⋂ i, U i) := by
    apply dense_iInter_of_isOpen
    · exact fun i ↦ hU_Open i
    · exact fun i ↦ hU_Dense i
  -- A dense set in a nonempty space cannot be meager
  rw [IsMeagre] at hM
  rw [mem_residual] at hM
  rcases hM with ⟨t, ht, some, ye⟩

  -- rw [isMeagre_iff_countable_union_isNowhereDense] at hM

  -- rw [IsMeagre, mem_residual_iff] at hM
  -- rcases hM with ⟨S, hS_open, hS_dense, hS_countable, hS_sub⟩
  sorry



/-- A countable intersection of residual sets is residual. -/
theorem residual.countable_sInter  {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (hS : S.Countable) (h : ∀ s ∈ S, s ∈ residual X) :
    (⋂₀ S) ∈ residual X := by
  rw [countable_sInter_mem]
  · exact fun s a ↦ h s a
  · exact hS

/-- In a nonempty Baire space, any dense `Gδ` set is not meagre. -/
theorem IsGδ_dense_not_meagre {X : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X] {s : Set X} (hs : IsGδ s) (hd : Dense s) :
    ¬ IsMeagre s := by
  intro h
  rcases (mem_residual).1 h with ⟨t, ht_subset, htGδ, htd⟩
  have hdense : Dense (s ∩ t) := (Dense.inter_of_Gδ hs htGδ hd htd)
  have hstempty : s ∩ t = (∅ : Set X) := by
     apply eq_empty_iff_forall_notMem.mpr
     intro x hx
     have : x ∈ sᶜ := ht_subset hx.2
     have : x ∉ s := by simpa using this
     exact this hx.1
  have : (s ∩ t).Nonempty := hdense.nonempty
  simpa [hstempty]

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [Nonempty X]

-- U : ι → Set X is a countable family of dense open sets
lemma nonempty_iInter_of_dense_open'
    {ι : Type*} [Countable ι] (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hUd : ∀ i, Dense (U i)) :
    (⋂ i, U i).Nonempty := by
  simpa [Set.univ_inter] using
    (dense_iff_inter_open.1 (dense_iInter_of_isOpen (f := U) hUo hUd))
      Set.univ isOpen_univ (by exact nonempty_iff_univ_nonempty.mp (by infer_instance))
