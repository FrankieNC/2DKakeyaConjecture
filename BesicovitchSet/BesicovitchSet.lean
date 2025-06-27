/-
Copyright (c) 2025 Yes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Yuming Guo, Bhavik Mehta
-/

import Mathlib

namespace Besicovitch

open Set Real Topology Metric Bornology TopologicalSpace

-- Formalise the entirety of Section 2. Section 4 is nonsense

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @FrankieNC: you should add the stuff you proved about this from CW3 to this section
/-- A subset of a normed real vector space `E` is Kakeya if it contains a segment of unit length in
every direction. -/
def IsKakeya (s : Set E) : Prop :=
    ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

/-- The universal set is Kakeya. -/
lemma univ_isKakeya : IsKakeya (Set.univ : Set E) := by
  simp [IsKakeya]

/-- If `s` is Kakeya and `s ⊆ t`, then `t` is Kakeya. -/
theorem IsKakeya.subset {s t : Set E} (h : IsKakeya s) (hs : s ⊆ t) : IsKakeya t := by
  intro v hv
  rcases h v hv with ⟨x, hx⟩
  exact ⟨x, hx.trans hs⟩
  -- exact Exists.intro x fun ⦃a⦄ a_1 ↦ hs (hx a_1)

/-- The closed unit ball is Kakeya. -/
theorem IsKakeya.ball : IsKakeya (closedBall (0 : E) 1) := by
  intro v hv
  use -v
  intro y hy
  calc
    dist y 0 = ‖y - 0‖ := by aesop
    _ ≤ ‖(-v) - 0‖ := by
      apply norm_sub_le_of_mem_segment
      simp only [neg_add_cancel] at hy
      rw [segment_symm]
      exact hy
    _ = ‖v‖ := by simp [norm_neg]
    _ = 1 := hv

/-- In a nontrivial normed space, any Kakeya set is nonempty. -/
theorem IsKakeya.nonempty [Nontrivial E] {s : Set E} (h : IsKakeya s) : s.Nonempty := by
  rcases exists_pair_ne E with ⟨a, b, hab⟩
  set x := a - b with hx
  have hx : x ≠ 0 := by
    intro h₀; apply hab
    simpa [hx] using sub_eq_zero.1 h₀
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set v := ‖x‖⁻¹ • x with hv
  have hv_norm : ‖v‖ = 1 := by
    rw [hv]
    simp only [norm_smul, norm_inv, norm_norm]
    aesop -- @b-mehta I am doing this at ungodly hours and I am too lazy to not use `aesop`
  rcases h v hv_norm with ⟨y, hy⟩
  use y
  exact hy (left_mem_segment ℝ y (y + v))

/--
A reformulation of the Kakeya condition: it suffices to check the existence of
a segment for all vectors with norm at most 1, rather than exactly 1.
-/
theorem isKakeya_iff_sub_unit [Nontrivial E] {s : Set E} :
    IsKakeya s ↔ ∀ v : E, ‖v‖ ≤ 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s := by
  constructor
  -- First, prove: IsKakeya s → ∀ v, ‖v‖ ≤ 1 → ∃ x, segment x x+v ⊆ s
  · intro h_kakeya v hv
    rw [IsKakeya] at h_kakeya

    -- Case: v = 0
    by_cases h₀ : v = 0
    · rw [h₀]
      simp only [add_zero, segment_same, Set.singleton_subset_iff]
      -- We still need to find some z, w such that segment z z+w ⊆ s
      obtain ⟨w, hw⟩ : ∃ v : E, ‖v‖ = 1 := by
        apply exists_norm_eq -- E is nontrivial, so such a unit vector exists
        positivity
      specialize h_kakeya w hw
      rcases h_kakeya with ⟨z, hz⟩
      use z
      apply hz
      exact left_mem_segment ℝ z (z + w) -- any point on a segment lies in the segment

    -- Case: v ≠ 0
    · set u := ‖v‖⁻¹ • v with hu -- rescale v to a unit vector u
      have h₁ : ‖v‖ ≠ 0 := by
        contrapose! h₀
        rw [norm_eq_zero] at h₀
        exact h₀
      -- Now u has norm 1
      have h₂ : ‖u‖ = 1 := by
        rw [hu]
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      -- By IsKakeya, s contains segment in direction u
      obtain ⟨x, hx⟩ := h_kakeya u h₂
      use x

      -- We want to show: segment x x+v ⊆ segment x x+u
      -- Since v is a scalar multiple of u, both segments lie along same ray
      have h₃ : segment ℝ x (x + v) ⊆ segment ℝ x (x + u) := by
        intro y hy
        refine mem_segment_iff_sameRay.mpr ?_
        rw [SameRay]
        right
        right
        -- Here we need to figure out the scalars greater than zero such that
        -- the two vectors are multiple of each other
        -- @b-mehta Could you finish this for us?
        sorry
      -- Apply inclusion of segments to conclude result
      exact fun ⦃a⦄ a_1 ↦ hx (h₃ a_1)
  -- Converse: ∀ v, ‖v‖ ≤ 1 → ... ⇒ IsKakeya s
  · intro h_segment v hv
    specialize h_segment v
    apply h_segment
    exact le_of_eq hv

end

section

/-- The rectangle [-1,1] × [0,1] -/
def rectangle : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc 0 1

/-- The segment from (x₁, 0) to (x₂, 1). -/
def segment01 (x₁ x₂ : ℝ) : Set (ℝ × ℝ) :=
  segment ℝ (x₁, 0) (x₂, 1)

-- Collection 𝒫 of subsets P ⊆ [-1,1] × [0,1] satisfying (i) and (ii)
def P_collection : Set (Set (ℝ × ℝ)) :=
  { P | IsClosed P ∧ P ⊆ rectangle ∧
    -- (i) P is a union of line segments from (x₁, 0) to (x₂, 1)
    (∃ A : Set (ℝ × ℝ), A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1 ∧
      P = ⋃ (p ∈ A), segment01 p.1 p.2) ∧
    -- (ii) for all v with |v| ≤ 1/2, there exists x₁, x₂ ∈ [-1,1] with x₂ - x₁ = v and segment ⊆ P
    (∀ v : ℝ, |v| ≤ 1/2 → ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1
        ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

-- Define 𝒦 as the collection of non-empty compact subsets of ℝ²
def P_collection' : Set (NonemptyCompacts (ℝ × ℝ)) :=
  { P | IsClosed (P : Set (ℝ × ℝ)) ∧ (P : Set (ℝ × ℝ)) ⊆ rectangle ∧
    -- (i) P is a union of line segments from (x₁, 0) to (x₂, 1)
    (∃ A : Set (ℝ × ℝ), A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1 ∧
      P = ⋃ (p ∈ A), segment01 p.1 p.2) ∧
    -- (ii) for all v with |v| ≤ 1/2, there exists x₁, x₂ ∈ [-1,1] with x₂ - x₁ = v and segment ⊆ P
    (∀ v : ℝ, |v| ≤ 1/2 → ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1
        ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

/-- The carrier image of `P_collection'` recovers the original set-level collection `P_collection`. -/
theorem P_collection'_image_eq : (↑) '' P_collection' = P_collection := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    have h_compact : IsCompact P := by
      rw [isCompact_iff_isClosed_bounded]
      obtain ⟨h₁, h₂, _⟩ := hP
      constructor
      · exact h₁
      · rw [isBounded_iff]
        use 10
        intro x hx y hy
        have ⟨hfx1, hfx2⟩ := h₂ hx
        have ⟨hfy1, hfy2⟩ := h₂ hy
        have hx_bound : |x.1 - y.1| ≤ 2 := by
          calc
            |x.1 - y.1| ≤ |x.1| + |y.1| := abs_sub x.1 y.1
            _ ≤ 1 + 1 := by
              have : |x.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfx1)
              have : |y.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfy1)
              (expose_names; exact add_le_add this_1 this)
            _ = 2 := by norm_num
        have hy_bound : |x.2 - y.2| ≤ 2 := by
          calc
            |x.2 - y.2| ≤ |x.2| + |y.2| := abs_sub x.2 y.2
            _ ≤ 1 + 1 := by
              apply add_le_add
              · apply abs_le.2
                constructor -- From here on it is all Yuming
                · have : 0 ≤ x.2 := by aesop
                  have : (-1 : ℝ) ≤ 0 := by norm_num
                  expose_names; exact le_trans this this_1
                · aesop
              · apply abs_le.2
                constructor
                · have : 0 ≤ y.2 := by aesop
                  have : (-1 : ℝ) ≤ 0 := by norm_num
                  expose_names; exact le_trans this this_1
                · aesop
            _ = 2 := by norm_num
        calc
          dist x y = ‖x - y‖ := rfl
          _ ≤ |(x - y).1| + |(x - y).2| := by aesop
          _ ≤ 2 + 2 := add_le_add hx_bound hy_bound
          _ ≤ 10 := by norm_num
    have h_nonempty : P.Nonempty := by
      have h_seg_exists : ∃ x ∈ Icc (-1 : ℝ) 1, segment01 x x ⊆ P := by
        obtain ⟨_, _, _, h⟩ := hP
        specialize h 0 (by norm_num)
        obtain ⟨x₁, x₂, h₁, _, h₂⟩ := h
        have : x₁ = x₂ := by linarith [h₂]
        subst this
        obtain ⟨_, h₂⟩ := h₂
        exact ⟨x₁, h₁, h₂⟩
      rcases h_seg_exists with ⟨x, hx, h_seg⟩
      use (x, 0)
      exact h_seg (left_mem_segment ℝ (x, 0) (x, 1))
    simp only [mem_image]
    let Q : NonemptyCompacts (ℝ × ℝ) := ⟨⟨P, h_compact⟩, h_nonempty⟩
    use Q
    exact ⟨hP, rfl⟩

-- Define 𝒦 as the collection of non-empty compact subsets of ℝ²
def K_collection : Set (Set (ℝ × ℝ)) :=
  { K | K.Nonempty ∧ IsCompact K }

lemma P_isNonempty {P : Set (ℝ × ℝ)} (hP : P ∈ P_collection) :
    ∃ x ∈ Icc (-1 : ℝ) 1, segment01 x x ⊆ P := by
  -- BM: I broke this because I changed P_collection to be more correct
  obtain ⟨_, _, _, h⟩ := hP
  specialize h 0 (by norm_num)
  obtain ⟨x₁, x₂, hx₁, hx₂, h_diff, h_seg⟩ := h
  have : x₁ = x₂ := by linarith [h_diff]
  subst this
  exact ⟨x₁, hx₁, h_seg⟩
  -- exact Filter.frequently_principal.mp fun a ↦ a hx₁ h_seg

-- lemma exists_mem_P {P : Set (ℝ × ℝ)}
--   (h : ∃ x ∈ Icc (-1 : ℝ) 1, segment01 x x ⊆ P) :
--     ∃ p, p ∈ P := by
--   rcases h with ⟨x, hx, hseg⟩
--   have h_left : (x, 0) ∈ segment01 x x := by
--     dsimp [segment01]
--     exact left_mem_segment ℝ (x, 0) (x, 1)
--   exact ⟨(x, 0), hseg h_left⟩

-- BM: I'd phrase this as P_collection ⊆ K_collection
-- lemma P_collection_in_K_collection {P : Set (ℝ × ℝ)} (hP : P ∈ P_collection) :
--     P ∈ K_collection := by
--   -- obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
--   have h_nonempty : P.Nonempty := by
--     rcases P_isNonempty hP with ⟨x, hx, hseg⟩
--     refine ⟨(x, 0), hseg (left_mem_segment ℝ (x, 0) (x, 1))⟩
--   have h_compact : IsCompact P := by
--     rw [isCompact_iff_isClosed_bounded]
--     -- BM: I broke this because I changed P_collection to be more correct
--     obtain ⟨h₁, h₂, _⟩ := hP
--     -- obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
--     constructor
--     · exact h₁
--     · rw [isBounded_iff]
--       use 10
--       intro x hx y hy
--       have ⟨hfx1, hfx2⟩ := h₂ hx
--       have ⟨hfy1, hfy2⟩ := h₂ hy
--       have hx_bound : |x.1 - y.1| ≤ 2 := by
--         calc
--           |x.1 - y.1| ≤ |x.1| + |y.1| := abs_sub x.1 y.1
--           _ ≤ 1 + 1 := by
--             have : |x.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfx1)
--             have : |y.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfy1)
--             (expose_names; exact add_le_add this_1 this)
--           _ = 2 := by norm_num
--       have hy_bound : |x.2 - y.2| ≤ 2 := by
--         calc
--           |x.2 - y.2| ≤ |x.2| + |y.2| := abs_sub x.2 y.2
--           _ ≤ 1 + 1 := by
--             exact add_le_add
--               (abs_le.2 ⟨by linarith [hfx2.1], hfx2.2⟩)
--               (abs_le.2 ⟨by linarith [hfy2.1], hfy2.2⟩)
--           _ = 2 := by norm_num
--       calc
--         dist x y = ‖x - y‖ := rfl
--         _ ≤ |(x - y).1| + |(x - y).2| := by aesop
--         _ ≤ 2 + 2 := add_le_add hx_bound hy_bound
--         _ ≤ 10 := by norm_num
--   rw [K_collection]
--   exact mem_sep h_nonempty h_compact

lemma P_collection_sub_K_collection :
    P_collection ⊆ K_collection := by
  intro P hP
  -- obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
  have h_nonempty : P.Nonempty := by
    rcases P_isNonempty hP with ⟨x, hx, hseg⟩
    refine ⟨(x, 0), hseg (left_mem_segment ℝ (x, 0) (x, 1))⟩
  have h_compact : IsCompact P := by
    rw [isCompact_iff_isClosed_bounded]
    -- BM: I broke this because I changed P_collection to be more correct
    obtain ⟨h₁, h₂, _⟩ := hP
    -- obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
    constructor
    · exact h₁
    · rw [isBounded_iff]
      use 10
      intro x hx y hy
      have ⟨hfx1, hfx2⟩ := h₂ hx
      have ⟨hfy1, hfy2⟩ := h₂ hy
      have hx_bound : |x.1 - y.1| ≤ 2 := by
        calc
          |x.1 - y.1| ≤ |x.1| + |y.1| := abs_sub x.1 y.1
          _ ≤ 1 + 1 := by
            have : |x.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfx1)
            have : |y.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfy1)
            (expose_names; exact add_le_add this_1 this)
          _ = 2 := by norm_num
      have hy_bound : |x.2 - y.2| ≤ 2 := by
        calc
          |x.2 - y.2| ≤ |x.2| + |y.2| := abs_sub x.2 y.2
          _ ≤ 1 + 1 := by
            exact add_le_add
              (abs_le.2 ⟨by linarith [hfx2.1], hfx2.2⟩)
              (abs_le.2 ⟨by linarith [hfy2.1], hfy2.2⟩)
          _ = 2 := by norm_num
      calc
        dist x y = ‖x - y‖ := rfl
        _ ≤ |(x - y).1| + |(x - y).2| := by aesop
        _ ≤ 2 + 2 := add_le_add hx_bound hy_bound
        _ ≤ 10 := by norm_num
  exact mem_sep h_nonempty h_compact

open Filter

-- BM: Don't you want to assume K ∈ 𝒦 here?
/--
If `P n ∈ P_collection` for all `n` and `hausdorffDist (P n) K → 0`, then `K` satisfies
property (i): for every `k ∈ K` there are `x₁,x₂ ∈ [-1,1]` with
`segment01 x₁ x₂ ⊆ K` and `k ∈ segment01 x₁ x₂`.
-/
lemma P_collection.hausdorff_limit_property_i
  {P : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
  (hP : ∀ n, P n ∈ P_collection)
  (hK : K ∈ K_collection)
  (hKlim : Tendsto (fun n ↦ hausdorffDist (P n) K) atTop (𝓝 0)) :
  ∀ k ∈ K, ∃ x₁ ∈ Icc (-1 : ℝ) 1, ∃ x₂ ∈ Icc (-1 : ℝ) 1,
    segment01 x₁ x₂ ⊆ K ∧ k ∈ segment01 x₁ x₂ := by
  intro k hk
  -- By compactness of Icc(-1,1)×Icc(-1,1) extract a convergent subsequence
  have h_compact_sq : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=  by
    refine IsCompact.prod ?_ ?_
    · exact isCompact_Icc
    · exact isCompact_Icc
  sorry

theorem P_collection'_IsClosed : IsClosed P_collection' := by
  sorry

theorem P_collection'_IsComplete : CompleteSpace P_collection' := by
  haveI : CompleteSpace (NonemptyCompacts (ℝ × ℝ)) :=
    inferInstance
  have : IsClosed P_collection' := P_collection'_IsClosed
  sorry

end

end Besicovitch
