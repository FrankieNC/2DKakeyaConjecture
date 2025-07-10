/-
Copyright (c) 2025 Yes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Yuming Guo, Bhavik Mehta
-/

import Mathlib

namespace Besicovitch

open Set Real Topology Metric Bornology TopologicalSpace MeasureTheory MetricSpace

-- Formalise the entirety of Section 2. Section 4 is nonsense

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A subset of a normed real vector space `E` is Kakeya if it contains a segment of unit length in
every direction. -/
def IsKakeya {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) : Prop :=
    ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

/-- The universal set is Kakeya. -/
lemma univ_isKakeya : IsKakeya (Set.univ : Set E) := by simp [IsKakeya]

/-- If `s` is Kakeya and `s ⊆ t`, then `t` is Kakeya. -/
theorem IsKakeya.subset {s t : Set E} (h : IsKakeya s) (hs : s ⊆ t) : IsKakeya t := by
  intro v hv
  rcases h v hv with ⟨x, hx⟩
  exact ⟨x, hx.trans hs⟩

/-- The closed unit ball is Kakeya. -/
theorem IsKakeya.ball : IsKakeya (closedBall (0 : E) 1) := by
  intro v hv
  use -v
  intro y hy
  calc
    dist y 0 = ‖y - 0‖ := by simp
    _ ≤ ‖(-v) - 0‖ := by
      apply norm_sub_le_of_mem_segment
      simp only [neg_add_cancel] at hy
      rw [segment_symm]
      exact hy
    _ = ‖v‖ := by simp
    _ = 1 := hv

/-- In a nontrivial normed space, any Kakeya set is nonempty. -/
theorem IsKakeya.nonempty [Nontrivial E] {s : Set E} (h : IsKakeya s) : s.Nonempty := by
  obtain ⟨v, hv_norm⟩ := exists_norm_eq E zero_le_one
  rcases h v hv_norm with ⟨y, hy⟩
  exact ⟨y, hy (left_mem_segment ..)⟩

/--
A reformulation of the Kakeya condition: it suffices to check the existence of
a segment for all vectors with norm at most 1, rather than exactly 1.
-/
theorem isKakeya_iff_sub_unit [Nontrivial E] {s : Set E} :
    IsKakeya s ↔ ∀ v : E, ‖v‖ ≤ 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s := by
  constructor
  -- First, prove: IsKakeya s → ∀ v, ‖v‖ ≤ 1 → ∃ x, segment x x+v ⊆ s
  · intro h_kakeya v hv

    -- Case: v = 0
    by_cases h₀ : v = 0
    · simpa [h₀] using h_kakeya.nonempty

    -- Case: v ≠ 0
    · set u := ‖v‖⁻¹ • v with hu -- rescale v to a unit vector u
      have h₁ : ‖v‖ ≠ 0 := by
        contrapose! h₀
        rw [norm_eq_zero] at h₀
        exact h₀
      -- Now u has norm 1
      have h₂ : ‖u‖ = 1 := by field_simp [hu, norm_smul]
      -- By IsKakeya, s contains segment in direction u
      obtain ⟨x, hx⟩ := h_kakeya u h₂
      use x
      -- We want to show: segment x x+v ⊆ segment x x+u
      -- Since v is a scalar multiple of u, both segments lie along same ray
      have h₃ : segment ℝ x (x + v) ⊆ segment ℝ x (x + u) := by
        apply (convex_segment _ _).segment_subset (left_mem_segment _ _ _)
        rw [segment_eq_image']
        exact ⟨‖v‖, by simp [*]⟩
      -- Apply inclusion of segments to conclude result
      exact h₃.trans hx
  -- Converse: ∀ v, ‖v‖ ≤ 1 → ... ⇒ IsKakeya s
  · intro h_segment v hv
    exact h_segment v hv.le

/--
A Besicovitch set in `ℝⁿ` is a Kakeya set of Lebesgue measure zero.
-/
def IsBesicovitch {n : ℕ} (s : Set (Fin n → ℝ)) : Prop := IsKakeya s ∧ volume s = 0

theorem dimH_segment_eq_one (x y : E) (h : x ≠ y) :
    dimH (segment ℝ x y) = 1 := by
  sorry

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

theorem P_is_bounded {P : NonemptyCompacts (ℝ × ℝ)} (hP : P ∈ P_collection') :
    IsBounded (P : Set (ℝ × ℝ)) := by
  obtain ⟨h₁, h₂, _⟩ := hP
  rw [isBounded_iff]
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
      _ ≤ 2 := by norm_num
  have hy_bound : |x.2 - y.2| ≤ 2 := by
    sorry
  calc
    dist x y = ‖x - y‖ := rfl
    _ ≤ |(x - y).1| + |(x - y).2| := by aesop
    _ ≤ 2 + 2 := add_le_add hx_bound hy_bound
    _ ≤ 10 := by norm_num

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

-- -- Define 𝒦 as the collection of non-empty compact subsets of ℝ²
-- def K_collection : Set (Set (ℝ × ℝ)) :=
--   { K | K.Nonempty ∧ IsCompact K }

-- lemma P_isNonempty {P : Set (ℝ × ℝ)} (hP : P ∈ P_collection) :
--     ∃ x ∈ Icc (-1 : ℝ) 1, segment01 x x ⊆ P := by
--   -- BM: I broke this because I changed P_collection to be more correct
--   obtain ⟨_, _, _, h⟩ := hP
--   specialize h 0 (by norm_num)
--   obtain ⟨x₁, x₂, hx₁, hx₂, h_diff, h_seg⟩ := h
--   have : x₁ = x₂ := by linarith [h_diff]
--   subst this
--   exact ⟨x₁, hx₁, h_seg⟩
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

-- lemma P_collection_sub_K_collection :
--     P_collection ⊆ K_collection := by
--   intro P hP
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
--   exact mem_sep h_nonempty h_compact

open Filter

-- attribute [-instance] Scott.topologicalSpace

theorem 𝓟_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (ℝ × ℝ)) := (K.toCompacts.isCompact).isClosed
  obtain ⟨k, hk_in_K⟩ := K.nonempty
  rw [Metric.tendsto_atTop] at h_lim
  simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (ℝ × ℝ)) := P_is_bounded (h_mem n)
  have hK_bdd : IsBounded (K : Set (ℝ × ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (ℝ × ℝ)) ≠ ⊤ := by
    apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
    exact NonemptyCompacts.nonempty (Pₙ n)
    · exact NonemptyCompacts.nonempty K
    · exact hPn_bdd n
    · exact hK_bdd
  have h_haus (n : ℕ) : hausdorffDist (K : Set (ℝ × ℝ)) (Pₙ n : Set (ℝ × ℝ)) < (1 : ℝ)/(n+1) := by
    rcases h_lim (1/(n+1)) (by positivity) with ⟨N, hN⟩
    sorry
    -- have : hausdorffDist (Pₙ n) K < 1/(n+1) := by
      -- sorry
    -- hN n (le_refl _)
    -- simpa [Metric.hausdorffDist_comm] using this
  choose pₙ hpₙ_mem hpₙ_lt using fun n ↦
    Metric.exists_dist_lt_of_hausdorffDist_lt
      (x := k) (s := K) (t := Pₙ n) (r := (1 : ℝ) / (n + 1))
      hk_in_K
      (h_haus n)
      (by simpa [EMetric.hausdorffEdist_comm] using fin_dist n)
      -- (by
      -- rcases h_lim (1 / ((n : ℕ) + 1)) (by positivity) with ⟨N, hN⟩
      -- have : ∀ (n : ℕ), hausdorffDist K (Pₙ n) < 1 / (n + 1)) := hN n (le_refl)
      -- simpa [Metric.hausdorffDist_comm] using sorry)
      -- (by
        -- have hfin : EMetric.hausdorffEdist (Pₙ n) (K : Set _) ≠ ⊤ := fin_dist n
        -- simpa [EMetric.hausdorffEdist_comm] using hfin)
  -- choose pₙ hpₙ_mem hpₙ_lt using fun n ↦
  --   Metric.exists_dist_lt_of_hausdorffDist_lt hk_in_K

  -- Hmm, this may not be correct, investigate further
  have h_sub : (K : Set _) ⊆ rectangle := by
    have hP_sub : ∀ n, (Pₙ n : Set _) ⊆ rectangle := by
      intro n
      specialize h_mem n
      obtain ⟨_, ⟨h⟩⟩ := h_mem
      exact h
    sorry
  have h_union : ∃ A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1, ↑K = ⋃ p ∈ A, segment01 p.1 p.2 := by
    sorry
  have h_forall : ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂,
      x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ ↑K := by
    intro v hv

    sorry
  rw [P_collection']
  exact ⟨h_closed, h_sub, h_union, h_forall⟩

  --   let A : Set (ℝ × ℝ) :=
  --   { p | p.1 ∈ Icc (-1 : ℝ) 1
  --        ∧ p.2 ∈ Icc (-1 : ℝ) 1
  --        ∧ segment01 p.1 p.2 ⊆ (K : _) }
  --   use A
  --   have hA : A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1 := by
  --     simp only [Icc_prod_Icc, subset_def, and_assoc]
  --     intro a ha
  --     aesop
  --   refine ⟨hA, ext fun x ↦ by
  --     constructor
  --     · intro hxK
  --       sorry
  --     · intro hx
  --       sorry
  --       ⟩
  -- have h_forall : ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂,
  --     x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ ↑K := by
  --   intro v hv
  --   use 0, 0
  --   constructor
  --   · simp
  --   · constructor
  --     · simp
  --     · constructor
  --       · simp only [sub_self]
  --         sorry
  --       · sorry
  -- have h_rect_closed : IsClosed rectangle :=
  --   isClosed_Icc.prod isClosed_Icc
  -- have h_sub : (K : Set _) ⊆ rectangle := by
  --   have h_in : ∀ n, F n ∈ {t | t ⊆ rectangle} := fun n ↦ (h_mem n).2.1
  --   sorry
  -- dsimp [P_collection'] at *
  -- exact ⟨h_closed, h_sub, h_union, h_forall⟩

-- Lemma 2.4 goes here

/-- In ℝ, there exists a Kakeya set. -/
theorem one_dim_exists_kakeya : ∃ s : Set ℝ, IsKakeya s := ⟨closedBall (0 : ℝ) 1, IsKakeya.ball⟩

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

/-- If a set contains some unit‐interval, then its dimH ≥ 1. -/
lemma dimH_of_contains_Icc {K : Set ℝ} {x₀} (h : Icc x₀ (x₀ + 1) ⊆ K) :
    1 ≤ dimH K := by
  calc
    1 = dimH (Icc x₀ (x₀ + 1)) := (dimH_Icc_length_one x₀).symm
    _ ≤ dimH K := dimH_mono h

/-- Any subset of `ℝ` has dimH ≤ 1. -/
lemma dimH_le_one_univ : ∀ (K : Set ℝ), dimH K ≤ 1 := fun K ↦ by
  calc
    dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = Module.finrank ℝ ℝ := by simp [dimH_univ]
    _ = 1 := by simp

/-- Any Kakeya set in `ℝ` has full Hausdorff dimension. -/
theorem dimH_kakeya_eq_one (K : Set ℝ) (hK : IsKakeya K) :
    dimH K = 1 := by
  rcases kakeya_contains_unit_Icc hK with ⟨x₀, hsub⟩
  exact le_antisymm (dimH_le_one_univ K) (dimH_of_contains_Icc hsub)

/-- Kakeya conjecture in ℝ: there exists a Kakeya set of Hausdorff dimension 1. -/
theorem one_dim_kakeya_conjecture : ∃ s : Set ℝ, IsKakeya s ∧ dimH s = 1 := by
  refine ⟨closedBall (0 : ℝ) 1, ⟨IsKakeya.ball, dimH_kakeya_eq_one _ IsKakeya.ball⟩⟩


-- /-- A Kakeya subset of ℝ has full Hausdorff dimension. -/
-- theorem dimH_kakeya_eq_one (K : Set ℝ)
--   (hK : IsKakeya K) :
--     dimH K = 1 := by
--   rw [IsKakeya] at hK
--   specialize hK 1
--   simp only [norm_one, le_add_iff_nonneg_right, zero_le_one, segment_eq_Icc, forall_const] at hK
--   rcases hK with ⟨x₀, hseg⟩
--   have hIcc_sub : Icc x₀ (x₀ + 1) ⊆ K := by
--     simpa [segment_eq_Icc (by linarith : x₀ ≤ x₀ + 1)] using hseg
--   have hlow : 1 ≤ dimH K := by
--     have eq1 : dimH (Icc x₀ (x₀ + 1)) = 1 := by
--       have nin : (interior (Icc x₀ (x₀ + 1))).Nonempty := by
--         rw [interior_Icc]; simp
--       calc
--         dimH (Icc x₀ (x₀ + 1)) = Module.finrank ℝ ℝ := Real.dimH_of_nonempty_interior nin
--         _ = 1 := by simp
--     calc
--       1 = dimH (Icc x₀ (x₀ + 1)) := eq1.symm
--       _ ≤ dimH K := by apply dimH_mono; exact hseg
--   have hup : dimH K ≤ 1 := by
--     calc
--       dimH K ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ K)
--       _ = Module.finrank ℝ ℝ := by simp only [Module.finrank_self, Nat.cast_one, dimH_univ]
--       _ = 1 := by simp
--   apply le_antisymm
--   · exact hup
--   · exact hlow

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

/-- Proposition 3.4 (Fox):
For any subset `A` of `ℝⁿ` there is a G₀‐set `G` with `A ⊆ G` and `dimH G = dimH A`. -/
-- theorem exists_Gδ_of_dimH {n : ℕ} (A : Set (Fin n → ℝ)) :
--     ∃ G : Set (Fin n → ℝ), IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
--   -- set s := dimH A with hs
--   -- have hs_nonneg : 0 ≤ dimH A := by positivity
--   obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0∞) < 1 by norm_num)
--   have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
--     tendsto_nhdsWithin_mono_right
--       (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
--   choose G' hG'_Gδ subG' meas_eq' using
--     fun k : ℕ ↦
--       have : (0 : ℝ) ≤ (dimH A + φ k).toReal := by positivity
--       asdf this A
--   let G := ⋂ k, G' k
--   have iGδ : IsGδ G := IsGδ.iInter fun k ↦ hG'_Gδ k
--   have Asub : A ⊆ G := subset_iInter fun k ↦ subG' k
--   have hge : dimH A ≤ dimH G := dimH_mono Asub
--   have hle : dimH G ≤ dimH A := by
--     rw [← forall_gt_iff_le]
--     intro t ht
--     have hpos : 0 < (t - dimH A) := by simpa
--     rw [ENNReal.tendsto_atTop_zero] at h₃φ
--     rcases (h₃φ _ hpos) with ⟨k, hφk⟩
--     set d := (dimH A + φ k) with hd
--     have h₅φ: 0 < φ k := by sorry
--     have hlt : dimH A < d.toNNReal := sorry --by simpa [hd] using lt_add_iff_pos_right.2 h₅φ
--     have hμA₀ : μH[d.toReal] A = 0 := hausdorffMeasure_of_dimH_lt hlt
--     have hμA : μH[d.toReal] (G' k) = 0 := -- (meas_eq' k).trans hμA₀
--       sorry
--       -- simpa [hd] using lt_add_iff_pos_right.2 h₅φ
--     have aux : μH[t.toReal] G = 0 := by
--       have : μH[t.toReal] G ≤ 0 := by
--         calc
--           μH[t.toReal] G ≤ μH[t.toReal] (G' k) := by sorry
--           _ ≤ μH[d.toReal] (G' k) := by sorry
--           _ = 0 := by sorry
--       exact le_bot_iff.1 this
--     have : μH[t.toReal] G ≤ μH[d.toReal] (G' k) := by sorry
--     sorry
--     -- rw [dimH_eq_iInf]
--     -- sorry
--   exact ⟨G, iGδ, Asub, le_antisymm hle hge⟩

theorem exists_Gδ_of_dimH {n : ℕ} (A : Set (Fin n → ℝ)) :
    ∃ G : Set (Fin n → ℝ), IsGδ G ∧ A ⊆ G ∧ dimH G = dimH A := by
  -- set s := dimH A with hs
  -- have hs_nonneg : 0 ≤ dimH A := by positivity
  observe dimHA_ne_top : dimH A ≠ ⊤
  observe dimHA_nt_top : dimH A < ⊤
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0∞) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right
      (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  choose G' hG'_Gδ subG' meas_eq' using
    fun k : ℕ ↦
      have : (0 : ℝ) ≤ (dimH A + φ k).toReal := by positivity
      asdf this A
  let G := ⋂ k, G' k
  have iGδ : IsGδ G := IsGδ.iInter fun k ↦ hG'_Gδ k
  have Asub : A ⊆ G := subset_iInter fun k ↦ subG' k
  have hge : dimH A ≤ dimH G := dimH_mono Asub
  have hle : dimH G ≤ dimH A := dimH_le fun d' hd' ↦ by
    by_contra! hgt
    have hd_pos : 0 < (d' : ℝ≥0∞) - dimH A := by aesop
    rw [ENNReal.tendsto_atTop_zero] at h₃φ
    rcases h₃φ _ hd_pos with ⟨k, hφk_lt⟩
    set D := (dimH A + φ k) with hD
    specialize h₂φ k
    simp only [mem_Ioo] at h₂φ
    cases' h₂φ with hφk_gt_0 hφk_lt_1
    have hφk_ne_top : φ k ≠ ⊤ := LT.lt.ne_top hφk_lt_1
    have hlt : (dimH A) < D.toNNReal := by
      -- add_lt_add_left hpos (dimH A)
      -- simpa [hD] using lt_add_iff_pos_right.2 h₅φ
      rw [hD]
      sorry
    have hμA : μH[D.toNNReal] A = 0 := hausdorffMeasure_of_dimH_lt hlt
      -- simpa [hD] using hausdorffMeasure_of_dimH_lt (by simpa using hlt)
      -- hausdorffMeasure_of_dimH_lt hlt
    have hμGk : μH[D.toReal] (G' k) = 0 := (meas_eq' k).trans hμA
    have hmono : μH[d'.toReal] G ≤ μH[D.toReal] (G' k) := by
      calc
        μH[d'.toReal] G ≤ μH[d'.toReal] (G' k) := by
          apply measure_mono
          exact iInter_subset_of_subset k fun ⦃a⦄ a ↦ a
        _ ≤ μH[D.toReal] (G' k) := by
          apply hausdorffMeasure_mono
          apply le_of_lt
          rw [hD]
          specialize hφk_lt k
          simp only [ge_iff_le, le_refl, forall_const] at hφk_lt
          sorry
    have h0 : μH[d'.toReal] G = 0 := by
      have hbot : μH[d'.toReal] G ≤ 0 := by
        apply hmono.trans_eq
        exact hμGk
      exact le_bot_iff.1 hbot
    simp [h0] at hd'
  exact ⟨G, iGδ, Asub, le_antisymm hle hge⟩

end

end Besicovitch
