/-
Copyright (c) 2025 Yes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck, Yuming Guo, Bhavik Mehta
-/

import Mathlib

namespace Besicovitch

open Set Real Topology Metric Bornology

-- Formalise the entirity of Section 2. Section 4 is nonsense

def IsKakeya {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) : Prop :=
    ∀ v : E, ‖v‖ = 1 → ∃ x : E, segment ℝ x (x + v) ⊆ s

def IsBesicovitch {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (s : Set (Fin n → ℝ)) : Prop :=
    IsKakeya s ∧ MeasureTheory.volume s = 0

-- The rectangle [-1,1] × [0,1]
def rectangle : Set (ℝ × ℝ) :=
  { p | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc 0 1 }

-- Segment from (x₁, 0) to (x₂, 1)
def segment01 (x₁ x₂ : ℝ) : Set (ℝ × ℝ) :=
  segment ℝ (x₁, 0) (x₂, 1)

-- Collection 𝒫 of subsets P ⊆ [-1,1] × [0,1] satisfying (i) and (ii)
def P_collection : Set (Set (ℝ × ℝ)) :=
  { P | IsClosed P ∧ P ⊆ rectangle ∧
    -- (i) P is a union of line segments from (x₁, 0) to (x₂, 1)
    ∃ A : Set (ℝ × ℝ), A ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ∧
      P = ⋃ (p ∈ A), segment01 p.1 p.2 ∧
    -- P = ⋃ (x₁ ∈ Icc (-1 : ℝ) 1) (x₂ ∈ Icc (-1 : ℝ) 1), segment01 x₁ x₂ ∧
    -- (∀ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1) 1 → x₂ ∈ Icc (-1) 1 →
      -- segment01 x₁ x₂ ⊆ P ∨ segment01 x₁ x₂ ∩ P = ∅) ∧
    -- (ii) for all v with |v| ≤ 1/2, there exists x₁, x₂ ∈ [-1,1] with x₂ - x₁ = v and segment ⊆ P
    (∀ v : ℝ, |v| ≤ 1/2 → ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1
        ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

-- Define 𝒦 as the collection of non-empty compact subsets of ℝ²
def K_collection : Set (Set (ℝ × ℝ)) :=
  { K | K.Nonempty ∧ IsCompact K }

lemma P_isNonempty {P : Set (ℝ × ℝ)} (hP : P ∈ P_collection) :
    ∃ x ∈ Icc (-1 : ℝ) 1, segment01 x x ⊆ P := by
  obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
  specialize h₅b 0 (by norm_num)
  obtain ⟨x₁, x₂, hx₁, hx₂, h_diff, h_seg⟩ := h₅b
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

lemma P_collection_in_K_collection {P : Set (ℝ × ℝ)} (hP : P ∈ P_collection) :
    P ∈ K_collection := by
  -- obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
  have h_nonempty : P.Nonempty := by
    rcases P_isNonempty hP with ⟨x, hx, hseg⟩
    refine ⟨(x, 0), hseg (left_mem_segment ℝ (x, 0) (x, 1))⟩
  have h_compact : IsCompact P := by
    rw [isCompact_iff_isClosed_bounded]
    obtain ⟨h₁, ⟨h₂, ⟨h₃, ⟨h₄, ⟨h₅a, h₅b⟩⟩⟩⟩⟩ := hP
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
  rw [K_collection]
  exact mem_sep h_nonempty h_compact

open Filter

/--
If `P n ∈ P_collection` for all `n` and `hausdorffDist (P n) K → 0`, then `K` satisfies
property (i): for every `k ∈ K` there are `x₁,x₂ ∈ [-1,1]` with
`segment01 x₁ x₂ ⊆ K` and `k ∈ segment01 x₁ x₂`.
-/
lemma P_collection.hausdorff_limit_property_i
  {P : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
  (hP : ∀ n, P n ∈ P_collection)
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

end Besicovitch
