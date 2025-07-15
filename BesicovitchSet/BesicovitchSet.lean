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

end

namespace temp

def rectangle : Set (Fin 2 → ℝ) := Icc ![-1, 0] ![1,1]

def segment01 (x₁ x₂ : ℝ) : Set (Fin 2 → ℝ) :=
  segment ℝ ![x₁, 0] ![x₂, 1]

/-- The collection 𝒫 of subsets `P ⊆ rectangle` satisfying
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

/-- Any set in `P_collection` is non‑empty: the segment guaranteed by the
definition already gives a point. -/
theorem Nonempty_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    P.Nonempty := by
  rcases hP with ⟨-, -, -, h⟩
  rcases h 0 (by norm_num) with ⟨x₁, x₂, -, -, -, hPseg⟩
  exact ⟨![x₁, 0], hPseg <| by rw [segment01]; apply left_mem_segment⟩

theorem IsBounded_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsBounded (P : Set (Fin 2 → ℝ)) := by
  rcases hP with ⟨-, h_subset, -⟩
  have h_rect_bdd : IsBounded (rectangle : Set (Fin 2 → ℝ)) := by
    simp [rectangle, isBounded_Icc]
  exact h_rect_bdd.subset h_subset

theorem IsCompact_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsCompact (P : Set (Fin 2 → ℝ)) := by
  simpa [isCompact_iff_isClosed_bounded] using ⟨hP.1, IsBounded_P hP⟩

/-- The carrier image of `P_collection'` recovers the original set-level collection `P_collection`. -/
theorem P_collection'_image_eq : (↑) '' P_collection' = P_collection := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨⟨P, IsCompact_P hP⟩, Nonempty_P  hP⟩, hP, rfl⟩

open Filter

theorem 𝓟_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := IsBounded_P (h_mem n)
  have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := by
    apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
    exact NonemptyCompacts.nonempty (Pₙ n)
    · exact NonemptyCompacts.nonempty K
    · exact hPn_bdd n
    · exact hK_bdd

  obtain ⟨k, hk_in_K⟩ := K.nonempty

  have : ∀ n, ∃ p ∈ Pₙ n, dist p (k) ≤ dist K (Pₙ n) := by
    intro n
    simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
    obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
    have hpk : dist p k = Metric.infDist k (Pₙ n : Set _) := by
      simpa [eq_comm, dist_comm] using hp_eq
    have fin : EMetric.hausdorffEdist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) ≠ ⊤ := by
      simpa [EMetric.hausdorffEdist_comm] using fin_dist n
    have h_le : Metric.infDist k (Pₙ n : Set _) ≤ Metric.hausdorffDist (K : Set (Fin 2 → ℝ)) (Pₙ n : Set _) := by
      apply Metric.infDist_le_hausdorffDist_of_mem (x := k) (s := (K : Set _)) (t := (Pₙ n : Set _)) hk_in_K fin
    have h_dist : dist p k ≤ dist K (Pₙ n) := by
      simpa [Metric.NonemptyCompacts.dist_eq, hpk] using h_le
    exact ⟨p, hp_mem, h_dist⟩

  choose pₙ hpₙ_mem hpₙ_lt using this

  have h_tendsto : Tendsto pₙ atTop (𝓝 k) := by
    rw [NormedAddCommGroup.tendsto_atTop']
    intro ε hε
    obtain ⟨N, hN⟩ := h_lim ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have h_le : dist (pₙ n) k ≤ dist K (Pₙ n) := hpₙ_lt n
    have h_small : dist K (Pₙ n) < ε := by
      have := hN n (Nat.le_of_lt hn)
      simpa [dist_comm] using this
    have : dist (pₙ n) k < ε := lt_of_le_of_lt h_le h_small
    simpa [dist_eq] using this

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


  sorry

end temp


section

/-- The rectangle [-1,1] × [0,1] -/
def rectangle : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc 0 1

/-- The segment from (x₁, 0) to (x₂, 1). -/
def segment01 (x₁ x₂ : ℝ) : Set (ℝ × ℝ) :=
  segment ℝ (x₁, 0) (x₂, 1)

/-- Collection 𝒫 of subsets P ⊆ [-1,1] × [0,1] satisfying (i) and (ii) -/
def P_collection : Set (Set (ℝ × ℝ)) :=
  { P | IsClosed P ∧ P ⊆ rectangle ∧
    -- (i) P is a union of line segments from (x₁, 0) to (x₂, 1)
    (∃ A : Set (ℝ × ℝ), A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1 ∧
      P = ⋃ (p ∈ A), segment01 p.1 p.2) ∧
    -- (ii) for all v with |v| ≤ 1/2, there exists x₁, x₂ ∈ [-1,1] with x₂ - x₁ = v and segment ⊆ P
    (∀ v : ℝ, |v| ≤ 1/2 → ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1
        ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ P) }

/-- Define 𝒦 as the collection of non-empty compact subsets of ℝ² -/
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
  have ⟨hfx₁, hfx₂⟩ := h₂ hx
  have ⟨hfy1, hfy2⟩ := h₂ hy
  have hx_bound : |x.1 - y.1| ≤ 2 := by
    calc
      |x.1 - y.1| ≤ |x.1| + |y.1| := abs_sub x.1 y.1
      _ ≤ 1 + 1 := by
        refine add_le_add (abs_le.2 (mem_Icc.1 hfx₁)) (abs_le.2 (mem_Icc.1 hfy1))
      _ ≤ 2 := by norm_num
  have hy_bound : |x.2 - y.2| ≤ 2 := by
    calc
      |x.2 - y.2| ≤ |x.2| + |y.2| := abs_sub _ _
      _ ≤ 1 + 1 := by
        have hx2 : |x.2| ≤ 1 := by
          have hx2_nonneg : (0 : ℝ) ≤ x.2 := (mem_Icc.1 hfx₂).1
          have hx2_le1 : x.2 ≤ 1 := (mem_Icc.1 hfx₂).2
          simpa [abs_of_nonneg hx2_nonneg] using hx2_le1
        have hy2 : |y.2| ≤ 1 := by
          have hy2_nonneg : (0 : ℝ) ≤ y.2 := (mem_Icc.1 hfy2).1
          have hy2_le1 : y.2 ≤ 1 := (mem_Icc.1 hfy2).2
          simpa [abs_of_nonneg hy2_nonneg] using hy2_le1
        exact add_le_add hx2 hy2
      _ ≤ 2 := by norm_num
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
        have ⟨hfx₁, hfx₂⟩ := h₂ hx
        have ⟨hfy1, hfy2⟩ := h₂ hy
        have hx_bound : |x.1 - y.1| ≤ 2 := by
          calc
            |x.1 - y.1| ≤ |x.1| + |y.1| := abs_sub x.1 y.1
            _ ≤ 1 + 1 := by
              have : |x.1| ≤ 1 := abs_le.2 (mem_Icc.1 hfx₁)
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

open Filter

-- attribute [-instance] Scott.topologicalSpace

theorem 𝓟_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (ℝ × ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (ℝ × ℝ)) := P_is_bounded (h_mem n)
  have hK_bdd : IsBounded (K : Set (ℝ × ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (ℝ × ℝ)) ≠ ⊤ := by
    apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
    exact NonemptyCompacts.nonempty (Pₙ n)
    · exact NonemptyCompacts.nonempty K
    · exact hPn_bdd n
    · exact hK_bdd

  obtain ⟨k, hk_in_K⟩ := K.nonempty

  have : ∀ n, ∃ p ∈ Pₙ n, dist p (k) ≤ dist K (Pₙ n) := by
    intro n
    simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
    obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ n).isCompact.exists_infDist_eq_dist (Pₙ n).nonempty k
    have hpk : dist p k = Metric.infDist k (Pₙ n : Set _) := by
      simpa [eq_comm, dist_comm] using hp_eq
    have fin : EMetric.hausdorffEdist (K : Set (ℝ × ℝ)) (Pₙ n : Set _) ≠ ⊤ := by
      simpa [EMetric.hausdorffEdist_comm] using fin_dist n
    have h_le : Metric.infDist k (Pₙ n : Set _) ≤ Metric.hausdorffDist (K : Set (ℝ × ℝ)) (Pₙ n : Set _) := by
      apply Metric.infDist_le_hausdorffDist_of_mem (x := k) (s := (K : Set _)) (t := (Pₙ n : Set _)) hk_in_K fin
    have h_dist : dist p k ≤ dist K (Pₙ n) := by
      simpa [Metric.NonemptyCompacts.dist_eq, hpk] using h_le
    exact ⟨p, hp_mem, h_dist⟩

  choose pₙ hpₙ_mem hpₙ_lt using this

  have h_tendsto : Tendsto pₙ atTop (𝓝 k) := by
    rw [NormedAddCommGroup.tendsto_atTop']
    intro ε hε
    obtain ⟨N, hN⟩ := h_lim ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have h_le : dist (pₙ n) k ≤ dist K (Pₙ n) := hpₙ_lt n
    have h_small : dist K (Pₙ n) < ε := by
      have := hN n (Nat.le_of_lt hn)
      simpa [dist_comm] using this
    have : dist (pₙ n) k < ε := lt_of_le_of_lt h_le h_small
    simpa [dist_eq] using this

  -- have h_p_rect : ∀ n, pₙ n ∈ rectangle := by
  --   intro n
  --   sorry

  -- This is the x_1 x_2 sub n sequences stuff
  have h_comp : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := (isCompact_Icc.prod isCompact_Icc)
  -- I think I have to put the sequence have statements in the respective proofs

  -- This is for the proof of prop 1
  have h_union : ∃ A ⊆ Icc (-1) 1 ×ˢ Icc (-1) 1, ↑K = ⋃ p ∈ A, segment01 p.1 p.2 := by
    have h_seg_exists : ∀ n, ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1 : ℝ) 1 ∧ x₂ ∈ Icc (-1 : ℝ) 1 ∧ pₙ n ∈ segment01 x₁ x₂ ∧ segment01 x₁ x₂ ⊆ (Pₙ n : Set _) := by
      intro n
      rcases h_mem n with ⟨_, h_sub_rect, ⟨A, hA_sub, hA_eq⟩, _⟩
      have hpₙ : (pₙ n)  ∈ (Pₙ n : Set _) := hpₙ_mem n
      have hp_union : (pₙ n) ∈ ⋃ p ∈ A, segment01 p.1 p.2 := by
        simpa [hA_eq] using hpₙ
      rcases mem_iUnion.1 hp_union with ⟨p, hp_union'⟩
      rcases mem_iUnion.1 hp_union' with ⟨hpA, hp_seg⟩
      rcases Set.mem_prod.1 (hA_sub hpA) with ⟨hx₁, hx₂⟩
      have h_seg_subset : segment01 p.1 p.2 ⊆ (Pₙ n : Set _) := by
        intro x hx
        have : x ∈ ⋃ q ∈ A, segment01 q.1 q.2 := by
          exact mem_biUnion hpA hx
        simpa [hA_eq] using this
      exact ⟨p.1, p.2, hx₁, hx₂, hp_seg, h_seg_subset⟩

    choose x₁ x₂ hx₁ hx₂ h_pn_in_seg_n h_seg_subset_n using h_seg_exists


    set A : Set (ℝ × ℝ) := closure (Set.range fun n : ℕ ↦ (x₁ n, x₂ n)) with hA

    have hA_sub : A ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
      have h_range : (Set.range fun n : ℕ ↦ (x₁ n, x₂ n)) ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
        intro p hp
        rcases hp with ⟨n, rfl⟩
        exact mk_mem_prod (hx₁ n) (hx₂ n)
      have h_closed : IsClosed (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by exact isClosed_Icc.prod isClosed_Icc
      simpa [hA] using closure_minimal h_range h_closed

    have h_cover : (K : Set (ℝ × ℝ)) ⊆ ⋃ p ∈ A, segment01 p.1 p.2 := by
      intro k' hk'

      have h_pair_mem : ∀ n, (x₁ n, x₂ n) ∈ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
        intro n
        exact mk_mem_prod (hx₁ n) (hx₂ n)

      rcases h_comp.tendsto_subseq h_pair_mem with ⟨p, hp_in, φ, hφ_mono, hφ_lim⟩
      set a₁ : ℝ := p.1
      set a₂ : ℝ := p.2

      have ha₁ : a₁ ∈ Icc (-1 : ℝ) 1 := by simpa [a₁] using hp_in.1
      have ha₂ : a₂ ∈ Icc (-1 : ℝ) 1 := by simpa [a₂] using hp_in.2

      have h_pj : ∀ j : ℕ, ∃ p, p ∈ Pₙ (φ j) ∧ dist p k' ≤ dist K (Pₙ (φ j)) := by
        intro j
        sorry

      choose q hq_mem hq_dist using h_pj

      have hx_sub : ∀ j, (x₁ (φ j), x₂ (φ j)) ∈ Set.range (fun n : ℕ ↦ (x₁ n, x₂ n)) := by
        intro j
        exact ⟨φ j, rfl⟩
      sorry
    have h_seg_subset_K : (⋃ p ∈ A, segment01 p.1 p.2) ⊆ (K : Set _) := by
      intro y hy
      rcases mem_iUnion.1 hy with ⟨p, hp⟩
      rcases mem_iUnion.1 hp with ⟨hpA, hy_seg⟩
      have hc : segment01 p.1 p.2 ⊆ (K : Set _) := by sorry
      exact hc hy_seg

    have h_eq : (K : Set _) = ⋃ p ∈ A, segment01 p.1 p.2 := (Set.Subset.antisymm h_cover h_seg_subset_K)

    exact ⟨A, hA_sub, h_eq⟩

    -- have h_in_rect : ∀ n, (x₁ n, x₂ n) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun n ↦ mem_prod.2 ⟨hx₁ n, hx₂ n⟩

    -- -- This needs to be rephrased or maybe prove that the limits are in [-1,1] x [-1,1]
    -- have h_sub_ex : ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ) (x1_lim x2_lim : Icc (-1 : ℝ) 1), Tendsto (fun j ↦ x₁ (φ j)) atTop (𝓝 x1_lim) ∧ Tendsto (fun j ↦ x₂ (φ j)) atTop (𝓝 x2_lim) := by
    --   sorry

    -- choose φ hφ_strict x1_lim x2_lim h_tend₁ h_tend₂ using h_sub_ex
    -- set L := segment01 x1_lim x2_lim with hL
    -- have h_p_in_L : ∀ n, pₙ n ∈ L := by
    --   intro n
    --   rw [hL]
    --   -- Need to show that the segements converge to this limiting segment and the result will follow
    --   sorry
    -- have h_L_in_K : L ⊆ ↑K := by
    --   sorry
    -- have k_in_L : k ∈ L := by
    --   sorry
    -- sorry
    -- -- I need to define the set A:
    -- -- I take it to be the the set {(x_1 (n_j), (x_2 (n_j))}
    -- -- let A : Set (ℝ × ℝ) := (fun k : ℝ×ℝ => (x1_lim n, x2_lim n)) '' (↑K)


  have h_forall : ∀ (v : ℝ), |v| ≤ 1 / 2 → ∃ x₁ x₂,
      x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ ↑K := by
    intro v hv
    have h_exists : ∀ n, ∃ (x₁ x₂ : ℝ), x₁ ∈ Icc (-1) 1 ∧ x₂ ∈ Icc (-1) 1 ∧ x₂ - x₁ = v ∧ segment01 x₁ x₂ ⊆ Pₙ n := by
      intro n
      rcases h_mem n with ⟨_, _, _, h_prop₂⟩
      simpa using h_prop₂ v hv
    choose! x₁ x₂ hx₁ hx₂ hdiff h_segP using h_exists

    have h_pair_mem : ∀ n, (x₁ n, x₂ n) ∈ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
      intro n
      exact mk_mem_prod (hx₁ n) (hx₂ n)

    rcases h_comp.tendsto_subseq h_pair_mem with ⟨p, hp_in, φ, hφ_mono, hφ_lim⟩
    set a₁ : ℝ := p.1
    set a₂ : ℝ := p.2

    have ha₁ : a₁ ∈ Icc (-1 : ℝ) 1 := by simpa [a₁] using hp_in.1
    have ha₂ : a₂ ∈ Icc (-1 : ℝ) 1 := by simpa [a₂] using hp_in.2

    have h_gap : a₂ - a₁ = v := by
      have h_sub_lim : Tendsto (fun n : ℕ ↦ x₂ (φ n) - x₁ (φ n)) atTop (𝓝 (a₂ - a₁)) := by
        -- simpa [a₁, a₂] using (tendsto_sub ((tendsto_snd.comp hφ_lim)) ((tendsto_fst.comp hφ_lim)))
        sorry
      have h_const : Tendsto (fun _ : ℕ ↦ v) atTop (𝓝 v) := tendsto_const_nhds
      have h_ident : (fun n : ℕ ↦ x₂ (φ n) - x₁ (φ n)) = fun _ ↦ v := by
        funext n
        sorry
      sorry
      -- simpa [h_ident] using tendsto_nhds_unique h_const h_sub_lim

    have h_segK : segment01 a₁ a₂ ⊆ (K : Set (ℝ × ℝ)) := by
      intro y hy
      -- this rcases needs to be fixed
      rcases hy with ⟨t, w, ht0, ht1⟩

      have h_y_in_P : ∀ n, (1 - t) • (x₁ (φ n), (0 : ℝ)) + t • (x₂ (φ n), (1 : ℝ)) ∈ (Pₙ (φ n) : Set (ℝ × ℝ)) := by
        intro n
        have : (1 - t) • (x₁ (φ n), 0) + t • (x₂ (φ n), 1) ∈ segment01 (x₁ (φ n)) (x₂ (φ n)) := by
          sorry
          -- exact ⟨t, ht0, ht1, by ring⟩
        exact (h_segP (φ n)) this

      have h_tendsto_y : Tendsto (fun n ↦ (1 - t) • (x₁ (φ n), 0) + t • (x₂ (φ n), 1)) atTop (𝓝 y) := by
        sorry

      -- missing a have statemtn here

      have hyK : y ∈ K := by
        sorry

      exact hyK

    exact ⟨a₁, a₂, ha₁, ha₂, h_gap, h_segK⟩

  -- To prove this, we need to use property 1 maybe or 2. The proof relies on the fact that the lines are contained in teh rectangle
  have h_sub : (K : Set _) ⊆ rectangle := by
    have hP_sub : ∀ n, (Pₙ n : Set _) ⊆ rectangle := by
      intro n
      rcases h_mem n with ⟨_, h_subset, _, _⟩
      exact h_subset
    have rect_closed : IsClosed rectangle := by
      rw [rectangle]
      simp only [Icc_prod_Icc]
      exact isClosed_Icc

    -- Main argument
    intro k' hk'
    by_contra h_notin

    have h_pos : 0 < Metric.infDist k' (rectangle : Set (ℝ × ℝ)) := by
      have h_ne : Metric.infDist k' (rectangle : Set (ℝ × ℝ)) ≠ 0 := by
        intro h_eq
        have h_cl : k' ∈ closure (rectangle : Set (ℝ × ℝ)) := by
          rw [Metric.mem_closure_iff_infDist_zero]
          · exact h_eq
          · dsimp [rectangle]
            refine ⟨(0,0), (by simp)⟩
        have : k' ∈ rectangle := by
          simpa [rect_closed.closure_eq] using h_cl
        exact h_notin this
      exact lt_of_le_of_ne Metric.infDist_nonneg h_ne.symm

    set d : ℝ := Metric.infDist k' (rectangle : Set (ℝ × ℝ)) with hd
    have h_half_pos : 0 < d / 2 := by linarith
    obtain ⟨N, hN⟩ := h_lim (d / 2) h_half_pos

    have h_haus : hausdorffDist (K : Set (ℝ × ℝ)) (Pₙ N : Set _) < d / 2 := by
      have : dist (Pₙ N) K < d / 2 := hN N (le_rfl)
      simpa [Metric.NonemptyCompacts.dist_eq, dist_comm] using this

    have h_edist_ne : EMetric.hausdorffEdist (K : Set (ℝ × ℝ)) (Pₙ N : Set _) ≠ ⊤ := by
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

  rw [P_collection']
  exact ⟨h_closed, h_sub, h_union, h_forall⟩

-- Lemma 2.4 goes here

-- https://proofwiki.org/wiki/Subspace_of_Complete_Metric_Space_is_Closed_iff_Complete
lemma P_col'_CompleteSpace : CompleteSpace P_collection' := IsClosed.completeSpace_coe 𝓟_IsClosed

/-- The family of those `P : P_collection'` which have Lebesgue measure zero. -/
def zero_measure_sets : Set P_collection' := { P | volume (P : Set (ℝ × ℝ)) = 0 }

/-- Theorem 2.3.  The set of `P ∈ P_collection'` of Lebesgue measure zero is of second
    category (i.e. non-meager) in the complete metric space `P_collection'`. -/
theorem zero_measure_sets_second_category :
    ¬ IsMeagre (zero_measure_sets : Set P_collection') := by
  sorry

theorem exists_zero_measure_set : Nonempty zero_measure_sets := by
  rw [zero_measure_sets]
  sorry

theorem exists_besicovitch_set :
    ∃ B : Set (Fin 2 → ℝ), IsBesicovitch B := by
  obtain ⟨P0, hP0μ⟩ := exists_zero_measure_set
  set B := (P0 : Set (ℝ × ℝ)) with hB
  sorry

end

section

-- /-- In ℝ, there exists a Kakeya set. -/
theorem one_dim_exists_kakeya : ∃ s : Set ℝ, IsKakeya s := ⟨closedBall (0 : ℝ) 1, IsKakeya.ball⟩

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


-- /-- A Kakeya subset of ℝ has full Hausdorff dimension. -/
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

end

end Besicovitch
