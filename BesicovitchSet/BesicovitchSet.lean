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

section

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
  exact ⟨![x₁, 0], hPseg <| left_mem_segment _ _ _⟩

theorem IsBounded_P {P : Set (Fin 2 → ℝ)} (hP : P ∈ P_collection) :
    IsBounded P := by
  rcases hP with ⟨-, h_subset, -⟩
  have : IsBounded rectangle := by simp [rectangle, isBounded_Icc]
  exact this.subset h_subset

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

open Filter

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
    exact ⟨x 0, x 1, by simp_all [Pi.le_def, Fin.forall_fin_two], by simp_all [Pi.le_def, Fin.forall_fin_two], hdiff, hP⟩

  -- constructor
  -- · intro h v hv
  --   rcases h v hv with ⟨x₁, x₂, hx₁, hx₂, hdiff, hP⟩
  --   let x : Fin 2 → ℝ := ![x₁, x₂]
  --   have hx_mem : x ∈ Icc ![-1, -1] ![1, 1] := by simp_all [x, Pi.le_def, Fin.forall_fin_two]
  --   use x
  --   constructor; · exact hx_mem
  --   constructor
  --   · simp [x, hdiff]
  --   · exact hP
  -- · intro h v hv
  --   rcases h v hv with ⟨x, ⟨hx0, hx1⟩, hdiff, hP⟩
  --   use (x 0), (x 1)
  --   constructor; · simp_all [Pi.le_def, Fin.forall_fin_two]
  --   constructor; · simp_all [Pi.le_def, Fin.forall_fin_two]
  --   constructor; · simpa
  --   · exact hP

theorem THE_THING {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {x y z : E} :
    hausdorffDist (segment ℝ x z) (segment ℝ y z) ≤ dist x y := by
  sorry

theorem P_col'_IsClosed : IsClosed P_collection' := by
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isClosed
  rw [Metric.tendsto_atTop] at h_lim
  -- simp only [Metric.NonemptyCompacts.dist_eq] at h_lim
  have hPn_bdd (n : ℕ) : IsBounded (Pₙ n : Set (Fin 2 → ℝ)) := IsBounded_P (h_mem n)
  have hK_bdd : IsBounded (K : Set (Fin 2 → ℝ)) := (K.toCompacts.isCompact).isBounded
  have fin_dist (n : ℕ) : EMetric.hausdorffEdist (Pₙ n) (K : Set (Fin 2 → ℝ)) ≠ ⊤ := hausdorffEdist_ne_top_of_nonempty_of_bounded (Pₙ n).nonempty K.nonempty (hPn_bdd n) hK_bdd

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
      specialize hx k hk
      obtain ⟨x_lim, hx_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hx
      have h_seg_j_P : ∀ j, segment01 (x k hk (φ j) 0) (x k hk (φ j) 1) ⊆ Pₙ (φ j) := by
        intro j y hy
        apply h_seg_subset_n
        exact hy

      set L := segment01 (x_lim 0) (x_lim 1) with hL

      have aux0 : ∀ y ∈ L, ∀ j, ∃ y_n ∈ segment01 (x k hk (φ j) 0) (x k hk (φ j) 1), dist y_n y ≤ hausdorffDist L (segment01 (x k hk (φ j) 0) (x k hk (φ j) 1)) := by

        sorry

      choose y_n hy_n_mem hy_n_lt using aux0

      have h_seg_tendsto : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L), Tendsto (fun j ↦ y_n y hy (φ j)) atTop (𝓝 y) := by
        sorry

      have aux1 : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L) (j : ℕ), y_n y hy j ∈ (Pₙ (φ j)) := by
        intro y hy j
        sorry

      have aux2 : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L), ∃ k ∈ K, Tendsto (fun j => y_n y hy (φ j)) atTop (𝓝 k) := by
        sorry

      have hpA : x_lim ∈ A := by
        dsimp [A]
        constructor
        · exact hx_lim_mem
        · intro y hy
          obtain ⟨k, hkK, hk_lim⟩ := aux2 y hy
          have hy_lim : Tendsto (fun j => y_n y hy (φ j)) atTop (𝓝 y) := h_seg_tendsto y hy
          have : k = y := tendsto_nhds_unique hk_lim hy_lim
          rwa [← this]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mem_iUnion, exists_prop]
      use x_lim
      constructor
      · exact hpA
      · sorry
    · intro hk_union
      rcases mem_iUnion₂.1 hk_union with ⟨p, hpA, hk_seg⟩
      rw [hA] at hpA
      rcases hpA with ⟨_, hseg_sub⟩
      exact hseg_sub hk_seg

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

    have aux0 : ∀ y ∈ L, ∀ j, ∃ y_n ∈ segment01 (x (φ j) 0) (x (φ j) 1), dist y_n y ≤ hausdorffDist L (segment01 (x (φ j) 0) (x (φ j) 1)) := by
      sorry

    choose y_n hy_n_mem hy_n_lt using aux0

    have h_seg_tendsto : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L), Tendsto (fun j ↦ y_n y hy (φ j)) atTop (𝓝 y) := by
      sorry

    have aux1 : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L) (j : ℕ), y_n y hy j ∈ (Pₙ (φ j)) := by
      intro y hy j
      sorry

    have aux2 : ∀ (y : Fin 2 → ℝ) (hy : y ∈ L), ∃ k ∈ K, Tendsto (fun j => y_n y hy (φ j)) atTop (𝓝 k) := by
      sorry

    -- rw[NormedAddCommGroup.tendsto_atTop'] at h_seg_cont
    have hdiff_lim : (x_lim 1) - (x_lim 0) = v := by
      have h1 : Tendsto (fun n ↦ (x (φ n)) 1) atTop (𝓝 (x_lim 1)) := by
        sorry
      have h0 : Tendsto (fun n ↦ (x (φ n)) 0) atTop (𝓝 (x_lim 0)) := by
        sorry
      have hsub_lim : Tendsto (fun n ↦ (x (φ n) 1) - (x (φ n) 0)) atTop (𝓝 ((x_lim 1) - (x_lim 0))) := by
        exact h1.sub h0
      have hconst : (fun n ↦ x (φ n) 1 - x (φ n) 0) = fun _ ↦ v := by funext n; simp [hdiff]
      have hconst_lim : Tendsto (fun n ↦ x (φ n) 1 - x (φ n) 0) atTop (𝓝 v) := by
        simpa using hconst ▸ tendsto_const_nhds
      exact tendsto_nhds_unique hsub_lim hconst_lim

    have h_segK : segment01 (x_lim 0) (x_lim 1) ⊆ (K : Set _) := by
      intro y hy
      have hyL : y ∈ L := by simpa [hL] using hy
      rcases aux2 y hyL with ⟨k', hk'_in_K, hk'_lim⟩
      have hy_lim : Tendsto (fun j => y_n y hyL (φ j)) atTop (𝓝 y) := h_seg_tendsto y hyL
      have : k' = y := tendsto_nhds_unique hk'_lim hy_lim
      rwa [this] at hk'_in_K

    exact ⟨x_lim 0, x_lim 1, by simp_all [Fin.forall_fin_two, Pi.le_def], by simp_all [Fin.forall_fin_two, Pi.le_def], hdiff_lim, h_segK⟩

  exact ⟨h_closed, h_sub, h_union, h_forall⟩

--So I need to prove 2.4 which will be used to prove 2.5 which then implies 2.3

-- https://proofwiki.org/wiki/Subspace_of_Complete_Metric_Space_is_Closed_iff_Complete
lemma P_col'_CompleteSpace : CompleteSpace P_collection' := IsClosed.completeSpace_coe P_col'_IsClosed

lemma P_col'_BaireSpace [CompleteSpace P_collection'] : BaireSpace P_collection' := BaireSpace.of_pseudoEMetricSpace_completeSpace

noncomputable section

variable [CompleteSpace P_collection'] [BaireSpace P_collection']

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

/-- The “good cover’’ condition appearing in Lemma 2.4. -/
def hasThinCover (P : Set (Fin 2 → ℝ)) (v ε : ℝ) : Prop :=
  ∃ (R : Finset (Set (Fin 2 → ℝ))),
      -- every element of `R` is an axis–aligned rectangle
      (∀ r ∈ R, ∃ a b c d, r = axisRect a b c d) ∧
      -- each slice of `P` in the window is covered by `⋃ R`
      (∀ y, y ∈ window v ε →
        hSlice P y ⊆ hSlice (⋃ r ∈ R, (r : Set _)) y) ∧
      -- and the total horizontal length is < 100 ε

      -- Hmm
      (∀ y, y ∈ window v ε → (volume (hSlice (⋃ r ∈ R, (r : Set _)) y)).toReal < 100 * ε)

instance : MetricSpace P_collection' := inferInstance   -- inherits the Hausdorff metric `d`

/-- `𝒫(v, ε)` inside plain subsets of the big rectangle. -/
def P_v_eps (v ε : ℝ) : Set P_collection :=
  {P | hasThinCover P v ε}

/-- The same collection, but as a subset of the Hausdorff–metric
    space `NonemptyCompacts (Fin 2 → ℝ)`. -/
def P_v_eps' (v ε : ℝ) : Set P_collection' :=
  {P | hasThinCover (P : Set _) v ε}

-- Hmm
theorem image_coe_P_v_eps' (v ε : ℝ) :
    ((↑) : P_collection' → Set (Fin 2 → ℝ)) '' P_v_eps' v ε = P_v_eps v ε := by
  ext P
  sorry

-- theorem image_coe_P_v_eps' (v ε : ℝ):
--     (↑) '' P_v_eps' v ε = P_v_eps v ε := by
  -- ext P
  -- constructor
  -- · rintro ⟨Q, hQ, rfl⟩
  --   exact hQ
  -- · rintro ⟨hPcol, hthin⟩
  --   have h : P ∈ (↑) '' P_collection' := by rwa [← P_collection'_image_eq] at hPcol
  --   rcases h with ⟨Q, hQ, rfl⟩
  --   have hthin' : hasThinCover (Q : Set _) v ε := by simpa using hthin
  --   exact ⟨Q, ⟨hQ, hthin'⟩, rfl⟩

theorem P_v_eps'_nonempty {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    (P_v_eps' v ε).Nonempty := by
  let p : Fin 2 → ℝ := ![0, 0]
  have h_comp : IsCompact ({p} : Set (Fin 2 → ℝ)) := isCompact_singleton
  have h_nonempty : ({p} : Set (Fin 2 → ℝ)).Nonempty := by simp
  sorry

theorem P_v_eps_open {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsOpen (P_v_eps' v ε) := by
  rw [Metric.isOpen_iff]
  intro P hP
  rcases hP with ⟨R, h_rects, h_cover, h_le⟩
  dsimp only [ball]
  sorry

/--
In a Baire space, every nonempty open set is non‐meagre,
that is, it cannot be written as a countable union of nowhere‐dense sets.
-/
theorem nonempty_open_nonmeagre {X : Type*} {s : Set X}
  [TopologicalSpace X] [BaireSpace X]
  (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ IsMeagre s := fun h ↦ by
  rcases (dense_of_mem_residual (by rwa [IsMeagre] at h)).inter_open_nonempty s hs hne
    with ⟨x, hx, hxc⟩
  exact hxc hx

theorem P_v_eps_dense {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (P_v_eps' v ε) := by
  sorry

theorem lemma2_4 {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    IsClosed (P_v_eps' v ε)ᶜ ∧ IsNowhereDense (P_v_eps' v ε)ᶜ := by
  rw [isClosed_isNowhereDense_iff_compl]
  simp only [compl_compl]
  exact ⟨P_v_eps_open hv₀ hv₁ hε, P_v_eps_dense hv₀ hv₁ hε⟩

theorem P_v_eps'_not_meagre {v ε : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (hε : 0 < ε) :
    ¬ IsMeagre (P_v_eps' v ε) := by
  exact nonempty_open_nonmeagre (P_v_eps_open h0 h1 hε) (P_v_eps'_nonempty h0 h1 hε)

def Pn (n : ℕ): Set P_collection' := ⋂ r ∈ Finset.range (n + 1), P_v_eps' (r / n) ((1 : ℕ) / n)

def Pstar : Set P_collection' := ⋂ n, Pn n

lemma something0 (n r : ℕ) (hn : 0 < n) (hrn : r ≤ n) : ¬ IsMeagre (P_v_eps' (r / n) ((1 : ℕ) / n)) :=  by
  apply nonempty_open_nonmeagre
  · apply P_v_eps_open
    · positivity
    · rw [div_le_iff₀]
      simp only [one_mul, Nat.cast_le]
      · exact hrn
      · exact Nat.cast_pos'.mpr hn
    · positivity
  · apply P_v_eps'_nonempty
    · positivity
    · rw [div_le_iff₀]
      simp only [one_mul, Nat.cast_le]
      · exact hrn
      · exact Nat.cast_pos'.mpr hn
    · positivity

-- Easy, the finite intersection of open sets is open, then apply lemma from above
lemma something1 (n : ℕ) : ¬ IsMeagre (Pn n) := by
  have : IsOpen (Pn n) := by
    rw [Pn]
    sorry
  apply nonempty_open_nonmeagre
  · exact this
  · sorry

-- the tough part, we need lemma 2.4 here. the fact that the collection is dense
lemma something2 : ¬ IsMeagre (Pstar) := by
  by_contra! h
  sorry

def E_collection (u : ℝ) : Set P_collection' := {E | volume (hSlice (E : Set _) u) = 0}

theorem thm2_5 (u : ℝ) : ¬IsMeagre (E_collection u) := by
  sorry

/-- A set of second category (i.e. non-meagre) is nonempty. -/
lemma nonempty_of_not_IsMeagre {X : Type*} [TopologicalSpace X] {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using (meagre_empty)

--hmm
def P_zero_vol : Set P_collection' := {P | volume (P : Set (Fin 2 → ℝ)) = 0}

theorem thm2_3 : ¬IsMeagre P_zero_vol := by sorry

theorem Exists_P0 : P_zero_vol.Nonempty := by exact nonempty_of_not_IsMeagre thm2_3

theorem exists_besicovitch_set : ∃ (B : Set (Fin 2 → ℝ)), IsBesicovitch B := by
  sorry

end


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
theorem thing {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {x y z : E} :
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace (Set E)]

theorem segment_tendsto_hausdorff {x₁ x₂ : E} (x₁ₙ x₂ₙ : ℕ → E)
  (h₁ : Tendsto x₁ₙ atTop (𝓝 x₁)) (h₂ : Tendsto x₂ₙ atTop (𝓝 x₂)) :
    Tendsto (fun n ↦ (segment ℝ (x₁ₙ n) (x₂ₙ n))) atTop (𝓝 (segment ℝ x₁ x₂)) := by
  rw [@Metric.tendsto_atTop]
  haveI : MetricSpace (Set E) := by sorry
  intro ε hε
  -- simp [Metric.NonemptyCompacts.dist_eq]
  sorry

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
  (coveringNumber s r).map (fun (n : ℕ) => (n : ℝ).toNNReal)


-- noncomputable def ballRatio (s : Set α) (r : ℝ) : ℝ≥0∞ :=
--   if r > 0 then
--     if N s r = 0 then 0
--     else ENNReal.log ((N s r)) / (- ENNReal.log r)
--   else 0

-- noncomputable def upperBoxDim (s : Set α) : ℝ≥0∞ :=
  -- limsup (fun r => ballRatio s r) (𝓝[>] (0 : ℝ))

-- noncomputable def upper_minkowski_dim (s : Set α) : ℝ :=
--   limsup (𝓝[>] (0 : ℝ)) (fun r => if r > 0 then log ((N s r).toReal) / (- log r) else 0)

-- /-- Upper (box / Minkowski) dimension of a bounded (or totally bounded) set. -/
-- noncomputable def upper (s : Set α) : ℝ≥0∞ :=

-- /-- Lower Minkowski dimension of a set. -/
-- noncomputable def lower (s : Set α) : ℝ≥0∞ := sorry

-- /-- If upper = lower we speak of "the" Minkowski dimension. -/
-- noncomputable def dim (s : Set α) : ℝ≥0∞ :=
--   if h : upper s = lower s then upper s else 0  -- or leave undefined
