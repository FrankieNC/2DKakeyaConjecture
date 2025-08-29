import BesicovitchSet.Besicovitch
import Mathlib

set_option maxHeartbeats 300000

open Besicovitch Set Topology Metric Bornology TopologicalSpace MeasureTheory NNReal Filter

theorem P_col'_IsClosed' : IsClosed P_collection' := by
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

    have hA_sub : A ⊆ Icc ![-1, -1] ![1, 1] := by
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
