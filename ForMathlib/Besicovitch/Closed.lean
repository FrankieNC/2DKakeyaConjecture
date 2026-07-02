/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Analysis.SegmentHausdorff
import ForMathlib.Besicovitch.Fibre

/-!
# Closedness of the Körner family

The Körner family, viewed inside the complete metric space of nonempty compact subsets of
`Fin (n+1) → ℝ` with the Hausdorff metric, is closed; consequently it is itself a complete
Baire space.  This is Körner's Lemma 2.2.

## Main results

* `isClosed_kornerCompacts` : `kornerCompacts` is closed in `NonemptyCompacts (Fin (n+1) → ℝ)`.
* The resulting `CompleteSpace` instance on `kornerCompacts` (from which the `BaireSpace`
  instance follows by instance resolution).

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Topology Metric Bornology TopologicalSpace NNReal Filter

namespace Besicovitch

variable {n : ℕ}

/-! ## `fibreSegment`-specific lemmas. -/

private lemma fibreSegment_nonempty (x₁ x₂ : Fin n → ℝ) : (fibreSegment x₁ x₂).Nonempty :=
  ⟨stripPoint x₁ 0, left_mem_segment ℝ _ _⟩

/-- If `L, T` are `fibreSegment`s, any `y ∈ L` has a point on `T` within the Hausdorff distance. -/
private lemma exists_mem_fibreSegment_dist_le
    {x₁ x₂ x₁' x₂' : Fin n → ℝ} {y : Fin (n+1) → ℝ}
    (hy : y ∈ fibreSegment x₁ x₂) :
    ∃ t ∈ fibreSegment x₁' x₂',
      dist t y ≤ hausdorffDist (fibreSegment x₁ x₂) (fibreSegment x₁' x₂') := by
  obtain ⟨t, ht_mem, ht_eq⟩ := (isCompact_fibreSegment x₁' x₂').exists_infDist_eq_dist
    (fibreSegment_nonempty x₁' x₂') y
  refine ⟨t, ht_mem, ?_⟩
  rw [dist_comm, ← ht_eq]
  exact infDist_le_hausdorffDist_of_mem hy (hausdorffEDist_segment_ne_top _ _ _ _)

/-- A point outside the closed `strip` has strictly positive distance to `strip`. -/
private theorem infDist_strip_pos_of_notMem {k' : Fin (n+1) → ℝ} (h_notin : k' ∉ strip) :
    0 < infDist k' strip :=
  (isClosed_strip.notMem_iff_infDist_pos strip_nonempty).1 h_notin

/-- Stability of `strip` under limits. -/
private theorem limit_subset_strip
    {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
    (h_mem : ∀ (m : ℕ), Pₙ m ∈ kornerCompacts)
    (h_lim : ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (Pₙ m) K < ε)
    (fin_dist : ∀ (m : ℕ),
      hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤) :
    (K : Set (Fin (n+1) → ℝ)) ⊆ strip := by
  intro k' hk'
  by_contra h_notin
  set d := infDist k' strip
  have hd_pos : 0 < d := infDist_strip_pos_of_notMem h_notin
  obtain ⟨N, hN⟩ := h_lim (d/2) (half_pos hd_pos)
  have hhd : hausdorffDist (K : Set (Fin (n+1) → ℝ)) (Pₙ N) < d/2 := by
    simpa [Metric.NonemptyCompacts.dist_eq, dist_comm] using hN N le_rfl
  obtain ⟨y, hyP, hy_lt⟩ := exists_dist_lt_of_hausdorffDist_lt hk' hhd
    (by simpa [hausdorffEDist_comm] using fin_dist N)
  have hd_le : d ≤ dist k' y :=
    infDist_le_dist_of_mem (kornerFamily_subset_strip (h_mem N) hyP)
  linarith

/-! ## Endpoint extraction. -/

/-- The set of admissible endpoint pairs of norm `≤ 1`. -/
private def ballPair (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {q | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1}

private lemma isCompact_ballPair : IsCompact (ballPair n) := by
  have : ballPair n = Metric.closedBall 0 1 ×ˢ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    ext q; simp [ballPair]
  rw [this]
  exact (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

/-- Every point of a member `P` of `kornerCompacts` lies on a `fibreSegment q.1 q.2` with
`q ∈ ballPair`, and that whole segment is inside `P`. -/
private theorem exists_fibreSegment_of_mem_kornerCompacts
    {P : NonemptyCompacts (Fin (n+1) → ℝ)} (hP : P ∈ kornerCompacts)
    {x : Fin (n+1) → ℝ} (hx : x ∈ (P : Set (Fin (n+1) → ℝ))) :
    ∃ q ∈ ballPair n, x ∈ fibreSegment q.1 q.2 ∧
      fibreSegment q.1 q.2 ⊆ (P : Set (Fin (n+1) → ℝ)) := by
  obtain ⟨A, hA_sub, hA_eq⟩ := kornerFamily_exists_iUnion_fibreSegment hP
  rcases mem_iUnion₂.1 (hA_eq ▸ hx : x ∈ ⋃ q ∈ A, fibreSegment q.1 q.2) with ⟨q, hqA, hq_seg⟩
  exact ⟨q, hA_sub q hqA, hq_seg,
    hA_eq ▸ fun y hy => mem_iUnion₂.2 ⟨q, hqA, hy⟩⟩

/-- For each `k ∈ K`, a point `p ∈ Pₙ m` at distance at most `dist K (Pₙ m)`. -/
private theorem exists_mem_dist_le_dist
  {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
  (fin_dist : ∀ (m : ℕ),
    hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤) :
    ∀ k ∈ (K : Set (Fin (n+1) → ℝ)), ∀ (m : ℕ),
      ∃ p ∈ (Pₙ m : Set (Fin (n+1) → ℝ)), dist p k ≤ dist K (Pₙ m) := by
  intro k hk m
  obtain ⟨p, hp_mem, hp_eq⟩ := (Pₙ m).isCompact.exists_infDist_eq_dist (Pₙ m).nonempty k
  refine ⟨p, hp_mem, ?_⟩
  rw [Metric.NonemptyCompacts.dist_eq, dist_comm, ← hp_eq]
  exact infDist_le_hausdorffDist_of_mem hk (by simpa [hausdorffEDist_comm] using fin_dist m)

private theorem tendsto_select_points
    {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
    (h_lim : ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (Pₙ m) K < ε) :
  ∀ (pₙ : (k : Fin (n+1) → ℝ) → k ∈ K → ℕ → Fin (n+1) → ℝ),
      (∀ k (hk : k ∈ (K : Set (Fin (n+1) → ℝ))) m, dist (pₙ k hk m) k ≤ dist K (Pₙ m)) →
      ∀ k (hk : k ∈ (K : Set (Fin (n+1) → ℝ))),
        Tendsto (fun m ↦ pₙ k hk m) atTop (𝓝 k) := by
  intro pₙ hle k hk
  have hPK : Tendsto (fun m => dist K (Pₙ m)) atTop (𝓝 0) := by
    simpa [dist_comm] using tendsto_iff_dist_tendsto_zero.1 (Metric.tendsto_atTop.2 h_lim)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (hle k hk) hPK)

/-- If fibre segments contained in `Pₙ (φ j)` have endpoint pairs converging to `q_lim`,
then the limit segment `fibreSegment q_lim.1 q_lim.2` is contained in `K`. -/
private lemma fibreSegment_lim_subset
    {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
    (h_lim : ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (Pₙ m) K < ε)
    (h_closed : IsClosed (K : Set (Fin (n+1) → ℝ)))
    (fin_dist : ∀ (m : ℕ),
      hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {q : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} {q_lim : (Fin n → ℝ) × (Fin n → ℝ)}
    (hlim1 : Tendsto (fun j => (q (φ j)).1) atTop (𝓝 q_lim.1))
    (hlim2 : Tendsto (fun j => (q (φ j)).2) atTop (𝓝 q_lim.2))
    (h_seg_sub : ∀ j, fibreSegment (q (φ j)).1 (q (φ j)).2 ⊆ (Pₙ (φ j) : Set (Fin (n+1) → ℝ))) :
    fibreSegment q_lim.1 q_lim.2 ⊆ (K : Set (Fin (n+1) → ℝ)) := by
  intro y hyL
  -- the approximating segments converge to the limit segment
  have h_seg_HD0 : Tendsto (fun j ↦
      hausdorffDist (fibreSegment (q (φ j)).1 (q (φ j)).2) (fibreSegment q_lim.1 q_lim.2))
      atTop (𝓝 0) :=
    tendsto_hausdorffDist_segment_of_tendsto_endpoints
      (tendsto_stripPoint 0 hlim1) (tendsto_stripPoint 1 hlim2)
  -- pick points `p j` on the approximating segments close to `y`
  choose p hpS hp_le using fun j =>
    exists_mem_fibreSegment_dist_le (x₁' := (q (φ j)).1) (x₂' := (q (φ j)).2) hyL
  have hdist_py : Tendsto (fun j ↦ dist (p j) y) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) hp_le
      (by simpa [hausdorffDist_comm] using h_seg_HD0)
  -- the sets `Pₙ (φ j)` converge to `K` in Hausdorff distance
  have hHD_PK : Tendsto (fun j ↦ hausdorffDist (Pₙ (φ j) : Set (Fin (n+1) → ℝ)) (K : Set _))
      atTop (𝓝 0) := by
    have : Tendsto (fun m ↦ dist (Pₙ m) K) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 (Metric.tendsto_atTop.2 h_lim)
    simpa [Metric.NonemptyCompacts.dist_eq, Function.comp_def]
      using this.comp hφ.tendsto_atTop
  -- project the `p j` onto `K`
  choose r hrK hr_eq using fun j =>
    K.isCompact.exists_infDist_eq_dist K.nonempty (p j)
  have hr_le_HD : ∀ j, dist (p j) (r j)
      ≤ hausdorffDist (Pₙ (φ j) : Set (Fin (n+1) → ℝ)) (K : Set _) := fun j =>
    hr_eq j ▸ infDist_le_hausdorffDist_of_mem (h_seg_sub j (hpS j)) (fin_dist (φ j))
  -- the projections converge to `y`
  have hdist_y_r : Tendsto (fun j ↦ dist y (r j)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j ↦ dist (p j) y
        + hausdorffDist (Pₙ (φ j) : Set (Fin (n+1) → ℝ)) (K : Set _)) atTop (𝓝 0) := by
      simpa using hdist_py.add hHD_PK
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ ?_) hsum
    calc dist y (r j) ≤ dist y (p j) + dist (p j) (r j) := dist_triangle y (p j) (r j)
      _ ≤ dist (p j) y + hausdorffDist (Pₙ (φ j) : Set (Fin (n+1) → ℝ)) (K : Set _) := by
          rw [dist_comm y (p j)]; exact add_le_add le_rfl (hr_le_HD j)
  exact h_closed.mem_of_tendsto
    (tendsto_iff_dist_tendsto_zero.2 (by simpa [dist_comm] using hdist_y_r))
    (Eventually.of_forall hrK)

/-- The union-of-fibre-segments representation of the limit `K`. -/
private theorem mem_iUnion_fibreSegment_of_limit
    {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
    (h_mem : ∀ (m : ℕ), Pₙ m ∈ kornerCompacts)
    (h_lim : ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (Pₙ m) K < ε)
    (h_closed : IsClosed (K : Set (Fin (n+1) → ℝ)))
    (fin_dist : ∀ (m : ℕ),
      hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤)
    (pₙ : (k : Fin (n+1) → ℝ) → k ∈ K → ℕ → Fin (n+1) → ℝ)
    (hpₙ_mem : ∀ (k : Fin (n+1) → ℝ) (a : k ∈ K) (m : ℕ), pₙ k a m ∈ Pₙ m)
    (h_tendsto : ∀ (k : Fin (n+1) → ℝ) (hk : k ∈ K),
      Tendsto (fun m ↦ pₙ k hk m) atTop (𝓝 k)) :
    ∀ k ∈ (K : Set (Fin (n+1) → ℝ)),
      k ∈ ⋃ q ∈ {q : (Fin n → ℝ) × (Fin n → ℝ) |
        q ∈ ballPair n ∧ fibreSegment q.1 q.2 ⊆ (K : Set (Fin (n+1) → ℝ))},
        fibreSegment q.1 q.2 := by
  intro k hk
  -- endpoint witnesses for each `m`
  choose q hqb h_pn_in_seg h_seg_sub using fun m =>
    exists_fibreSegment_of_mem_kornerCompacts (h_mem m) (hpₙ_mem k hk m)
  -- extract a convergent subsequence of the endpoint pairs
  obtain ⟨q_lim, hq_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_ballPair.tendsto_subseq hqb
  have hlim1 : Tendsto (fun j => (q (φ j)).1) atTop (𝓝 q_lim.1) :=
    (continuous_fst.tendsto q_lim).comp hφ_lim
  have hlim2 : Tendsto (fun j => (q (φ j)).2) atTop (𝓝 q_lim.2) :=
    (continuous_snd.tendsto q_lim).comp hφ_lim
  have h_seg_HD0 : Tendsto (fun j ↦
      hausdorffDist (fibreSegment (q (φ j)).1 (q (φ j)).2)
        (fibreSegment q_lim.1 q_lim.2)) atTop (𝓝 0) :=
    tendsto_hausdorffDist_segment_of_tendsto_endpoints
      (tendsto_stripPoint 0 hlim1) (tendsto_stripPoint 1 hlim2)
  refine mem_iUnion₂.2 ⟨q_lim, ⟨hq_lim_mem,
    fibreSegment_lim_subset h_lim h_closed fin_dist hφ hlim1 hlim2
      fun j => h_seg_sub (φ j)⟩, ?_⟩
  -- `k` lies on the limit segment
  have h_inf_to_zero : Tendsto
      (fun j ↦ infDist (pₙ k hk (φ j)) (fibreSegment q_lim.1 q_lim.2)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_seg_HD0
      (fun _ => infDist_nonneg) fun i => infDist_le_hausdorffDist_of_mem
        (h_pn_in_seg (φ i)) (hausdorffEDist_segment_ne_top _ _ _ _)
  have h_inf_to_k : Tendsto
      (fun j ↦ infDist (pₙ k hk (φ j)) (fibreSegment q_lim.1 q_lim.2)) atTop
      (𝓝 (infDist k (fibreSegment q_lim.1 q_lim.2))) :=
    ((continuous_infDist_pt _).tendsto k).comp ((h_tendsto k hk).comp hφ.tendsto_atTop)
  exact ((isCompact_fibreSegment _ _).isClosed.mem_iff_infDist_zero
    (fibreSegment_nonempty _ _)).2 (tendsto_nhds_unique h_inf_to_k h_inf_to_zero)

/-- The spanning property passes to the limit `K`. -/
private theorem exists_fibreSegment_subset_K_of_diff_le_half
    {Pₙ : ℕ → NonemptyCompacts (Fin (n+1) → ℝ)} {K : NonemptyCompacts (Fin (n+1) → ℝ)}
    (h_mem : ∀ (m : ℕ), Pₙ m ∈ kornerCompacts)
    (h_lim : ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (Pₙ m) K < ε)
    (h_closed : IsClosed (K : Set (Fin (n+1) → ℝ)))
    (fin_dist : ∀ (m : ℕ),
      hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤) :
    ∀ v : Fin n → ℝ, ‖v‖ ≤ 1 / 2 → ∃ x₁ x₂ : Fin n → ℝ,
      ‖x₁‖ ≤ 1 ∧ ‖x₂‖ ≤ 1 ∧ x₂ - x₁ = v ∧
        fibreSegment x₁ x₂ ⊆ (K : Set (Fin (n+1) → ℝ)) := by
  intro v hv
  -- For each `m` obtain a spanning pair inside `Pₙ m`.
  have h_exists : ∀ m, ∃ q : (Fin n → ℝ) × (Fin n → ℝ),
      q ∈ ballPair n ∧ q.2 - q.1 = v ∧ fibreSegment q.1 q.2 ⊆ (Pₙ m : Set _) := by
    intro m
    rcases kornerFamily_exists_fibreSegment (h_mem m) hv with ⟨x₁, x₂, hx₁, hx₂, hdiffn, hsegPn⟩
    exact ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, hdiffn, hsegPn⟩
  choose! q hqb hdiff h_segP using h_exists
  obtain ⟨q_lim, hq_lim_mem, φ, hφ, hφ_lim⟩ := isCompact_ballPair.tendsto_subseq hqb
  have hlim1 : Tendsto (fun j => (q (φ j)).1) atTop (𝓝 q_lim.1) :=
    (continuous_fst.tendsto q_lim).comp hφ_lim
  have hlim2 : Tendsto (fun j => (q (φ j)).2) atTop (𝓝 q_lim.2) :=
    (continuous_snd.tendsto q_lim).comp hφ_lim
  refine ⟨q_lim.1, q_lim.2, hq_lim_mem.1, hq_lim_mem.2,
    tendsto_nhds_unique (hlim2.sub hlim1) (by simp only [hdiff]; exact tendsto_const_nhds),
    fibreSegment_lim_subset h_lim h_closed fin_dist hφ hlim1 hlim2 fun j => h_segP (φ j)⟩

/-- **Main theorem**: `kornerCompacts` is closed in the Hausdorff metric. -/
theorem isClosed_kornerCompacts :
    IsClosed (kornerCompacts : Set (NonemptyCompacts (Fin (n+1) → ℝ))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro Pₙ K h_mem h_lim
  have h_closed : IsClosed (K : Set (Fin (n+1) → ℝ)) := K.isCompact.isClosed
  rw [Metric.tendsto_atTop] at h_lim
  have fin_dist (m : ℕ) :
      hausdorffEDist (Pₙ m : Set (Fin (n+1) → ℝ)) (K : Set (Fin (n+1) → ℝ)) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (Pₙ m).nonempty K.nonempty
      (isBounded_strip.subset (kornerFamily_subset_strip (h_mem m))) K.isCompact.isBounded
  refine ⟨h_closed, ?_, ?_, ?_⟩
  · exact limit_subset_strip h_mem h_lim fin_dist
  · -- union representation
    refine ⟨{q : (Fin n → ℝ) × (Fin n → ℝ) |
        q ∈ ballPair n ∧ fibreSegment q.1 q.2 ⊆ (K : Set (Fin (n+1) → ℝ))}, ?_, ?_⟩
    · rintro q ⟨hqb, -⟩; exact hqb
    · ext k
      constructor
      · intro hk
        choose pₙ hpₙ_mem hpₙ_le using exists_mem_dist_le_dist fin_dist
        exact mem_iUnion_fibreSegment_of_limit h_mem h_lim h_closed fin_dist pₙ hpₙ_mem
          (tendsto_select_points h_lim pₙ hpₙ_le) k hk
      · intro hk
        rcases mem_iUnion₂.1 hk with ⟨q, hqA, hk_seg⟩
        exact hqA.2 hk_seg
  · exact exists_fibreSegment_subset_K_of_diff_le_half h_mem h_lim h_closed fin_dist

/-- `kornerCompacts` is complete, being closed in a complete space. -/
instance : CompleteSpace (kornerCompacts (n := n)) :=
  isClosed_kornerCompacts.completeSpace_coe

end Besicovitch
