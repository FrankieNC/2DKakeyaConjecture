/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Closeds

/-!
# The Körner strip and its fibred segments in `ℝⁿ`

Fix `n` and work in `Fin (n+1) → ℝ`, viewing the last coordinate as *height* ranging over
`[0,1]` and the first `n` coordinates as a *cross-section* in `Fin n → ℝ`.  Körner's Baire
construction of a Besicovitch set studies closed sets built as unions of segments joining a
point `(x, 0)` on the bottom face to a point `(x', 1)` on the top face, subject to a spanning
condition: every cross-sectional displacement `v` with `‖v‖ ≤ 1/2` is realised.

This file sets up the ambient objects: the `strip`, the fibre `segment`s, and the collection
`kornerFamily` of admissible sets, together with their basic topological properties.

## Main definitions

* `stripPoint x h` : the point `(x, h) : Fin (n+1) → ℝ` with cross-section `x` and height `h`.
* `strip` : the slab `{p | ‖cross-section p‖ ≤ 1 ∧ p (last) ∈ [0,1]}`.
* `fibreSegment x₁ x₂` : the segment from `(x₁, 0)` to `(x₂, 1)`.
* `kornerFamily` : closed subsets of `strip` that are unions of fibre segments and realise
  every cross-sectional displacement of norm `≤ 1/2`.
* `kornerCompacts` : `kornerFamily` viewed inside `NonemptyCompacts (Fin (n+1) → ℝ)`.
* `hSlice S u` : the cross-sectional slice of `S` at height `u`.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Topology Metric Bornology TopologicalSpace Filter

namespace Besicovitch

variable {n : ℕ}

/-- The point of `Fin (n+1) → ℝ` with cross-section `x : Fin n → ℝ` (first `n` coordinates)
and height `h : ℝ` (last coordinate). -/
def stripPoint (x : Fin n → ℝ) (h : ℝ) : Fin (n + 1) → ℝ := Fin.snoc x h

/-- The cross-section coordinates of `stripPoint x h` recover `x`. -/
@[simp] lemma stripPoint_castSucc (x : Fin n → ℝ) (h : ℝ) (i : Fin n) :
    stripPoint x h i.castSucc = x i := Fin.snoc_castSucc ..

/-- The height coordinate of `stripPoint x h` is `h`. -/
@[simp] lemma stripPoint_last (x : Fin n → ℝ) (h : ℝ) :
    stripPoint x h (Fin.last n) = h := Fin.snoc_last ..

/-- `stripPoint` unfolds to `Fin.snoc`. -/
lemma stripPoint_eq_snoc (x : Fin n → ℝ) (h : ℝ) : stripPoint x h = Fin.snoc x h := rfl

/-- The **fibre segment** from `(x₁, 0)` to `(x₂, 1)` in `Fin (n+1) → ℝ`. -/
def fibreSegment (x₁ x₂ : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  segment ℝ (stripPoint x₁ 0) (stripPoint x₂ 1)

/-- The fibre segment is compact (continuous image of `[0,1]`). -/
lemma isCompact_fibreSegment (x₁ x₂ : Fin n → ℝ) : IsCompact (fibreSegment x₁ x₂) := by
  rw [fibreSegment, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- The **Körner strip**: cross-section of norm at most `1`, height in `[0,1]`. -/
def strip : Set (Fin (n + 1) → ℝ) :=
  {p | ‖(Fin.init p : Fin n → ℝ)‖ ≤ 1 ∧ p (Fin.last n) ∈ Icc (0 : ℝ) 1}

/-- The collection `𝒫` of admissible sets: closed subsets of `strip` that are unions of fibre
segments (indexed by an endpoint-pair set `A`) and realise every cross-sectional displacement
`v` with `‖v‖ ≤ 1/2`. -/
def kornerFamily : Set (Set (Fin (n + 1) → ℝ)) :=
  { P | IsClosed P ∧ P ⊆ strip ∧
      (∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        (∀ q ∈ A, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1) ∧ P = ⋃ q ∈ A, fibreSegment q.1 q.2) ∧
      (∀ v : Fin n → ℝ, ‖v‖ ≤ 1 / 2 →
        ∃ x₁ x₂ : Fin n → ℝ, ‖x₁‖ ≤ 1 ∧ ‖x₂‖ ≤ 1 ∧ x₂ - x₁ = v ∧
          fibreSegment x₁ x₂ ⊆ P) }

/-- `kornerFamily` viewed inside the complete metric space of nonempty compact sets with the
Hausdorff metric. -/
def kornerCompacts : Set (NonemptyCompacts (Fin (n + 1) → ℝ)) :=
  { P | (P : Set (Fin (n + 1) → ℝ)) ∈ kornerFamily }

/-- Unfolding lemma for membership in `kornerFamily`. -/
lemma mem_kornerFamily {P : Set (Fin (n + 1) → ℝ)} :
    P ∈ kornerFamily ↔ IsClosed P ∧ P ⊆ strip ∧
      (∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        (∀ q ∈ A, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1) ∧ P = ⋃ q ∈ A, fibreSegment q.1 q.2) ∧
      (∀ v : Fin n → ℝ, ‖v‖ ≤ 1 / 2 →
        ∃ x₁ x₂ : Fin n → ℝ, ‖x₁‖ ≤ 1 ∧ ‖x₂‖ ≤ 1 ∧ x₂ - x₁ = v ∧
          fibreSegment x₁ x₂ ⊆ P) := Iff.rfl

/-- Membership in `kornerCompacts` is membership of the carrier in `kornerFamily`. -/
@[simp] lemma mem_kornerCompacts {P : NonemptyCompacts (Fin (n + 1) → ℝ)} :
    P ∈ kornerCompacts ↔ (P : Set (Fin (n + 1) → ℝ)) ∈ kornerFamily := Iff.rfl

/-- Members of the Körner family are contained in the strip. -/
lemma kornerFamily_subset_strip {P : Set (Fin (n + 1) → ℝ)} (hP : P ∈ kornerFamily) :
    P ⊆ strip := hP.2.1

/-- Members of the Körner family are unions of fibre segments with endpoints in the
unit ball. -/
lemma kornerFamily_exists_iUnion_fibreSegment {P : Set (Fin (n + 1) → ℝ)}
    (hP : P ∈ kornerFamily) :
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      (∀ q ∈ A, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1) ∧ P = ⋃ q ∈ A, fibreSegment q.1 q.2 :=
  hP.2.2.1

/-- Members of the Körner family contain a fibre segment realising every cross-sectional
displacement `v` with `‖v‖ ≤ 1/2`. -/
lemma kornerFamily_exists_fibreSegment {P : Set (Fin (n + 1) → ℝ)} (hP : P ∈ kornerFamily)
    {v : Fin n → ℝ} (hv : ‖v‖ ≤ 1 / 2) :
    ∃ x₁ x₂ : Fin n → ℝ, ‖x₁‖ ≤ 1 ∧ ‖x₂‖ ≤ 1 ∧ x₂ - x₁ = v ∧ fibreSegment x₁ x₂ ⊆ P :=
  hP.2.2.2 v hv

/-- The cross-sectional slice of `S` at height `u`: the set of cross-sections `x` with
`(x, u) ∈ S`. -/
def hSlice (S : Set (Fin (n + 1) → ℝ)) (u : ℝ) : Set (Fin n → ℝ) :=
  {x | stripPoint x u ∈ S}

/-- A cross-section `x` lies in the height-`u` slice of `S` iff `(x, u) ∈ S`. -/
@[simp] lemma mem_hSlice {S : Set (Fin (n + 1) → ℝ)} {u : ℝ} {x : Fin n → ℝ} :
    x ∈ hSlice S u ↔ stripPoint x u ∈ S := Iff.rfl

/-! ## Infrastructure: `stripPoint`, `strip`. -/

/-- Dropping the height coordinate from `stripPoint x h` recovers the cross-section `x`. -/
@[simp] lemma init_stripPoint (x : Fin n → ℝ) (h : ℝ) :
    Fin.init (stripPoint x h) = x := Fin.init_snoc ..

/-- For fixed height `h`, the map `x ↦ stripPoint x h` is continuous. -/
@[fun_prop] lemma continuous_stripPoint (h : ℝ) :
    Continuous (fun x : Fin n → ℝ => stripPoint x h) :=
  Continuous.finSnoc continuous_id continuous_const

/-- If cross-sections `xn` converge to `x`, then `stripPoint (xn ·) h` converges to
`stripPoint x h`. -/
lemma tendsto_stripPoint {ι : Type*} {l : Filter ι} {xn : ι → Fin n → ℝ} {x : Fin n → ℝ}
    (h : ℝ) (hx : Tendsto xn l (𝓝 x)) :
    Tendsto (fun i => stripPoint (xn i) h) l (𝓝 (stripPoint x h)) :=
  hx.finSnoc tendsto_const_nhds

/-- A point lies in the strip iff its cross-section has norm `≤ 1` and its height lies
in `[0,1]`. -/
lemma mem_strip_iff {p : Fin (n+1) → ℝ} :
    p ∈ (strip : Set (Fin (n+1) → ℝ)) ↔
      ‖(Fin.init p : Fin n → ℝ)‖ ≤ 1 ∧ p (Fin.last n) ∈ Icc (0:ℝ) 1 := Iff.rfl

/-- `stripPoint x h` lies in the strip when `‖x‖ ≤ 1` and `h ∈ [0,1]`. -/
lemma stripPoint_mem_strip {x : Fin n → ℝ} {h : ℝ} (hx : ‖x‖ ≤ 1) (hh : h ∈ Icc (0:ℝ) 1) :
    stripPoint x h ∈ (strip : Set (Fin (n+1) → ℝ)) :=
  mem_strip_iff.2 ⟨by simpa using hx, by simpa using hh⟩

/-- The strip is closed. -/
lemma isClosed_strip : IsClosed (strip : Set (Fin (n+1) → ℝ)) := by
  have : (strip : Set (Fin (n+1) → ℝ)) =
      {p : Fin (n+1) → ℝ | ‖(Fin.init p : Fin n → ℝ)‖ ≤ 1} ∩
      {p : Fin (n+1) → ℝ | p (Fin.last n) ∈ Icc (0:ℝ) 1} :=
    Set.ext fun _ => mem_strip_iff
  rw [this]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_Icc.preimage (continuous_apply _))

/-- The strip is convex. -/
lemma convex_strip : Convex ℝ (strip : Set (Fin (n+1) → ℝ)) := by
  have h1 : Convex ℝ {p : Fin (n+1) → ℝ | ‖(Fin.init p : Fin n → ℝ)‖ ≤ 1} := by
    have : {p : Fin (n+1) → ℝ | ‖(Fin.init p : Fin n → ℝ)‖ ≤ 1}
        = LinearMap.funLeft ℝ ℝ Fin.castSucc ⁻¹' Metric.closedBall 0 1 := by
      ext p
      simp only [mem_setOf_eq, mem_preimage, mem_closedBall_zero_iff]
      rfl
    rw [this]
    exact (convex_closedBall 0 1).linear_preimage _
  exact h1.inter ((convex_Icc 0 1).linear_preimage (LinearMap.proj (Fin.last n)))

/-- The strip is contained in the closed unit ball. -/
lemma strip_subset_closedBall : (strip : Set (Fin (n+1) → ℝ)) ⊆ Metric.closedBall 0 1 := by
  intro p hp
  rw [mem_strip_iff] at hp
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  induction i using Fin.lastCases with
  | last => rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [hp.2.1], hp.2.2⟩
  | cast j => exact (norm_le_pi_norm (Fin.init p) j).trans hp.1

/-- The strip is bounded. -/
lemma isBounded_strip : IsBounded (strip : Set (Fin (n+1) → ℝ)) :=
  (Metric.isBounded_closedBall).subset strip_subset_closedBall

/-- The strip is compact. -/
lemma isCompact_strip : IsCompact (strip : Set (Fin (n+1) → ℝ)) :=
  isCompact_of_isClosed_isBounded isClosed_strip isBounded_strip

/-- The strip is nonempty. -/
lemma strip_nonempty : (strip : Set (Fin (n + 1) → ℝ)).Nonempty :=
  ⟨stripPoint 0 0, stripPoint_mem_strip (by simp) (by norm_num)⟩

/-- The parametrisation of `fibreSegment x₁ x₂` by height. -/
lemma fibreSegment_eq_image (x₁ x₂ : Fin n → ℝ) :
    fibreSegment x₁ x₂ =
      (fun y : ℝ => stripPoint (fun i => x₁ i + y * (x₂ i - x₁ i)) y) '' Icc (0 : ℝ) 1 := by
  rw [fibreSegment, segment_eq_image']
  refine image_congr fun y _ => funext fun i => ?_
  induction i using Fin.lastCases <;> simp

/-- Fibre segments with endpoints of norm ≤ 1 lie in the strip. -/
lemma fibreSegment_subset_strip {x₁ x₂ : Fin n → ℝ} (h₁ : ‖x₁‖ ≤ 1) (h₂ : ‖x₂‖ ≤ 1) :
    fibreSegment x₁ x₂ ⊆ (strip : Set (Fin (n+1) → ℝ)) :=
  convex_strip.segment_subset (stripPoint_mem_strip h₁ (by norm_num))
    (stripPoint_mem_strip h₂ (by norm_num))

/-- The Körner family is nonempty: the strip itself is compact, nonempty, closed,
contained in the strip, a union of fibre segments, and realises every displacement. -/
lemma nonempty_kornerCompacts : (kornerCompacts (n := n)).Nonempty := by
  refine ⟨⟨⟨strip, isCompact_strip⟩, strip_nonempty⟩, ?_⟩
  rw [mem_kornerCompacts, NonemptyCompacts.coe_mk, Compacts.coe_mk]
  refine ⟨isClosed_strip, subset_rfl,
    ⟨{q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1}, fun q hq => hq, ?_⟩, ?_⟩
  · -- strip = union of all fibre segments with endpoints in the unit ball
    apply Subset.antisymm
    · intro p hp
      rw [mem_strip_iff] at hp
      refine mem_iUnion₂.2 ⟨(Fin.init p, Fin.init p), ⟨hp.1, hp.1⟩, ?_⟩
      rw [fibreSegment, segment_eq_image']
      refine ⟨p (Fin.last n), ⟨hp.2.1, hp.2.2⟩, ?_⟩
      funext i
      induction i using Fin.lastCases with
      | last => simp [stripPoint_last]
      | cast k => simp [stripPoint_castSucc, Fin.init]
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 hp
      exact fibreSegment_subset_strip hq.1 hq.2 hpq
  · intro v hv
    have hv1 : ‖v‖ ≤ 1 := hv.trans (by norm_num)
    exact ⟨0, v, by norm_num, hv1, by simp, fibreSegment_subset_strip (by norm_num) hv1⟩

end Besicovitch
