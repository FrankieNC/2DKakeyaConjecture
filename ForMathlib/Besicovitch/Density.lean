/-
Copyright (c) 2025 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
import ForMathlib.Besicovitch.ThinCover

/-!
# Density of the thin-cover condition

The heart of Körner's Baire-category argument (the density half of Lemma 2.4): for every
window `(v, ε)` the members of `kornerCompacts` admitting a thin cover are dense in the
Hausdorff metric.  An arbitrary member is approximated by a union of finitely many *fans*
(families of fibre segments pivoting at height `v`, with slopes in a small box around a
grid of anchor slopes) together with a finite net of its own fibre segments; near height
`v` each fan is squeezed into a thin bowtie, coverable by a staircase of boxes of small
total cross-sectional volume.

## Main results

* `dense_thinCoverSet` : for `n ≥ 1`, `thinCoverSet v ε` is dense in `kornerCompacts`.

## References

* T. W. Körner, *Besicovitch via Baire*, Studia Math. 158 (2003), no. 1, 65–78.
-/

open Set Metric TopologicalSpace

namespace Besicovitch

variable {n : ℕ}

/-- Coordinatewise absolute-value bounds give a sup-norm bound. -/
private lemma pi_norm_le_of_abs_le {m : ℕ} {x : Fin m → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, |x i| ≤ a) : ‖x‖ ≤ a :=
  (pi_norm_le_iff_of_nonneg ha).2 h

/-- If `|A| ≤ 1 - η`, `u ∈ [0, 1]` and `|z| ≤ η`, then `|A + u * z| ≤ 1`. -/
private lemma abs_add_mul_le_one {η A u z : ℝ} (hA : |A| ≤ 1 - η) (hu₀ : 0 ≤ u)
    (hu₁ : u ≤ 1) (hz : |z| ≤ η) : |A + u * z| ≤ 1 :=
  calc |A + u * z| ≤ |A| + |u * z| := abs_add_le _ _
    _ ≤ (1 - η) + η := add_le_add hA <| by
        rw [abs_mul, abs_of_nonneg hu₀]
        exact (mul_le_of_le_one_left (abs_nonneg _) hu₁).trans hz
    _ = 1 := by ring

/-! ## Fans in `ℝⁿ` -/

/-- The `n`-dimensional fan pivoting at `(c, v)` with slopes `t` in the box
`∏ᵢ [s i - ρ, s i + ρ]`. -/
def fan (c s : Fin n → ℝ) (ρ v : ℝ) : Set (Fin (n+1) → ℝ) :=
  ⋃ t ∈ {t : Fin n → ℝ | ∀ i, t i ∈ Icc (s i - ρ) (s i + ρ)},
    fibreSegment (fun i => c i - v * t i) (fun i => c i + (1 - v) * t i)

/-- Membership in an `n`-fan, in coordinates. -/
lemma mem_fan {c s : Fin n → ℝ} {ρ v : ℝ} {p : Fin (n+1) → ℝ} :
    p ∈ fan c s ρ v ↔
      ∃ t : Fin n → ℝ, (∀ i, t i ∈ Icc (s i - ρ) (s i + ρ)) ∧
        ∃ y ∈ Icc (0 : ℝ) 1, p = stripPoint (fun i => c i + (y - v) * t i) y := by
  simp only [fan, mem_iUnion, mem_setOf_eq, fibreSegment_eq_image, mem_image, exists_prop]
  constructor <;> rintro ⟨t, ht, y, hy, rfl⟩ <;>
    exact ⟨t, ht, y, hy, by congr 1; funext i; ring⟩

/-- The height coordinate of a fan point lies in `[0, 1]`. -/
private lemma fan_last_mem_Icc {c s : Fin n → ℝ} {ρ v : ℝ} {p : Fin (n+1) → ℝ}
    (hp : p ∈ fan c s ρ v) : p (Fin.last n) ∈ Icc (0:ℝ) 1 := by
  rw [mem_fan] at hp
  obtain ⟨t, -, y, hy, rfl⟩ := hp
  simpa using hy

/-- Fans are compact. -/
lemma isCompact_fan (c s : Fin n → ℝ) (ρ v : ℝ) : IsCompact (fan c s ρ v) := by
  have himage : fan c s ρ v =
      (fun q : (Fin n → ℝ) × ℝ => stripPoint (fun i => c i + (q.2 - v) * q.1 i) q.2) ''
        ((Set.univ.pi (fun i => Icc (s i - ρ) (s i + ρ))) ×ˢ Icc (0 : ℝ) 1) := by
    ext p
    rw [mem_fan]
    constructor
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨(t, y), ⟨Set.mem_univ_pi.2 ht, hy⟩, rfl⟩
    · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
      exact ⟨t, Set.mem_univ_pi.1 ht, y, hy, rfl⟩
  rw [himage]
  refine IsCompact.image ?_ ?_
  · exact (isCompact_univ_pi (fun i => isCompact_Icc)).prod isCompact_Icc
  · unfold stripPoint
    fun_prop

/-! ## Staircase counting lemmas -/

private lemma staircase_band_card_le {K : ℕ} {h σ v ε y : ℝ} (hh0 : 0 < h) (hσh : 2 * σ ≤ h)
    (F : Finset (Fin K))
    (hF : F = Finset.univ.filter
      (fun j : Fin K => y ∈ Ioo (v - ε + h * (j : ℝ) - σ) (v - ε + h * ((j : ℝ) + 1) + σ))) :
    F.card ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty F with hFe | hFne
  · simp [hFe]
  · have hmem : ∀ j ∈ F,
        v - ε + h * (j : ℝ) - σ < y ∧ y < v - ε + h * ((j : ℝ) + 1) + σ := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      exact hj.2
    have hpair : ∀ j ∈ F, ∀ j' ∈ F, (j : ℕ) ≤ (j' : ℕ) + 1 := by
      intro j hj j' hj'
      have h1 := (hmem j hj).1
      have h2 := (hmem j' hj').2
      have hjj' : (j : ℝ) < (j' : ℝ) + 2 := lt_of_mul_lt_mul_left (by linarith) hh0.le
      have : (j : ℕ) < (j' : ℕ) + 2 := by exact_mod_cast hjj'
      omega
    have hne : (F.image Fin.val).Nonempty := hFne.image _
    set m := (F.image Fin.val).min' hne with hm
    clear_value m
    obtain ⟨jm, hjm, hjmv⟩ := Finset.mem_image.1 ((F.image Fin.val).min'_mem hne)
    have himg : F.image Fin.val ⊆ Finset.Icc m (m + 1) := by
      intro nn hnn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hnn
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · rw [hm]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)
      · rw [hm, ← hjmv]
        exact hpair j hj jm hjm
    calc F.card = (F.image Fin.val).card :=
          (Finset.card_image_of_injective F Fin.val_injective).symm
      _ ≤ (Finset.Icc m (m + 1)).card := Finset.card_le_card himg
      _ ≤ 2 := by rw [Nat.card_Icc]; omega

private lemma staircase_mem_band {K : ℕ} (hK : 0 < K) {h v ε y : ℝ} (hh0 : 0 < h)
    (hKh : (K : ℝ) * h = 2 * ε) (hy : |y - v| ≤ ε) :
    let m := min ⌊(y - (v - ε)) / h⌋₊ (K - 1)
    m < K ∧ v - ε + h * (m : ℝ) ≤ y ∧ y ≤ v - ε + h * ((m : ℝ) + 1) := by
  intro m
  have habs := abs_le.1 hy
  have hz0 : 0 ≤ (y - (v - ε)) / h := div_nonneg (by linarith [habs.1]) hh0.le
  have hzK : y - (v - ε) ≤ (K : ℝ) * h := by rw [hKh]; linarith [habs.2]
  have hfl1 : (⌊(y - (v - ε)) / h⌋₊ : ℝ) * h ≤ y - (v - ε) := by
    have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le hz0) hh0.le
    rwa [div_mul_cancel₀ _ hh0.ne'] at h1
  have hfl2 : y - (v - ε) < ((⌊(y - (v - ε)) / h⌋₊ : ℝ) + 1) * h := by
    have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one ((y - (v - ε)) / h)) hh0
    rwa [div_mul_cancel₀ _ hh0.ne'] at h2
  have hnK : m < K := by
    have : m ≤ K - 1 := min_le_right _ _
    omega
  refine ⟨hnK, ?_⟩
  rcases le_or_gt ⌊(y - (v - ε)) / h⌋₊ (K - 1) with hc | hc
  · have hne : (m : ℝ) = (⌊(y - (v - ε)) / h⌋₊ : ℝ) := by
      simp only [m, min_eq_left hc]
    rw [hne]
    constructor <;> linarith
  · have hge : (K : ℝ) ≤ (⌊(y - (v - ε)) / h⌋₊ : ℝ) := Nat.cast_le.2 (by omega)
    have hyt : (K : ℝ) * h ≤ y - (v - ε) :=
      (mul_le_mul_of_nonneg_right hge hh0.le).trans hfl1
    have hcast : (m : ℝ) = (K : ℝ) - 1 := by
      have hne : m = K - 1 := min_eq_right (by omega)
      rw [hne]
      push_cast [Nat.cast_sub hK]
      ring
    rw [hcast]
    constructor <;> linarith

/-! ## Staircase covering of an `n`-fan near its pivot height -/

private theorem exists_staircase_fan (c s : Fin n → ℝ) (ρ v ε : ℝ) (K : ℕ) {σ : ℝ}
    (hρ : 0 ≤ ρ) (hs : ∀ i, |s i| + ρ ≤ 2) (hε : 0 < ε) (hK : 0 < K)
    (hσ : 0 < σ) (hσK : σ ≤ ε / K) :
    ∃ (lo hi : Fin K → Fin n → ℝ) (cc dd : Fin K → ℝ),
      (∀ j i, lo j i ≤ hi j i) ∧
      (∀ p ∈ fan c s ρ v, |p (Fin.last n) - v| ≤ ε →
        ∃ j, p ∈ openBox (lo j) (hi j) (cc j) (dd j)) ∧
      (∀ y : ℝ, ∑ j, (Ioo (cc j) (dd j)).indicator
          (fun _ => ∏ i, (hi j i - lo j i)) y
          ≤ 2 * (2 * (2 * ε / K + ε * ρ + σ)) ^ n) := by
  set h : ℝ := 2 * ε / K with hh
  have hh0 : 0 < h := by rw [hh]; positivity
  have hKh : (K : ℝ) * h = 2 * ε := by rw [hh]; field_simp
  have hσh : 2 * σ ≤ h := by
    have h1 : ε / K = h / 2 := by rw [hh]; ring
    linarith [hσK.trans_eq h1]
  clear_value h
  set w : ℝ := 2 * ε / K + ε * ρ + σ with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  clear_value w
  set μ : Fin K → ℝ := fun j => v - ε + ((j : ℝ) + 1 / 2) * h with hμ
  set γ : Fin K → Fin n → ℝ := fun j i => c i + (μ j - v) * s i with hγ
  have hμv : ∀ j : Fin K, |μ j - v| ≤ ε := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast j.2
    simp only [hμ]
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨fun j i => γ j i - w, fun j i => γ j i + w,
    fun j => v - ε + h * (j : ℝ) - σ, fun j => v - ε + h * ((j : ℝ) + 1) + σ, ?_, ?_, ?_⟩
  · intro j i
    linarith
  · -- covering property
    rintro p hp hp1
    rw [mem_fan] at hp
    obtain ⟨t, ht, y, hy, rfl⟩ := hp
    have hy1 : (stripPoint (fun i => c i + (y - v) * t i) y) (Fin.last n) = y := by
      simp [stripPoint_last]
    rw [hy1] at hp1
    have ht' : ∀ i, |t i - s i| ≤ ρ := fun i => by
      rw [abs_sub_comm]; exact mem_Icc_iff_abs_le.2 (ht i)
    have htabs : ∀ i, |t i| ≤ 2 := by
      intro i
      calc |t i| = |s i + (t i - s i)| := by ring_nf
        _ ≤ |s i| + |t i - s i| := abs_add_le _ _
        _ ≤ 2 := by linarith [ht' i, hs i]
    obtain ⟨hnK, hband⟩ := staircase_mem_band hK hh0 hKh hp1
    set m : ℕ := min ⌊(y - (v - ε)) / h⌋₊ (K - 1) with hn
    clear_value m
    have hyn : |y - μ ⟨m, hnK⟩| ≤ ε / K := by
      have hεK : ε / K = h / 2 := by rw [hh]; ring
      have hμn : μ ⟨m, hnK⟩ = v - ε + ((m : ℝ) + 1 / 2) * h := by simp [hμ]
      rw [hμn, hεK, abs_le]
      constructor <;> linarith [hband.1, hband.2]
    refine ⟨⟨m, hnK⟩, mem_openBox.2 ⟨?_, ?_⟩⟩
    · -- horizontal membership: each coordinate
      intro i
      have hkey : |(c i + (y - v) * t i) - γ ⟨m, hnK⟩ i| < w := by
        have hexp : (c i + (y - v) * t i) - γ ⟨m, hnK⟩ i
            = (y - μ ⟨m, hnK⟩) * t i + (μ ⟨m, hnK⟩ - v) * (t i - s i) := by
          simp only [hγ]; ring
        rw [hexp]
        calc |(y - μ ⟨m, hnK⟩) * t i + (μ ⟨m, hnK⟩ - v) * (t i - s i)|
            ≤ |(y - μ ⟨m, hnK⟩) * t i| + |(μ ⟨m, hnK⟩ - v) * (t i - s i)| := abs_add_le _ _
          _ = |y - μ ⟨m, hnK⟩| * |t i| + |μ ⟨m, hnK⟩ - v| * |t i - s i| := by
              rw [abs_mul, abs_mul]
          _ ≤ (ε / K) * 2 + ε * ρ := by
              have h1 : |y - μ ⟨m, hnK⟩| * |t i| ≤ (ε / K) * 2 :=
                mul_le_mul hyn (htabs i) (abs_nonneg _) (by positivity)
              have h2 : |μ ⟨m, hnK⟩ - v| * |t i - s i| ≤ ε * ρ :=
                mul_le_mul (hμv _) (ht' i) (abs_nonneg _) hε.le
              linarith
          _ < w := by
              have h3 : (ε / K) * 2 = 2 * ε / K := by ring
              rw [hw, h3]; linarith
      rw [abs_lt] at hkey
      simp only [stripPoint_castSucc]
      exact ⟨by linarith [hkey.1], by linarith [hkey.2]⟩
    · -- vertical membership
      rw [hy1]
      exact ⟨by linarith [hband.1], by linarith [hband.2]⟩
  · -- thinness
    intro y
    classical
    rw [Finset.sum_indicator_eq_sum_filter]
    set F := Finset.univ.filter
      (fun j : Fin K => y ∈ Ioo (v - ε + h * (j : ℝ) - σ) (v - ε + h * ((j : ℝ) + 1) + σ)) with hF
    have hcard : F.card ≤ 2 := staircase_band_card_le hh0 hσh F hF
    clear_value F
    have hterm : ∀ j ∈ F, ∏ i, ((γ j i + w) - (γ j i - w)) = (2 * w) ^ n := fun j _ => by
      simp [add_sub_sub_cancel, two_mul, Finset.prod_const]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      show h + ε * ρ + σ = w by rw [hw, hh]]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-! ## Degenerate fan, scalar bounds -/

/-- Every `fibreSegment` is a degenerate `n`-fan (zero opening), pivoting at height `v`. -/
private lemma fibreSegment_eq_fan (x₁ x₂ : Fin n → ℝ) (v : ℝ) :
    fibreSegment x₁ x₂ =
      fan (fun i => x₁ i + v * (x₂ i - x₁ i)) (fun i => x₂ i - x₁ i) 0 v := by
  rw [fan]
  have hset : {t : Fin n → ℝ | ∀ i, t i ∈ Icc ((x₂ i - x₁ i) - 0) ((x₂ i - x₁ i) + 0)}
      = {fun i => x₂ i - x₁ i} := by
    ext t
    simp only [mem_setOf_eq, sub_zero, add_zero, mem_singleton_iff, Icc_self, mem_singleton_iff]
    constructor
    · intro h; funext i; exact h i
    · intro h i; rw [h]
  rw [hset]
  simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
  congr 1
  · funext i; ring
  · funext i; ring

/-- The one-dimensional horizontal displacement bound underlying the fan estimate. -/
private lemma fan_anchor_horizontal_bound {η v x₁ s' t y σ' : ℝ} (hη : 0 < η)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hx₁ : |x₁| ≤ 1) (hs'half : |s'| ≤ 1/2)
    (hσs' : σ' = (1 - η) * s') (htσ : |t - σ'| ≤ η) (hyv : |y - v| ≤ 1) :
    |(1 - η) * x₁ + v * σ' + (y - v) * t - (x₁ + y * s')| ≤ 3 * η := by
  have hexp : (1 - η) * x₁ + v * σ' + (y - v) * t - (x₁ + y * s')
      = -(η * x₁) + (y - v) * (t - s') - v * η * s' := by
    rw [hσs']; ring
  rw [hexp]
  have hts' : |t - s'| ≤ 3 * η / 2 := by
    have h1 : |σ' - s'| = η * |s'| := by
      rw [hσs', show (1 - η) * s' - s' = -(η * s') by ring, abs_neg, abs_mul, abs_of_pos hη]
    have h2 := abs_sub_le t σ' s'
    rw [h1] at h2
    linarith [mul_le_mul_of_nonneg_left hs'half hη.le]
  have htri : |(-(η * x₁) + (y - v) * (t - s') - v * η * s')|
      ≤ |η * x₁| + |(y - v) * (t - s')| + |v * η * s'| := by
    simpa [sub_eq_add_neg] using abs_add_three (-(η * x₁)) ((y - v) * (t - s')) (-(v * η * s'))
  have e1 : |η * x₁| ≤ η := by
    rw [abs_mul, abs_of_pos hη]
    exact mul_le_of_le_one_right hη.le hx₁
  have e2 : |(y - v) * (t - s')| ≤ 3 * η / 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hyv).trans hts'
  have e3 : |v * η * s'| ≤ η / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hv₀, abs_of_pos hη]
    have h1 : v * η * |s'| ≤ 1 * η * (1/2) :=
      mul_le_mul (mul_le_mul hv₁ le_rfl hη.le zero_le_one) hs'half (abs_nonneg s') (by positivity)
    linarith
  linarith

/-- The one-dimensional grid: midpoints of `M` equal subdivisions of `[-1/2, 1/2]`
approximate every point of `[-1/2, 1/2]` to within `1/(2M)`. -/
private lemma exists_grid_point_dist_le {M : ℕ} (hM0 : 0 < M) {w : ℝ} (hw : |w| ≤ 1 / 2) :
    ∃ nn : Fin M, |w - (-(1/2) + ((nn : ℝ) + 1/2) / M)| ≤ 1 / (2 * (M : ℝ)) := by
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hw' := abs_le.1 hw
  have hz0 : 0 ≤ (w + 1/2) * M := mul_nonneg (by linarith) hM0'.le
  have hzM : (w + 1/2) * M ≤ M := mul_le_of_le_one_left hM0'.le (by linarith)
  set nn : ℕ := min ⌊(w + 1/2) * M⌋₊ (M - 1) with hn
  have hnM : nn < M := by
    have : nn ≤ M - 1 := min_le_right _ _
    omega
  have hfl1 : (⌊(w + 1/2) * M⌋₊ : ℝ) ≤ (w + 1/2) * M := Nat.floor_le hz0
  have hfl2 : (w + 1/2) * M < (⌊(w + 1/2) * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨⟨nn, hnM⟩, ?_⟩
  have hval : (((⟨nn, hnM⟩ : Fin M) : ℝ)) = (nn : ℝ) := rfl
  rw [hval]
  rcases le_or_gt ⌊(w + 1/2) * M⌋₊ (M - 1) with hc | hc
  · have hne : (nn : ℝ) = (⌊(w + 1/2) * M⌋₊ : ℝ) := by rw [hn, min_eq_left hc]
    have hexp : w - (-(1/2) + ((nn : ℝ) + 1/2) / M)
        = ((w + 1/2) * M - ((⌊(w + 1/2) * M⌋₊ : ℝ) + 1/2)) / M := by
      rw [hne]; field_simp; ring
    rw [hexp, abs_div, abs_of_pos hM0',
      div_le_div_iff₀ hM0' (by positivity : (0:ℝ) < 2 * M)]
    have hnum : |(w + 1/2) * M - ((⌊(w + 1/2) * M⌋₊ : ℝ) + 1/2)| ≤ 1/2 := by
      rw [abs_le]; constructor <;> linarith
    linarith [mul_le_mul_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 2 * M)]
  · have hge : (M : ℝ) ≤ (⌊(w + 1/2) * M⌋₊ : ℝ) := Nat.cast_le.2 (by omega)
    have hwM : (w + 1/2) * M = M := le_antisymm hzM (hge.trans hfl1)
    have hw12 : w = 1/2 := by
      have := mul_right_cancel₀ hM0'.ne' (hwM.trans (one_mul (M : ℝ)).symm)
      linarith
    have hcast : (nn : ℝ) = (M : ℝ) - 1 := by
      have hne : nn = M - 1 := min_eq_right (by omega)
      rw [hne]; push_cast [Nat.cast_sub hM0]; ring
    have hexp : w - (-(1/2) + ((nn : ℝ) + 1/2) / M) = (1/2) / M := by
      rw [hcast, hw12]; field_simp; ring
    rw [hexp, abs_of_nonneg (by positivity),
      div_le_div_iff₀ hM0' (by positivity : (0:ℝ) < 2 * M)]
    linarith

/-! ## The δ-net of fibre segments -/

private theorem exists_segment_net (P : kornerCompacts (n := n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset ((Fin n → ℝ) × (Fin n → ℝ)),
      (∀ q ∈ s, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1 ∧
        fibreSegment q.1 q.2 ⊆ (P : Set (Fin (n+1) → ℝ))) ∧
      (∀ p ∈ (P : Set (Fin (n+1) → ℝ)), ∃ q ∈ s, ∃ p' ∈ fibreSegment q.1 q.2,
        dist p p' ≤ δ) := by
  obtain ⟨A, hA, hPA⟩ := kornerFamily_exists_iUnion_fibreSegment P.2
  obtain ⟨t, htP, htfin, htcover⟩ :=
    (P : NonemptyCompacts (Fin (n+1) → ℝ)).isCompact.finite_cover_balls hδ
  lift t to Finset (Fin (n+1) → ℝ) using htfin
  have hchoice : ∀ x ∈ t, ∃ q : (Fin n → ℝ) × (Fin n → ℝ),
      q ∈ A ∧ x ∈ fibreSegment q.1 q.2 := by
    intro x hx
    have hxP : x ∈ (P : Set (Fin (n+1) → ℝ)) := htP hx
    rw [hPA] at hxP
    rcases mem_iUnion₂.1 hxP with ⟨q, hqA, hxq⟩
    exact ⟨q, hqA, hxq⟩
  choose f hfA hfx using hchoice
  refine ⟨t.attach.image fun x => f x.1 x.2, ?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hp := hA _ (hfA x hx)
    refine ⟨hp.1, hp.2, ?_⟩
    rw [hPA]
    exact subset_biUnion_of_mem (u := fun q => fibreSegment q.1 q.2) (hfA x hx)
  · intro p hp
    obtain ⟨x, hxt, hdist⟩ := mem_iUnion₂.1 (htcover hp)
    have hxt' : x ∈ t := hxt
    exact ⟨f x hxt',
      Finset.mem_image.2 ⟨⟨x, hxt'⟩, Finset.mem_attach _ _, rfl⟩,
      x, hfx x hxt', (mem_ball.1 hdist).le⟩

/-! ## Fan anchors -/

private theorem exists_fan_anchors (P : kornerCompacts (n := n)) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1/2) (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ∃ (M₀ : ℕ) (c s : (Fin n → Fin M₀) → Fin n → ℝ),
      (∀ g i, |s g i| + η ≤ 1) ∧
      (∀ g, ∀ t : Fin n → ℝ, (∀ i, t i ∈ Icc (s g i - η) (s g i + η)) →
        ‖(fun i => c g i - v * t i)‖ ≤ 1 ∧ ‖(fun i => c g i + (1 - v) * t i)‖ ≤ 1) ∧
      (∀ g, ∀ p ∈ fan (c g) (s g) η v, ∃ p' ∈ (P : Set (Fin (n+1) → ℝ)), dist p p' ≤ 3 * η) ∧
      (∀ w : Fin n → ℝ, ‖w‖ ≤ (1/2 : ℝ) → ∃ g, ∀ i, w i ∈ Icc (s g i - η) (s g i + η)) ∧
      ((M₀ : ℝ) ^ n * η ^ n ≤ 1) := by
  have hη1 : η < 1 := lt_of_le_of_lt hη' (by norm_num)
  have h1η : 0 < 1 - η := by linarith
  set M₀ : ℕ := ⌈1 / (2 * η)⌉₊ with hM₀def
  have hM₀0 : 0 < M₀ := by rw [hM₀def]; exact Nat.ceil_pos.2 (by positivity)
  have hM₀0' : (0 : ℝ) < M₀ := by exact_mod_cast hM₀0
  have hM₀1 : 1 / (2 * η) ≤ (M₀ : ℝ) := by rw [hM₀def]; exact Nat.le_ceil _
  have hM₀2 : (M₀ : ℝ) < 1 / (2 * η) + 1 := by
    rw [hM₀def]; exact Nat.ceil_lt_add_one (by positivity)
  clear_value M₀
  have hinv : 1 / (2 * η) * η = 1 / 2 := by field_simp
  have hM₀η : (M₀ : ℝ) * η ≤ 1 := by linarith [mul_lt_mul_of_pos_right hM₀2 hη]
  have hM₀η' : 1 / (2 * (M₀ : ℝ)) ≤ η := by
    rw [div_le_iff₀ (by positivity)]; linarith [mul_le_mul_of_nonneg_right hM₀1 hη.le]
  have hηM₀ : η / 2 ≤ 1 / (2 * (M₀ : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  -- The grid of slope vectors
  set σ' : (Fin n → Fin M₀) → Fin n → ℝ :=
    fun g i => -(1/2) + ((g i : ℝ) + 1/2) / M₀ with hσ'
  have hσ'abs : ∀ g i, |σ' g i| ≤ 1/2 - 1 / (2 * (M₀ : ℝ)) := by
    intro g i
    have hm0 : (0 : ℝ) ≤ ((g i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm1 : ((g i : ℕ) : ℝ) + 1 ≤ M₀ := by exact_mod_cast (g i).2
    have hlo : 1 / (2 * (M₀ : ℝ)) ≤ (((g i : ℕ) : ℝ) + 1/2) / M₀ := by
      rw [div_le_div_iff₀ (by positivity) hM₀0']; linarith [mul_nonneg hm0 hM₀0'.le]
    have hhi : (((g i : ℕ) : ℝ) + 1/2) / M₀ ≤ 1 - 1 / (2 * (M₀ : ℝ)) := by
      rw [div_le_iff₀ hM₀0']
      have hexp : (1 - 1 / (2 * (M₀ : ℝ))) * M₀ = M₀ - 1/2 := by field_simp
      rw [hexp]; linarith
    simp only [hσ']
    rw [abs_le]; constructor <;> linarith
  have hσ'half : ∀ g i, |σ' g i| ≤ (1 - η) / 2 := by
    intro g i
    have h1 := hσ'abs g i
    linarith [hηM₀]
  have hσ'norm : ∀ g, ‖σ' g‖ ≤ 1/2 := fun g =>
    pi_norm_le_of_abs_le (by norm_num) fun i => by
      have hp : (0:ℝ) ≤ 1 / (2 * (M₀:ℝ)) := by positivity
      linarith [hσ'abs g i]
  -- anchor fibre-segments of P for each grid slope
  have hanchor : ∀ g : Fin n → Fin M₀, ∃ x₁ x₂ : Fin n → ℝ, ‖x₁‖ ≤ 1 ∧ ‖x₂‖ ≤ 1 ∧
      (∀ i, x₂ i - x₁ i = σ' g i / (1 - η)) ∧
      fibreSegment x₁ x₂ ⊆ (P : Set (Fin (n+1) → ℝ)) := by
    intro g
    have hnorm : ‖(fun i => σ' g i / (1 - η))‖ ≤ 1 / 2 :=
      pi_norm_le_of_abs_le (by norm_num) fun i => by
        rw [abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
        linarith [hσ'half g i]
    obtain ⟨x₁, x₂, hx₁, hx₂, hdiff, hseg⟩ := kornerFamily_exists_fibreSegment P.2 hnorm
    refine ⟨x₁, x₂, hx₁, hx₂, fun i => ?_, hseg⟩
    have := congrFun hdiff i
    simpa using this
  choose x₁ x₂ hx₁ hx₂ hslope hseg using hanchor
  have hx2eq : ∀ g i, (1 - η) * x₂ g i = (1 - η) * x₁ g i + σ' g i := by
    intro g i
    have h := hslope g i
    rw [eq_div_iff h1η.ne'] at h
    linarith [h]
  refine ⟨M₀, fun g i => (1 - η) * x₁ g i + v * σ' g i, σ', ?_, ?_, ?_, ?_, ?_⟩
  · -- slopes bounded away from 1
    intro g i
    have := hσ'half g i
    linarith
  · -- fan segments stay in strip
    intro g t ht
    have htσ : ∀ i, |t i - σ' g i| ≤ η := fun i => by
      rw [abs_sub_comm]; exact mem_Icc_iff_abs_le.2 (ht i)
    have habs : ∀ (x : (Fin n → Fin M₀) → Fin n → ℝ), (∀ g, ‖x g‖ ≤ 1) →
        ∀ i, |(1 - η) * x g i| ≤ 1 - η := fun x hx i => by
      rw [abs_mul, abs_of_pos h1η]
      exact mul_le_of_le_one_right h1η.le ((norm_le_pi_norm (x g) i).trans (hx g))
    constructor
    · refine pi_norm_le_of_abs_le (by norm_num) fun i => ?_
      have hexp : (1 - η) * x₁ g i + v * σ' g i - v * t i
          = (1 - η) * x₁ g i + v * (σ' g i - t i) := by ring
      simp only [hexp]
      exact abs_add_mul_le_one (habs x₁ hx₁ i) hv₀ hv₁ (by rw [abs_sub_comm]; exact htσ i)
    · refine pi_norm_le_of_abs_le (by norm_num) fun i => ?_
      have hexp : (1 - η) * x₁ g i + v * σ' g i + (1 - v) * t i
          = (1 - η) * x₂ g i + (1 - v) * (t i - σ' g i) := by
        rw [hx2eq]; ring
      simp only [hexp]
      exact abs_add_mul_le_one (habs x₂ hx₂ i) (by linarith) (by linarith) (htσ i)
  · -- fan points within 3η of P
    intro g p hp
    rw [mem_fan] at hp
    obtain ⟨t, ht, y, hy, rfl⟩ := hp
    rw [mem_Icc] at hy
    have htσ : ∀ i, |t i - σ' g i| ≤ η := fun i => by
      rw [abs_sub_comm]; exact mem_Icc_iff_abs_le.2 (ht i)
    set s' : Fin n → ℝ := fun i => σ' g i / (1 - η) with hs'
    have hs'half : ∀ i, |s' i| ≤ 1/2 := by
      intro i
      rw [hs', abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
      linarith [hσ'half g i]
    have hσs' : ∀ i, σ' g i = (1 - η) * s' i := by
      intro i; rw [hs']; field_simp
    refine ⟨stripPoint (fun i => x₁ g i + y * s' i) y, ?_, ?_⟩
    · apply hseg g
      rw [fibreSegment_eq_image]
      refine ⟨y, mem_Icc.2 hy, ?_⟩
      have hfun : (fun i => x₁ g i + y * ((x₂ g) i - (x₁ g) i)) = (fun i => x₁ g i + y * s' i) := by
        funext i
        rw [hslope g i, hs']
      simp only [hfun]
    · have hyv : |y - v| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      rw [dist_pi_le_iff (by positivity)]
      intro i
      induction i using Fin.lastCases with
      | last =>
          simp only [stripPoint_last]
          rw [dist_self]; positivity
      | cast j =>
          simp only [stripPoint_castSucc]
          rw [Real.dist_eq]
          have hx₁abs : |x₁ g j| ≤ 1 := (norm_le_pi_norm (x₁ g) j).trans (hx₁ g)
          exact fan_anchor_horizontal_bound hη hv₀ hv₁ hx₁abs (hs'half j) (hσs' j) (htσ j) hyv
  · -- grid covers {‖w‖ ≤ 1/2}
    intro w hw
    have hwcoord : ∀ i, |w i| ≤ 1/2 := fun i => (norm_le_pi_norm w i).trans hw
    have hgrid : ∀ i, ∃ nn : Fin M₀,
        |w i - (-(1/2) + ((nn : ℝ) + 1/2) / M₀)| ≤ 1 / (2 * (M₀ : ℝ)) :=
      fun i => exists_grid_point_dist_le hM₀0 (hwcoord i)
    choose g hg using hgrid
    refine ⟨g, fun i => mem_Icc_iff_abs_le.1 ?_⟩
    rw [abs_sub_comm, show σ' g i = -(1/2) + ((g i : ℝ) + 1/2) / M₀ from by simp [hσ']]
    exact (hg i).trans hM₀η'
  · -- M₀^n * η^n ≤ 1
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) hM₀η

/-! ## Combining thin covers -/

private lemma hasThinCover_iUnion {ι : Type*} [Fintype ι] {S : ι → Set (Fin (n+1) → ℝ)} {v ε : ℝ}
    (B : ι → ℝ)
    (h : ∀ i, ∃ (K : ℕ) (lo hi : Fin K → Fin n → ℝ) (c d : Fin K → ℝ),
      (∀ j i, lo j i ≤ hi j i) ∧
      (∀ p ∈ S i, |p (Fin.last n) - v| ≤ ε →
        ∃ j, p ∈ openBox (lo j) (hi j) (c j) (d j)) ∧
      (∀ y : ℝ, ∑ j, (Ioo (c j) (d j)).indicator (fun _ => ∏ i, (hi j i - lo j i)) y ≤ B i))
    (hB : ∑ i, B i < 100 * 4 ^ n * ε) :
    HasThinCover (⋃ i, S i) v ε := by
  choose K lo hi c d hab hcov hthin using h
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ((i : ι) × Fin (K i))) ≃ (i : ι) × Fin (K i)) :=
    ⟨(Fintype.equivFin _).symm⟩
  refine ⟨Fintype.card ((i : ι) × Fin (K i)),
    fun j => lo (e j).1 (e j).2, fun j => hi (e j).1 (e j).2,
    fun j => c (e j).1 (e j).2, fun j => d (e j).1 (e j).2,
    fun j i => hab _ _ i, ?_, ?_⟩
  · intro p hp hpv
    obtain ⟨i, hi'⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj⟩ := hcov i p hi' hpv
    obtain ⟨j', hj'⟩ : ∃ j', e j' = ⟨i, j⟩ := ⟨e.symm ⟨i, j⟩, e.apply_symm_apply _⟩
    -- rewrite along `hj'` with an explicit motive: the sigma projections are dependent,
    -- so we substitute the whole sigma term at once.
    exact ⟨j', hj'.symm.subst
      (motive := fun q => p ∈ openBox (lo q.1 q.2) (hi q.1 q.2) (c q.1 q.2) (d q.1 q.2)) hj⟩
  · intro y _
    rw [Equiv.sum_comp e (fun q : (i : ι) × Fin (K i) =>
        (Ioo (c q.1 q.2) (d q.1 q.2)).indicator
          (fun _ => ∏ i, (hi q.1 q.2 i - lo q.1 q.2 i)) y),
      Fintype.sum_sigma]
    calc (∑ i, ∑ j, (Ioo (c i j) (d i j)).indicator
            (fun _ => ∏ k, (hi i j k - lo i j k)) y)
        ≤ ∑ i, B i := Finset.sum_le_sum fun i _ => hthin i y
      _ < 100 * 4 ^ n * ε := hB

/-! ## Assembly of the thin cover for `Q = fans ∪ net` -/

private lemma hasThinCover_fans_union_net {M₀ : ℕ} (hn : 0 < n)
    {cM sM : (Fin n → Fin M₀) → Fin n → ℝ} {η v ε : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/2) (hε : 0 < ε) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1)
    (hMη : (M₀ : ℝ) ^ n * η ^ n ≤ 1)
    (hs1 : ∀ g i, |sM g i| + η ≤ 2)
    (nt : Finset ((Fin n → ℝ) × (Fin n → ℝ)))
    (hntP : ∀ q ∈ nt, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1) :
    HasThinCover
      ((⋃ g : Fin n → Fin M₀, fan (cM g) (sM g) η v) ∪
        (⋃ q ∈ nt, fibreSegment q.1 q.2)) v ε := by
  -- Work with the clamped width `εw = min ε 1 ≤ 1`; covering band remains `ε`.
  set εw : ℝ := min ε 1 with hεw
  have hεwpos : 0 < εw := lt_min hε one_pos
  have hεw1 : εw ≤ 1 := min_le_right _ _
  have hεwε : εw ≤ ε := min_le_left _ _
  -- every strip height is within the εw-band once inside the ε-band
  have hband : ∀ y : ℝ, y ∈ Icc (0:ℝ) 1 → |y - v| ≤ ε → |y - v| ≤ εw := by
    intro y hy hyε
    rw [hεw, le_min_iff]
    refine ⟨hyε, ?_⟩
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  -- Choose N large: N η ≥ 3, and N large enough for the net term.
  set C : ℝ := (nt.card : ℝ) * 12 ^ n + 1 with hC
  obtain ⟨N, hN3, hNC⟩ : ∃ N : ℕ, 3 / η ≤ (N : ℝ) ∧ C ≤ (N : ℝ) :=
    ⟨max ⌈3 / η⌉₊ ⌈C⌉₊,
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_left _ _)),
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))⟩
  have hN0 : 0 < N := Nat.cast_pos.1 (lt_of_lt_of_le (by positivity) hN3)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hσ0 : 0 < εw / N := by positivity
  -- rewrite the union
  have hQU : (⋃ g : Fin n → Fin M₀, fan (cM g) (sM g) η v) ∪
        (⋃ q ∈ nt, fibreSegment q.1 q.2)
      = ⋃ i : (Fin n → Fin M₀) ⊕ {q : (Fin n → ℝ) × (Fin n → ℝ) // q ∈ nt},
        Sum.elim (fun g => fan (cM g) (sM g) η v)
          (fun q => fibreSegment q.1.1 q.1.2) i := by
    rw [iUnion_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    exact (iUnion_subtype (fun q => q ∈ nt)
      (fun q : {q : (Fin n → ℝ) × (Fin n → ℝ) // q ∈ nt} =>
        fibreSegment q.1.1 q.1.2)).symm
  rw [hQU]
  refine hasThinCover_iUnion
    (Sum.elim (fun _ => 2 * (2 * (2 * εw / N + εw * η + εw / N)) ^ n)
      (fun _ => 2 * (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n)) ?_ ?_
  · rintro (g | q)
    · obtain ⟨lo, hi, cc, dd, h1, h2, h3⟩ :=
        exists_staircase_fan (cM g) (sM g) η v εw N (σ := εw / N) hη.le
          (hs1 g) hεwpos hN0 hσ0 le_rfl
      refine ⟨N, lo, hi, cc, dd, h1, ?_, h3⟩
      intro p hp hpv
      rw [Sum.elim_inl] at hp
      exact h2 p hp (hband _ (fan_last_mem_Icc hp) hpv)
    · have hq1 := (hntP q.1 q.2).1
      have hq2 := (hntP q.1 q.2).2
      have hs2 : ∀ i, |(fun i => q.1.2 i - q.1.1 i) i| + 0 ≤ 2 := by
        intro i
        rw [add_zero]
        have h1 : |q.1.1 i| ≤ 1 := (norm_le_pi_norm q.1.1 i).trans hq1
        have h2 : |q.1.2 i| ≤ 1 := (norm_le_pi_norm q.1.2 i).trans hq2
        have : |q.1.2 i - q.1.1 i| ≤ |q.1.2 i| + |q.1.1 i| := abs_sub _ _
        simpa using (le_trans this (by linarith))
      obtain ⟨lo, hi, cc, dd, h1, h2, h3⟩ :=
        exists_staircase_fan (fun i => q.1.1 i + v * (q.1.2 i - q.1.1 i))
          (fun i => q.1.2 i - q.1.1 i) 0 v εw N (σ := εw / N) le_rfl hs2 hεwpos hN0 hσ0 le_rfl
      refine ⟨N, lo, hi, cc, dd, h1, ?_, h3⟩
      intro p hp hpv
      rw [Sum.elim_inr, fibreSegment_eq_fan q.1.1 q.1.2 v] at hp
      exact h2 p hp (hband _ (fan_last_mem_Icc hp) hpv)
  · -- numeric bound (in terms of εw)
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
    -- n ≥ 1: work with the clamped width `εw ≤ 1`, then relax to `ε`.
    have hNη : 3 ≤ (N:ℝ) * η := by rwa [div_le_iff₀ hη] at hN3
    have hη3 : 3 * (εw / N) ≤ εw * η := by
      have hmul : 3 * εw ≤ εw * η * N := by
        linarith [mul_le_mul_of_nonneg_left hNη hεwpos.le]
      rw [mul_div_assoc']
      rw [div_le_iff₀ hNR]
      linarith [hmul]
    have hfanw : 2 * εw / N + εw * η + εw / N ≤ 2 * (εw * η) := by
      have h2 : 2 * εw / N + εw * η + εw / N = 3 * (εw / N) + εw * η := by ring
      rw [h2]; linarith [hη3]
    have hfanpow : (2 * (2 * εw / N + εw * η + εw / N)) ^ n ≤ (2 * (2 * (εw * η))) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [hfanw]
    have hεn : εw ^ n ≤ εw := by
      conv_rhs => rw [← pow_one εw]
      exact pow_le_pow_of_le_one hεwpos.le hεw1 hn
    have hfanterm : (M₀ : ℝ) ^ n * (2 * (2 * εw / N + εw * η + εw / N)) ^ n
        ≤ 2 * 4 ^ n * εw := by
      calc (M₀ : ℝ) ^ n * (2 * (2 * εw / N + εw * η + εw / N)) ^ n
          ≤ (M₀ : ℝ) ^ n * (2 * (2 * (εw * η))) ^ n :=
            mul_le_mul_of_nonneg_left hfanpow (by positivity)
        _ = (M₀ : ℝ) ^ n * ((4 : ℝ) ^ n * (εw ^ n * η ^ n)) := by ring
        _ = 4 ^ n * εw ^ n * ((M₀ : ℝ) ^ n * η ^ n) := by ring
        _ ≤ 4 ^ n * εw ^ n * 1 :=
            mul_le_mul_of_nonneg_left hMη (by positivity)
        _ = 4 ^ n * εw ^ n := by ring
        _ ≤ 4 ^ n * εw := mul_le_mul_of_nonneg_left hεn (by positivity)
        _ ≤ 2 * 4 ^ n * εw := by
            linarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 4) n) hεwpos.le]
    have hnetterm : (nt.card : ℝ) * (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n ≤ εw := by
      have hbnd : (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n ≤ 12 ^ n * (εw / N) := by
        have hstep : 2 * (2 * εw / N + εw * 0 + εw / N) ≤ 12 * (εw / N) := by
          rw [show (2:ℝ) * (2 * εw / N + εw * 0 + εw / N) = 6 * (εw / N) by ring]
          have hεN : (0:ℝ) ≤ εw / N := by positivity
          linarith
        calc (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n
            ≤ (12 * (εw / N)) ^ n := pow_le_pow_left₀ (by positivity) hstep n
          _ = 12 ^ n * (εw / N) ^ n := by rw [mul_pow]
          _ ≤ 12 ^ n * (εw / N) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hεN1 : εw / N ≤ 1 := by
                rw [div_le_one hNR]
                calc εw ≤ 1 := hεw1
                  _ ≤ (N:ℝ) := by
                      have : (1:ℝ) ≤ 3 / η := by
                        rw [le_div_iff₀ hη]; linarith [hη']
                      linarith [hN3]
              conv_rhs => rw [← pow_one (εw / N)]
              exact pow_le_pow_of_le_one (by positivity) hεN1 hn
      calc (nt.card : ℝ) * (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n
          ≤ (nt.card : ℝ) * (12 ^ n * (εw / N)) :=
            mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ ≤ C * (εw / N) := by
            rw [hC]
            have : (0:ℝ) ≤ εw / N := by positivity
            linarith
        _ ≤ εw := by
            rw [mul_div_assoc', div_le_iff₀ hNR]
            linarith [mul_le_mul_of_nonneg_right hNC hεwpos.le]
    -- combine (bound in terms of εw, then relax εw ≤ ε)
    calc ((M₀ ^ n : ℕ) : ℝ) * (2 * (2 * (2 * εw / N + εw * η + εw / N)) ^ n)
          + (nt.card : ℝ) * (2 * (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n)
        = 2 * ((M₀ : ℝ) ^ n * (2 * (2 * εw / N + εw * η + εw / N)) ^ n)
          + 2 * ((nt.card : ℝ) * (2 * (2 * εw / N + εw * 0 + εw / N)) ^ n) := by
          push_cast; ring
      _ ≤ 2 * (2 * 4 ^ n * εw) + 2 * εw := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hfanterm (by norm_num)
          · exact mul_le_mul_of_nonneg_left hnetterm (by norm_num)
      _ < 100 * 4 ^ n * εw := by
          have h4 : (1:ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
          linarith [mul_le_mul_of_nonneg_right h4 hεwpos.le,
            mul_pos (show (0:ℝ) < 4 ^ n by positivity) hεwpos]
      _ ≤ 100 * 4 ^ n * ε := by
          apply mul_le_mul_of_nonneg_left hεwε (by positivity)

/-! ## Main density theorem -/

/-- For `n ≥ 1`, the set `thinCoverSet v ε` is dense in `kornerCompacts` whenever
`v ∈ [0,1]` and `ε > 0`. -/
theorem dense_thinCoverSet [NeZero n] {v ε : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hε : 0 < ε) :
    Dense (thinCoverSet (n := n) v ε) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Metric.dense_iff]
  intro P δ hδ
  -- `hasThinCover_fans_union_net` handles the volume budget for all ε via clamping
  -- parameters
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min (δ / 4) (1 / 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact lt_min (by positivity) (by norm_num)
  have hη' : η ≤ 1 / 2 := hη_def.trans_le (min_le_right _ _)
  have hηδ : η ≤ δ / 4 := hη_def.trans_le (min_le_left _ _)
  -- the fans and the net
  obtain ⟨M₀, cM, sM, hs1', hends, hnear, hcovs, hM₀η⟩ :=
    exists_fan_anchors P hη hη' v hv₀ hv₁
  obtain ⟨nt, hntP, hntnet⟩ := exists_segment_net P (show (0:ℝ) < δ / 2 by positivity)
  -- slope bounds ≤ 2 for staircase
  have hs1 : ∀ g i, |sM g i| + η ≤ 2 := fun g i => le_trans (hs1' g i) (by norm_num)
  -- the approximating set
  obtain ⟨Q, hQ⟩ : ∃ Q : Set (Fin (n+1) → ℝ),
      Q = (⋃ g : Fin n → Fin M₀, fan (cM g) (sM g) η v) ∪
        (⋃ q ∈ nt, fibreSegment q.1 q.2) := ⟨_, rfl⟩
  have hfan_sub : ∀ g : Fin n → Fin M₀, fan (cM g) (sM g) η v ⊆ Q := by
    intro g; rw [hQ]
    exact (subset_iUnion (fun g => fan (cM g) (sM g) η v) g).trans subset_union_left
  have hseg_sub : ∀ q ∈ nt, fibreSegment q.1 q.2 ⊆ Q := by
    intro q hq y hy; rw [hQ]
    exact Or.inr (mem_iUnion₂.2 ⟨q, hq, hy⟩)
  -- `Q` is nonempty
  obtain ⟨g₀, -⟩ := hcovs 0 (by simp)
  have hQne : Q.Nonempty := by
    refine ⟨stripPoint (fun i => cM g₀ i - v * sM g₀ i) 0, hfan_sub g₀ ?_⟩
    rw [mem_fan]
    refine ⟨sM g₀, fun i => ?_, 0, ?_, ?_⟩
    · rw [mem_Icc]; constructor <;> linarith
    · rw [mem_Icc]; norm_num
    · congr 1; funext i; ring
  -- `Q` is compact
  have hQcomp : IsCompact Q := by
    rw [hQ]
    apply IsCompact.union
    · exact isCompact_iUnion fun g => isCompact_fan _ _ _ _
    · exact nt.finite_toSet.isCompact_biUnion fun q _ => isCompact_fibreSegment _ _
  -- `Q ⊆ strip`
  have hQstrip : Q ⊆ (strip : Set (Fin (n+1) → ℝ)) := by
    rw [hQ]
    apply union_subset
    · refine iUnion_subset fun g => ?_
      rw [fan]
      refine iUnion₂_subset fun t ht => ?_
      exact fibreSegment_subset_strip (hends g t ht).1 (hends g t ht).2
    · refine iUnion₂_subset fun q hq => ?_
      exact fibreSegment_subset_strip (hntP q hq).1 (hntP q hq).2.1
  -- `Q` is a union of fibre segments (endpoint pairs in ballPair)
  have hQdecomp : ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      (∀ q ∈ A, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1) ∧
      Q = ⋃ q ∈ A, fibreSegment q.1 q.2 := by
    set A : Set ((Fin n → ℝ) × (Fin n → ℝ)) := (⋃ g : Fin n → Fin M₀,
        (fun t => ((fun i => cM g i - v * t i), (fun i => cM g i + (1 - v) * t i)))
          '' {t : Fin n → ℝ | ∀ i, t i ∈ Icc (sM g i - η) (sM g i + η)}) ∪ ↑nt
    refine ⟨A, ?_, ?_⟩
    · apply union_subset
      · refine iUnion_subset fun g => ?_
        rintro - ⟨t, ht, rfl⟩
        exact ⟨(hends g t ht).1, (hends g t ht).2⟩
      · intro q hq
        exact ⟨(hntP q hq).1, (hntP q hq).2.1⟩
    · apply Subset.antisymm
      · rw [hQ]
        apply union_subset
        · refine iUnion_subset fun g => ?_
          rw [fan]
          refine iUnion₂_subset fun t ht => ?_
          have hpA : ((fun i => cM g i - v * t i), (fun i => cM g i + (1 - v) * t i)) ∈ A :=
            mem_union_left _ (mem_iUnion.2 ⟨g, mem_image_of_mem _ ht⟩)
          exact subset_biUnion_of_mem (u := fun p => fibreSegment p.1 p.2) hpA
        · refine iUnion₂_subset fun q hq => ?_
          have hpA : q ∈ A := mem_union_right _ (Finset.mem_coe.2 hq)
          exact subset_biUnion_of_mem (u := fun p => fibreSegment p.1 p.2) hpA
      · refine iUnion₂_subset fun p hpA => ?_
        rcases hpA with hpA | hpA
        · obtain ⟨g, hm⟩ := mem_iUnion.1 hpA
          obtain ⟨t, ht, rfl⟩ := hm
          refine subset_trans ?_ (hfan_sub g)
          rw [fan]
          exact subset_biUnion_of_mem
            (u := fun t => fibreSegment (fun i => cM g i - v * t i)
              (fun i => cM g i + (1 - v) * t i)) ht
        · exact hseg_sub p (Finset.mem_coe.1 hpA)
  -- `Q` contains fibre segments of every admissible displacement
  have hQslopes : ∀ w : Fin n → ℝ, ‖w‖ ≤ (1/2 : ℝ) → ∃ x₁ x₂ : Fin n → ℝ, ‖x₁‖ ≤ 1 ∧
      ‖x₂‖ ≤ 1 ∧ x₂ - x₁ = w ∧ fibreSegment x₁ x₂ ⊆ Q := by
    intro w hw
    obtain ⟨g, hm⟩ := hcovs w hw
    refine ⟨(fun i => cM g i - v * w i), (fun i => cM g i + (1 - v) * w i),
      (hends g w hm).1, (hends g w hm).2, ?_, ?_⟩
    · funext i; simp only [Pi.sub_apply]; ring
    · refine subset_trans ?_ (hfan_sub g)
      rw [fan]
      have hmem : w ∈ {t : Fin n → ℝ | ∀ i, t i ∈ Icc (sM g i - η) (sM g i + η)} := hm
      exact subset_biUnion_of_mem
        (u := fun t : Fin n → ℝ => fibreSegment (fun i => cM g i - v * t i)
          (fun i => cM g i + (1 - v) * t i)) hmem
  -- thin cover of `Q`
  have hQthin : HasThinCover Q v ε := by
    rw [hQ]
    exact hasThinCover_fans_union_net hn hη hη' hε hv₀ hv₁ hM₀η hs1 nt
      fun q hq => ⟨(hntP q hq).1, (hntP q hq).2.1⟩
  -- assemble the element of kornerCompacts
  have hQP : (⟨⟨Q, hQcomp⟩, hQne⟩ : NonemptyCompacts (Fin (n+1) → ℝ)) ∈ kornerCompacts :=
    ⟨hQcomp.isClosed, hQstrip, hQdecomp, hQslopes⟩
  refine ⟨⟨⟨⟨Q, hQcomp⟩, hQne⟩, hQP⟩, ?_, ?_⟩
  · -- δ-close to P
    rw [mem_ball, Subtype.dist_eq, NonemptyCompacts.dist_eq]
    have hd1 : ∀ x ∈ Q, ∃ y ∈ (P : Set (Fin (n+1) → ℝ)), dist x y ≤ 3 * (δ / 4) := by
      intro x hx
      rw [hQ] at hx
      rcases hx with hx | hx
      · obtain ⟨g, hm⟩ := mem_iUnion.1 hx
        obtain ⟨y, hyP, hyd⟩ := hnear g x hm
        exact ⟨y, hyP, hyd.trans (by linarith)⟩
      · obtain ⟨q, hq⟩ := mem_iUnion.1 hx
        obtain ⟨hqnt, hxq⟩ := mem_iUnion.1 hq
        exact ⟨x, (hntP q hqnt).2.2 hxq, by rw [dist_self]; positivity⟩
    have hd2 : ∀ x ∈ (P : Set (Fin (n+1) → ℝ)), ∃ y ∈ Q, dist x y ≤ 3 * (δ / 4) := by
      intro x hx
      obtain ⟨q, hq, y, hyq, hyd⟩ := hntnet x hx
      exact ⟨y, hseg_sub q hq hyq, hyd.trans (by linarith)⟩
    exact (hausdorffDist_le_of_mem_dist (by positivity) hd1 hd2).trans_lt (by linarith)
  · exact hQthin

end Besicovitch
