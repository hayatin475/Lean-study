import KahanProject.NoOverflow.Defs
import KahanProject.NoOverflow.Underflow

/-!
# Sterbenz の補題

`y/2 ≤ x ≤ 2y` のとき `x - y` は丸め誤差なく厳密に表現できる，という定理。
-/

namespace FloatLibNoOverflow

lemma ufp_eq_zpow (a : ℝ) (ha : a ≠ 0) :
    ufp a = (2 : ℝ) ^ (Int.floor (log2r |a|)) := by
  unfold ufp
  rw [dif_neg ha, Real.rpow_intCast]

lemma floor_log2r_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Int.floor (log2r a) ≤ Int.floor (log2r b) := by
  apply Int.floor_mono
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  unfold log2r
  gcongr

/-- `ufp` は単調： `|a| ≤ |b|` なら `ufp a ≤ ufp b`。 -/
lemma ufp_mono {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≤ |b|) :
    ufp a ≤ ufp b := by
  have ha' : 0 < |a| := abs_pos.mpr ha
  rw [ufp_eq_zpow a ha, ufp_eq_zpow b hb]
  have hle : Int.floor (log2r |a|) ≤ Int.floor (log2r |b|) := floor_log2r_mono ha' hab
  exact zpow_le_zpow_right₀ (by norm_num) hle

/-- `Δ` の単調性：`|a| ≤ |b|` なら `Δ a ≤ Δ b`。 -/
lemma Δ_mono {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≤ |b|) :
    Δ a ≤ Δ b := by
  have h1 : u * ufp a = (1 / 2) * ulp a := same2 a
  have h2 : u * ufp b = (1 / 2) * ulp b := same2 b
  have hmono : ufp a ≤ ufp b := ufp_mono ha hb hab
  have hmul : u * ufp a ≤ u * ufp b := mul_le_mul_of_nonneg_left hmono hu_pos.le
  have : ulp a ≤ ulp b := by nlinarith [h1, h2, hmul]
  simpa [Δ] using this

/-- `ufp` は 2 のべき比：大きい方は小さい方の 2ⁿ 倍になっている。 -/
lemma ufp_dvd_of_le {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≤ |b|) :
    ∃ m : ℕ, ufp b = ufp a * 2 ^ m := by
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hle : Int.floor (log2r |a|) ≤ Int.floor (log2r |b|) := floor_log2r_mono ha' hab
  refine ⟨(Int.floor (log2r |b|) - Int.floor (log2r |a|)).toNat, ?_⟩
  rw [ufp_eq_zpow a ha, ufp_eq_zpow b hb]
  have hcast : ((Int.floor (log2r |b|) - Int.floor (log2r |a|)).toNat : ℤ)
      = Int.floor (log2r |b|) - Int.floor (log2r |a|) := Int.toNat_of_nonneg (by linarith)
  rw [← zpow_natCast (2 : ℝ) (Int.floor (log2r |b|) - Int.floor (log2r |a|)).toNat, hcast]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp

lemma Δ_dvd_of_le {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≤ |b|) :
    ∃ m : ℕ, Δ b = Δ a * 2 ^ m := by
  obtain ⟨m, hm⟩ := ufp_dvd_of_le ha hb hab
  refine ⟨m, ?_⟩
  have h1 : u * ufp a = (1 / 2) * ulp a := same2 a
  have h2 : u * ufp b = (1 / 2) * ulp b := same2 b
  have hkey : (1 / 2 : ℝ) * ulp b = (1 / 2 : ℝ) * ulp a * 2 ^ m := by
    rw [← h1, ← h2, hm]; ring
  have : ulp b = ulp a * 2 ^ m := by linarith [hkey]
  simpa [Δ] using this

/-- `RN` の不動点は，アンダーフローしていなければ `Δ` 格子上にある。 -/
lemma grid_of_fixed_normal {a : ℝ} (h : Fmin ≤ |a|) (hfix : RN a = a) :
    ∃ k : ℤ, a = (k : ℝ) * Δ a := by
  rw [RN_eq_normal a h] at hfix
  by_cases hc : rem_of a ≤ Δ a * (1 / 2 : ℝ)
  · have hval : RN_normal a h = (K_of a : ℝ) * Δ a := by
      unfold RN_normal
      exact if_pos hc
    rw [hval] at hfix
    exact ⟨K_of a, hfix.symm⟩
  · have hval : RN_normal a h = ((K_of a + 1 : Int) : ℝ) * Δ a := by
      unfold RN_normal
      exact if_neg hc
    rw [hval] at hfix
    exact ⟨K_of a + 1, hfix.symm⟩

/-- `a` が `Δ a` の整数倍なら，`RN_normal` の不動点になる。 -/
lemma normal_of_exact_multiple {a : ℝ} (h : Fmin ≤ |a|) (k : ℤ) (hk : a = (k : ℝ) * Δ a) :
    RN_normal a h = a := by
  have hΔne : Δ a ≠ 0 := (Δ_pos a).ne'
  have hK : K_of a = k := by
    unfold K_of
    nth_rewrite 1 [hk]
    rw [mul_div_cancel_right₀ _ hΔne, Int.floor_intCast]
  have hrem : rem_of a = 0 := by
    unfold rem_of
    rw [hK]
    nth_rewrite 1 [hk]
    ring
  have hle : rem_of a ≤ Δ a * (1 / 2 : ℝ) := by
    rw [hrem]; nlinarith [Δ_pos a]
  have hval : RN_normal a h = (K_of a : ℝ) * Δ a := by
    unfold RN_normal
    exact if_pos hle
  rw [hval, hK]
  exact hk.symm

/-- Sterbenz の補題：`Rsup` が一切登場せず，前提がかなり簡潔になる。 -/
theorem teiri1_11
    (x y : ℝ)
    (hx : RN x = x)
    (hy : RN y = y)
    (hxy : y / 2 ≤ x ∧ x ≤ 2 * y)
  :
    x - y = RN (x - y) := by
  by_cases hU : |x - y| < Fmin
  · have hUnder : Underflow (x - y) := hU
    have heq : RN (x - y) = RN_underflow (x - y) hUnder := by
      unfold RN
      rw [dif_pos hU]
    rw [heq]
    exact (teiri1_8_2 x y hUnder).symm
  · have hFmin_xy : Fmin ≤ |x - y| := not_lt.mp hU
    have hxy_ne : x - y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hFmin_xy
      exact absurd hFmin_xy (not_le.mpr Fmin_pos)
    have hy_pos : 0 < y := by
      by_contra hy_le
      push Not at hy_le
      have h1 := hxy.1
      have h2 := hxy.2
      have hy0 : y = 0 := le_antisymm hy_le (by linarith)
      have hx0 : x = 0 := by linarith
      exact hxy_ne (by rw [hx0, hy0]; ring)
    have hx_pos : 0 < x := by linarith [hxy.1]
    have hbound : |x - y| ≤ min x y := by
      rcases le_total y x with hxy' | hxy'
      · rw [abs_of_nonneg (by linarith), min_eq_right hxy']
        linarith [hxy.2]
      · rw [abs_of_nonpos (by linarith), min_eq_left hxy']
        linarith [hxy.1]
    have hboundx : |x - y| ≤ x := le_trans hbound (min_le_left x y)
    have hboundy : |x - y| ≤ y := le_trans hbound (min_le_right x y)
    have hFmin_x : Fmin ≤ x := le_trans hFmin_xy hboundx
    have hFmin_y : Fmin ≤ y := le_trans hFmin_xy hboundy
    have hxabs : |x| = x := abs_of_pos hx_pos
    have hyabs : |y| = y := abs_of_pos hy_pos
    obtain ⟨kx, hkx⟩ := grid_of_fixed_normal (a := x) (by rw [hxabs]; exact hFmin_x) hx
    obtain ⟨ky, hky⟩ := grid_of_fixed_normal (a := y) (by rw [hyabs]; exact hFmin_y) hy
    have hxne : x ≠ 0 := hx_pos.ne'
    have hyne : y ≠ 0 := hy_pos.ne'
    have hboundx' : |x - y| ≤ |x| := by rw [hxabs]; exact hboundx
    have hboundy' : |x - y| ≤ |y| := by rw [hyabs]; exact hboundy
    obtain ⟨mx, hmx⟩ := Δ_dvd_of_le hxy_ne hxne hboundx'
    obtain ⟨my, hmy⟩ := Δ_dvd_of_le hxy_ne hyne hboundy'
    have hxfinal : x = ((kx * 2 ^ mx : ℤ) : ℝ) * Δ (x - y) := by
      nth_rewrite 1 [hkx]
      rw [hmx]
      push_cast
      ring
    have hyfinal : y = ((ky * 2 ^ my : ℤ) : ℝ) * Δ (x - y) := by
      nth_rewrite 1 [hky]
      rw [hmy]
      push_cast
      ring
    have hfinal : x - y = ((kx * 2 ^ mx - ky * 2 ^ my : ℤ) : ℝ) * Δ (x - y) := by
      push_cast at hxfinal hyfinal ⊢
      linear_combination hxfinal - hyfinal
    have heq2 : RN (x - y) = RN_normal (x - y) hFmin_xy := by
      unfold RN
      rw [dif_neg hU]
    rw [heq2]
    exact (normal_of_exact_multiple hFmin_xy (kx * 2 ^ mx - ky * 2 ^ my) hfinal).symm

end FloatLibNoOverflow
