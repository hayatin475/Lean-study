import KahanProject.NoOverflow.Defs
import KahanProject.NoOverflow.Rounding

/-!
# アンダーフロー域の丸めと、和・積・商の誤差評価

`RN_underflow` に関する基本補題と，`RN` が丸めた和・積・商を
「アンダーフロー域の誤差 η」と「通常域の誤差 δ」に分解する定理群。
-/

namespace FloatLibNoOverflow

-- 最近接・中点下の基本評価
axiom ceil_sub_half_abs_le (t : ℝ) :
  |t - (Int.ceil (t - (1/2 : ℝ)) : ℝ)| ≤ (1/2 : ℝ)

noncomputable def RN_underflow' (x : ℝ) : ℝ :=
  let t : ℝ := |x| / Smin
  let k : ℤ := Int.ceil (t - (1/2 : ℝ))
  (k : ℝ) * Smin

-- underflow のとき、|x| は Smin の整数倍（格子点）になる、という性質
axiom underflow_abs_eq_zsmul_Smin (z : ℝ) (hz : Underflow z) :
  ∃ n : ℤ, |z| = (n : ℝ) * Smin

axiom sgn_mul_abs_real (z : ℝ) : sgn z * |z| = z


lemma teiri1_8 (x y : ℝ) (h : Underflow (x + y)) : RN_underflow (x + y) h = x + y := by
  dsimp [RN_underflow]
  have hSmin : 0 < (2 : ℝ) ^ (-1074 : ℤ) := by
   have h2 : (0 : ℝ) < 2 := by norm_num
   have hpow : 0 < (2 : ℝ) ^ (1074 : ℕ) := by
    simp[pow_pos h2 1074]
   have h: 0 < ((2 : ℝ) ^ (1074 : ℕ))⁻¹ := inv_pos.mpr hpow
   exact h
  have hclose :
    |(|x + y| / Smin)
        - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)|
      ≤ (1/2 : ℝ) := by
    simpa using
      ceil_sub_half_abs_le (|x + y| / Smin)
  have hclose' :
    |(|x + y|)
        - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin|
      ≤ Smin / 2 := by
    have hSmin0 : Smin ≠ 0 := by
      exact ne_of_gt hSmin
    have hSmin_nonneg : 0 ≤ Smin := le_of_lt hSmin
    have hrewrite :
        |(|x + y|
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)|
          =
        |((|x + y| / Smin)
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin| := by
      have hscale : (|x + y| / Smin) * Smin = |x + y| := by
        simp [div_eq_mul_inv, hSmin0]
      calc
        |(|x + y| - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)|
            =
          |((|x + y| / Smin) * Smin
              - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)| := by
                simp [hscale]
        _ =
          |((|x + y| / Smin)
              - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin| := by
                simpa using congrArg abs
                  ( (sub_mul (|x + y| / Smin)
                      (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) Smin).symm )
    have hmul' :
        |(|x + y| / Smin
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ))| * Smin
          ≤ (1/2 : ℝ) * Smin :=
       mul_le_mul_of_nonneg_right hclose hSmin_nonneg
    have hmul :
        |((|x + y| / Smin)
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin|
          ≤ (1/2 : ℝ) * Smin := by
      simpa [abs_mul, abs_of_nonneg hSmin_nonneg, mul_assoc, mul_left_comm, mul_comm]
        using hmul'
    have hno1 :
        |((|x + y| / Smin)
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin|
          ≤ Smin / 2 := by
      have hhalf : (2⁻¹ : ℝ) * Smin = Smin / 2 := by
        simp [div_eq_mul_inv, mul_comm]
      simpa [hhalf] using hmul
    have hno :
        |(|x + y|
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)|
          ≤ Smin / 2 := by
      rw [hrewrite.symm] at hno1
      exact hno1
    exact hno
  have hsmall : |x + y| < Fmin := h
  have hgrid :
    (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin = |x + y| := by
    rcases underflow_abs_eq_zsmul_Smin (z := x + y) h with ⟨n, hn⟩
    have hSn : Smin ≠ 0 := by exact (ne_of_gt Smin_pos)
    have ht : |x + y| / Smin = (n : ℝ) := by
      calc
        |x + y| / Smin
            = ((n : ℝ) * Smin) / Smin := by simp [hn]
        _   = (n : ℝ) := by field_simp [hSn]
    have hceil : Int.ceil ((|x + y| / Smin) - (1/2 : ℝ)) = n := by
      simp [ht]
      norm_num
      exact ceil_sub_half_int n
    calc
      (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
          = (n : ℝ) * Smin := by rw [hceil]
      _   = |x + y| := by simp [hn]
  have hgrid' :
    sgn (x + y) *
        (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
      = x + y := by
   have hL :
      sgn (x + y) *
          (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
        = sgn (x + y) *
            ((Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin) := by
    simp [mul_assoc]
   calc
    sgn (x + y) *
        (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
        = sgn (x + y) * (↑⌈|x + y| / Smin - 1 / 2⌉ * Smin) := by
            simp [mul_assoc]
    _ = sgn (x + y) * |x + y| := by
            rw [hgrid]
    _ = x + y := by
            simpa using (sgn_mul_abs_real (x + y))
  exact hgrid'

lemma teiri1_8_2 (x y : ℝ) (h : Underflow (x - y)) :
    RN_underflow (x - y) h = x - y := by
  have h' : Underflow (x + (-y)) := by
    simpa [sub_eq_add_neg] using h
  simpa [sub_eq_add_neg] using teiri1_8 (x := x) (y := -y) h'

theorem hanni (a b : ℝ) : Underflow (a + b) ∨ Fmin ≤ |a + b| := by
  by_cases hFmin : |a + b| < Fmin
  · left
    exact hFmin
  · right
    exact le_of_not_gt hFmin

theorem teiri1_9_1 (a b δ : ℝ)
    (hsum_ne : a + b ≠ 0)
    (hRN : RN (a + b) = (a + b) * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  let x : ℝ := a + b
  rcases hanni a b with hunder | hmiddle
  · have hUnder : Underflow x := by simpa [x] using hunder
    have hUnder' : |x| < Fmin := hUnder
    have hnear : RN x = x := by
      unfold RN
      rw [dif_pos hUnder']
      simpa [x] using teiri1_8 (x := a) (y := b) hunder
    have hmul : x * (1 + δ) = x := by
      calc
        x * (1 + δ) = RN x := by simpa [x] using hRN.symm
        _ = x := hnear
    have hzero_mul : x * δ = 0 := by linarith [hmul]
    have hx_ne : x ≠ 0 := by simpa [x] using hsum_ne
    have hδ0 : δ = 0 := by
      exact (mul_eq_zero.mp hzero_mul).resolve_left hx_ne
    rw [hδ0]
    have hnonneg : 0 ≤ u / (1 + u) := by
      exact div_nonneg hu_pos.le ittanneo5.le
    simpa using hnonneg
  · have hnormal : RN x = x * (1 + δ) := by simpa [x] using hRN
    exact teiri2_abs x δ hmiddle hnormal

theorem teiri1_9_1_sub (a b δ : ℝ)
    (hsum_ne : a - b ≠ 0)
    (hRN : RN (a - b) = (a - b) * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  have hsum_ne' : a + (-b) ≠ 0 := by
    simpa [sub_eq_add_neg] using hsum_ne
  have hRN' : RN (a + (-b)) = (a + (-b)) * (1 + δ) := by
    simpa [sub_eq_add_neg] using hRN
  simpa [sub_eq_add_neg] using teiri1_9_1 (a := a) (b := -b) (δ := δ) hsum_ne' hRN'

theorem teiri1_9_2 (a b δ : ℝ)
    (hsum_ne : a + b ≠ 0)
    (hRN : (a + b) = RN (a + b) * (1 + δ)) :
    |δ| ≤ u  := by
  rcases hanni a b with hunder | hmiddle
  · have hunder' : |a + b| < Fmin := hunder
    have hnear : RN (a + b) = a + b := by
      unfold RN
      rw [dif_pos hunder']
      exact teiri1_8 (x := a) (y := b) hunder
    have hmul : (a + b) * (1 + δ) = a + b := by
      calc
        (a + b) * (1 + δ) = RN (a + b) * (1 + δ) := by rw [hnear]
        _ = a + b := by simpa using hRN.symm
    have hzero_mul : (a + b) * δ = 0 := by linarith [hmul]
    have hδ0 : δ = 0 := by
      exact (mul_eq_zero.mp hzero_mul).resolve_left hsum_ne
    rw [hδ0]
    simpa using hu_pos.le
  · exact teiri3o (a + b) δ hmiddle hRN

theorem teiri1_9_2_sub (a b δ : ℝ)
    (hsum_ne : a - b ≠ 0)
    (hRN : (a - b) = RN (a - b) * (1 + δ)) :
    |δ| ≤ u := by
  have hsum_ne' : a + (-b) ≠ 0 := by
    simpa [sub_eq_add_neg] using hsum_ne
  have hRN' : (a + (-b)) = RN (a + (-b)) * (1 + δ) := by
    simpa [sub_eq_add_neg] using hRN
  simpa [sub_eq_add_neg] using teiri1_9_2 (a := a) (b := -b) (δ := δ) hsum_ne' hRN'

theorem udgosa (a : ℝ) (ha : |a| < Fmin) :
  |a - RN_underflow a ha| ≤  Smin / 2 := by
  have hEq : RN_underflow a ha = a := by
    simpa using (teiri1_8 a 0 (by simpa [Underflow] using ha))
  rw [hEq]
  have hS : 0 ≤ Smin / 2 := by
    nlinarith [Smin_pos]
  simpa using hS

theorem teiri3
    (a b δ η : ℝ)
    (hRN : RN (a * b) = a * b + δ + η)
    (hδ0 : |a * b| < Fmin → δ = 0)
    (hη0 : ¬(|a * b| < Fmin) → η = 0)
  :
    |δ| ≤ u * ufp (a * b)
    ∧ |η| ≤ Smin / 2
    ∧ δ * η = 0 := by
  by_cases hUF : |a * b| < Fmin
  · have hδ : δ = 0 := hδ0 hUF
    have hnear : RN (a * b) = RN_underflow (a * b) hUF := by
      unfold RN
      rw [dif_pos hUF]
    have hunder : RN_underflow (a * b) hUF = a * b := by
      simpa [Underflow] using (teiri1_8 (x := a * b) (y := 0) (by simpa [Underflow] using hUF))
    have hη : η = 0 := by
      have : a * b = a * b + δ + η := by
        calc
          a * b = RN_underflow (a * b) hUF := hunder.symm
          _ = RN (a * b) := hnear.symm
          _ = a * b + δ + η := hRN
      linarith [this, hδ]
    have hδbound : |δ| ≤ u * ufp (a * b) := by
      rw [hδ, abs_zero]
      have hpos : 0 < u * ufp (a * b) := by
        have hs : u * ufp (a * b) = (1 / 2 : ℝ) * ulp (a * b) := same2 (a * b)
        rw [hs]
        nlinarith [ulp_pos (a * b)]
      exact le_of_lt hpos
    have hηbound : |η| ≤ Smin / 2 := by
      rw [hη, abs_zero]
      nlinarith [Smin_pos]
    exact ⟨hδbound, hηbound, by simp [hδ, hη]⟩
  · have hη : η = 0 := hη0 hUF
    have hmid : Fmin ≤ |a * b| := le_of_not_gt hUF
    have hnear : RN (a * b) = RN_normal (a * b) hmid := by
      unfold RN
      rw [dif_neg hUF]
    have hδrepr : δ = RN_normal (a * b) hmid - (a * b) := by
      have : RN_normal (a * b) hmid = a * b + δ := by
        calc
          RN_normal (a * b) hmid = RN (a * b) := hnear.symm
          _ = a * b + δ + η := hRN
          _ = a * b + δ := by simp [hη]
      linarith
    have hδbound : |δ| ≤ u * ufp (a * b) := by
      rw [hδrepr]
      rw [← RN_eq_normal (a * b) hmid]
      simpa [abs_sub_comm] using (teiri1o (a * b) hmid)
    have hηbound : |η| ≤ Smin / 2 := by
      rw [hη, abs_zero]
      nlinarith [Smin_pos]
    exact ⟨hδbound, hηbound, by simp [hη]⟩

theorem teiri4
    (a b δ η : ℝ)
    (hRN : RN (a / b) = a / b + δ + η)
    (hδ0 : |a / b| < Fmin → δ = 0)
    (hη0 : ¬(|a / b| < Fmin) → η = 0)
  :
    |δ| ≤ u * ufp (a / b)
    ∧ |η| ≤ Smin / 2
    ∧ δ * η = 0 := by
  by_cases hUF : |a / b| < Fmin
  · have hδ : δ = 0 := hδ0 hUF
    have hnear : RN (a / b) = RN_underflow (a / b) hUF := by
      unfold RN
      rw [dif_pos hUF]
    have hunder : RN_underflow (a / b) hUF = a / b := by
      simpa [Underflow] using (teiri1_8 (x := a / b) (y := 0) (by simpa [Underflow] using hUF))
    have hη : η = 0 := by
      have : a / b = a / b + δ + η := by
        calc
          a / b = RN_underflow (a / b) hUF := hunder.symm
          _ = RN (a / b) := hnear.symm
          _ = a / b + δ + η := hRN
      linarith [this, hδ]
    have hδbound : |δ| ≤ u * ufp (a / b) := by
      rw [hδ, abs_zero]
      have hpos : 0 < u * ufp (a / b) := by
        have hs : u * ufp (a / b) = (1 / 2 : ℝ) * ulp (a / b) := same2 (a / b)
        rw [hs]
        nlinarith [ulp_pos (a / b)]
      exact le_of_lt hpos
    have hηbound : |η| ≤ Smin / 2 := by
      rw [hη, abs_zero]
      nlinarith [Smin_pos]
    exact ⟨hδbound, hηbound, by simp [hδ, hη]⟩
  · have hη : η = 0 := hη0 hUF
    have hmid : Fmin ≤ |a / b| := le_of_not_gt hUF
    have hnear : RN (a / b) = RN_normal (a / b) hmid := by
      unfold RN
      rw [dif_neg hUF]
    have hδrepr : δ = RN_normal (a / b) hmid - (a / b) := by
      have : RN_normal (a / b) hmid = a / b + δ := by
        calc
          RN_normal (a / b) hmid = RN (a / b) := hnear.symm
          _ = a / b + δ + η := hRN
          _ = a / b + δ := by simp [hη]
      linarith
    have hδbound : |δ| ≤ u * ufp (a / b) := by
      rw [hδrepr]
      rw [← RN_eq_normal (a / b) hmid]
      simpa [abs_sub_comm] using (teiri1o (a / b) hmid)
    have hηbound : |η| ≤ Smin / 2 := by
      rw [hη, abs_zero]
      nlinarith [Smin_pos]
    exact ⟨hδbound, hηbound, by simp [hη]⟩

end FloatLibNoOverflow
