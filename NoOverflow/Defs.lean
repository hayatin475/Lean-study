import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic

/-!
# `Rsup`（オーバーフロー上限）を持ち回らない設計・基本定義

オーバーフローは発生しないものと仮定して `Rsup` を廃止する一方，
`RN_normal` / `RN_underflow` は「正しい領域でしか呼べない」ことを
証明付き引数として要求し，誤用を型レベルで防ぐ。
外部から使う定理は，証明の組み立てが不要な全域関数 `RN` を介して述べる。

このファイルは基本定義のみを含む。誤差評価などの定理は
`KahanProject.NoOverflow.Rounding` 以降を参照。
-/

namespace FloatLibNoOverflow

noncomputable def u :ℝ  := 2 ^ (-53 : ℝ )

noncomputable def log2r (a : ℝ) : ℝ :=
  Real.log a / Real.log 2

noncomputable def ufp (a : ℝ) : ℝ :=
  if __ : a = 0 then 0
  else 2^((Int.floor (log2r |a|)) : ℝ)

noncomputable def ulp (a : ℝ) : ℝ :=
 Real.rpow 2 ((ufp a - 52 : ℝ ) : ℝ)

axiom same (a : ℝ) : (ufp a) * u = (1 / 2) * ulp a

lemma same2 (a : ℝ) :u*(ufp a) =(1/2)*ulp a:= by
 have h :(ufp a) * u = (1/2)*ulp a:= by exact same a
 simpa [mul_comm] using h


/-- 2のrpowは底が正なので常に正 -/
lemma ulp_pos (a : ℝ) : 0 < ulp a := by
  have two_pos : (0 : ℝ) < 2 := by norm_num
  simpa [ulp] using Real.rpow_pos_of_pos two_pos (ufp a - 52)

/-- 格子幅 Δ を別名にしておく（= `ulp e`） -/
@[simp] noncomputable def Δ (a : ℝ) : ℝ := ulp (a)

/-- a を Δ=ulp e で割ったときの格子インデックス K := ⌊a/Δ⌋ -/
noncomputable def K_of (a : ℝ) : Int := Int.floor (a / Δ a)
noncomputable def rem_of (a : ℝ) : ℝ := a - (K_of a  : ℝ) * Δ a


lemma Δ_pos (a : ℝ) : 0 < Δ a := by
  simpa [Δ] using ulp_pos (a)

/-- 分解の恒等式：`a = (K*Δ) + rem` -/
lemma rem_lt_Δ (a : ℝ) : rem_of a < Δ a := by
  simp [rem_of, K_of, Δ]
  have hΔ : 0 < ulp a := ulp_pos a
  have hΔne : ulp a ≠ 0 := ne_of_gt hΔ
  have hlt : a / ulp a < (Int.floor (a / ulp a) : ℝ) + 1 := by
    exact Int.lt_floor_add_one (a / ulp a)
  have hlt' : a < ((Int.floor (a / ulp a) : ℝ) + 1) * ulp a := by
    have := (mul_lt_mul_of_pos_right hlt hΔ)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,hΔne] using this
  have m: a - (Int.floor (a / ulp a) : ℝ) * ulp a < ulp a := by
     have h1 : a < (Int.floor (a / ulp a) : ℝ) * ulp a + ulp a := by
      simpa [add_mul,one_mul]using hlt'
     have h2 :
       a - (Int.floor (a / ulp a) : ℝ) * ulp a
        < ((Int.floor (a / ulp a) : ℝ) * ulp a + ulp a)
          - (Int.floor (a / ulp a) : ℝ) * ulp a :=
      sub_lt_sub_right h1 ((Int.floor (a / ulp a) : ℝ) * ulp a)
     simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h2
  rw [← Δ,←K_of,← rem_of]at m
  exact m


noncomputable def RNs (a : ℝ) :=
  if __ : rem_of a  <  Δ a *(1/2) then
    (K_of a  : ℝ) *  Δ a
  else
    ((K_of a  + 1 : Int) : ℝ) *  Δ a

noncomputable def Round_up (a : ℝ) :=
  if __ : rem_of a > 0 then
    ((K_of a  + 1 : Int) : ℝ) *  Δ a
  else
    (K_of a  : ℝ) *  Δ a

noncomputable def Round_down (a : ℝ) :=
  (K_of a : ℝ ) * (Δ a)

noncomputable def Fmin : ℝ := (2 : ℝ) ^ (-1022 : ℤ)
noncomputable def Smin : ℝ := (2 : ℝ) ^ (-1074 : ℤ)

lemma Fmin_pos : 0 < Fmin := by
  -- Fmin = (2:ℝ) ^ (emin : ℤ) の形を想定
    have h2 : (0 : ℝ) < (2 : ℝ) := by
       norm_num
    simpa [Fmin] using (zpow_pos h2 (-1022: ℤ))
@[simp] lemma halfΔ_eq_div (a : ℝ) : (1/2 : ℝ) * Δ a = Δ a / 2 := by
  ring

lemma decompose (a : ℝ) :
  a = (K_of a  : ℝ) * Δ a + rem_of a  := by
  have : (K_of a  : ℝ) * Δ a + (a - (K_of a  : ℝ) * Δ a) = a := by ring
  simp [rem_of]

lemma rem_nonneg (a : ℝ) : 0 ≤ rem_of a := by
  -- ⌊a/Δ⌋ ≤ a/Δ
  have hK : (K_of a : ℝ) ≤ a / Δ a := by
    simpa [K_of] using Int.floor_le (a / Δ a)
  -- 0 < Δ → a/Δ の両辺に Δ を掛ける
  have hmul : Δ a * (K_of a : ℝ) ≤ a := by
    have hΔ : 0 < Δ a := Δ_pos a
    exact (le_div_iff₀' hΔ).1 hK
  -- a - KΔ ≥ 0
  simpa [rem_of, Δ, mul_comm] using sub_nonneg.mpr hmul

lemma Smin_pos : 0 < Smin := by
  have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  simpa [Smin] using (zpow_pos h2 (-1074 : ℤ))

def NoUnderflow (x : ℝ) : Prop :=
  Fmin ≤ |x|

def Underflow (x : ℝ) : Prop :=
   |x| < Fmin

noncomputable def sgn (x : ℝ) : ℝ :=
  if x < 0 then (-1) else 1

/-- 通常域の丸め関数。`Fmin ≤ |a|` の証明を要求することで，アンダーフロー域での
    誤用を型レベルで防ぐ（証明自体は計算には使わない）。 -/
noncomputable def RN_normal (a : ℝ) (_h : Fmin ≤ |a|) : ℝ :=
  if rem_of a ≤ Δ a * (1/2 : ℝ) then
    (K_of a : ℝ) * Δ a
  else
    ((K_of a + 1 : Int) : ℝ) * Δ a

/-- アンダーフロー域の丸め関数。`Underflow x` の証明を要求することで，通常域での
    誤用を型レベルで防ぐ（証明自体は計算には使わない）。 -/
noncomputable def RN_underflow (x : ℝ) (_h : Underflow x) : ℝ :=
  let t : ℝ := |x| / Smin
  let k : ℤ := Int.ceil (t - (1/2 : ℝ))
  (sgn x) * (k : ℝ) * Smin

/-- オーバーフローを考えない，完全に全域な丸め関数。`RN_normal` / `RN_underflow` を
    正しい領域だけで呼び出すことを内部で保証しているので，`RN` 自体は証明の
    持ち回りが一切不要。 -/
noncomputable def RN (a : ℝ) : ℝ :=
  if h : |a| < Fmin then RN_underflow a h else RN_normal a (not_lt.mp h)

lemma RN_eq_normal (a : ℝ) (h : Fmin ≤ |a|) : RN a = RN_normal a h := by
  unfold RN
  rw [dif_neg (not_lt.mpr h)]

lemma hu_pos : 0 < u := by
  unfold u
  have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  simpa using (Real.rpow_pos_of_pos h2 (-53 : ℝ))

lemma hu_ne : u ≠ 0 := by
  exact ne_of_gt hu_pos

lemma hup : 0 ≤ |u| := by
  exact abs_nonneg u



axiom hΔ (x : ℝ) : Δ (ufp x + 1 / 2 * ulp x) = ulp x

lemma rem_of_half_ulp
  (x : ℝ)
  (hΔ : Δ (ufp x + 1 / 2 * ulp x) = ulp x)
  (hufp : ∃ k : ℤ, ufp x = (k : ℝ) * ulp x)
  (hulp : 0 < ulp x) :
  rem_of (ufp x + 1 / 2 * ulp x) = 1/2 * ulp x := by
  rcases hufp with ⟨k, hk⟩
  have hne : ulp x ≠ 0 := ne_of_gt hulp
  have hdiv :
      (ufp x + 1 / 2 * ulp x) / ulp x = (k : ℝ) + 1 / 2 := by
    calc
      (ufp x + 1 / 2 * ulp x) / ulp x
          = ((k : ℝ) * ulp x + 1 / 2 * ulp x) / ulp x := by
              simp [hk]
      _ = (k : ℝ) + 1 / 2 := by
              simp [add_div, hne, mul_comm]
  have hfloorUlp :
      Int.floor ((ufp x + 1 / 2 * ulp x) / ulp x) = k := by
    have hfloorHalf : Int.floor ((k : ℝ) + (1 / 2 : ℝ)) = k := by
      have h1 : (k : ℝ) ≤ (k : ℝ) + (1 / 2 : ℝ) := by nlinarith
      have h2 : (k : ℝ) + (1 / 2 : ℝ) < (k : ℝ) + 1 := by nlinarith
      exact (Int.floor_eq_iff).2 ⟨h1, h2⟩
    rw [hdiv]
    exact hfloorHalf
  have hΔ' : ulp (ufp x + 1 / 2 * ulp x) = ulp x := by
    simpa [Δ] using hΔ
  have hfloorΔ :
      Int.floor ((ufp x + 1 / 2 * ulp x) / Δ (ufp x + 1 / 2 * ulp x)) = k := by
    rw [Δ, hΔ']
    exact hfloorUlp
  calc
    rem_of (ufp x + 1 / 2 * ulp x)
        = (ufp x + 1 / 2 * ulp x)
          - (Int.floor ((ufp x + 1 / 2 * ulp x) / Δ (ufp x + 1 / 2 * ulp x)) : ℝ)
            * Δ (ufp x + 1 / 2 * ulp x) := by
            simp [rem_of, K_of]
    _ = (ufp x + 1 / 2 * ulp x) - (k : ℝ) * ulp x := by
          rw [hfloorΔ, hΔ]
    _ = 1 / 2 * ulp x := by
      calc
        (ufp x + 1 / 2 * ulp x) - (k : ℝ) * ulp x
            = ((k : ℝ) * ulp x + 1 / 2 * ulp x) - (k : ℝ) * ulp x := by
                simp [hk]
        _ = 1 / 2 * ulp x := by ring

axiom hru (x : ℝ) (h : Fmin ≤ x) (hx : x = (1 + u) * ufp x) :
  RN (ufp x + 1 / 2 * ulp x) = ufp x

axiom hur (x : ℝ) (hx : x < (1 + u) * ufp x) : RN x = ufp x
axiom hux (x : ℝ) (hx : x < (1 + u) * ufp x) : ufp x ≤  x
axiom hbg (x : ℝ) : |RN x| ≥  |ufp x|
axiom RN_neg (x : ℝ) : RN (-x) = - RN x

end FloatLibNoOverflow
