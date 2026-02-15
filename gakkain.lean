import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic

namespace FloatLib

noncomputable def u :ℝ  := 2 ^ (-53 : ℝ )

noncomputable def log2r (a : ℝ) : ℝ :=
  Real.log a / Real.log 2

noncomputable def ufp (a : ℝ) : ℝ :=
  if __ : a = 0 then 0
  else 2^((Int.floor (log2r |a|)) : ℝ)

noncomputable def ulp (a : ℝ ) : ℝ :=
 Real.rpow 2 ((ufp a - 52 : ℝ ) : ℝ)

axiom same (a :ℝ ) : (ufp a) * u = (1 / 2) * ulp a

lemma same2 (a :ℝ ) :u*(ufp a) =(1/2)*ulp a:= by
 have h :(ufp a) * u = (1/2)*ulp a:= by exact same a
 simpa [mul_comm] using h


/-- 2のrpowは底が正なので常に正 -/
lemma ulp_pos (a : ℝ) : 0 < ulp a := by
  have two_pos : (0 : ℝ) < 2 := by norm_num
  simpa [ulp] using Real.rpow_pos_of_pos two_pos (ufp a - 52)

/-- 格子幅 Δ を別名にしておく（= `ulp e`） -/
@[simp] noncomputable def Δ (a: ℝ ) : ℝ := ulp (a)

/-- a を Δ=ulp e で割ったときの格子インデックス K := ⌊a/Δ⌋ -/

noncomputable def K_of  (a : ℝ ) : Int := Int.floor (a / Δ a)
noncomputable def rem_of (a : ℝ)  : ℝ := a - (K_of a  : ℝ) * Δ a
noncomputable def RN (a : ℝ)   :=
  if __ : rem_of a  ≤  Δ a *(1/2) then
    (K_of a  : ℝ) *  Δ a
  else
    ((K_of a  + 1 : Int) : ℝ) *  Δ a

/-- Δ は正（`ulp_pos` を流用） -/

lemma Δ_pos (a : ℝ ) : 0 < Δ a := by
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


noncomputable def RNs (a : ℝ)   :=
  if __ : rem_of a  <  Δ a *(1/2) then
    (K_of a  : ℝ) *  Δ a
  else
    ((K_of a  + 1 : Int) : ℝ) *  Δ a

noncomputable def Round_up (a : ℝ ) :=
  if __ : rem_of a > 0 then
    ((K_of a  + 1 : Int) : ℝ) *  Δ a
  else
    (K_of a  : ℝ) *  Δ a

noncomputable def Round_down (a :ℝ ) :=
  (K_of a : ℝ ) * (Δ a)

noncomputable def Fmin : ℝ := (2 : ℝ) ^ (-1022 : ℤ)
noncomputable def Smin : ℝ := (2 : ℝ) ^ (-1074 : ℤ)

lemma Fmin_pos : 0 < Fmin := by
  -- Fmin = (2:ℝ) ^ (emin : ℤ) の形を想定
    have h2 : (0 : ℝ) < (2 : ℝ) := by
       norm_num
    simpa [Fmin] using (zpow_pos h2 (-1022: ℤ))
@[simp] lemma halfΔ_eq_div (a : ℝ ) : (1/2 : ℝ) * Δ a = Δ a / 2 := by
  ring

lemma decompose (a : ℝ)  :
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

noncomputable def Fmax : ℝ :=
  ((2 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) * (2 : ℝ) ^ (1023 : ℤ)

def NoOverflow (x : ℝ) : Prop :=
  |x| ≤ Fmax

noncomputable def Rsup : ℝ :=
  Fmax + u * ufp Fmax

def middle (x : ℝ ) : Prop :=
  Fmin ≤ |x| ∧  |x| ≤ Rsup

def Underflow (x : ℝ) : Prop :=
   |x| < Fmin

def Overflow (x : ℝ) : Prop :=
  |x| ≥ Rsup

noncomputable def RN_normal : {a : ℝ // middle a} → ℝ
| ⟨a, _h⟩ =>
    if rem_of a ≤ Δ a * (1/2 : ℝ) then
      (K_of a : ℝ) * Δ a
    else
      ((K_of a + 1 : Int) : ℝ) * Δ a

noncomputable def sgn (x : ℝ) : ℝ :=
  if x < 0 then (-1) else 1

noncomputable def RN_underflow : {x : ℝ // Underflow x} → ℝ
| ⟨x, _hx⟩ =>
  let t : ℝ := |x| / Smin
  let k : ℤ := Int.ceil (t - (1/2 : ℝ))
  (sgn x) * (k : ℝ) * Smin

noncomputable def RN_nearest (a : ℝ) (hsup : |a| ≤ Rsup) : ℝ :=
  if hunder : |a| < Fmin then
    have hunder' : Underflow a := by
      simpa [Underflow] using hunder
    RN_underflow ⟨a, hunder'⟩
  else
    have hmin : Fmin ≤ |a| := le_of_not_gt hunder
    RN_normal ⟨a, ⟨hmin, hsup⟩⟩

lemma hu_pos : 0 < u := by
  unfold u
  have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  simpa using (Real.rpow_pos_of_pos h2 (-53 : ℝ))

lemma hu_ne : u ≠ 0 := by
  exact ne_of_gt hu_pos

lemma hup : 0 ≤ |u| := by
  exact abs_nonneg u


#print ufp

axiom hru (x: ℝ ) (hx : x= (1+u)* ufp x) : RN (ufp x + 1 / 2 * ulp x) = ufp x
axiom hur (x: ℝ ) (hx : x < (1 + u) * ufp x) : RN x = ufp x
axiom hux (x: ℝ ) (hx : x < (1 + u) * ufp x) : ufp x ≤  x
axiom hbg (x :ℝ ) : |RN x| ≥  |ufp x|
axiom RN_neg (x : ℝ) : RN (-x) = - RN x


theorem teiri1o (a : ℝ)  (ha : Fmin ≤ |a| ∧  |a| ≤  Rsup) :
  |a - RN_normal ⟨a, ha⟩| ≤ u * ufp a := by
  classical

  have hc   : 0 < Δ a := by simpa [Δ] using Δ_pos a
  have hr0  : 0 ≤ rem_of a := by simpa [rem_of] using rem_nonneg (a:=a)
  have hrd  : rem_of a < Δ a := by simpa [rem_of, Δ] using rem_lt_Δ (a:=a)

  have hsplit : a = (K_of a : ℝ) * Δ a + rem_of a := by
    exact decompose (a := a)

  have hsub : a - (K_of a : ℝ) * Δ a = rem_of a := by
   calc
    a - (K_of a : ℝ) * Δ a
        = ((K_of a : ℝ) * Δ a + rem_of a) - (K_of a : ℝ) * Δ a := by
         nth_rewrite 1  [hsplit]
         rfl
      _ = rem_of a := by ring

  have abs_k : |a - (K_of a : ℝ) * Δ a| = rem_of a := by
    rw[hsub]
    simp [rem_nonneg]

  have hk1 : a - ((K_of a + 1 : Int) : ℝ) * Δ a = rem_of a - Δ a := by
    have := congrArg (fun x => x - ((K_of a + 1 : Int) : ℝ) * Δ a) hsplit
    simpa [Int.cast_add, Int.cast_one, add_mul, one_mul, add_comm, add_left_comm, add_assoc]
      using this

  have abs_up : |a - ((K_of a + 1 : Int) : ℝ) * Δ a| = Δ a - rem_of a := by
    have h1 : |a - ((K_of a + 1 : Int) : ℝ) * Δ a| = |rem_of a - Δ a| := by
      rw [hk1]

    have h2 : |rem_of a - Δ a| = Δ a - rem_of a := by
      simpa [neg_sub] using abs_of_neg (sub_lt_zero.mpr hrd)

    rw [h1, h2]

  by_cases hle : rem_of a  ≤ Δ a*(1/2)
  case pos =>
    -- RN_normal = k·d
   have itiou : rem_of a ≤ Δ a / 2 := by
    simpa [div_eq_mul_inv] using hle

   have hle : rem_of a  ≤ Δ a *(1/ 2) := by
    exact hle

   have hRN_normal0 : RN_normal  ⟨a, ha⟩  = (K_of a  : ℝ) * Δ a := by
    classical
    unfold RN_normal
    exact if_pos hle
   have hRN_normal :RN_normal  ⟨a, ha⟩  = (K_of a : ℝ ) * Δ a := by
    simp [hRN_normal0]
   have hdist : |a - RN_normal ⟨a, ha⟩| = rem_of a := by
    simp [hRN_normal]
    rw[← Δ,abs_k]
   have huufp : Δ a / 2 = u * ufp a := by
    calc
      Δ a / 2 = (1 / 2 : ℝ) * Δ a := by ring
      _ = (1 / 2 : ℝ) * ulp a := by simp [Δ]
      _ = u * ufp a := by simpa [mul_comm] using (same2 a).symm
   rw [hdist]
   calc
    rem_of a ≤ Δ a / 2 := itiou
    _ = u * ufp a := huufp


  case neg =>
   have hRG : RN_normal ⟨a, ha⟩ = ((K_of a  + 1 : Int) : ℝ) * Δ a := by
    classical
    unfold RN_normal
    exact if_neg hle


   have hdistu : |a - RN_normal ⟨a, ha⟩|  = Δ a - rem_of a := by
    rw [hRG]
    rw [abs_up]

   have small : Δ a - rem_of a ≤ Δ a / 2 := by
    have : rem_of a > Δ a / 2 :=by
     simpa  using hle
    linarith

   have saigo: |a - RN_normal ⟨a, ha⟩| ≤ Δ a / 2 := by
    rw [hdistu]
    exact small

   have huufp : Δ a / 2 = u * ufp a := by
    calc
      Δ a / 2 = (1 / 2 : ℝ) * Δ a := by ring
      _ = (1 / 2 : ℝ) * ulp a := by simp [Δ]
      _ = u * ufp a := by simpa [mul_comm] using (same2 a).symm

   calc
    |a - RN_normal ⟨a, ha⟩| ≤ Δ a / 2 := saigo
    _ = u * ufp a := huufp

lemma teiri1o' (a:ℝ ) (ha : Fmin ≤ |a| ∧  |a| ≤ Rsup):|a - RN_normal ⟨a, ha⟩| ≤ ufp a * u := by
 simpa [mul_comm] using (teiri1o a ha)

axiom ittanneo3 (x: ℝ ) (hx : x < (1 + u) * ufp x) (ha : Fmin ≤ |x| ∧  |x| ≤ Rsup): RN_normal ⟨x, ha⟩ = ufp x
axiom ittanneo4 (x: ℝ ) (hx : x < (1 + u) * ufp x)(ha : Fmin ≤ |x| ∧  |x| ≤ Rsup) : ufp x < x
axiom ittanneo8 (x :ℝ ) (ha : Fmin ≤ |x| ∧  |x| ≤ Rsup) : |RN_normal ⟨x, ha⟩| ≥  |ufp x|

lemma ittanneo5 : 0 < 1 + u := by
  have h1 : (0 : ℝ) < 1 := by
    norm_num
  exact add_pos h1 hu_pos

lemma ittanneo5' : 0 < u + 1 := by
  simpa [add_comm] using ittanneo5

lemma ittanneo2 : - u / (1 + u) < 0 :=by
 have h : u / (1 + u) > 0 := by
  exact div_pos hu_pos ittanneo5
 have h' : -(u / (1 + u)) < 0 := by
    exact neg_lt_zero.mpr h
 simpa [neg_div] using h'


theorem teiri2_pos (a δ : ℝ)   (harange : Fmin ≤  a ∧ a ≤ Rsup)
    (hRN : RN_normal ⟨a, by
      constructor
      · simpa [abs_of_nonneg (le_trans Fmin_pos.le harange.1)] using harange.1
      ·
        have hnonneg : 0 ≤ a := le_trans Fmin_pos.le harange.1
        simpa [abs_of_nonneg hnonneg] using harange.2
    ⟩ = a * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  have hRN' : RN a = a * (1 + δ) := by
    simpa [RN_normal, RN] using hRN

  have ha' : 0 < a := by
    exact lt_of_lt_of_le Fmin_pos harange.1

  have ha : a ≠ 0 := by
    exact ne_of_gt ha'

  have hufp_pos : ufp a > 0 := by
    have two_pos : (0 : ℝ ) < 2 := by
      norm_num
    unfold ufp
    by_cases h : a = 0
    · exfalso
      exact ha h
    · have : (0 : ℝ ) < (2 : ℝ ) ^ ((Int.floor (log2r |a|)) : ℝ ) := by
       exact Real.rpow_pos_of_pos two_pos _
      simpa [h] using this

  have ha0 : ufp a ≠ 0 := ne_of_gt hufp_pos

  have ho_up : 0 < 1 + u := by
   have h1 : (0 : ℝ) < 1 := by
    norm_num
   exact add_pos h1 hu_pos
  have hu : 1+u ≠ 0:= by
    exact ne_of_gt ho_up

  have huufp_pos : u*ufp a > 0 := by
    exact mul_pos hu_pos hufp_pos

  have hj : (1 + u) *ufp a > 0 := by
    exact mul_pos ho_up hufp_pos

  have hxabs : |a| = a := abs_of_pos ha'

  have hn : δ =  (RN a - a) / a := by
    simp [mul_add] at hRN'
    have h1 : RN a -a = a * δ := by
     simp [hRN']
    have h2 : (RN a -a) / a = δ := by
      apply (div_eq_iff ha).2
      simpa [mul_comm] using h1
    simpa using h2.symm

  have htri := lt_trichotomy |a| ((1 + u) * ufp a)
  rcases htri with h_lt | h_eq | h_gt

  ·
    have h_lt' : a< (1+u) *ufp a := by
      rw [hxabs] at h_lt
      exact h_lt

    have atai : RN a = ufp a := by
      rw [hur a h_lt']

    have Delta : δ =  (ufp a -a) / a := by
      rw [atai] at hn
      exact hn

    have keisan : |δ| = (a - ufp a) / a := by
     rw [Delta]
     have hnonpos : ufp a - a ≤ 0 := by
      calc
       ufp a - a ≤ a - a := by simp [hux a h_lt']
       _ = 0 := by ring

     have habs : |ufp a - a| = a - ufp a := by
      have : |ufp a - a| = -(ufp a - a) := by
       simp [abs_of_nonpos hnonpos]
      simpa [neg_sub] using this

     simp [abs_div]
     rw [habs]
     simp [abs_of_pos ha']


    have final : (a - ufp a) / a < u / (1 + u) := by
      have hsub : a - (1+u) * ufp a < 0 :=
        sub_neg.mpr h_lt'

      have hsub2 :a + u * a - (u + 1) * ufp a < u*a := by
        have h' : u * a + (a - (1+u) * ufp a) < u * a + 0 :=
         add_lt_add_left hsub (u * a)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

      have hsub3 : a + u * a < u * a + (u + 1) * ufp a :=
       (sub_lt_iff_lt_add).1 hsub2

      have hsub4 : (u + 1) * a < u * a + (u + 1) * ufp a := by
       simpa [add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hsub3

      have hsub5 :
        (u + 1) * a - (u + 1) * ufp a < u * a :=
        (sub_lt_iff_lt_add).2 hsub4


      have hsub6 : (a - ufp a) * (u + 1) < u * a := by
       have h : (u +1) * (a - ufp a) < u*a := by
        simpa [mul_sub] using hsub5
       simpa [mul_comm] using h

      have hfinal : a - ufp a < (u * a) / (u + 1) := by
       have hne : (u + 1) ≠ 0 := by
        exact ne_of_gt (by simpa [add_comm] using ho_up)
       have ho_up' :0< u +1 := by
        simpa [add_comm] using ho_up
       have h'' := mul_lt_mul_of_pos_right hsub6 (inv_pos.mpr ho_up')
       simpa [ mul_comm, mul_left_comm, mul_assoc,div_eq_mul_inv, hne ] using h''

      have hf : (a - ufp a) / a < u / (u + 1) := by
       have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha'

       have h1 : (a - ufp a) / a < ((u * a) / (u + 1)) / a :=
         div_lt_div_of_pos_right hfinal ha'
       simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ha_ne] using h1

      have realfinal : (a - ufp a) / a < u  / (1 + u) := by
        simpa [add_comm] using hf
      exact realfinal
    rw [← keisan] at final
    have saisyuu :  |δ| ≤ u / (1 + u) :=by
      exact le_of_lt final
    exact saisyuu


  ·
    have h_eq' : a = (1+u) * ufp a := by
      rw [hxabs] at h_eq
      exact h_eq

    have atai : RN a = ufp a := by
     have h : RN |a| = ufp a := by
      rw[h_eq,add_mul, one_mul,same2 a,hru a]
      exact h_eq'
     simpa [hxabs] using h

    rw [atai] at hn
    nth_rewrite 2 [h_eq'] at hn
    nth_rewrite 3 [h_eq'] at hn
    have keisan :  ufp a - (1 + u) * ufp a = - u *ufp a := by
      simp [add_mul]
    rw [keisan] at hn

    have hcancel :
      -u * ufp a / ((1 + u) * ufp a) = -u / (1 + u) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
      using mul_div_mul_left (-u) (1 + u) (ha0)
    rw [hcancel] at hn

    have huw_pos : - u / (1 + u) < 0 :=by
     have h : u / (1 + u) > 0 := by
      exact div_pos hu_pos ho_up
     have h' : -(u / (1 + u)) < 0 := by
       exact neg_lt_zero.mpr h
     simpa [neg_div] using h'
    have final : |δ| =  u / (1 + u) := by
      simpa [hn, neg_div, neg_neg] using (abs_of_neg huw_pos)

    have answer: |δ| ≤ u / (1 + u) := by
      simp [final]

    exact answer
  ·
    have h_gt' : (1 +u) * ufp a < a := by
      rw [hxabs] at h_gt
      exact h_gt

    have kateihennkei : RN a -a = δ * a := by
      simp [hRN', mul_add, mul_comm]

    have detekuru : |δ * a| ≤ u * ufp a := by
     have h : |RN a - a| ≤ u * ufp a := by
      have h1 : Fmin ≤ |a| ∧ |a| ≤ Rsup := by
        simpa [hxabs] using harange
      simpa [mul_comm,abs_sub_comm] using teiri1o a h1
     simpa [kateihennkei] using h

    have h1 :|δ| ≤ u * ufp a / a:= by
     have h : 0 < |a| := abs_pos.mpr (ne_of_gt ha')
     have h2 : |(δ * a)| / |a| ≤ (u * ufp a) / |a| :=
      div_le_div_of_nonneg_right detekuru (le_of_lt h)
     rw [abs_mul, hxabs] at h2
     simpa [ha] using h2

    have hden : (1 + u) * ufp a ≠ 0 := mul_ne_zero hu ha0

    have saigo  : |δ| ≤   u / (1 + u) :=
     have h : |δ| <  u / (1 + u) := by
      calc
      |δ| ≤ u * ufp a / a := by exact h1
       _  < u * ufp a / ((1 + u)* ufp a ):= by
        exact div_lt_div_of_pos_left huufp_pos hj h_gt'
       _  = u / (1 + u) := by
        field_simp [hden,hu]
        ring_nf
     le_of_lt h

    exact saigo

theorem teiri2_neg (a δ : ℝ)
    (hxrange : -Rsup ≤  a ∧ a ≤ -Fmin)
    (hRN : RN_normal ⟨a, by
      have ha_nonpos : a ≤ 0 := le_trans hxrange.2 (neg_nonpos.mpr Fmin_pos.le)
      constructor
      ·
        have h' : Fmin ≤ -a := by simpa using (neg_le_neg hxrange.2)
        simpa [abs_of_nonpos ha_nonpos] using h'
      ·
        have h' : -a ≤ Rsup := by simpa using (neg_le_neg hxrange.1)
        simpa [abs_of_nonpos ha_nonpos] using h'
    ⟩ = a * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  have hRN' : RN a = a * (1 + δ) := by
    simpa [RN_normal, RN] using hRN

  set b : ℝ := -a
  have hyrange : Fmin ≤ b ∧ b ≤ Rsup := by
    constructor
    ·
      have hle : a ≤ -Fmin := hxrange.2
      have : Fmin ≤ -a := by
        simpa using (neg_le_neg hle)
      simpa [b] using this
    ·
      have hlt : -Rsup ≤ a := hxrange.1
      have : -a ≤ Rsup := by
        simpa using (neg_le_neg hlt)
      simpa [b] using this
  have hRNy : RN b = b * (1 + δ) := by
    calc
      RN b = RN (-a) := by simp [b]
      _ = - RN a := by simpa using (RN_neg a)
      _ = - (a * (1 + δ)) := by simp [hRN']
      _ = (-a) * (1 + δ) := by simp [neg_mul]
      _ = b * (1 + δ) := by simp [b]

  exact teiri2_pos b δ hyrange hRNy


theorem teiri2_abs
  (a δ : ℝ)
  (hxrange : Fmin ≤ |a| ∧ |a| ≤  Rsup)
  (hRN : RN_normal ⟨a, by
      constructor
      · exact hxrange.1
      · exact hxrange.2
    ⟩ = a * (1 + δ)) :
  |δ| ≤ u / (1 + u) := by
  have hx0 : a ≠ 0 := by
    have : 0 < |a| := lt_of_lt_of_le
      (by
        have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
        simpa [Fmin] using (zpow_pos h2 (-1022 : ℤ)))
      hxrange.1
    exact abs_pos.mp this

  have hcases : a < 0 ∨ 0 < a := lt_or_gt_of_ne hx0
  cases hcases with
  | inl hxneg =>
      have hxrange_neg : -Rsup ≤ a ∧ a ≤ -Fmin := by
        constructor
        ·
          have : -|a| ≤ a := by simpa using (neg_abs_le a)
          exact le_trans (by simpa using (neg_le_neg hxrange.2)) this
        · have : Fmin ≤ -a := by
            simpa [abs_of_neg hxneg] using hxrange.1
          simpa using (neg_le_neg this)
      exact teiri2_neg a δ hxrange_neg hRN

  | inr hxpos =>
      have hxrange' : Fmin ≤ a ∧ a ≤ Rsup := by
        constructor
        · simpa [abs_of_pos hxpos] using hxrange.1
        · simpa [abs_of_pos hxpos] using hxrange.2
      exact teiri2_pos a δ hxrange' hRN


lemma ittanneo6(x: ℝ )(ha : Fmin ≤ |x| ∧  |x| ≤ Rsup): |RN_normal ⟨x, ha⟩ - x|≤ u * ufp x := by
 simpa [abs_sub_comm] using teiri1o x ha

axiom ceil_sub_half_int (n : ℤ) :
  Int.ceil ((n : ℝ) - (1/2 : ℝ)) = n

theorem teiri3o (x δ : ℝ )  (ha : Fmin ≤ |x| ∧  |x| ≤ Rsup)(hr : x = RN_normal ⟨x, ha⟩ * (1 + δ))
: |δ| ≤ u:= by
    -- まず ha から x ≠ 0 を作る（Fmin_pos は別途用意済みとして使う）
  have hx : x ≠ 0 := by
    have hFmin : 0 < Fmin := Fmin_pos
    have hxabs_pos : 0 < |x| := lt_of_lt_of_le hFmin ha.1
    intro hx0
    have : |x| = 0 := by simp [hx0]
    exact (ne_of_gt hxabs_pos) this

  have ne : |RN_normal ⟨x, ha⟩| ≠ 0 := by
    intro habs0
    have h0 : RN_normal ⟨x, ha⟩ = 0 := by
      exact (abs_eq_zero.mp habs0)
    have : x = 0 := by
      -- hr : x = RN_normal ... * (1+δ)
      simpa [h0] using hr
    exact hx this

  have hpo : |RN_normal ⟨x, ha⟩| > 0 := by
   have hge : 0 ≤ |RN_normal ⟨x, ha⟩| := abs_nonneg (RN_normal ⟨x, ha⟩)
   exact lt_of_le_of_ne hge (Ne.symm ne)

  have h' : |x - RN_normal ⟨x, ha⟩| =|δ * RN_normal ⟨x, ha⟩| := by
   have h : x - RN_normal ⟨x, ha⟩ = δ * RN_normal ⟨x, ha⟩ := by
    nth_rewrite 1 [hr]
    calc
     RN_normal ⟨x, ha⟩ * (1 + δ) - RN_normal ⟨x, ha⟩
      =  RN_normal ⟨x, ha⟩ + RN_normal ⟨x, ha⟩ * δ- RN_normal ⟨x, ha⟩ := by
              simp [mul_add]
      _   = RN_normal ⟨x, ha⟩ * δ := by ring
      _   = δ * RN_normal ⟨x, ha⟩ := by simp [mul_comm]
   rw [h]

  have teiri1o' (a:ℝ ):|x - RN_normal ⟨x, ha⟩| ≤ ufp x * u := by
   simpa [mul_comm] using teiri1o x ha
  have hf :|x - RN_normal ⟨x, ha⟩| ≤  |ufp x * u| := by
   calc
    |x - RN_normal ⟨x, ha⟩| ≤ ufp x * u  := by exact teiri1o' x
     _ ≤  |ufp x * u|:= by exact le_abs_self  (ufp x * u)

  have hl : |δ * RN_normal ⟨x, ha⟩| ≤  |ufp x * u| := by
   simpa [h'] using hf

  have hk : |δ| * |RN_normal ⟨x, ha⟩| ≤  |u| *|ufp x|  := by
    simpa [abs_mul,mul_comm] using hl

  have saisyuu : |δ| ≤ |u| * |ufp x| / |RN_normal ⟨x, ha⟩| := by
   have hne : |RN_normal ⟨x, ha⟩| ≠ 0 := by
     exact ne
   have hinv_nonneg : 0 ≤ (|RN_normal ⟨x, ha⟩|)⁻¹ := by
    exact inv_nonneg.2 (le_of_lt hpo)
   have h' :
      (|δ| * |RN_normal ⟨x, ha⟩|) * (|RN_normal ⟨x, ha⟩|)⁻¹
        ≤ (|u| * |ufp x|) * (|RN_normal ⟨x, ha⟩|)⁻¹ := by
    exact mul_le_mul_of_nonneg_right hk hinv_nonneg
   simp [div_eq_mul_inv, mul_assoc] at *
   simpa [mul_assoc, mul_left_comm, mul_comm, hne]
    using h'
  have hu : 0 < |u| := by
    simpa [abs_of_pos hu_pos] using hu_pos
  have hle : |u| * |ufp x| / |RN_normal ⟨x, ha⟩| ≤  |u|:= by
   have hden : |ufp x| /|RN_normal ⟨x, ha⟩| ≤  1 := by
    exact (div_le_one hpo).2 (by
    simpa [ge_iff_le] using (ittanneo8 x ha))
   calc
    |u| * |ufp x| / |RN_normal ⟨x, ha⟩|
      = |u| * (|ufp x| / |RN_normal ⟨x, ha⟩|):= by
        rw [mul_div_assoc, mul_comm]
    _ ≤  |u| * 1 := by
     have hu : 0 < |u| :=by simpa [abs_of_pos hu_pos] using hu_pos
     exact mul_le_mul_of_nonneg_left hden hup
    _ = |u| := by rw [mul_one]

  have saigo : |δ| ≤ |u| := by
    calc
      |δ| ≤ |u| * |ufp x| / |RN_normal ⟨x, ha⟩| := by exact saisyuu
        _ ≤  |u|:= by exact hle
  have saigo' : |u| = u := by
    simp[abs_of_pos hu_pos]

  have nice : |δ| ≤ u := by
    rw [saigo'] at saigo
    exact saigo
  exact nice

-- 最近接・中点下の基本評価
axiom ceil_sub_half_abs_le (t : ℝ) :
  |t - (Int.ceil (t - (1/2 : ℝ)) : ℝ)| ≤ (1/2 : ℝ)

noncomputable def RN_underflow' : {x : ℝ // Underflow x} → ℝ
| ⟨x, _hx⟩ =>
  let t : ℝ := |x| / Smin
  let k : ℤ := Int.ceil (t - (1/2 : ℝ))
  (k : ℝ) * Smin

-- underflow のとき、|x| は Smin の整数倍（格子点）になる、という性質
axiom underflow_abs_eq_zsmul_Smin (z : ℝ) (hz : Underflow z) :
  ∃ n : ℤ, |z| = (n : ℝ) * Smin

axiom sgn_mul_abs_real (z : ℝ) : sgn z * |z| = z


lemma teiri1_8 (x y : ℝ)(h : Underflow (x + y)) :RN_underflow ⟨x + y, h⟩ = x + y := by
  dsimp [RN_underflow]
  have hSmin : 0 < (2 : ℝ) ^ (-1074 : ℤ) := by
   have h2 : (0 : ℝ) < 2 := by norm_num
   have hpow : 0 < (2 : ℝ) ^ (1074 : ℕ) := by
    simp[pow_pos h2 1074]
   have h: 0 < ((2 : ℝ) ^ (1074 : ℕ))⁻¹ := inv_pos.mpr hpow
   exact h
  -- ① 最近接丸めの基本評価（半刻み以内）
  have hclose :
    |(|x + y| / Smin)
        - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)|
      ≤ (1/2 : ℝ) := by
    -- ceil(t - 1/2) の一般補題を使う
    simpa using
      ceil_sub_half_abs_le (|x + y| / Smin)

  -- ② スケールを戻す（Smin を掛ける）
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
      -- (|x+y|/Smin)*Smin = |x+y| を使って factor
      have hscale : (|x + y| / Smin) * Smin = |x + y| := by
        simp [div_eq_mul_inv, hSmin0]
      -- a*c - b*c = (a-b)*c
      calc
        |(|x + y| - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)|
            =
          |((|x + y| / Smin) * Smin
              - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)| := by
                simp [hscale]
        _ =
          |((|x + y| / Smin)
              - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin| := by
                -- sub_mul: (a-b)*c = a*c - b*c
                simpa using congrArg abs
                  ( (sub_mul (|x + y| / Smin)
                      (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) Smin).symm )
        -- ② スケールを戻す（Smin を掛ける）
    have hmul' :
        |(|x + y| / Smin
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ))| * Smin
          ≤ (1/2 : ℝ) * Smin :=
       mul_le_mul_of_nonneg_right hclose hSmin_nonneg

    -- |((...)*Smin)| に直す（abs_mul と |Smin|=Smin）
    have hmul :
        |((|x + y| / Smin)
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin|
          ≤ (1/2 : ℝ) * Smin := by
      -- 左辺: |a*Smin| = |a|*|Smin| = |a|*Smin
      simpa [abs_mul, abs_of_nonneg hSmin_nonneg, mul_assoc, mul_left_comm, mul_comm]
        using hmul'

    have hno1 :
        |((|x + y| / Smin)
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ)) * Smin|
          ≤ Smin / 2 := by
      -- 2⁻¹ * Smin = Smin / 2 を作ってから使う
      have hhalf : (2⁻¹ : ℝ) * Smin = Smin / 2 := by
        simp [div_eq_mul_inv, mul_comm]
      -- hmul の右辺を置換
      simpa [hhalf] using hmul

    have hno :
        |(|x + y|
            - (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin)|
          ≤ Smin / 2 := by
      -- scaled → orig なので hrewrite.symm
      rw [hrewrite.symm] at hno1
      exact hno1

    exact hno





  -- ③ underflow 仮定
  have hsmall : |x + y| < Fmin := h

  -- ④ underflow 領域では Smin 格子の一意性
  have hgrid :
    (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin = |x + y| := by
    -- まず underflow から格子点表示を取る（ここが本質）
    rcases underflow_abs_eq_zsmul_Smin (z := x + y) h with ⟨n, hn⟩

    -- hn : |x+y| = (n:ℝ)*Smin を使って ceil の中身を整数に落とす
    -- t = |x+y|/Smin = n が言えれば、ceil(n - 1/2) = n
    have hSn : Smin ≠ 0 := by exact (ne_of_gt Smin_pos)  -- Smin_pos : 0 < Smin

    have ht : |x + y| / Smin = (n : ℝ) := by
      -- hn を割り算に変形
      -- |x+y| = (n:ℝ)*Smin なので /Smin すると n
      calc
        |x + y| / Smin
            = ((n : ℝ) * Smin) / Smin := by simp [hn]
        _   = (n : ℝ) := by field_simp [hSn]

    -- ceil の評価：ceil((n:ℝ) - 1/2) = n
    have hceil : Int.ceil ((|x + y| / Smin) - (1/2 : ℝ)) = n := by
      -- ht で置き換えて、整数 n の ceil を計算
      -- `simp` で通ることが多い（ceil(↑n - 1/2)=n）
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
  -- まずゴールの左辺を h1 の左辺に合わせる（括弧付け替え）
   have hL :
      sgn (x + y) *
          (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
        = sgn (x + y) *
            ((Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin) := by
    simp [mul_assoc]
  -- これで一気に終わる
   calc
    sgn (x + y) *
        (Int.ceil (|x + y| / Smin - (1/2 : ℝ)) : ℝ) * Smin
        = sgn (x + y) * (↑⌈|x + y| / Smin - 1 / 2⌉ * Smin) := by
            -- ↑⌈...⌉ の表記ゆれを吸収しつつ括弧を揃える
            simp [mul_assoc]
    _ = sgn (x + y) * |x + y| := by
            -- ここで h1 を使う
            rw [hgrid]
    _ = x + y := by
            simpa using (sgn_mul_abs_real (x + y))
  exact hgrid'

theorem hanni (a b : ℝ) (hRsup : |a + b| ≤ Rsup) :
    Underflow (a + b) ∨ middle (a + b) := by
  by_cases hFmin : |a + b| < Fmin
  · left
    exact hFmin
  · right
    exact ⟨le_of_not_gt hFmin, hRsup⟩

theorem teiri1_9 (a b δ : ℝ) (hrange : |a + b| ≤ Rsup)
    (hRN : RN_nearest (a + b) hrange = (a + b) * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
