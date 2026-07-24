import KahanProject.NoOverflow.Defs

/-!
# 丸め誤差の評価定理

`RN_normal` / `RN` による丸め誤差の限界を与える定理群。
-/

namespace FloatLibNoOverflow

/-- `Rsup` が登場しないぶん，前提は `Fmin ≤ |a|` の一つだけ。 -/
theorem teiri1o (a : ℝ) (ha : Fmin ≤ |a|) : |a - RN a| ≤ u * ufp a := by
  classical
  rw [RN_eq_normal a ha]
  have hc   : 0 < Δ a := Δ_pos a
  have hr0  : 0 ≤ rem_of a := rem_nonneg a
  have hrd  : rem_of a < Δ a := rem_lt_Δ a
  have hsplit : a = (K_of a : ℝ) * Δ a + rem_of a := decompose a
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
   have itiou : rem_of a ≤ Δ a / 2 := by
    simpa [div_eq_mul_inv] using hle
   have hRN_normal : RN_normal a ha = (K_of a : ℝ) * Δ a := by
    unfold RN_normal
    exact if_pos hle
   have hdist : |a - RN_normal a ha| = rem_of a := by
    rw [hRN_normal]; exact abs_k
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
   have hRG : RN_normal a ha = ((K_of a  + 1 : Int) : ℝ) * Δ a := by
    unfold RN_normal
    exact if_neg hle
   have hdistu : |a - RN_normal a ha|  = Δ a - rem_of a := by
    rw [hRG]; exact abs_up
   have small : Δ a - rem_of a ≤ Δ a / 2 := by
    have : Δ a * (1/2) < rem_of a := not_le.mp hle
    linarith
   have huufp : Δ a / 2 = u * ufp a := by
    calc
      Δ a / 2 = (1 / 2 : ℝ) * Δ a := by ring
      _ = (1 / 2 : ℝ) * ulp a := by simp [Δ]
      _ = u * ufp a := by simpa [mul_comm] using (same2 a).symm
   calc
    |a - RN_normal a ha| = Δ a - rem_of a := hdistu
    _ ≤ Δ a / 2 := small
    _ = u * ufp a := huufp

lemma teiri1o' (a : ℝ) (ha : Fmin ≤ |a|) : |a - RN a| ≤ ufp a * u := by
 simpa [mul_comm] using (teiri1o a ha)

axiom ittanneo3 (x : ℝ) (hx : x < (1 + u) * ufp x) (ha : Fmin ≤ |x|) : RN_normal x ha = ufp x
axiom ittanneo4 (x : ℝ) (hx : x < (1 + u) * ufp x) (ha : Fmin ≤ |x|) : ufp x < x
axiom ittanneo8 (x : ℝ) (ha : Fmin ≤ |x|) : |RN_normal x ha| ≥  |ufp x|

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


theorem teiri2_pos (a δ : ℝ) (harange : Fmin ≤ a)
    (hRN : RN a = a * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  have ha' : 0 < a := lt_of_lt_of_le Fmin_pos harange
  have ha : a ≠ 0 := ne_of_gt ha'
  have hxabs : |a| = a := abs_of_pos ha'
  have hRN' : RN a = a * (1 + δ) := hRN
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
  · have h_lt' : a< (1+u) *ufp a := by
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
        have h' : a - (1+u) * ufp a + u * a < 0 + u * a :=
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
  · have h_eq' : a = (1+u) * ufp a := by
      rw [hxabs] at h_eq
      exact h_eq
    have atai : RN a = ufp a := by
     have h : RN |a| = ufp a := by
      rw[h_eq,add_mul, one_mul,same2 a,hru a harange]
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
  · have h_gt' : (1 + u) * ufp a < a := by
      rw [hxabs] at h_gt
      exact h_gt
    have kateihennkei : RN a -a = δ * a := by
      simp [hRN', mul_add, mul_comm]
    have detekuru : |δ * a| ≤ u * ufp a := by
     have h : |RN a - a| ≤ u * ufp a := by
      have h1 : Fmin ≤ |a| := by
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
     le_of_lt h
    exact saigo

theorem teiri2_neg (a δ : ℝ)
    (hxrange : a ≤ -Fmin)
    (hRN : RN a = a * (1 + δ)) :
    |δ| ≤ u / (1 + u) := by
  have ha_nonpos : a ≤ 0 := le_trans hxrange (by linarith [Fmin_pos])
  set b : ℝ := -a
  have hyrange : Fmin ≤ b := by
    have h' : Fmin ≤ -a := by simpa using (neg_le_neg hxrange)
    simpa [b] using h'
  have hRNy : RN b = b * (1 + δ) := by
    calc
      RN b = RN (-a) := by simp [b]
      _ = - RN a := by simpa using (RN_neg a)
      _ = - (a * (1 + δ)) := by simp [hRN]
      _ = (-a) * (1 + δ) := by simp [neg_mul]
      _ = b * (1 + δ) := by simp [b]
  exact teiri2_pos b δ hyrange hRNy


theorem teiri2_abs
  (a δ : ℝ)
  (hxrange : Fmin ≤ |a|)
  (hRN : RN a = a * (1 + δ)) :
  |δ| ≤ u / (1 + u) := by
  have hx0 : a ≠ 0 := by
    have : 0 < |a| := lt_of_lt_of_le Fmin_pos hxrange
    exact abs_pos.mp this
  have hcases : a < 0 ∨ 0 < a := lt_or_gt_of_ne hx0
  cases hcases with
  | inl hxneg =>
      have hxrange_neg : a ≤ -Fmin := by
        have : Fmin ≤ -a := by
          simpa [abs_of_neg hxneg] using hxrange
        simpa using (neg_le_neg this)
      exact teiri2_neg a δ hxrange_neg hRN
  | inr hxpos =>
      have hxrange' : Fmin ≤ a := by
        simpa [abs_of_pos hxpos] using hxrange
      exact teiri2_pos a δ hxrange' hRN


lemma ittanneo6 (x : ℝ) (ha : Fmin ≤ |x|) : |RN_normal x ha - x|≤ u * ufp x := by
 rw [← RN_eq_normal x ha]
 simpa [abs_sub_comm] using teiri1o x ha

axiom ceil_sub_half_int (n : ℤ) :
  Int.ceil ((n : ℝ) - (1/2 : ℝ)) = n

theorem teiri3o (x δ : ℝ) (ha : Fmin ≤ |x|) (hr : x = RN x * (1 + δ))
: |δ| ≤ u:= by
  rw [RN_eq_normal x ha] at hr
  have hx : x ≠ 0 := by
    have hxabs_pos : 0 < |x| := lt_of_lt_of_le Fmin_pos ha
    intro hx0
    have : |x| = 0 := by simp [hx0]
    exact (ne_of_gt hxabs_pos) this
  have ne : |RN_normal x ha| ≠ 0 := by
    intro habs0
    have h0 : RN_normal x ha = 0 := by
      exact (abs_eq_zero.mp habs0)
    have : x = 0 := by
      simpa [h0] using hr
    exact hx this
  have hpo : |RN_normal x ha| > 0 := by
   have hge : 0 ≤ |RN_normal x ha| := abs_nonneg (RN_normal x ha)
   exact lt_of_le_of_ne hge (Ne.symm ne)
  have h' : |x - RN_normal x ha| =|δ * RN_normal x ha| := by
   have h : x - RN_normal x ha = δ * RN_normal x ha := by
    nth_rewrite 1 [hr]
    calc
     RN_normal x ha * (1 + δ) - RN_normal x ha
      =  RN_normal x ha + RN_normal x ha * δ- RN_normal x ha := by
              simp [mul_add]
      _   = RN_normal x ha * δ := by ring
      _   = δ * RN_normal x ha := by simp [mul_comm]
   rw [h]
  have hf :|x - RN_normal x ha| ≤  |ufp x * u| := by
   calc
    |x - RN_normal x ha| ≤ ufp x * u  := by
      rw [← RN_eq_normal x ha]; simpa [mul_comm] using teiri1o x ha
     _ ≤  |ufp x * u|:= by exact le_abs_self  (ufp x * u)
  have hl : |δ * RN_normal x ha| ≤  |ufp x * u| := by
   simpa [h'] using hf
  have hk : |δ| * |RN_normal x ha| ≤  |u| *|ufp x|  := by
    simpa [abs_mul,mul_comm] using hl
  have saisyuu : |δ| ≤ |u| * |ufp x| / |RN_normal x ha| := by
   have hne : |RN_normal x ha| ≠ 0 := by
     exact ne
   have hinv_nonneg : 0 ≤ (|RN_normal x ha|)⁻¹ := by
    exact inv_nonneg.2 (le_of_lt hpo)
   have h' :
      (|δ| * |RN_normal x ha|) * (|RN_normal x ha|)⁻¹
        ≤ (|u| * |ufp x|) * (|RN_normal x ha|)⁻¹ := by
    exact mul_le_mul_of_nonneg_right hk hinv_nonneg
   simp [div_eq_mul_inv, mul_assoc] at *
   simpa [mul_assoc, mul_left_comm, mul_comm, hne]
    using h'
  have hu : 0 < |u| := by
    simpa [abs_of_pos hu_pos] using hu_pos
  have hle : |u| * |ufp x| / |RN_normal x ha| ≤  |u|:= by
   have hden : |ufp x| /|RN_normal x ha| ≤  1 := by
    exact (div_le_one hpo).2 (by
    simpa [ge_iff_le] using (ittanneo8 x ha))
   calc
    |u| * |ufp x| / |RN_normal x ha|
      = |u| * (|ufp x| / |RN_normal x ha|):= by
        rw [mul_div_assoc, mul_comm]
    _ ≤  |u| * 1 := by
     have hu : 0 < |u| :=by simpa [abs_of_pos hu_pos] using hu_pos
     exact mul_le_mul_of_nonneg_left hden hup
    _ = |u| := by rw [mul_one]
  have saigo : |δ| ≤ |u| := by
    calc
      |δ| ≤ |u| * |ufp x| / |RN_normal x ha| := by exact saisyuu
        _ ≤  |u|:= by exact hle
  have saigo' : |u| = u := by
    simp[abs_of_pos hu_pos]
  have nice : |δ| ≤ u := by
    rw [saigo'] at saigo
    exact saigo
  exact nice

end FloatLibNoOverflow
