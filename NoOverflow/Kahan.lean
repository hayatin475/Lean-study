import KahanProject.NoOverflow.Defs

/-!
# Kahan の補正総和

`x : ℕ → ℝ` の先頭 `n+1` 項を Kahan の補正付きで足し合わせる。
`kahanStep x n = (s, c)` の `s` が現在までの総和，`c` が補正項（＝「借用書」）。
各ステップは直前の `(s, c)` を**値として**受け取るだけなので，
丸めが展開されて何重にもネストすることはない
（唯一のネストは `fl (fl (t - s) - y)` というアルゴリズム自体が持つ 1 段だけ）。

各ステップでは `|·| < Fmin` かどうかで `RN_underflow` / `RN_normal` を明示的に
使い分け，かつ `RN_normal` / `RN_underflow` が要求する証明（`dif` の `h`）も
正しく渡している。`RN` を経由しないので，証明を渡し忘れて誤った領域の
丸めを使ってしまう心配が型レベルでなくなる。
-/

namespace FloatLibNoOverflow

noncomputable def kahanStep (x : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (x 0, 0)
  | (n + 1) =>
      let s := (kahanStep x n).1
      let c := (kahanStep x n).2
      -- y = fl(x_{n+1} - c)
      let ydiff := x (n + 1) - c
      let y := if h : |ydiff| < Fmin then RN_underflow ydiff h else RN_normal ydiff (not_lt.mp h)
      -- t = fl(s + y)
      let tsum := s + y
      let t := if h : |tsum| < Fmin then RN_underflow tsum h else RN_normal tsum (not_lt.mp h)
      -- c' = fl(fl(t - s) - y)（内側の丸めと外側の丸め，それぞれ独立に場合分けする）
      let inner := t - s
      let innerR :=
        if h : |inner| < Fmin then RN_underflow inner h else RN_normal inner (not_lt.mp h)
      let outer := innerR - y
      let outerR :=
        if h : |outer| < Fmin then RN_underflow outer h else RN_normal outer (not_lt.mp h)
      (t, outerR)

/-- Kahan 補正総和の値（`x 0 + ⋯ + x n` の丸め込み総和）。 -/
noncomputable def kahanS (x : ℕ → ℝ) (n : ℕ) : ℝ := (kahanStep x n).1

/-- Kahan 補正総和の補正項。 -/
noncomputable def kahanC (x : ℕ → ℝ) (n : ℕ) : ℝ := (kahanStep x n).2

end FloatLibNoOverflow
