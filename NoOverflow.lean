import KahanProject.NoOverflow.Defs
import KahanProject.NoOverflow.Rounding
import KahanProject.NoOverflow.Underflow
import KahanProject.NoOverflow.Sterbenz
import KahanProject.NoOverflow.Kahan

/-!
# `NoOverflow` 索引ファイル

`Rsup`（オーバーフロー上限）を持ち回らない設計一式をまとめて読み込む。
他のファイルからはこれ一つを `import KahanProject.NoOverflow` するだけで、
`FloatLibNoOverflow` 名前空間の全ての定義・定理が使えるようになる。
-/
