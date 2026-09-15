import RISCVarray.TileRiscV_simple
open Sparkle.Core.Signal

/-- Signal 版（Signal.loop + Signal.memory）と純粋参照モデルを全サイクル比較 -/
def main : IO Unit := do
  let n := 24
  let sig := (fun g => summary g) <$> tileArray cfg12 prog12
  let hw  := sig.sample n
  let ref := (simPure cfg12 prog12 n).map summary
  IO.println s!"Signal.memory版 最終: {hw.getLast?}"
  IO.println s!"参照モデル     最終: {ref.getLast?}"
  let diffs := (List.range n).filter fun t => hw[t]? != ref[t]?
  if diffs.isEmpty then IO.println s!"PASS: {n} サイクル全一致"
  else do
    IO.println s!"FAIL: 不一致サイクル {diffs}"
    IO.Process.exit 1
  -- 4×4 / 1024 語メモリの規模でも回ることの確認
  let top := tileArrayTop.sample 5
  IO.println s!"4x4 top (imem=0 → halt): {top.map (·.toList.all id)}"
