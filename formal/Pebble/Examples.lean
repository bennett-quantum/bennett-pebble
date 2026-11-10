import Pebble.Checker

/-! Small executable regression examples: all four rules, full capacity boundary,
a forbidden residue overwrite, and an attempt to erase the last token. -/
namespace Pebble.Chain.Examples

def play : List (Move 2 2) :=
  [.dup 0 1 0, .adv 1 0, .ret 1 0, .undup 0 1 0, .adv 0 0, .adv 0 1]

example : (checkFrom 1 1 3 7 2 (start (T := 2) (P := 2) 0) play).map
    (fun q => (q.peak, q.cost)) = some (3,32) := by decide

example : accepts 1 1 3 7 2 0 play = true := by decide
example : accepts 1 1 2 7 2 0 play = false := by decide

example : accepts 1 1 3 7 2 0
    ([.dup 0 1 0, .adv 0 0, .adv 1 0] : List (Move 2 2)) = false := by decide

example : accepts 1 1 3 7 2 0 ([.undup 0 0 0] : List (Move 2 2)) = false := by decide

example : (replay (start 0) play).token 0 = some 2 := by decide

end Pebble.Chain.Examples
