import SignedSearch

namespace Case24992
open TwoLit100268

def positives : List (Fin 6 × Fin 6) := [(0, 0), (0, 1), (0, 2), (1, 1), (2, 2), (3, 3), (4, 4)]
def negatives : List (Fin 6 × Fin 6) := [(0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5), (5, 5)]

def sample (s : Bool) (i : Fin 110) : Fin 6 × Fin 6 :=
  if s then positives.getD ((i.val % 98)/14) (0,0) else negatives.getD ((i.val % 98)%14) (0,0)

def xs : List Sig := [(0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x0, 0x2913a44e913a44e913a44e913a44)]

theorem rows_ok : ∀ s i, input (sample s i).1 (sample s i).2 = xs.map (bit s i) := by decide +kernel
theorem labels_ok : ∀ s i, maskLabel 270549127 (sample s i).1 (sample s i).2 = s := by decide +kernel
theorem xs_nodup : xs.Nodup := by decide +kernel
theorem all_essential : xs.all (fun a => unionSep true (xs.erase a) != top) = true := by decide +kernel
theorem nonmono : unionSep false xs ≠ top := by decide +kernel

theorem no_nine_of_profiles (one : Impossible 9 1 xs) (two : Impossible 9 2 xs)
    (three : Impossible 9 3 xs) (four : Impossible 9 4 xs) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (270549127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  apply impossible_for_six (budget := 9) rows_ok labels_ok xs_nodup all_essential nonmono
  intro t lo hi
  change 6 + t ≤ 9 + 1 at hi
  have ht : t ≤ 4 := by omega
  interval_cases t
  · exact one
  · exact two
  · exact three
  · exact four

end Case24992
