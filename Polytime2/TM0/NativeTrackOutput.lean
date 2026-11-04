import Polytime2.TM0.BlockDecoder
import Polytime2.TM0.TrackOutput
import Polytime2.TM0.Tracks

/-! # Native-word extraction after fixed-block decoding

The block decoder leaves actual native symbols on its output tape. Extract
that tape through the shared nonblank-symbol pass, erase all simulator rows,
and restore the physical head. No count or padding is emitted.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.NativeTrackOutput

open MultiTape

variable {Letter : Type}

private def format (outputRow : Letter → Tracks.Row (BlockDecoder.Alphabet (Letter := Letter)))
    (_ : Unit) (symbol : Option Letter) : Unit × Tracks.Row (BlockDecoder.Alphabet (Letter := Letter)) :=
  ((), match symbol with | none => Tracks.blank | some letter => outputRow letter)

/-- Extract native symbols directly, with their fixed external row embedding. -/
noncomputable def machine (outputRow : Letter → Tracks.Row (BlockDecoder.Alphabet (Letter := Letter))) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row (BlockDecoder.Alphabet (Letter := Letter)))) (Fin 8 × Unit) := by
  classical
  exact TrackOutput.Symbolic.machine (Source := Option Letter) (fun row => row.2 true) (fun row => row.1 true) (format outputRow)

private theorem native_word (outputRow : Letter → Tracks.Row (BlockDecoder.Alphabet (Letter := Letter)))
    (letters : List Letter) :
    TrackOutput.Symbolic.word (format outputRow) () (letters.map some) =
      letters.map (Sweep.row ∘ outputRow) := by
  induction letters with
  | nil => rfl
  | cons letter letters hypothesis => simp only [List.map_cons, TrackOutput.Symbolic.word, format, hypothesis]; rfl

/-- Physical native-word output has the same linear extraction bound as
binary output, including an empty word and complete simulator-frame erasure. -/
theorem steps (outputRow : Letter → Tracks.Row (BlockDecoder.Alphabet (Letter := Letter)))
    (letters : List Letter) (rows : List (Tracks.Row (BlockDecoder.Alphabet (Letter := Letter))))
    (represented : Tracks.RepresentsAt true rows (BlockDecoder.wordTape [] (letters.map some))) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧
      Steps (machine outputRow) ticks
        ((0, ()), Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        ((7, ()), Sweep.tape [] (letters.map (Sweep.row ∘ outputRow))) := by
  classical
  obtain ⟨before, current, after, split, unmarked, marked, _, tapeEq⟩ := represented
  have payload : Turing.ListBlank.mk ((current :: after).map (fun row => row.1 true)) =
      Turing.ListBlank.mk (letters.map some) := by
    have right := congrArg (fun source : Turing.Tape (Option Letter) => source.right.cons source.head) tapeEq
    have reconstruct (contents : List (Option Letter)) :
        Turing.ListBlank.mk (contents.headI :: contents.tail) = Turing.ListBlank.mk contents := by
      cases contents with
      | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
      | cons => rfl
    symm
    simpa only [BlockDecoder.wordTape, Turing.Tape.mk'_head, Turing.Tape.mk'_right,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk, reconstruct,
      List.map_cons] using right
  have nonblank : ∀ symbol ∈ letters.map some, symbol ≠ (default : Option Letter) := by
    intro symbol member
    obtain ⟨letter, _, rfl⟩ := List.mem_map.mp member
    exact Option.some_ne_none letter
  subst rows
  obtain ⟨ticks, bound, trace⟩ := TrackOutput.Symbolic.steps (fun row => row.2 true) (fun row => row.1 true)
    (format outputRow) () before current after (letters.map some) unmarked marked nonblank payload
  refine ⟨ticks, bound, ?_⟩
  have memory : TrackOutput.Symbolic.finalMemory (format outputRow) () (letters.map some) = () := Subsingleton.elim _ _
  simpa only [machine, native_word, memory] using trace

end Polytime2.NativeTrackOutput
