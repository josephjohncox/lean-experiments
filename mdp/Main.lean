import Mdp

open Examples

def showState (s : Fin 2 × Fin 2) : String :=
  s!"({s.1.val}, {s.2.val})"

def fin0 : Fin 2 := ⟨0, by decide⟩
def fin1 : Fin 2 := ⟨1, by decide⟩

def gridStates : List (Fin 2 × Fin 2) :=
  [(fin0, fin0), (fin0, fin1), (fin1, fin0), (fin1, fin1)]

def main : IO Unit := do
  let n := 5
  let v := gridPolicyEvalDetRat n
  IO.println s!"Deterministic grid policy eval after {n} iterations"
  for s in gridStates do
    IO.println ("  " ++ showState s ++ ": " ++ toString (v s))
