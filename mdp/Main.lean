import Mdp

open Examples

def showState (s : Fin 2 × Fin 2) : String :=
  s!"({s.1.val}, {s.2.val})"

def fin0 : Fin 2 := ⟨0, by decide⟩
def fin1 : Fin 2 := ⟨1, by decide⟩

def gridStates : List (Fin 2 × Fin 2) :=
  [(fin0, fin0), (fin0, fin1), (fin1, fin0), (fin1, fin1)]

def finA0 : Fin 4 := ⟨0, by decide⟩
def finA1 : Fin 4 := ⟨1, by decide⟩
def finA2 : Fin 4 := ⟨2, by decide⟩
def finA3 : Fin 4 := ⟨3, by decide⟩

def gridActions : List (Fin 4) :=
  [finA0, finA1, finA2, finA3]

def main : IO Unit := do
  let n := 5
  let v := gridPolicyEvalDetRat n
  IO.println s!"Deterministic grid policy eval after {n} iterations"
  for s in gridStates do
    IO.println ("  " ++ showState s ++ ": " ++ toString (v s))
  let q := gridQIterDetRat n
  IO.println s!"Deterministic grid Q-iteration after {n} iterations"
  for s in gridStates do
    IO.println ("  " ++ showState s)
    for a in gridActions do
      IO.println ("    a" ++ toString a.val ++ ": " ++ toString (q s a))
