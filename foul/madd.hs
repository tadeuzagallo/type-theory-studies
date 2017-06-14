data Nat = Ze|Su Nat
add :: Nat->Nat->Nat
add (Ze) m = m
add (Su n) m = (Su (add n m))