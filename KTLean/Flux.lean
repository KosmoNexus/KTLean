inductive Flux where
  | neg
  | zero
  | pos
deriving Repr, DecidableEq

#check Flux.neg
def fluxValue : Flux → Int
  | Flux.neg => -1
  | Flux.zero => 0
  | Flux.pos => 1

#eval fluxValue Flux.neg
#eval fluxValue Flux.zero
#eval fluxValue Flux.pos

def triadicCompletion : Flux → Flux → Flux
  | Flux.neg, Flux.zero => Flux.pos
  | Flux.zero, Flux.neg => Flux.pos
  | Flux.neg, Flux.pos => Flux.zero
  | Flux.pos, Flux.neg => Flux.zero
  | Flux.zero, Flux.pos => Flux.neg
  | Flux.pos, Flux.zero => Flux.neg
  | Flux.neg, Flux.neg => Flux.neg
  | Flux.zero, Flux.zero => Flux.zero
  | Flux.pos, Flux.pos => Flux.pos

#eval triadicCompletion Flux.neg Flux.zero
#eval triadicCompletion Flux.zero Flux.pos
#eval triadicCompletion Flux.neg Flux.pos
theorem triadic_neg_zero :
    triadicCompletion Flux.neg Flux.zero = Flux.pos := by
   rfl
  theorem triadic_zero_pos :
    triadicCompletion Flux.zero Flux.pos = Flux.neg := by
   rfl
   theorem closure_neg_zero :
  triadicCompletion Flux.neg Flux.zero = Flux.pos := by
    rfl

theorem closure_neg_pos :
  triadicCompletion Flux.neg Flux.pos = Flux.zero := by
  rfl

theorem closure_zero_pos :
  triadicCompletion Flux.zero Flux.pos = Flux.neg := by
  rfl
  theorem comm_neg_zero :
  triadicCompletion Flux.neg Flux.zero =
  triadicCompletion Flux.zero Flux.neg := by
   rfl

   theorem comm_neg_pos :
  triadicCompletion Flux.neg Flux.pos =
  triadicCompletion Flux.pos Flux.neg := by
    rfl
