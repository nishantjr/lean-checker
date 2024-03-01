inductive Pattern where
    | metavar(id: Nat) : Pattern
    | bot : Pattern --- TODO: Replace with $mu X. X$ Not needed by $phi -> phi$
    | implies(left: Pattern)(right: Pattern) : Pattern
deriving DecidableEq, Repr

def implies := Pattern.implies

def ph0 : Pattern := (Pattern.metavar 0)
def ph1 : Pattern := (Pattern.metavar 1)
def ph2 : Pattern := (Pattern.metavar 2)
def ph0_implies_ph0 : Pattern := (implies ph0 ph0)

def subst_from_pairs(pairs: List (Nat × Pattern))(n: Nat): Option Pattern :=
    match pairs with
        | [] => none
        | (x, p) :: xs => if x = n then p else (subst_from_pairs xs n)

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
def Option.get_or_default (opt: Option α) (default: α) : α :=
  match opt with
  | some x => x
  | none => default

def Pattern.instantiate(p: Pattern)(subst: Nat -> Option Pattern) : Pattern :=
    match p with
      | Pattern.metavar id' =>  (subst id').get_or_default p
      | Pattern.bot => Pattern.bot
      | Pattern.implies left right => Pattern.implies (left.instantiate subst) (right.instantiate subst)

example : (Pattern.instantiate Pattern.bot  $ subst_from_pairs [(0, ph0)]) = Pattern.bot := by rfl
example : (Pattern.instantiate ph0 $ subst_from_pairs [(0, ph0)]) = ph0 := by rfl
example : (Pattern.instantiate ph1 $ subst_from_pairs [(0, ph0)]) = ph1 := by rfl
example : (Pattern.instantiate ph0_implies_ph0 $ subst_from_pairs [(0, ph1)]) = (implies ph1 ph1) := by rfl
example : (Pattern.instantiate ph0_implies_ph0 $ subst_from_pairs [(0, ph0_implies_ph0)]) = (implies ph0_implies_ph0 ph0_implies_ph0) := by rfl
