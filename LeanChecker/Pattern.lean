
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

def Pattern.instantiate(p: Pattern)(subst: List (Nat × Pattern)) : Pattern :=
    match p with
      | Pattern.metavar id' =>
            match subst with
             | [] => p
             | (id, plug) :: rest
                => if id' = id then plug else p.instantiate rest
      | Pattern.bot => Pattern.bot
      | Pattern.implies left right => Pattern.implies (left.instantiate subst) (right.instantiate subst)

theorem test_inst_1 :
    (Pattern.instantiate Pattern.bot [(0, ph0)]) = Pattern.bot := by rfl
theorem test_inst_2 :
    (Pattern.instantiate ph0 [(0, ph0)]) = ph0 := by rfl
theorem test_inst_3 :
    (Pattern.instantiate ph1 [(0, ph0)]) = ph1 := by rfl
theorem test_inst_4 :
    (Pattern.instantiate ph0_implies_ph0 [(0, ph1)]) = (implies ph1 ph1) := by rfl
theorem test_inst_5 :
    (Pattern.instantiate ph0_implies_ph0 [(0, ph0_implies_ph0)]) = (implies ph0_implies_ph0 ph0_implies_ph0) := by rfl



