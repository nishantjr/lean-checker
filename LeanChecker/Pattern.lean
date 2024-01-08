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


inductive Proof where
    | instantiate(schema: Proof)(subst: List (Nat × Pattern)) : Proof /-- TODO: We need simultanous substitutions here --/
    | prop1 : Proof
    | prop2 : Proof
    | modus_ponens(left: Proof)(right: Proof) : Proof

def inst := Proof.instantiate
def prop1 := Proof.prop1
def prop2 := Proof.prop2
def mp := Proof.modus_ponens

def Proof.conclusion(pi: Proof) : Option Pattern :=
    match pi with
      | Proof.instantiate pi' subst' =>
        match pi'.conclusion with
          | none => none
          | some concl' => (concl'.instantiate subst')
      | Proof.prop1 => (implies ph0 (implies ph1 ph0))
      | Proof.prop2 => (implies (implies ph0 (implies ph1 ph2)) (implies (implies ph0  ph1) (implies ph0 ph2)))
      | Proof.modus_ponens pi1 pi2 =>
        match (pi2.conclusion, pi1.conclusion) with
          | (_, none) => none
          | (none, _) => none
          | (some concl_1, some (Pattern.implies concl_2_left concl_2_right)) =>
                if concl_2_left = concl_1 then concl_2_right else none
          | (some _, some _) => none

def imp_refl: Proof :=
    (mp (mp (inst prop2 [(1, ph0_implies_ph0), (2, ph0)])
            (inst prop1 [(1, ph0_implies_ph0)])
        )
        (inst prop1 [(1, ph0)])
    )

theorem test_imp_refl : imp_refl.conclusion = some ph0_implies_ph0 := by rfl
