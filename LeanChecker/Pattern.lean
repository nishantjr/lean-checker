
inductive Pattern where
    | metavar(id: Nat) : Pattern
    | bot : Pattern
    | implies(left: Pattern)(right: Pattern) : Pattern

def implies := Pattern.implies

def ph0 : Pattern := (Pattern.metavar 0)
def ph1 : Pattern := (Pattern.metavar 1)
def ph0_implies_ph0 : Pattern := (implies ph0 ph0)

def Pattern.instantiate(p: Pattern)(id: Nat)(plug: Pattern) : Pattern :=
    match p with
      | Pattern.metavar id' => if id' = id then plug else p
      | Pattern.bot => Pattern.bot
      | Pattern.implies left right => Pattern.implies (instantiate left id plug) (instantiate right id plug)

theorem test_inst_1 :
    (Pattern.instantiate Pattern.bot 0 ph0) = Pattern.bot := by rfl
theorem test_inst_2 :
    (Pattern.instantiate ph0 0 ph0) = ph0 := by rfl
theorem test_inst_3 :
    (Pattern.instantiate ph1 0 ph0) = ph1 := by rfl
theorem test_inst_4 :
    (Pattern.instantiate ph0_implies_ph0 0 ph1) = (implies ph1 ph1) := by rfl
theorem test_inst_5 :
    (Pattern.instantiate ph0_implies_ph0 0 ph0_implies_ph0) = (implies ph0_implies_ph0 ph0_implies_ph0) := by rfl


inductive Proof where
    | instantiate(schema: Proof)(id: Nat)(value: Pattern) : Proof /-- TODO: We need simultanous substitutions here --/
    | prop1 : Proof
    | prop2 : Proof
    | modus_ponens(left: Proof)(right: Proof) : Proof

def inst := Proof.instantiate
def prop1 := Proof.prop1
def prop2 := Proof.prop2
def mp := Proof.modus_ponens

def imp_refl: Proof :=
    (mp (mp (inst (inst Proof.prop2 1 ph0_implies_ph0)
                                    2 ph0)
            (inst Proof.prop1 1 ph0_implies_ph0)
        )
        prop1
    )
