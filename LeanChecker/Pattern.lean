
inductive Pattern where
    | metavar(id: Nat) : Pattern
    | bot : Pattern
    | implies(left: Pattern)(right: Pattern) : Pattern

def ph0 : Pattern := (Pattern.metavar 0)
def ph0_implies_ph0 : Pattern := (Pattern.implies ph0 ph0)

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
