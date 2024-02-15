import LeanChecker.Pattern

inductive Proof where
    | instantiate(schema: Proof)(subst: List (Nat × Pattern)) : Proof /-- TODO: We need simultanous substitutions here --/
    | prop1 : Proof
    | prop2 : Proof
    | modus_ponens(left: Proof)(right: Proof) : Proof
deriving DecidableEq, Repr

def inst := Proof.instantiate
def prop1 := Proof.prop1
def prop2 := Proof.prop2
def mp := Proof.modus_ponens

def prop1_concl := (implies ph0 (implies ph1 ph0))
def prop2_concl := (implies (implies ph0 (implies ph1 ph2)) (implies (implies ph0  ph1) (implies ph0 ph2)))

@[simp]
def mp_conclusion(hyp1: Option Pattern)(hyp2: Option Pattern) : Option Pattern := match (hyp1, hyp2) with
          | (_, none) => none
          | (none, _) => none
          | (some concl_1, some (Pattern.implies concl_2_left concl_2_right)) =>
                if concl_2_left = concl_1 then concl_2_right else none
          | (some _, some _) => none

@[simp]
def Proof.conclusion(pi: Proof) : Option Pattern :=
    match pi with
      | Proof.instantiate pi' subst' =>
        match pi'.conclusion with
          | none => none
          | some concl' => (concl'.instantiate subst')
      | Proof.prop1 => prop1_concl
      | Proof.prop2 => prop2_concl
      | Proof.modus_ponens pi1 pi2 => mp_conclusion pi2.conclusion  pi1.conclusion


def imp_refl: Proof :=
    (mp (mp (inst prop2 [(1, ph0_implies_ph0), (2, ph0)])
            (inst prop1 [(1, ph0_implies_ph0)])
        )
        (inst prop1 [(1, ph0)])
    )

theorem test_imp_refl : imp_refl.conclusion = some ph0_implies_ph0 := by rfl


theorem instantiate_commutes_with_implies(left: Pattern)(right: Pattern)(subst: List (Nat × Pattern))
    : ((Pattern.implies left right).instantiate subst) = (Pattern.implies (left.instantiate subst) (right.instantiate subst))
    := by rw [Pattern.instantiate]
theorem instantiate_commutes_with_mp_happy(left: Proof)(right: Proof)(subst: List (Nat × Pattern))
    : left.conclusion = (Pattern.implies phi psi)
   -> right.conclusion = some phi
   -> (Proof.instantiate (Proof.modus_ponens left right) subst).conclusion
    = (Proof.modus_ponens (Proof.instantiate left subst) (Proof.instantiate right subst)).conclusion
    := by {
    intro h_left_conc
    intro h_right_conc
    simp [  mp_conclusion, h_right_conc, h_left_conc, instantiate_commutes_with_implies]
    }
theorem instantiate_commutes_with_mp(left: Proof)(right: Proof)(subst: List (Nat × Pattern))
    : (Proof.instantiate (Proof.modus_ponens left right) subst).conclusion
    = (Proof.modus_ponens (Proof.instantiate left subst) (Proof.instantiate right subst)).conclusion
    := by {
        generalize h_left_conc: left.conclusion = lconc
        generalize h_right_conc: right.conclusion = rconc
        match lconc with
        | none  => simp [h_left_conc]
        | some (Pattern.implies phi psi)  => {
            match rconc with
            | none => simp [h_left_conc, h_right_conc]
            | some phi' => sorry --- Need to do case analysis on if `phi == phi'`
                                 --- In the first case, apply instantiate_commutes_with_mp_happy
                                 --- in the second, the proof should reduce to `none = none`
        }
        | some _  => sorry -- This is strictly more general than the previous case
                           -- However, we want to assume that it is *not* an implication
    }
