import LeanChecker.Pattern
import Mathlib.Tactic.Contrapose

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
          | (none, _) => none
          | (_, none) => none
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

@[simp]
def Proof.wf(p: Proof) : Bool := p.conclusion != none


def Proof.is_instantiated_schema(p: Proof) : Bool :=
    match p with
    | Proof.prop1 => True
    | Proof.prop2 => True
    | (Proof.instantiate subp _) => is_instantiated_schema subp
    | (Proof.modus_ponens _ _) => False

def Pattern.is_concrete(p: Pattern) : Bool :=
    match p with
      | Pattern.metavar _ => False
      | Pattern.bot => True
      | Pattern.implies left right => left.is_concrete ∧ right.is_concrete

@[simp]
def Proof.is_pre_instantiated(p: Proof) : Bool :=
    match p with
    | (Proof.modus_ponens p1 p2) => p1.is_pre_instantiated ∧ p2.is_pre_instantiated
    | _  => p.is_instantiated_schema ∧ p.conclusion.isSome

def mp_wf_left : (Proof.modus_ponens l r).wf -> l.wf ∧ r.wf :=
    by {
        generalize h_left_conc: l.conclusion = lconc
        generalize h_right_conc: r.conclusion = rconc
        match rconc with
        | none  => simp [h_left_conc, h_right_conc]
        | some (Pattern.implies phi psi)  => {
            match lconc with
            | none => simp [h_left_conc, h_right_conc]

            | some phi' => { apply @Classical.byCases (phi = phi')
                             . intro
                               simp [h_left_conc, h_right_conc]
                             . intro
                               simp[h_left_conc, h_right_conc]
                           }
        }
        | some Pattern.bot  => cases lconc <;> simp[h_left_conc, h_right_conc]
        | some (Pattern.metavar _)  => cases lconc <;> simp[h_left_conc, h_right_conc]
    }

theorem instantiate_commutes_with_implies(left: Pattern)(right: Pattern)(subst: List (Nat × Pattern))
    : ((Pattern.implies left right).instantiate subst) = (Pattern.implies (left.instantiate subst) (right.instantiate subst))
    := by rw [Pattern.instantiate]

theorem instantiate_commutes_with_mp(left: Proof)(right: Proof)(subst: List (Nat × Pattern))
     (h_left_conc : left.conclusion = (Pattern.implies phi psi))
     (h_right_conc : right.conclusion = some phi):
      (Proof.instantiate (Proof.modus_ponens left right) subst).conclusion
    = (Proof.modus_ponens (Proof.instantiate left subst) (Proof.instantiate right subst)).conclusion
    := by {
    simp [  mp_conclusion, h_right_conc, h_left_conc, instantiate_commutes_with_implies]
    }

def merge_instantiation(inner: List (Nat × Pattern))(outer: List (Nat × Pattern)) : List (Nat × Pattern) :=
    sorry

def push_instantiations(p: Proof) : Proof :=
    match p with
    | Proof.prop1 => p
    | Proof.prop2 => p
    | (Proof.instantiate Proof.prop1 subst)  => p
    | (Proof.instantiate Proof.prop2 subst)  => p
    | (Proof.modus_ponens l r) => (Proof.modus_ponens (push_instantiations l) (push_instantiations r))
    | (Proof.instantiate (Proof.modus_ponens l' r') subst)
         => (Proof.modus_ponens (push_instantiations (Proof.instantiate l' subst))
                                (push_instantiations (Proof.instantiate r' subst)))
    | (Proof.instantiate (Proof.instantiate p' subst_inner) subst_outer)
         => (Proof.instantiate p'  (merge_instantiation subst_inner subst_outer))
