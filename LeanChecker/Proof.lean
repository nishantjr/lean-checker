import LeanChecker.Pattern
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Propose
import Mathlib.Tactic.GCongr

inductive Proof where
    | instantiate(schema: Proof)(subst: Nat -> Option Pattern) : Proof /-- TODO: We need simultanous substitutions here --/
    | prop1 : Proof
    | prop2 : Proof
    | modus_ponens(left: Proof)(right: Proof) : Proof

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
          | (some (Pattern.implies concl_2_left concl_2_right), some concl_1) =>
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
      | Proof.modus_ponens pi1 pi2 => mp_conclusion pi1.conclusion  pi2.conclusion

---

def imp_refl: Proof :=
    (mp (inst (mp (inst prop2 $ subst_from_pairs [(2, ph0)])
                  prop1)
              $ subst_from_pairs [(1, ph0_implies_ph0)]
        )
        (inst prop1 $ subst_from_pairs [(1, ph0)])
    )

example : imp_refl.conclusion = some ph0_implies_ph0 := by rfl

---

def merge_instantiation(inner: Nat -> Option Pattern)(outer: Nat -> Option Pattern)
 : Nat -> Option Pattern :=
    fun(n) => match inner n with
    | none => outer n
    | some p => some $ p.instantiate outer

@[simp]
def push_instantiations(p: Proof) : Proof :=
    match p with
    | Proof.prop1 => p
    | Proof.prop2 => p
    | (Proof.modus_ponens l r) => (Proof.modus_ponens (push_instantiations l) (push_instantiations r))
    | (Proof.instantiate Proof.prop1 _)  => p
    | (Proof.instantiate Proof.prop2 _)  => p
    | (Proof.instantiate (Proof.modus_ponens l' r') subst)
         => (Proof.modus_ponens (push_instantiations (Proof.instantiate l' subst))
                                (push_instantiations (Proof.instantiate r' subst)))
    | (Proof.instantiate (Proof.instantiate p' subst_inner) subst_outer)
         => (push_instantiations (Proof.instantiate p'  (merge_instantiation subst_inner subst_outer)))


example : (push_instantiations imp_refl).conclusion = some ph0_implies_ph0 := by rfl

@[simp]
def Proof.wf(p: Proof) : Prop := ∃ phi, p.conclusion = some phi

theorem mp_wf_prime : (Proof.modus_ponens l r).conclusion = some psi
                         -> ∃ phi, r.conclusion = some phi ∧ l.conclusion = (some $ Pattern.implies phi psi) :=
by
   simp
   split
   case h_1 => simp
   case h_2 => simp
   case h_3 concl_2_left concl_2_right concl_1 heq
    => split
       case inl h => intro a
                     use concl_2_left
                     simp at heq; simp at a
                     exact ⟨ by simp [heq.2, h], by simp[heq, <- a]⟩
       case inr => simp
   case h_4 => simp

theorem mp_wf : (Proof.modus_ponens l r).wf -> l.wf ∧ r.wf :=
    by {
        generalize h_left_conc: l.conclusion = lconc
        generalize h_right_conc: r.conclusion = rconc
        match lconc with
        | none  => simp [h_left_conc, h_right_conc]
        | some (Pattern.implies phi psi)  => {
            match rconc with
            | none => simp [h_left_conc, h_right_conc]

            | some phi' => { apply @Classical.byCases (phi = phi')
                             . intro
                               simp [h_left_conc, h_right_conc]
                             . intro
                               simp[h_left_conc, h_right_conc]
                           }
        }
        | some Pattern.bot  => cases rconc <;> simp[h_left_conc, h_right_conc]
        | some (Pattern.metavar _)  => cases rconc <;> simp[h_left_conc, h_right_conc]
    }

theorem instantiate_wf : (Proof.instantiate p' subst).wf -> p'.wf := sorry
theorem instantiate_wf_inv : p'.wf -> (Proof.instantiate p' subst).wf  := sorry


theorem instantiate_commutes_with_implies(left: Pattern)(right: Pattern)(subst: Nat -> Option Pattern)
    : ((Pattern.implies left right).instantiate subst) = (Pattern.implies (left.instantiate subst) (right.instantiate subst))
    := by rw [Pattern.instantiate]

theorem instantiate_commutes_with_mp(left: Proof)(right: Proof)(subst: Nat -> Option Pattern)
     (h_left_conc : left.conclusion = (Pattern.implies phi psi))
     (h_right_conc : right.conclusion = some phi):
      (Proof.instantiate (Proof.modus_ponens left right) subst).conclusion
    = (Proof.modus_ponens (Proof.instantiate left subst) (Proof.instantiate right subst)).conclusion
    := by {
    simp [  mp_conclusion, h_right_conc, h_left_conc, instantiate_commutes_with_implies]
    }

theorem xxx (p: Proof) (p_has_conclusion : p.wf) :
    (push_instantiations p).conclusion = p.conclusion := by
    induction p with
    | prop1 => rfl
    | prop2 => rfl
    | modus_ponens l r pl pr =>
        have l : Proof.conclusion (push_instantiations l) = Proof.conclusion l
        · exact pl (mp_wf p_has_conclusion).1
        have r : Proof.conclusion (push_instantiations r) = Proof.conclusion r
        · exact pr (mp_wf p_has_conclusion).2
        simp [l,r]
    | instantiate p' subst h' =>
        have pp_has_concl : p'.wf := instantiate_wf p_has_conclusion
        have xx := h' pp_has_concl
        cases p' with
        | prop1 => rfl
        | prop2 => rfl
        | modus_ponens l r =>
          rcases pp_has_concl with ⟨pp_concl, pp_has_concl⟩
          . simp[pp_has_concl,push_instantiations]
            simp at h'
            unfold push_instantiations
            have xxx := (mp_wf pp_has_concl).1



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
