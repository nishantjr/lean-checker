import LeanChecker.Util

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
deriving DecidableEq, Repr

def inst := Proof.instantiate
def prop1 := Proof.prop1
def prop2 := Proof.prop2
def mp := Proof.modus_ponens

def prop1_concl := (implies ph0 (implies ph1 ph0))
def prop2_concl := (implies (implies ph0 (implies ph1 ph2)) (implies (implies ph0  ph1) (implies ph0 ph2)))
def mp_conclusion(hyp1: Option Pattern)(hyp2: Option Pattern) : Option Pattern := match (hyp1, hyp2) with
          | (_, none) => none
          | (none, _) => none
          | (some concl_1, some (Pattern.implies concl_2_left concl_2_right)) =>
                if concl_2_left = concl_1 then concl_2_right else none
          | (some _, some _) => none

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


inductive Instruction where
    | metavar(id: Nat) : Instruction
    | bot : Instruction
    | implies : Instruction
    | instantiate(subst: List Nat) : Instruction
    | prop1 : Instruction
    | prop2 : Instruction
    | modus_ponens : Instruction

    | save : Instruction
    | load(loc: Nat) : Instruction

    --- | publish : Instruction
deriving DecidableEq, Repr


inductive ProofPhase where
    | gamma
    | claims
    | proof

inductive Term where
    | pattern(pattern: Pattern)
    | proved(pattern: Pattern)
deriving DecidableEq, Repr

structure ProverState where
    memory : List Term
    stack  : List Term
deriving DecidableEq, Repr

--- TODO: Could be implemented with `take n`, and `zip`?
def mk_subst(rev_ids: List Nat)(stack: List Term) : Option ((List (Nat × Pattern)) × List Term) :=
    match rev_ids with
      | [] => some ([], stack)
      | id :: ids_rest => match stack with
                | Term.pattern p :: stack_rest
                => match mk_subst ids_rest stack_rest with
                    | none => none
                    | some (ret_subst, ret_stack) => (((id, p) :: ret_subst), ret_stack)
                | _ => none

open Instruction
def execute_instruction(state: ProverState)(instr: Instruction) : Option ProverState :=
    match instr with
      | metavar n
        => some { state with stack  := Term.pattern (Pattern.metavar n) :: state.stack  }
      | Instruction.bot
        => some { state with stack  := Term.pattern Pattern.bot :: state.stack  }
      | Instruction.implies
        => match state.stack with
             | Term.pattern left :: Term.pattern right :: tail
               => some { state with stack := Term.pattern (implies left right) :: tail }
             | _ => none

      | Instruction.prop1
        => some { state with stack  := Term.proved prop1_concl :: state.stack  }
      | Instruction.prop2
        => some { state with stack  := Term.proved prop2_concl :: state.stack  }
      | modus_ponens
        => match state.stack with
             | Term.proved hyp1 :: Term.proved hyp2 :: tail =>
                match (mp_conclusion hyp1 hyp2) with
                    | some mp_concl => some { state with stack := Term.proved mp_concl :: tail }
                    | none => none
             | _ => none

      | Instruction.instantiate ids
        => match state.stack with
            | [] => none
            | p :: stack_tail =>
                match mk_subst (rev ids) stack_tail with
                | none => none
                | some (subst, rest_stack) =>
                    match p with
                      | Term.pattern pat => some { state with stack := Term.pattern (pat.instantiate subst) :: rest_stack }
                      | Term.proved  pat => some { state with stack := Term.proved  (pat.instantiate subst) :: rest_stack }

      | save      => match state.stack with
                       | head :: _ => some { state with memory := head :: state.memory }
                       | [] => none
      | load n    => match getElement n (rev state.memory) with
                       | some loaded => some { state with stack := loaded :: state.stack }
                       | none => none

def execute_instructions(state: ProverState) (instrs: List Instruction) : Option ProverState :=
    match instrs with
    | [] => state
    | instr :: instrs'
    => match (execute_instruction state instr) with
       | none => none
       | some state' => execute_instructions state' instrs'


def imp_refl_instrs :=
    [ metavar 0         --- stack: $ph0
    , save              --- @0
    , load 0            --- stack: $ph0; ph0
    , load 0            --- stack: $ph0; $ph0; ph0
    , implies           --- stack: $ph0; ph0 -> ph0
    , save              --- @1
    , prop2             --- stack: $ph0; $ph0 -> ph0; [prop2: (ph0 -> (ph1 -> ph2)) -> ((ph0 -> ph1) -> (ph0 -> ph2))]
    , instantiate [1]   --- stack: $ph0; [p1: (ph0 -> ((ph0 -> ph0) -> ph2)) -> (ph0 -> (ph0 -> ph0)) -> (ph0 -> ph2)]
    , instantiate [2]   --- stack: [p1: (ph0 -> ((ph0 -> ph0) -> ph0)) -> (ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0)]
    , load 1            --- stack: p1 ; $ph0 -> ph0
    , prop1             --- stack: p1 ; $ph0 -> ph0; [prop1: ph0 -> (ph1 -> ph0)]
    , instantiate [1]   --- stack: p1 ; [p2: (ph0 -> (ph0 -> ph0) -> ph0) ]
    , modus_ponens      --- stack: [p3: (ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0)]
    , load 0            --- stack: p3 ; ph0;
    , prop1             --- stack: p3 ; ph0; prop1
    , instantiate [1]   --- stack: p3 ; ph0 -> (ph0 -> ph0)
    , modus_ponens      --- stack: ph0 -> ph0
    ]

theorem test_exec_imp_refl :
     (execute_instructions { stack := [], memory := [] : ProverState } imp_refl_instrs)
   = { stack := [Term.proved ph0_implies_ph0], memory := [Term.pattern ph0_implies_ph0, Term.pattern ph0] : ProverState }
    := by rfl
