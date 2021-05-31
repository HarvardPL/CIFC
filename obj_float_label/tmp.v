Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals. Require Vector.


(* identifiers *)
Inductive id : Type :=
  | Id : string -> id.

Definition state := id -> R.

Definition traceFun := R -> state.

Inductive trace : Type :=
  | emptyTrace
  | consTrace (n : traceFun) (l : trace).

Inductive traceSem : Type :=
  | nil
  | cons (t : trace) (s : traceSem). 


(** Definition traceSem :=  list trace -> Prop. **)

Inductive tm : Type :=
  | Tvar : id -> tm.

Inductive traceDynamicSemantic : tm -> traceSem -> Prop :=
  | trace1 : traceDynamicSemantic (Tvar (Id "")) nil.



Inductive KTnum :=
| KTNnat  (n : nat) : KTnum
| KTNreal (r : R)   : KTnum.

(** Terms --- see Definition 1, Section 2.1 *)
Inductive Term : Type :=
| KTdot          (n : nat)             : Term        (* dot symbol for terms *)
| KTfuncOf       (f : FunctionSymbol)
                 (n : nat)
                 (a : Vector.t Term n) : Term        (* application of function symbol *)
| KTnumber       (r : KTnum)           : Term        (* number constant *)
| KTread         (var : KAssignable)   : Term        (* read variable x or diff. symbol x' *)
| KTneg          (child : Term)        : Term        (* negation       -x  *)
| KTplus         (left right : Term)   : Term        (* addition       x+y *)
| KTminus        (left right : Term)   : Term        (* subtraction    x-y *)
| KTtimes        (left right : Term)   : Term        (* multiplication x*y *)
| KTdifferential (child : Term)        : Term        (* differential   x'  *)
.

(** Formulas --- see Definition 2, Section 2.1 *)
Inductive Formula : Type :=
| KFdot                             : Formula           (* dot symbol for formulas *)
| KFtrue                            : Formula           (* true   *)
| KFfalse                           : Formula           (* false  *)
| KFequal       (left right : Term) : Formula           (* x == y *)
| KFnotequal    (left right : Term) : Formula           (* x != y *)
| KFgreaterEqual(left right : Term) : Formula           (* x >= y *)
| KFgreater     (left right : Term) : Formula           (* x > y  *)
| KFlessEqual   (left right : Term) : Formula           (* x =< y *)
| KFless        (left right : Term) : Formula           (* x < y  *)
| KFpredOf      (f : PredicateSymbol)
                (n : nat)
                (a : Vector.t Term n)                : Formula          (* appliction of predicate symbol *)
(* predicational or quantifier symbol applied to argument formula child *)
| KFquantifier  (f : QuantifierSymbol) (a : Formula) : Formula
| KFnot         (child : Formula)                    : Formula           (* ~p *)
| KFand         (left right : Formula)               : Formula           (* p /\ q *)
| KFor          (left right : Formula)               : Formula           (* p \/ q *)
| KFimply       (left right : Formula)               : Formula           (* p -> q *)
| KFequiv       (left right : Formula)               : Formula           (* p <-> q *)
(* quantifiers *)
| KFforallVars  (vars : list KVariable) (child : Formula)    : Formula           (* Forall x,y,z. p *)
| KFexistsVars  (vars : list KVariable) (child : Formula)    : Formula           (* Exists x,y,z. p *)
(* modal formulas *)
| KFbox         (prog : Program) (child : Formula)           : Formula           (* [alpha] p *)
| KFdiamond     (prog : Program) (child : Formula)           : Formula           (* <alpha> p *)

(** Hybrid programs --- see Definition 3, Section 2.1 *)
with Program : Type :=
     | KPconstant     (name : ProgramConstName)                : Program           (* program constant e.g., alpha *)
     | KPassign       (x : KAssignable) (e : Term)             : Program           (* x := e or x' := e *)
     | KPassignAny    (x : KAssignable)                        : Program           (* x := * or x' := * *)
     | KPtest         (cond : Formula)                         : Program           (* ?cond *)
     | KPchoice       (left : Program)(right : Program)        : Program           (* alpha u beta *)
     | KPcompose      (left : Program)(right : Program)        : Program           (* alpha ; beta *)
     | KPloop         (child : Program)                        : Program           (* alpha* *)
     | KPodeSystem (ode : ODE) (constraint : Formula) : Program
.

Definition traceSem :=  list traceFun -> Prop.



Definition state := nat -> nat. 
Definition programSem := state -> state -> Prop. 
Check state.  
Check programSem.


Definition traceFun := nat -> state. 


Definition traceSem :=  list traceFun -> Prop.



Fixpoint dynamic_semantics_program
         (p : tm)
     : programSem  :=
  match p with
  | Tvar i => (fun v w => True)
  end.

Definition trace := list traceFun. 

Definition v : state := fun x => x+1. 

Check dynamic_semantics_program (Tvar (Id "")) v v.


Inductive traceSemantics : tm -> list trace -> Prop :=
| Trace1 : forall p t v w,
    dynamic_semantics_program p v w -> traceSemantics p t.

Check traceSemantics. 



  