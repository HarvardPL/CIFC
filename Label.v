Require Import List.
Require Import Coq.Strings.String.


Inductive principal : Type :=
  | Principal : string -> principal.



(* centralized label: the readers of this data*)
Inductive Label : Type :=
  | LB : (list principal) -> Label.

Definition beq_principal x y :=
  match x,y with
    | Principal n1, Principal n2 => if string_dec n1 n2 then true else false
  end.

Fixpoint principals_find (p : principal) (pl : list principal) :=
  match pl with
    | nil => false
    | h :: t => if beq_principal p h then true else (principals_find p t)
  end.

Definition principals_add (p : principal) (pl : list principal) :=
  if (principals_find p pl) then cons p pl else pl.

Fixpoint principals_remove (p : principal) (pl : list principal) := 
  match pl with
    | nil => nil
    | h :: t => if beq_principal p h then (principals_remove p t) else 
        h :: (principals_remove p t)
  end.

Fixpoint principals_inter (pl1 : list principal) (pl2 : list principal) :=
  match pl1 with 
    | nil => nil
    | h :: t => if (principals_find h pl2) then (h :: (principals_inter t pl2))
                 else (principals_inter t pl2)
  end.

Fixpoint principals_union (pl1 : list principal) (pl2 : list principal) :=
  match pl1 with 
    | nil => pl2
    | h :: t => principals_add h (principals_union t pl2)
  end.

Definition join_label (lb1 :Label) (lb2 : Label) := 
  match lb1 with  
    | LB p1 => match lb2 with
                  | LB p2 => LB (principals_inter  p1 p2)
                 end
  end.

Definition meet_label (lb1 :Label) (lb2 : Label) := 
  match lb1 with  
    | LB p1 => match lb2 with
                  | LB p2 => principals_union p2 p1
                 end
  end.



Fixpoint subset (p1 : list principal) (p2 : list principal) := 
    match p1 with
        | nil => true
        | h :: t => if (principals_find h p2) then (subset t p2) else false
    end. 


Definition flow_to (lb1 : Label) ( lb2 : Label) :=
  match lb1 with
    | (LB p1) => match lb2 with 
                          | LB p2 => subset p2 p1
                  end
  end.
