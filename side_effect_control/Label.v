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
                          | LB p2 => subset p1 p2
                  end
  end.

Definition label_eq (lb1 : Label) (lb2 : Label) :=
  if flow_to lb1 lb2 then flow_to lb2 lb1 else false. 


(* unrestricted access L *)
Definition L_Label := LB nil.
(* unrestricted access L *)
Definition H_Label := LB (cons (Principal "Jian") nil).


Axiom flow_join_label : forall lb joined_lb lb' L,
  flow_to lb L = false ->
  lb' = join_label joined_lb lb ->
  flow_to lb' L = false.

Axiom flow_transitive : forall lb lb',
  flow_to lb' L_Label = false ->
  flow_to lb' lb = true ->
  flow_to lb L_Label = false.


Axiom flow_no_H_to_L : forall lb lb',
  flow_to lb L_Label = true ->
  flow_to lb' L_Label = false ->
  flow_to lb lb' = false.


Axiom join_label_commutative : forall l1 l2, 
    join_label l1 l2 = join_label l2 l1. 


Axiom H_Label_not_flow_to_L : forall lb, 
   flow_to lb L_Label = false -> lb = H_Label.


Axiom L_Label_flow_to_L : forall lb, 
   flow_to lb L_Label = true -> lb = L_Label.


Axiom join_L_label_flow_to_L : forall lb1 lb2, 
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  flow_to (join_label lb1 lb2) L_Label = true.

Axiom join_L_Label_irrelevant : forall lb,
    (join_label lb L_Label) = lb. 


Axiom exclude_middle_label : forall (lb1:Label) (lb2:Label),
    lb1 = lb2 \/ lb1 <> lb2.

Compute flow_to H_Label L_Label.
Compute flow_to H_Label H_Label.
