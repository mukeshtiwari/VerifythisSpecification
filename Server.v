Require Import Coq.FSets.FMapList.
Require Import List.
Import ListNotations.



Section Abstractmap.    
  (* I need finiteness. *)
  Variables Key Value : Type.
  
  Variables 
    (keylist : list Key)
    (vallist : list Value).

  Variables 
    (Hkeyfin : forall (k : Key), In k keylist)
    (Hvalfin : forall (v : Value), In v vallist).

  Variables
    (Hkeydec : forall x y : Key,   {x = y} + {x <> y})
    (Hvaldec : forall x y : Value, {x = y} + {x <> y}).
  

  
  (* A better way to model all the Scala function using 
     Coq map interface 
     https://coq.inria.fr/library/Coq.FSets.FMapList.html *) 
  Fixpoint get (k : Key) (maps : list (Key * Value)) : option Value :=
    match maps with
    | [] => None
    | (k', v') :: t => match Hkeydec k' k with
                     | left _ => Some v'
                     | right _ => get k t
                     end
    end.

  Fixpoint contains (k : Key) (maps : list (Key * Value)) : bool :=
    match maps with
    | [] => false
    | (k', v') :: t => match Hkeydec k' k with
                     | left _ => true
                     | right _ => contains k t
                     end
    end.


  Definition dom (maps : list (Key * Value)) : list Key :=
    List.map (fun '(x, y) => x) maps.

  Definition codom (maps : list (Key * Value)) : list Value :=
    List.map (fun '(x, y) => y) maps. 

  Theorem get_and_contains_true :
     forall k maps v, get k maps = Some v <-> contains k maps = true.
  Proof.
    intros ? ? ?.  split; intro H.
    generalize dependent maps.
    induction maps.
    + cbn. intro. congruence.
    + cbn. Admitted.
  
      
  Theorem get_and_contains_false :
    forall k maps, get k maps = None <-> contains k maps = false. 
  Admitted.


  
 (* I need these to interplay between list and function *) 
 Definition list_to_fun : list (Key *  Value) -> (Key  -> Value).  
 Proof.
 Admitted.
  
 Definition fun_to_list :  (Key -> Value) -> list (Key * Value).
 Admitted.

 
 Axiom list_fun_same :
   forall (l : list (Key * Value)),  fun_to_list (list_to_fun l) = l.
 

    
    
End Abstractmap.


Section Server.

  Variables 
    Keyid Fingerprint Identity 
    UToken VToken MToken : Type.

  Variables
    (kidlist : list Keyid)
    (finlist : list Fingerprint)
    (idelist : list Identity)
    (utolist : list UToken)
    (vtolist : list VToken)
    (mtolist : list MToken).

  Variables
    (Hkidfin : forall x, In x kidlist)
    (Hfinfin : forall x, In x finlist)
    (Hidefin : forall x, In x idelist)
    (Hutofin : forall x, In x utolist)
    (Hvtofin : forall x, In x vtolist)
    (Hmtofin : forall x, In x mtolist).

   Variables
    (Hkiddec : forall x y : Keyid      ,  {x = y} + {x <> y})
    (Hfindec : forall x y : Fingerprint,  {x = y} + {x <> y})
    (Hidedec : forall x y : Identity   ,  {x = y} + {x <> y})
    (Hutodec : forall x y : UToken     ,  {x = y} + {x <> y})
    (Hvtodec : forall x y : VToken     ,  {x = y} + {x <> y})
    (Hmtodec : forall x y : MToken     ,  {x = y} + {x <> y}).
  
  
   Record Key : Type := 
    mkKey {
        keyId : Keyid;
        fingerprint : Fingerprint;
        identities : Identity}.

   Variables
     (keylist : list Key)
     (Hkeyfin : forall x : Key, In x keylist)
     (Hkeydec : forall x y : Key, {x = y} + {x <> y}).
     
    

   Variables 
     (keys keys' : Fingerprint -> Key)
     (upload upload' : UToken -> Fingerprint)
     (pending pending' : VToken -> (Fingerprint * Identity)%type)
     (confirmed confirmed' : Identity -> Fingerprint)
     (managed managed' : MToken -> Fingerprint).
   


   

   Definition byFingerprint (fingerprint : Fingerprint) : option Key :=
     get _ _ Hfindec fingerprint (fun_to_list Fingerprint Key
                                              finlist keylist Hfinfin Hkeyfin Hfindec
                                              Hkeydec keys).

   Variable freshtoken : forall {A : Type}, A -> Prop. 

   Variable update : forall {A B : Type}, 
     A -> B -> (A -> B) -> (A -> B).
     
   (* If upload would have been implemented in Coq, then this would be a 
      theorem based on the definitions of upload *)
   Definition upload_correctness (key : Key) (token : UToken) : Prop :=
     match contains Fingerprint Key Hfindec (fingerprint key)
                    (fun_to_list _ _ finlist keylist Hfinfin Hkeyfin Hfindec Hkeydec keys) with
     | false => upload' = upload /\ keys = keys'
     | true =>  keys (fingerprint key) = key /\ keys' = update (fingerprint key) key keys
               /\ upload' = update token (fingerprint key) upload /\ freshtoken token
     end.
   
   
   
   
