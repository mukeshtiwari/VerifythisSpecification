Require Import Coq.FSets.FMapList.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.FinFun.
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
     
    
   (* 
   Variables 
     (keys keys' : Fingerprint -> Key)
     (upload upload' : UToken -> Fingerprint)
     (pending pending' : VToken -> (Fingerprint * Identity)%type)
     (confirmed confirmed' : Identity -> Fingerprint)
     (managed managed' : MToken -> Fingerprint). 
   


   

   Definition byFingerprint (fingerprint : Fingerprint) : option Key :=
     get _ _ Hfindec fingerprint (fun_to_list Fingerprint Key
                                              finlist keylist Hfinfin Hkeyfin Hfindec
                                              Hkeydec keys). *)

   Variable freshtoken : forall {A : Type}, A -> Prop. 

   Variable update : forall {A B : Type}, 
     A -> B -> (A -> B) -> (A -> B).

   (* Wrapping different maps in one record *)
   Record State : Type :=
     mkState {
         keys : Fingerprint -> Key;
         upload : UToken -> Fingerprint;
         pending : VToken -> Fingerprint * Identity;
         confirmed : Identity -> Fingerprint;
         managed : MToken -> Fingerprint}. 
         

   
   Definition upload_state (key : Key) (fstate sstate : State) : Prop :=
      match contains Fingerprint Key Hfindec (fingerprint key)
                    (fun_to_list _ _ finlist keylist Hfinfin Hkeyfin Hfindec Hkeydec (keys fstate)) with
     | false => (upload sstate = upload fstate) /\ (keys sstate = keys fstate)
     | true =>  exists (token : UToken), freshtoken token /\
               (keys fstate) (fingerprint key) = key /\
               (keys sstate = update (fingerprint key) key (keys fstate))
               /\ (upload sstate = update token (fingerprint key) (upload fstate))
      end.


   (* Am I thinking right? The question that is bothering me is: how are 
      the two states, fstate and sstate, are related in the beginning of 
      execution of upload? My hypothesis is they should be same, or 
      am I misinterpreting the relational style, or I don't have the 
      enough understanding to ask even meaningful questions? *)
   
   Definition upload_precond_In (key : Key) (fstate sstate : State) :=
     In (fingerprint key)
        (dom _ _ (fun_to_list _ _ finlist keylist Hfinfin Hkeyfin Hfindec Hkeydec (keys fstate))).
   
   Definition upload_postcond_In (key : Key) (fstate sstate : State) :=
     exists (token : UToken), freshtoken token /\ (keys fstate) (fingerprint key) = key /\
     (keys sstate = update (fingerprint key) key (keys fstate))
     /\ (upload sstate = update token (fingerprint key) (upload fstate)).


   Definition upload_combined_cond (key : Key) (fstate sstate : State) :=
     ( upload_precond_In key fstate sstate -> upload_postcond_In key fstate sstate) /\
     (~upload_precond_In key fstate sstate -> upload sstate = upload fstate
                                             /\ keys sstate = keys fstate).
   

   (* l1 is subset of l2 *)
   Definition Subset {A : Type} (l1 l2 : set A) :=
     forall x, In x l1 -> In x l2.
   
   (* In requestVerify function, the only state is changing is 
      pending. It changes when two conditions hold: 
      1. from token is in uploaded. 
      2. identities are subset of key.identities where 
         key = keys(upload(from)). 
      Otherwise, there is no change in pending *)
   
   Definition requestVerify_precond_In (from : UToken) (idn : set Identity)
              (fstate sstate : State) :=
     In from (dom _ _
                  (fun_to_list
                     _ _ utolist finlist Hutofin Hfinfin Hutodec Hfindec (upload fstate))) /\
     Subset idn  ([identities ((keys fstate) ((upload fstate) from))]).
   

   (* How to union two maps represented as function. One idea is: turn 
      both them as a list, combine the list and turn the list again back to 
      function, which, now, represents the union of two maps *)

   Definition Setunion {A B : Type} (f : A -> B) (g : A -> B) := f. (* This is not correct *)

   (* This is for the moment to escapte various implicity definitions *)
   Definition Listtofun : forall {A B : Type}, list (A * B) ->  (A -> B).
   Admitted.
                                                                 

   
   Definition requestVerify_postcond_In (from : UToken) (idn : set Identity)
              (fstate sstate : State) :=
     exists (f : Identity -> VToken),
       Injective f /\ (pending sstate) = Setunion (pending fstate)
                                                 (Listtofun (List.map (fun h => (f h, (upload fstate from, h))) idn)).


   Definition requestVerifty_combined_cond (from : UToken) (idn : set Identity) (fstate sstate : State) :=
     ( requestVerify_precond_In from idn fstate sstate -> requestVerify_postcond_In from idn fstate sstate) /\
     (~requestVerify_precond_In from idn fstate sstate -> (pending sstate) = (pending fstate)).
                    

   (* list (Fingerprint * Identity) *)
   Definition ziplist : forall {A B : Type}, list A -> list B -> list (A * B).
   Admitted.

   (* When two types, A and B, have decidable equality, then their pair also has
      decidable equality *)
   Definition zipdec : forall (A B : Type), (forall x y : A * B, {x = y} + {x <> y}).
   Admitted.

   (* forall v : Fingerprint * Identity, In v (ziplist finlist idelist) *)
   Definition fintype : forall v : Fingerprint * Identity, In v (ziplist finlist idelist).
   Admitted.
   
   Check fun_to_list.
   Definition verify_precond_In  (token : VToken) (fstate sstate : State) :=
     In token (dom _ _
                   (fun_to_list _ _ vtolist (ziplist finlist idelist) Hvtofin
                                fintype  Hvtodec (zipdec Fingerprint Identity)  (pending fstate))).

   
   Definition delete : forall {A B : Type}, (A -> B) -> A -> (A -> B).
   Admitted.
   
   Definition verify_postcond_In (token : VToken) (fstate sstate : State) :=
     let (fingerprint, identity) := (pending fstate token) in
     (pending sstate) = delete (pending fstate) token (* delete the token *)
     /\ (confirmed sstate) = update identity fingerprint (confirmed fstate).
     
     
   Definition verify_combined_cond (token : VToken) (fstate sstate : State) :=
     ( verify_precond_In token fstate sstate -> verify_postcond_In token fstate sstate) /\
     (~verify_precond_In token fstate sstate -> (pending sstate = pending fstate) /\
                                               (confirmed sstate = confirmed fstate)).


   Definition requestManage_precond_In (id : Identity) (fstate sstate : State) :=
     In id (dom _ _
                (fun_to_list _ _ idelist finlist Hidefin Hfinfin Hidedec Hfindec (confirmed fstate))).


   Definition requestManage_postcond_In (id : Identity) (fstate sstate : State) :=
     exists token : MToken, freshtoken token /\
                       (managed sstate = update token (confirmed fstate id) (managed fstate)). 
     

   Definition requestManage_combined_cond (id : Identity) (fstate sstate : State) :=
     ( requestManage_precond_In id fstate sstate -> requestManage_postcond_In id fstate sstate) /\
     (~requestManage_precond_In id fstate sstate -> managed sstate = managed fstate).



   Definition revoke_precond_In (token : MToken) (ids : set Identity) (fstate sstate : State) :=
     (In token (dom _ _
                   (fun_to_list _ _ mtolist finlist Hmtofin Hfinfin Hmtodec Hfindec (managed fstate)))) /\
     (let fingerprint := managed fstate token in
      let key := keys fstate fingerprint in
      Subset ids [identities key] (* Did I misunderstood the Scala or there is something going on in Scala*)).

   Definition dubminus : forall {A B : Type}, (A -> B) -> set A -> (A -> B).
   Admitted.
   
   Definition revoke_postcond_In (token : MToken) (ids : set Identity) (fstate sstate : State) :=
     confirmed sstate = dubminus (confirmed fstate) ids.


   Definition revoke_combined_cond (token : MToken) (ids : set Identity) (fstate sstate : State) :=
     ( revoke_precond_In token ids fstate sstate -> revoke_postcond_In token ids fstate sstate) /\
     (~revoke_precond_In token ids fstate sstate -> confirmed sstate = confirmed fstate).


   (* Specificate are fairly straight forward. One of things to do would be coming up all the 
      definitions in Coq, then proving all the definitions ending with combined_cond. *)

   
     
   
