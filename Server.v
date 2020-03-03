(* 
Require Import Coq.FSets.FMapList.
Require Import Coq.Lists.ListSet *)
Require Import Coq.Logic.FinFun.

(*Require Import List.
Import ListNotations. *)


Section Settheory.

  (* Simulating isabelle set *)
  Definition set (A : Type) := A -> Prop.

  Definition In {A : Type} (x : A) (f : set A) : Prop := f x.

  Definition Union {A : Type} (f g : set A) : set A :=
    fun x => f x \/ g x.

  Definition Intersection {A : Type} (f g : set A) : set A :=
    fun x => f x /\ g x.

  Definition Insert {A : Type} (x : A) (f : set A) : set A :=
    fun y => y = x \/ In y f.

  Definition Singleton {A : Type} (x : A) : set A. 
    (* Now this also can not be implemented withtout 
       decidable equality. fun y => match dec_eq x y with
                               | left _ => True
                               | right _ => False
                               end. *)
    refine (fun y => _).
  Admitted.

  (* f is the subset of g *)
  Definition Subset {A : Type} (f g : set A) : Prop :=
    forall x, f x = True -> g x = True.
  
      
End Settheory.
  

Section Server. 

  
  Variables 
    Keyid
    Fingerprint
    Identity 
    UToken
    VToken
    MToken : Type.
  
  
  
  Record Key : Type := 
    mkKey {
        keyId : Keyid;
        fingerprint : Fingerprint;
        identities : set Identity}.

 

  (* Wrapping different maps in one record *)
  Record State : Type :=
    mkState {
        keys : Fingerprint -> option Key;
        upload : UToken -> option Fingerprint;
        pending : VToken -> option (Fingerprint * Identity);
        confirmed : Identity -> option Fingerprint;
        managed : MToken -> option Fingerprint;
        prev_utokens : set UToken;
        prev_vtokens : set VToken;
        prev_mtokens : set MToken}.




  Definition fresh_utoken (uto : UToken) (s : State) : Prop :=
    ~In uto (prev_utokens s).


  Definition fresh_vtoken (vto : VToken) (s : State) : Prop :=
    ~In vto (prev_vtokens s).


  Definition fresh_mtoken (mto : MToken) (s : State) : Prop :=
    ~In mto (prev_mtokens s).

  
  (* Mimicing the isabelle dom function *)
  Definition dom {A B : Type} (f : A -> option B) : set A :=
    fun x => match f x with
          | None => False
          | Some x => True
          end.
  

  
  
  Definition Update {A B : Type} (x : A) (v : B) (f : A -> option B) : A -> option B.
  (* Now here, we need decidable equality of A. 
     fun y => match dec_eq x y with
              | left _ => Some v
              | right _ => f x *)
  Admitted.
  
  
  Definition upload_pre (key : Key) (state : State) : Prop :=
    In (fingerprint key) (dom (keys state)) -> match (keys state) (fingerprint key) with
                                              | Some k => k = key
                                              | None => True
                                              end.
  


  Definition upload_post (key : Key) (state state' : State) : Prop :=
    exists (token : UToken), fresh_utoken token state /\
                        (keys   state' = Update (fingerprint key) key (keys state)) /\
                        (upload state' = Update token (fingerprint key) (upload state)) /\
                        (prev_utokens state' = Union (prev_utokens state) (Singleton token)).
                        
  
         

  Definition upload_combined_cond (key : Key) (state state' : State) : Prop :=
    ( upload_pre key state -> upload_post key state state') /\
    (~upload_pre key state -> state = state'). 
   

  
   
   (* In requestVerify function, the only state is changing is 
      pending. It changes when two conditions hold: 
      1. from token is in uploaded. 
      2. identities are subset of key.identities where 
         key = keys(upload(from)). 
      Otherwise, there is no change in pending *)


  Definition requestVerify_precond (from : UToken) (idn : set Identity) (state : State) :=
    In from (dom (upload state)) /\
    (match (upload state from) with
     | None => False
     | Some fingerprint' => match (keys state fingerprint') with
                           | None => False
                           | Some key' => Subset idn (identities key')
                           end
     end).



  Definition OptionUpdata  {A B C : Type} (f : A -> option (B * C)) (g : A -> option (B * C)) : A -> option (B * C).
    (* fun z => eq_dec x z 
                | left _ => Some y
                | right _ => f z 
                end. *)
  Admitted.
  

  (* Stuck here because of list and function stuff *)
  Definition requestVerify_postcond (from : UToken) (idn : set Identity) (state state' : State) :=
    exists (f : Identity -> VToken),
      Injective f /\ (pending state' = 

      

     
  
                                                                 

   
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

   
     
   
