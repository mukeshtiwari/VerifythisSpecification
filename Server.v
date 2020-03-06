Require Import Coq.Logic.FinFun.


Section Settheory.

  (* Simulating isabelle set *)
  Definition set (A : Type) := A -> bool.

  Definition In {A : Type} (x : A) (f : set A) : bool := f x.

  Definition Union {A : Type} (f g : set A) : set A :=
    fun x => andb (f x)  (g x).

  Definition Intersection {A : Type} (f g : set A) : set A :=
    fun x => orb (f x) (g x).

  Definition Insert {A : Type} (Hdec : forall x y : A, {x = y} + {x <> y})
             (x : A) (f : set A) : set A :=
    fun y => match Hdec x y with
          | left _ => true
          | right _ => false
          end.

  Definition emptyset {A : Type} : set A :=
    fun _ => false.
  

  Definition Singleton {A : Type} (Hdec : forall x y : A, {x = y} + {x <> y})
             (x : A) : set A :=
    Insert Hdec x emptyset.
    

  (* f is the subset of g *)
  Definition Subset {A : Type} (f g : set A) :=
    forall a, f a = true -> g a = true. 

   (* Mimicing the isabelle dom function *)
  Definition dom {A B : Type} (f : A -> option B) : set A :=
    fun x => match f x with
          | None => false
          | Some x => true
          end.
  

  Definition ran {A B : Type} (f : A -> option B) : set B.
    (* This can not be written as boolean function, because 
       B is not finite. 
       definition
       ran :: "('a ⇀ 'b) ⇒ 'b set" where
       "ran m = {b. ∃a. m a = Some b}"
       This is not constructive!  
       Unless I assume A and B are finite types. In that case, 
   ran  f := List.filter (fun (x, y) => if y = None then false else true ) 
               (List.zip (l : list l) (list.map f l) *)
  Admitted. 
  
  
  Definition Update {A B : Type} (Hdec : forall x y : A, {x = y} + {x <> y})
             (x : A) (v : B) (f : A -> option B) : A -> option B :=
    fun y => match Hdec x y with
          | left _ => Some v
          | right _ => f y
          end.

 
  Definition delete {A B : Type} (x : A) (f : A -> option B) : A -> option B :=
    fun y => match f x with
          | None => None 
          | Some v => None
          end.

  
      
End Settheory.
  

Section Server. 

  
  Variables 
    Keyid
    Fingerprint
    Identity 
    UToken
    VToken
    MToken : Type.
  
  Variables
    (Hfindec : forall x y : Fingerprint, {x = y} + {x <> y})
    (Hutodec : forall x y : UToken, {x = y} + {x <> y})
    (Hidedec : forall x y : Identity, {x = y} + {x <> y})
    (Hmtodec : forall x y : MToken, {x = y} + {x <> y})
    (Hvtodec : forall x y : VToken, {x = y} + {x <> y}).
                                                                                    
  
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
    In uto (prev_utokens s) = false. 


  Definition fresh_vtoken (vto : VToken) (s : State) : Prop :=
    In vto (prev_vtokens s) = false.


  Definition fresh_mtoken (mto : MToken) (s : State) : Prop :=
    In mto (prev_mtokens s) = false.

  
  

  Lemma fingerprint_key_lemma : forall (key : Key) state,
    In (fingerprint key) (dom (keys state)) = true ->
    exists key', Some key' = keys state (fingerprint key). 
  Proof.
    intros ? ? Hin.
    unfold In in *; unfold dom in *.
    remember (keys state (fingerprint key)) as r.
    destruct r.
    exists k. auto.  discriminate Hin.
  Qed.
  

  Lemma upload_some : forall k f s, 
      Some k = keys s f -> In f (dom (keys s)) = true.
  Proof.
    intros ? ? ? Hs.
    unfold In, dom. rewrite <- Hs.
    auto.
  Qed.
  
    
    
  Definition upload_pre (key : Key) (state : State) : Prop :=
    In (fingerprint key) (dom (keys state)) = true -> match keys state (fingerprint key) with
                                                     | Some k => k = key
                                                     | None => True (* This would not happen. See fingerprint_key_lemma *)
                                                     end.
  

  
  Definition upload_post (key : Key) (state state' : State) : Prop :=
    exists (token : UToken), fresh_utoken token state /\
                        (keys state' = Update Hfindec (fingerprint key) key (keys state)) /\
                        (upload state' = Update Hutodec token (fingerprint key) (upload state)) /\
                        (prev_utokens state' = Union (prev_utokens state) (Singleton Hutodec token)).

  
  Definition inv (s : State) : Prop :=
    (forall (f : Fingerprint) (k : Key), Some k = keys s f ->  fingerprint k = f) /\
    (forall (f : Fingerprint) (t : UToken), Some f = upload s t -> In f (dom (keys s)) = true) /\
    (forall (t : VToken) (f : Fingerprint) (i : Identity) (k' : Key), 
        Some (f, i) = pending s t -> In f (dom (keys s)) = true /\
                                    Some k' = keys s f /\
                                    In i (identities k') = true) /\
    (forall (f : Fingerprint) (i : Identity) (k' : Key),
        Some f = confirmed s i -> In f (dom (keys s)) = true /\
                                 Some k' = keys s f /\
                                 In i (identities k') = true) /\
    (forall (f : Fingerprint) (t : MToken),
        Some f = managed s t -> In f (dom (keys s)) = true).
      
    
  Definition upload_combined_cond (key : Key) (state state' : State) : Prop :=
    ( upload_pre key state -> upload_post key state state') /\
    (~upload_pre key state -> state = state'). 
   

  Lemma upload_inv :
    forall k s s', inv s -> upload_combined_cond k s s' -> inv s'.
  Proof.
    (* Couple of subtle things: if_split. Decidability does not come for free. 
       I need to prove that upload_pre is decidable, but for the memoment, 
       just assert it. First taste of law of excluded middle. *)
    unfold inv, upload_combined_cond.
    intros ? ? ? [H1 [H2 [H3 [H4 H5]]]] [Hu1 Hu2].
     (* decidability is key*) 
    assert (Hin : ~upload_pre k s \/ upload_pre k s).
    admit.
    split. 

    + intros ? ? Hs.
      (* Precondition does not hold *)
      destruct Hin.
      specialize (Hu2 H). subst.
      apply H1. auto.

      (* Precondition holds *)
      specialize (Hu1 H).
      unfold upload_post in Hu1.
      destruct Hu1 as [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
      rewrite Hu12 in Hs.
      unfold Update in Hs.
      destruct (Hfindec (fingerprint k)).
      inversion Hs. auto.
      apply H1.  auto.

    + split.
      intros ? ? Hs.
      destruct Hin.

      (* Precondtion does not hold *)
      specialize (Hu2 H).
      subst. apply H2 with (t := t).
      auto.

      (* Precondition holds *)
      specialize (Hu1 H).
      unfold upload_post in Hu1.
      destruct Hu1 as [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
      rewrite Hu13 in Hs.
      unfold Update in Hs.
      destruct (Hutodec tok t).
      inversion Hs. rewrite Hu12.
      unfold In, dom.
      unfold Update.
      destruct  (Hfindec (fingerprint k) (fingerprint k)).
      auto. pose proof (n eq_refl). inversion H0.
      rewrite Hu12. unfold In, dom, Update.
      destruct (Hfindec (fingerprint k) f). auto.
      pose proof (H2 f t Hs). unfold In, dom in H0.
      auto.

      (* Can it be automated using Ltac ? *)

      ++ split.
         intros ? ? ? ? Hs.
         destruct Hin.

         (* Precondition does not hold *)
         specialize (Hu2 H).
         rewrite  <- Hu2. 
         apply H3 with t; auto.
         rewrite <- Hu2 in Hs.
         auto.
         
         (* Precondition holds *)
         specialize (Hu1 H).
         unfold upload_post in Hu1.
         destruct Hu1 as [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
         (* No record update is tricky *)
         
         
         

         
         
  Admitted.
  
  
  Lemma upload_state_lemma : forall (from : UToken) state,
    In from (dom (upload state)) = true ->
    exists fingerprint, Some fingerprint = upload state from. 
  Proof.
    intros ? ? Hin.
    unfold In in *; unfold dom in *.
    remember (upload state from) as r.
    destruct r.
    exists f. auto. discriminate Hin.
  Qed.
  
  
  Definition requestVerify_precond (from : UToken) (idn : set Identity) (state : State) :=
    In from (dom (upload state)) = true /\
    (match (upload state from) with
     | None => False (* This would not happen. See the proof upload_state_from *)
     | Some fingerprint' => match (keys state fingerprint') with
                           | None => False (* What can I say about this assuming the first two? *)
                           | Some key' => Subset idn (identities key')
                           end
     end).




  
  Definition requestVerify_postcond (from : UToken) (idn : Identity -> bool ) (state state' : State) :=
    exists (f : Identity -> VToken),
      Injective f /\ True (* Figure out how to use partial map as a list *).
      

  Definition requestVerify_combined_cond (from : UToken) (idn : set Identity) (state state' : State) :=
     ( requestVerify_precond from idn state -> requestVerify_postcond from idn state state') /\
     (~requestVerify_precond from idn state -> pending state' = pending state).

  
  

  
                    
  Definition verify_precond  (token : VToken) (state : State) : Prop :=
    In token (dom (pending state)) = true.

  Lemma some_pending : forall (token : VToken) state ,
      In token (dom (pending state)) = true ->
      exists fingerprint identity,  Some (fingerprint, identity) = pending state token.
  Proof.
    intros ? ? Hin. unfold In in *.
    unfold dom in *.
    remember (pending state token) as r.
    destruct r. destruct p.
    exists f, i; auto.
    discriminate.
  Qed.
  

  (* after deleting the token, it will no longer exists in the 
     return map *)
  Lemma pending_delete :forall (token : VToken) state,
      In token (dom (pending state)) = true ->
      let pending' := delete token (pending state) in
      In token (dom pending') = false. 
  Proof.
    intros ? ? Hin.
    unfold delete, In in * |- *.
    unfold dom in * |- *.
    remember (pending state token) as r.
    destruct r; auto.
  Qed.
  
  
    
    
  Definition verify_postcond (token : VToken) (state state' : State) :=
    match pending state token with
    | None => True (* This would not happend because token is in the domain of pending. See the proof some_pending *)
    | Some (fingerprint, identity) =>
      pending state' = delete token (pending state)  /\
      confirmed state' = Update Hidedec identity fingerprint (confirmed state)
    end.
  

  
     
   Definition verify_combined_cond (token : VToken) (state state': State) :=
     ( verify_precond token state -> verify_postcond token state state') /\
     (~verify_precond token state -> (pending state' = pending state) /\
                                    (confirmed state' = confirmed state)).


   


   Definition requestManage_precond  (id : Identity) (state : State) :=
     In id (dom (confirmed state)) = true.
   

   Lemma confirmed_fingerprint : forall (id : Identity) state,
     In id (dom (confirmed state)) = true -> exists fingerprint, Some fingerprint = confirmed state id.
   Proof.
     intros ? ? Hin.
     unfold In in *;
       unfold dom in *.
     remember (confirmed state id) as r.
     destruct r.
     exists f.  auto. discriminate Hin.
   Qed.
   
   Definition requestManage_postcond (id : Identity) (state state' : State) :=
     exists token : MToken, fresh_mtoken token state /\
                       (match confirmed state id with
                        | None => True (* This would also not happen. confirmed_fingerprint*)
                        | Some fingerprint =>
                           managed state' = Update Hmtodec token fingerprint (managed state)
                        end) /\
                        (prev_mtokens state' = Union (prev_mtokens state) (Singleton Hmtodec token)).
                        
                       
                       
   Lemma token_managed : forall (token : MToken) state,
     In token (dom (managed state)) = true ->
     exists fingerprint, Some fingerprint = managed state token. 
   Proof.
     intros ? ? Hin.
     unfold In in *; unfold dom in *.
     remember (managed state token) as r.
     destruct r.
     exists f. auto. discriminate Hin.
   Qed.
   
   Lemma token_managed_keys : forall (token : MToken) state fingerprint, 
     In token (dom (managed state)) = true -> Some fingerprint = managed state token ->
     exists k, Some k = keys state fingerprint.
   Proof.
     intros ? ? ? Hin Hd.
     eexists.  unfold In in *; unfold dom in *.
     remember (managed state token) as r. 
     destruct r. 
     (* There is no information in assumption to discharge the goal. *)
   Admitted.
   
     
   Definition revoke_precond (token : MToken) (ids : set Identity) (state : State) :=
     In token (dom (managed state)) = true /\
     (match managed state token with
      | None => True (* This would not happen. See the proof token_managed *)
      | Some fingerprint =>
        match keys state fingerprint with
        | None => False  
        | Some key => Subset ids (identities key)
        end
      end).

  

   Definition dubminus : forall {A B : Type}, (A -> option B) -> set A -> (A -> option B).
     intros ? ? f g x.
   Admitted.
   
   
   Definition revoke_postcond (token : MToken) (ids : set Identity) (state state' : State) :=
     confirmed state' = dubminus (confirmed state) ids.


   Definition revoke_combined_cond (token : MToken) (ids : set Identity) (state state' : State) :=
     ( revoke_precond token ids state -> revoke_postcond token ids state state') /\
     (~revoke_precond token ids state -> confirmed state' = confirmed state).

   (* Specificate are fairly straight forward. One of things to do would be coming up all the 
      definitions in Coq, then proving all the definitions ending with combined_cond. *)

   
     
   
