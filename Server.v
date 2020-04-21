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
  
 
