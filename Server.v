Require Import Coq.Logic.FinFun.


Section Settheory.

  (* Simulating isabelle set; however, it is fundamentally 
     different because of underlying logic. It's membership is 
   decidable, i.e. we can if an element x in this set of not. *)
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
  

  
  Definition Update {A B : Type} (Hdec : forall x y : A, {x = y} + {x <> y})
             (x : A) (v : B) (f : A -> option B) : A -> option B :=
    fun y => match Hdec x y with
          | left _ => Some v
          | right _ => f y
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
    (Hkeydec : forall x y : Keyid, {x = y} + {x <> y})
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

  (* This can be proved because every element in 
     record Key has decidable equality with 
     function_extensionality of set Identities *)
  Variable Hkdec : forall x y : Key, {x = y} + {x <> y}.

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
    In (fingerprint key) (dom (keys state)) = true ->
    match keys state (fingerprint key) with
    | Some k => k = key
    | None => True (* This would not happen. See fingerprint_key_lemma *)
    end.
  

  (*  There is no record update syntax in Coq! Hence, we need to keep 
   those field which are not chaning *)
  Definition upload_post (key : Key) (state state' : State) : Prop :=
    exists (token : UToken),
      fresh_utoken token state /\
      (keys state' = Update Hfindec (fingerprint key) key (keys state)) /\
      (upload state' = Update Hutodec token (fingerprint key) (upload state)) /\
      (prev_utokens state' = Union (prev_utokens state) (Singleton Hutodec token)) /\
      (* if we have a record update, then we don't need the below ones *)
      (* Maybe write a Ltac *)
      (pending state' = pending state) /\
      (confirmed state' = confirmed state) /\
      (managed state' = managed state) /\
      (prev_vtokens state' = prev_vtokens state) /\
      (prev_mtokens state' = prev_mtokens state). 
      
        

  
  Definition inv (s : State) : Prop :=
    (forall (f : Fingerprint) (k : Key),
        Some k = keys s f ->  fingerprint k = f) /\
    (forall (f : Fingerprint) (t : UToken),
        Some f = upload s t -> In f (dom (keys s)) = true) /\
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

  Lemma dec_upload : forall k s,  ~upload_pre k s \/ upload_pre k s.
  Proof.
    intros k s. unfold upload_pre, In, dom.
    remember (keys s (fingerprint k)) as c.
    destruct (keys s (fingerprint k)).
    subst. destruct (Hkdec  k k0).
    right.  auto.
    left. intro. firstorder.

    subst. right.  intro. inversion H.
  Qed.
  

  Lemma upload_inv :
    forall k s s', inv s -> upload_combined_cond k s s' -> inv s'.
  Proof. 
    (* Couple of subtle things: Decidability does not come for free 
      in contructive logic. We need to write a decision procedure *)
    unfold inv, upload_combined_cond.
    intros ? ? ? [H1 [H2 [H3 [H4 H5]]]] [Hu1 Hu2].
     (* decidability is key*) 
    assert (Hin : ~upload_pre k s \/ upload_pre k s).
    apply dec_upload.
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

      (* Now, the above proof pattern will follow everywhere. 
         Ltac? *)
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
      inversion Hs.  
      rewrite Hu12.
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
         destruct Hu1 as
             [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
         destruct Hu14 as [H14 [H15 [H16 [H17 [H18]]]]].

         rewrite H15 in Hs. pose proof (H3 _ _ _ k' Hs). 
         destruct H6 as [H19 [H20 H21]].
         split. rewrite Hu12.
         unfold In, dom, Update. 
         destruct (Hfindec (fingerprint k) f). 
         auto.    unfold not in n.
         auto.

         split. rewrite Hu12.
         unfold In, dom, Update. 
         destruct (Hfindec (fingerprint k) f). 
         rewrite H20. pose proof (H3 _ _ _ k Hs).
         destruct H6 as [H6 [H7 H8]]. auto.
         auto.  auto.

         +++ split.
             intros ? ? ? Hs.
             destruct Hin.
             apply Hu2 in H.  subst.
             pose proof (H4 _ _ k'  Hs).
             auto.
             
             apply Hu1 in H.
             unfold upload_post in H.
             destruct H as [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
             destruct Hu14 as [H14 [H15 [H16 [H17 [H18]]]]].
             rewrite H16 in Hs.
             pose proof (H4 _ _ k' Hs).
             pose proof (H4 _ _ k Hs).
             destruct H0 as [H0 [H9 H10]].
             destruct H6 as [H6 [H7 H8]].
             split.   
             rewrite Hu12. unfold In, dom, Update.
             unfold In, dom in H0. 
             destruct (Hfindec (fingerprint k) f).  
             auto. auto. 
             split.  rewrite Hu12.
             unfold Update. 
             destruct (Hfindec (fingerprint k) f).
             unfold In in H10.
             rewrite <- H9 in H7. auto. auto.
             auto. 

             (* one more to go *)
             ++++
               intros ? ? Hs.
               destruct Hin.
               apply Hu2 in H.
               rewrite <- H.
               rewrite <- H in Hs.
               apply H5 with (t := t). auto.


               apply Hu1 in H. unfold upload_post in H.
               destruct H as [tok [Hu11 [Hu12 [Hu13 Hu14]]]].
               destruct Hu14 as [H14 [H15 [H16 [H17 [H18]]]]].
               rewrite H17 in Hs.
               pose proof (H5 _ _ Hs).

               rewrite Hu12.  unfold In, dom, Update.
               destruct (Hfindec (fingerprint k) f).  
               auto. auto. 
  Qed.
  
End Server.  
