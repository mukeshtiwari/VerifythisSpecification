Require Import List. 

Section Abstractmap.    
  (* I need finiteness. *)
  Variables Key Value : Type.
  
  Variables 
    (keylist : list Key)
    (vallist : list Value).

  Variables 
    (Hkeyfin : forall (k : Key), In k keylist)
    (Hvalfin : forall (v : Value), In v vallist).

  Variables maps : Key -> Value. 

  (* A better way to model all the Scala function using 
     Coq map interface 
     https://coq.inria.fr/library/Coq.FSets.FMapList.html *) 
  Definition get (key : Key) :=  maps key.

End Abstractmap.


Section Server.

  Variables 
    Keyid Fingerprint Identity 
    UToken VToken MToken : Type.

  Variables
    (keylist : list Keyid)
    (finlist : list Fingerprint)
    (idelist : list Identity)
    (utolist : list UToken)
    (vtolist : list VToken)
    (mtolist : list MToken).

  
  Record Key : Type := 
    mkKey {
        keyId : Keyid;
        fingerprint : Fingerprint;
        identities : Identity}.


 Variables 
   (keys : Fingerprint -> Key)
   (uploaded : UToken -> Fingerprint)
   (pending : VToken -> (Fingerprint * Identity)%type)
   (confirmed : Identity -> Fingerprint)
   (managed : MToken -> Fingerprint).
   

 

    


