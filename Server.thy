theory Server
  imports Main
begin

typedecl fingerprint
typedecl identity
typedecl utoken
typedecl vtoken
typedecl mtoken
typedecl keyid
 
record key = 
  kid :: keyid
  finger :: fingerprint
  ids :: "identity set"

record state =
  keys :: "fingerprint \<Rightarrow> key option"
  uploaded :: "utoken \<Rightarrow> fingerprint option"
  pending :: "vtoken \<Rightarrow> (fingerprint \<times> identity) option"
  confirmed :: "identity \<Rightarrow> fingerprint option"
  managed :: "mtoken \<Rightarrow> fingerprint option"
  prev_utokens :: "utoken set"

definition fresh :: "utoken \<Rightarrow> state \<Rightarrow> bool" where
  "fresh t s \<equiv> t \<notin> prev_utokens s"

definition upload_pre :: "key \<Rightarrow> state \<Rightarrow> bool" where
  "upload_pre k s \<equiv> finger k \<in> dom (keys s) \<longrightarrow> the ((keys s) (finger k)) = k"

lemma upload_pre_def2:
  "upload_pre k s = (case ((keys s) (finger k)) of Some k' \<Rightarrow> k' = k | None \<Rightarrow> True)"
  by(auto simp: upload_pre_def split: option.splits)

definition upload_post :: "key \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "upload_post k s s' \<equiv> \<exists> t. fresh t s \<and> 
   s' = (s\<lparr>keys := (keys s)((finger k) \<mapsto> k),
           uploaded := (uploaded s)(t \<mapsto> finger k),
           prev_utokens := (prev_utokens s) \<union> {t}\<rparr>)"

definition upload :: "key \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "upload k s s' \<equiv>  if upload_pre k s then upload_post k s s' else s' = s"

text {* Gidon's invariant -- are there any other invariants we should encode? *}
definition inv :: "state \<Rightarrow> bool" where
  "inv s \<equiv> (\<forall>f \<in> dom (keys s). finger (the ((keys s) f)) = f) \<and>
           (ran (uploaded s) \<subseteq> (dom (keys s))) \<and>
           (\<forall>(f,i) \<in> ran (pending s). f \<in> dom (keys s) \<and> i \<in> ids (the (keys s f))) \<and>
           (\<forall>i f. (confirmed s) i = Some f \<longrightarrow>  f \<in> dom (keys s) \<and> i \<in> ids (the (keys s f))) \<and>
           (ran (managed s) \<subseteq> (dom (keys s)))"

(* super uninteresting proof -- how to automate? *)
lemma upload_inv:
  "\<lbrakk>inv s; upload k s s'\<rbrakk> \<Longrightarrow> inv s'"
  apply(clarsimp simp: upload_def inv_def simp: upload_pre_def upload_post_def split: if_splits)
  apply(rule conjI)
  apply(clarsimp simp: upload_def inv_def simp: upload_pre_def upload_post_def split: if_splits simp: ran_def dom_def)
   apply blast
  apply(rule conjI)
  apply(clarsimp simp: upload_def inv_def simp: upload_pre_def upload_post_def split: if_splits simp: ran_def dom_def)
   apply fastforce
  apply(rule conjI)
  apply(clarsimp simp: upload_def inv_def simp: upload_pre_def upload_post_def split: if_splits simp: ran_def dom_def)
   apply fastforce
  apply(clarsimp simp: upload_def inv_def simp: upload_pre_def upload_post_def split: if_splits simp: ran_def dom_def)
  apply blast
  done


end