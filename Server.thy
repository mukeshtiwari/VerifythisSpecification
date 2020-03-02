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

definition upload_post :: "key \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "upload_post k s s' \<equiv> \<exists> t. fresh t s \<and> 
   s' = (s\<lparr>keys := (keys s)((finger k) \<mapsto> k),
           uploaded := (uploaded s)(t \<mapsto> finger k),
           prev_utokens := (prev_utokens s) \<union> {t}\<rparr>)"

definition upload :: "key \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "upload k s s' \<equiv>  if upload_pre k s then upload_post k s s' else s' = s"

(* TODO: other operations :) *)

end