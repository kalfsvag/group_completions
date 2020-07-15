Require Import HoTT.

(** We introduce the notion of connected pointed types, which we will use as a tool later.  *)
Definition isconn (X : pType) := forall (x : X), merely (point X = x).
Record Conn_pType := {ptype_conn_ptype :> pType ; isconn_conn_ptype : isconn ptype_conn_ptype}.

Definition ptype_prod (X Y : pType) : pType
  := Build_pType (X * Y) (point _, point _).


Definition conn_ptype_prod (X Y : Conn_pType) : Conn_pType.
Proof.
  apply (Build_Conn_pType (ptype_prod X Y)).
  unfold isconn.
  intros [x y].
  generalize (isconn_conn_ptype X x). intro p.
  generalize (isconn_conn_ptype Y y). intro q.
  strip_truncations. apply tr. exact (path_prod (_,_) (_,_) p q).
Defined.
