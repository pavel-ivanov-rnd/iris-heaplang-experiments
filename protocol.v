From iris.algebra Require Export sts.
From iris.program_logic Require Import ghost_ownership.
From iris.prelude Require Export gmap.

Inductive state :=
  | Init
  | Req
  | Exec
  | Resp
  | Ack.

Inductive token := White | Black | Lock.

Global Instance stateT_inhabited: Inhabited state := populate Init.

Inductive prim_step : relation state :=
  | Initialize: prim_step Init Req
  | Execute: prim_step Req Exec
  | Respond: prim_step Exec Resp
  | Acknowledge: prim_step Resp Ack.

Definition tok (s : state) : set token :=
  match s with
  | Init | Ack  => {[ Black; White ]}
  | Req  | Resp => {[ White ]}
  | Exec        => {[ Lock ]}
  end.

Global Arguments tok !_ /.

Canonical Structure sts := sts.STS prim_step tok.
