(* Type is Object. *)
Variable Obj: Type.
(* Lambda calculus are arrows from object to object. *)
Definition Obj_id : Obj -> Obj := fun (obj: Obj) => obj.
(* Homset: a set of lambda calculus, still represented as type (all inhabitants of the type) *)
Definition Hom_Obj_Obj := Obj -> Obj.

(* Functor maps Type to Type (and exists a map p maps coresponding arrows to arrows), I skill the commute definition *)
Definition commute := True.
Definition Func (F: Type -> Type) := {p: forall C C', (C -> C') -> F C -> F C'| commute}.
Definition ContraFunc (F: Type -> Type) := { p: forall C C', (C -> C') -> F C' -> F C | commute }.

(* Set valued functor, is still a kind of functor... I kind of hacked here *)
(* Arbitrary set valued functor, make it contravaraint. *)
Inductive set_C_op: (Type -> Type) -> Type :=
| SetCOP: forall (F: Type -> Type), ContraFunc (fun (T: Type) => T -> F T) -> set_C_op (fun (T: Type) => T -> F T).
(* Arbitrary set valued functor, covaraint. *)
Inductive set_C: (Type -> Type) -> Type :=
| SetC: forall (F: Type -> Type), Func (fun (T: Type) => F T -> T) -> set_C (fun (T: Type) => F T -> T).
(* E.g. Yoneda embedding, maps a type to a functor, maps arrows to arrows! *)
Definition y (C: Type) := fun T: Type => T -> C.
Definition y_p (C: Type) : forall A B, (A -> B) -> y C B -> y C A.
Proof. unfold y. auto. Qed.
Definition co_y (C: Type) := fun T: Type => C -> T.
Definition co_y_p (C: Type) : forall A B, (A -> B) -> co_y C A -> co_y C B.
Proof. unfold co_y. auto. Qed.

Theorem YonedaEmbMapsToSetCOP (C: Type): set_C_op (y C).
Proof.
  unfold y.
  apply SetCOP.
  intros. unfold ContraFunc.
  exists (y_p C). unfold commute. auto.
Qed.

(* Natrual Transformation, maps between two functors (Type -> Type), is a family of arrows, still a type. *)
Definition Natrual (F: Type -> Type) (G: Type -> Type) := forall T, F T -> G T.

(* Yoneda lemma: we have two maps, yl_left and yl_right *)
Definition yl_left (C: Type) (F: Type -> Type): set_C_op F -> (Natrual (y C) F) -> F C.
Proof.
  unfold Natrual.
  intros.
  destruct X.
  remember (X0 C (fun c:C => c)).
  apply f.
Defined.

Definition yl_right (C: Type) (F: Type -> Type): set_C_op F -> F C -> (Natrual (y C) F).
Proof.
  unfold y.
  unfold Natrual.
  intro.
  destruct X.
  intros fa C'.
  intro h.
  destruct c.
  remember (x C' C h fa).
  apply f.
Defined.

(* co-Yoneda lemma: we have two maps, yl_left and yl_right *)
Definition co_yl_left (C: Type) (F: Type -> Type): set_C F -> (Natrual (co_y C) F) -> F C.
Proof.
  unfold Natrual.
  intros.
  destruct X.
  remember (X0 C (fun c:C => c)).
  apply c.
Defined.

Definition co_yl_right (C: Type) (F: Type -> Type): set_C F -> F C -> (Natrual (co_y C) F).
Proof.
  unfold co_y.
  unfold Natrual.
  intro.
  destruct X.
  intros fa C'.
  intro h.
  destruct f.
  remember (x C C' h fa).
  apply c0.
Defined.

(* CPS *)

Definition ClosureConvert (A B: Type) (f: A -> B): forall T, (B -> T) -> (A -> T).
Proof.
  remember (co_yl_right B (co_y A)) as H.
  unfold co_y in H.
  unfold Natrual in H.
  auto.
Qed.
