(** A nominal representation of STLC terms.

    This version looks a lot like we expect a representation of
    the lambda calculus to look like. Unlike the LN version,
    the syntax does not distinguish between bound and free
    variables and abstractions include the name of binding
    variables.  *)

(*************************************************************)
(** * Imports                                                *)
(*************************************************************)

(** Some of our proofs are by induction on the *size* of
    terms. We'll use Coq's [omega] tactic to easily dispatch
    reasoning about natural numbers. *)
Require Export Omega.

(** We will use the [atom] type from the metatheory library to
    represent variable names. *)
Require Export Metalib.Metatheory.

(** Although we are not using LNgen, some of the tactics from
    its library are useful for automating reasoning about
    names (i.e. atoms).  *)
Require Export Metalib.LibLNgen.


(** Some fresh atoms *)
Notation X := (fresh nil).
Notation Y := (fresh (X :: nil)).
Notation Z := (fresh (X :: Y :: nil)).

Lemma YneX : Y <> X.
Proof.
  pose proof Atom.fresh_not_in (X :: nil) as H.
  apply elim_not_In_cons in H.
  auto.
Qed.


(*************************************************************)
(** * A nominal representation of terms                      *)
(*************************************************************)

Inductive n_exp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(** For example, we can encode the expression [(\X.Y X)] as below.  *)

Definition demo_rep1 := n_abs X (n_app (n_var Y) (n_var X)).

(** For example, we can encode the expression [(\Z.Y Z)] as below.  *)

Definition demo_rep2 := n_abs Z (n_app (n_var Y) (n_var Z)).


(** As usual, the free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  end.

(** The tactics for reasoning about lists and sets of atoms are useful here
    too. *)

Example fv_nom_rep1 : fv_nom demo_rep1 [=] {{ Y }}.
Proof.
  pose proof YneX.
  simpl.
  fsetdec.
Qed.

(** What makes this a *nominal* representation is that our
    operations are based on the following swapping function for
    names.  Note that this operation is symmetric: [x] becomes
    [y] and [y] becomes [x]. *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

(** The main insight of nominal representations is that we can
    rename variables, without capture, using a simple
    structural induction. Note how in the [n_abs] case we swap
    all variables, both bound and free.

    For example:

      (swap x y) (\z. (x y)) = \z. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:atom) (y:atom) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.


(** Because swapping is a simple, structurally recursive
    function, it is highly automatable using the [default_simp]
    tactic from LNgen library.

    This tactic "simplifies" goals using a combination of
    common proof steps, including case analysis of all disjoint
    sums in the goal. Because atom equality returns a sumbool,
    this makes this tactic useful for reasoning by cases about
    atoms.

    For more information about the [default_simp] tactic, see
    [metalib/LibDefaultSimp.v].

    WARNING: this tactic is not always safe. It's a power tool
    and can put your proof in an irrecoverable state. *)

Example swap1 : forall x y z, x <> z -> y <> z ->
    swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap2 : forall x y, x <> y ->
    swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap3 : forall x y, x <> y ->
     swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.


(** We define the "alpha-equivalence" relation that declares
    when two nominal terms are equivalent (up to renaming of
    bound variables).

    Note the two different rules for [n_abs]: either the
    binders are the same and we can directly compare the
    bodies, or the binders differ, but we can swap one side to
    make it look like the other.  *)

Inductive aeq : n_exp -> n_exp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y ->
     x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2').

Hint Constructors aeq.


Example aeq1 : forall x y, x <> y -> aeq (n_abs x (n_var x)) (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

(*************************************************************)
(** ** Properties about swapping                             *)
(*************************************************************)


(** Now let's look at some simple properties of swapping. *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.

(** Demo: We will need the next two properties later in the tutorial,
    so we show that even though there are many cases to consider,
    [default_simp] can find these proofs. *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  (* WORKED IN CLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 
Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  (* WORKED IN CLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 
(*************************************************************)
(** ** Exercises                                             *)
(*************************************************************)


(** *** Recommended Exercise: [swap] properties

    Prove the following properties about swapping, either
    explicitly (by destructing [x == y]) or automatically
    (using [default_simp]).  *)

Ltac swapped := simpl; unfold swap_var; default_simp.

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  induction t; swapped.
Qed.

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
  induction t; swapped.
Qed.

(** *** Challenge exercises: equivariance

    Equivariance is the property that all functions and
    relations are preserved under swapping.  Show that this
    holds for the various functions and relations below.

    (Hint: [default_simp] will be slow and sometimes
    ineffective on *some* of these properties. If it puts
    you in an dead-end state, you'll need to prove the
    lemm another way. *)

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  swapped.
Qed.

Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  induction t; simpl; intros.
  - now rewrite swap_var_equivariance.
  - now rewrite <- swap_var_equivariance, <- IHt.
  - now rewrite <- IHt1, <- IHt2.
Qed.

Lemma notin_fv_nom_equivariance : forall x0 x y t ,
  x0 `notin` fv_nom t ->
  swap_var x y x0  `notin` fv_nom (swap x y t).
Proof.
  induction t; simpl; intros.
  - swapped.
  - apply notin_remove_1 in H.
    destruct H; subst; fsetdec.
  - fsetdec.
Qed.

(* HINT: For a helpful fact about sets of atoms, check AtomSetImpl.union_1 *)

Lemma in_fv_nom_equivariance : forall x y x0 t,
  x0 `in` fv_nom t ->
  swap_var x y x0 `in` fv_nom (swap x y t).
Proof.
  induction t; simpl; intros.
  - swapped; fsetdec.
  - apply remove_iff in H; destruct H.
    apply AtomSetImpl.remove_2; auto.
    swapped.
  - apply AtomSetImpl.union_1 in H.
    destruct H; fsetdec.
Qed.

(*************************************************************)
(** * An abstract machine for cbn evaluation                 *)
(*************************************************************)

(** The advantage of named terms is an efficient operational
    semantics! Compared to LN or de Bruijn representation, we
    don't need always need to modify terms (such as via open or
    shifting) as we traverse binders. Instead, as long as the
    binder is "sufficiently fresh" we can use the name as is,
    and only rename (via swapping) when absolutely
    necessary. *)

(** Below, we define an operational semantics based on an
    abstract machine. As before, it will model execution as a
    sequence of small-step transitions. However, transition
    will be between _machine configurations_, not just
    expressions.

    Our abstract machine configurations have three components

    - the current expression being evaluated the heap (aka
    - environment): a mapping between variables and expressions
    - the stack: the evaluation context of the current
    - expression

    Because we have a heap, we don't need to use substitution
    to define our semantics. To implement [x ~> e] we add a
    definition that [x] maps to [e] in the heap and then look
    up the definition when we get to [x] during evaluation.  *)


Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition configuration := (heap * n_exp * stack)%type.

(** The (small-step) semantics is a _function_ from
    configurations to configurations, until completion or
    error. *)

Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.

Definition isVal (t : n_exp) :=
  match t with
  | n_abs _ _ => true
  | _         => false
  end.

Definition machine_step (avoid : atoms) (c : configuration) : Step configuration :=
  match c with
    (h, t, s) =>
    if isVal t then
      match s with
      | nil => Done _
      | n_app2 t2 :: s' =>
        match t with
        | n_abs x t1 =>
          (* if the bound name [x] is not fresh, we need to rename it *)
          if AtomSetProperties.In_dec x avoid  then
            let (y,_) := atom_fresh avoid in
             TakeStep _ ((y,t2)::h, swap x y t1, s')
          else
            TakeStep _ ((x,t2)::h, t1, s')
        | _ => Error _ (* non-function applied to argument *)
        end
      end
    else match t with
         | n_var x => match get x h with
                     | Some t1 => TakeStep _ (h, t1, s)
                     | None    => Error _ (* Unbound variable *)
                     end
         | n_app t1 t2 => TakeStep _ (h, t1, n_app2 t2 :: s)
         | _ => Error _ (* unreachable (value in nonValueStep) *)
         end
  end.

Definition initconf (t : n_exp) : configuration := (nil,t,nil).


(** Example: evaluation of  "(\y. (\x. x) y) 3"

<<
     machine                                       corresponding term

      {}, (\y. (\x. x) y) 3, nil                   (\y. (\x. x) y) 3
  ==> {}, (\y. (\x. x) y), n_app2 3 :: nil         (\y. (\x. x) y) 3
  ==> {y -> 3}, (\x.x) y, nil                      (\x. x) 3
  ==> {y -> 3}, (\x.x), n_app2 y :: nil            (\x. x) 3
  ==> {x -> y, y -> 3}, x, nil                     3
  ==> {x -> y, y -> 3}, y, nil                     3
  ==> {x -> y, y -> 3}, 3, nil                     3
  ==> Done
>>

(Note that the machine takes extra steps compared to the
substitution semantics.)

We will prove that this machine implements the substitution
semantics in the next section.

*)

(** ** Recommended Exercise [values_are_done]

    Show that values don't step using this abstract machine.
    (This is a simple proof.)
*)

Lemma values_are_done : forall D t,
    isVal t = true -> machine_step D (initconf t) = Done _.
Proof.
  induction t; auto; discriminate.
Qed.

(*************************************************************)
(** * Size based reasoning                                   *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (t : n_exp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  end.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. *)

(* Note: This version does not use a fuel based definition for a helper, but
   directly employs the fact that size gives us a well-founded ordering. This
   does make some later proofs more difficult, so it's doubtful that this is
   much of an improvement.

   We use [Fix] here directly because it allows us to use [Fix_eq] in the
   proofs that immediately follow. Both [Function] and [Program Fixpoint]
   generate definitions with too much complexity to allow us to "unroll" the
   fixed point by a single iteration. *)

Program Definition subst (u :n_exp) (x:atom) : n_exp -> n_exp :=
  Fix (well_founded_ltof n_exp size)
      (fun (_ : n_exp) => n_exp)
      (fun t rec =>
         match t with
         | n_var y =>
           if (x == y) then u else t
         | n_abs y t1 =>
           if (x == y) then t
           else
             (* rename to avoid capture *)
             let (z,_) := atom_fresh (fv_nom u `union` fv_nom t
                                               `union` {{x}}) in
             n_abs z (rec (swap y z t1) _)
         | n_app t1 t2 =>
           n_app (rec t1 _) (rec t2 _)
         end).
Next Obligation. unfold ltof; rewrite swap_size_eq; auto. Defined.
Next Obligation. unfold ltof; simpl; omega. Defined.
Next Obligation. unfold ltof; simpl; omega. Defined.

(** ** Challenge Exercise [subst]

    Use the definitions above to prove the following results about the
    nominal substitution function.  *)

(* Note: All these definitions follow a precise form: Proving that the lemma
   statement is exactly the definition of "one step" of the fixed-point. This
   is why they have identical proof scripts. *)

Lemma subst_n_var u x y :
  subst u x (n_var y) = if x == y then u else n_var y.
Proof.
  unfold subst.
  rewrite Fix_eq; auto.
  intros.
  destruct x0; auto.
    destruct (x == x0); auto.
    destruct (atom_fresh _); auto;
    rewrite !H; auto.
  rewrite !H; auto.
Qed.

Lemma subst_n_abs u x y t :
  subst u x (n_abs y t) =
    if x == y
    then n_abs y t
    else
      let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t)
                                        `union` {{x}}) in
      n_abs z (subst u x (swap y z t)).
Proof.
  unfold subst.
  rewrite Fix_eq; auto.
  intros.
  destruct x0; auto.
    destruct (x == x0); auto.
    destruct (atom_fresh _); auto;
    rewrite !H; auto.
  rewrite !H; auto.
Qed.

Lemma subst_n_app u x t1 t2 :
  subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof.
  unfold subst.
  rewrite Fix_eq; auto.
  intros.
  destruct x0; auto.
    destruct (x == x0); auto.
    destruct (atom_fresh _); auto;
    rewrite !H; auto.
  rewrite !H; auto.
Qed.

(** ** Challenge Exercise [subst properties]

    Now show the following property by induction on the size of terms. *)

(* Note: If we use a regular [Lemma] statement here, the only thing we can
   induct on is [t], which leaves us with an induction hypthesis that is too
   weak, forcing us to prove the following:

     forall y, aeq (subst (n_var y) y t) t -> forall y, aeq (subst (n_var y) y
     (swap x x0 t)) (swap x x0 t)

   However, since we know that [swap x x0 t] is structurally the same size as
   [t], we don't care about swap here, and should be able to recurse directly.
   This is what the fuel-based version does, since the induction on [n] leaves
   [t] variable in the induction hypothesis. We can achieve the exact same
   hypothesis here by recursing on the lemma statement. To do this, however,
   we need to express that the recursive structure is over [size]. In the end,
   we're pretty much doing precisely what the fuel-based definition did, just
   confounded in the definition of [subst]. *)

Program Fixpoint subst_same t {measure (size t)} :
  forall y, aeq (subst (n_var y) y t) t :=
  match t with
  | n_var x => _
  | n_abs x t => _
  | n_app t1 t2 => _
  end.
Next Obligation.
  rewrite subst_n_var.
  default_simp.
Qed.
Next Obligation.
  rewrite subst_n_abs.
  default_simp.
    apply aeq_refl.
  destruct (x0 == x).
    subst.
    apply aeq_abs_same.
    rewrite swap_id.
    apply subst_same.
    omega.
  apply aeq_abs_diff; auto.
  apply subst_same.
  rewrite swap_size_eq.
  omega.
Qed.
Next Obligation.
  rewrite subst_n_app.
  apply aeq_app.
    apply subst_same; simpl; omega.
  apply subst_same; simpl; omega.
Qed.

Program Fixpoint subst_fresh_eq x t {measure (size t)} :
  forall u, x `notin` fv_nom t -> aeq (subst u x t) t :=
  match t with
  | n_var x0 => _
  | n_abs x0 t => _
  | n_app t1 t2 => _
  end.
Next Obligation.
  rewrite subst_n_var.
    default_simp.
  fsetdec.
Qed.
Next Obligation.
  simpl in H.
  rewrite subst_n_abs.
  default_simp.
    apply aeq_refl.
  destruct (x1 == x0).
    subst.
    rewrite swap_id.
    apply aeq_abs_same.
    apply subst_fresh_eq; fsetdec.
  apply aeq_abs_diff; auto.
  apply subst_fresh_eq; simpl.
    rewrite swap_size_eq; omega.
  replace x with (swap_var x0 x1 x).
    apply notin_fv_nom_equivariance.
    fsetdec.
  assert (x <> x1) by fsetdec.
  swapped.
Qed.
Next Obligation.
  simpl in H.
  rewrite subst_n_app.
  apply aeq_app.
    apply subst_fresh_eq; simpl.
      omega.
    fsetdec.
  apply subst_fresh_eq; simpl.
    omega.
  fsetdec.
Qed.
