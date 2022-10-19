Require Import ZBase String Sint63 List.
Local Open Scope sint63_scope.
Local Open Scope string_scope.

(* In my version of cfwae numbers are 63-bit signed integers. I'm not
   implementing a numeric tower *)

Inductive primop : Set := P_Add | P_Sub | P_Mul | P_Div.

Inductive cfwae : Set :=
| Num : int -> cfwae
| Primop : primop -> cfwae -> cfwae -> cfwae
| Var : string -> cfwae
| If0 : cfwae -> cfwae -> cfwae -> cfwae
| With : list (string * cfwae) -> cfwae -> cfwae
| Fun : list string -> cfwae -> cfwae
| App : cfwae -> list cfwae -> cfwae.

Coercion Var : string >-> cfwae.
Coercion Num : int >-> cfwae.

(* Define capture-avoiding substitution *)
Fixpoint subst (e : cfwae) (v : string) (e0 : cfwae) :=
  match e0 with
  | Num x => Num x
  | Primop op e1 e2 => Primop op (subst e v e1) (subst e v e2)
  | Var x => if (x =? v) then e else Var x
  | If0 c t f => If0 (subst e v c) (subst e v t) (subst e v f)
  | With bs body =>
      With (map (fun ve => (fst ve, subst e v (snd ve))) bs)
(if existsb (fun xe => fst xe =? v) bs
 then body else subst e v body)
  | Fun xs body =>
      (if existsb (fun x => x =? v) xs
       then body
       else subst e v body)
  | App f es => App (subst e v f) (map (subst e v) es)
  end.

Local Close Scope string_scope.

Definition subst_all (bs : list (string * cfwae)) :=
  fold_left (fun body ve => subst (snd ve) (fst ve) body) bs.

(* The semantics are primops are simple, but we give it as a relation because we
   must avoid divison by zero. *)
Definition step_primop (p : primop) (x y z : int) : Prop :=
  match p with
  | P_Add => add x y = z
  | P_Sub => sub x y = z
  | P_Mul => mul x y = z
  | P_Div => y <> 0 /\ div x y = z
  end.

(* To enforce the correct evaluation order (strict), we introduce the notion of
   a value (all expressions must be values before substitution) *)
Inductive value : cfwae -> Prop :=
| V_Num : forall x, value (Num x)
| V_Fun : forall xs body, value (Fun xs body).

(* Small-step semantics.  Note that we enforce left-to-right evaluation order
   even though we have no side effects (yet?) *)
Inductive step : cfwae -> cfwae -> Prop :=

| S_Primop_l : forall op e1 e1' e2,
    e1 --> e1' -> Primop op e1 e2 --> Primop op e1' e2
| S_Primop_r : forall op v1 e2 e2',
    e2 --> e2' -> Primop op (Num v1) e2 --> Primop op (Num v1) e2'
| S_Primop : forall op v1 v2 v,
    step_primop op v1 v2 v
    -> Primop op (Num v1) (Num v2) --> Num v

| S_If0_c : forall ec ec' et ef, ec --> ec' -> If0 ec et ef --> If0 ec' et ef
| S_If0_t : forall et ef, If0 0 et ef --> et
| S_If0_f : forall v et ef, v <> 0 -> If0 v et ef --> et

(* Evaluate bindings first to last.  We do this by allowing stepping only once
   every preceding binding is a value. *)
| S_With_b : forall bs1 v e e' bs2 body,
    Forall (fun ve => value (snd ve)) bs1
    -> e --> e'
    -> With (bs1 ++ (v, e) :: bs2) body --> With (bs1 ++ (v, e') :: bs2) body
(* Once every binding is a value, substitute them into the body, but only if
   there are no duplicate bindings *)
| S_With_body : forall bs body,
    Forall (fun ve => value (snd ve)) bs
    -> NoDup (map fst bs)
    -> With bs body --> subst_all bs body

(* Evaluate the function value and then arguments left to right in a similar
   way. *)
| S_App_fun : forall f f' es, f --> f' -> App f es --> App f' es
| S_App_arg : forall f es1 e e' es2,
    value f
    -> Forall value es1
    -> e --> e'
    -> App f (es1 ++ e :: es2) --> App f (es1 ++ e' :: es2)
(* If the function evaluates to a lambda, and we have the right number of
   arguments, substitute them in *)
| S_App : forall vs body es,
    length vs = length es
    -> App (Fun vs body) es --> subst_all (combine vs es) body

where "a --> b" := (step a b).

(* ------------------------------------------------- *)
(* Semantics done.  Implementation from here on out. *)
(* ------------------------------------------------- *)

Require Import Int OrderedTypeEx FMapAVL.

Module Env := FMapAVL.Make (String_as_OT).

Inductive err :=
| E_Unbound : string -> err
| E_ExpectedNum
| E_ExpectedFun
| E_DuplicateBinding
| E_ArgNum
| E_Div0.

(* I'm not digging into the guts of FMapAVL to figure out why coq won't see
   through the record *)
#[bypass_check(positivity)]
Inductive runtime_val :=
| RV_Num : int -> runtime_val
| RV_Closure : Env.t runtime_val -> list string -> cfwae -> runtime_val.

CoInductive itree (E : Type -> Type) (R : Type) :=
| Ret : R -> itree E R
| Tau : itree E R -> itree E R
| Vis : forall {A : Type} (e : E A) (k : A -> itree E R), itree E R.
Arguments Ret {E R}.
Arguments Tau {E R}.
Arguments Vis {E R A}.

Definition bind {E R S} (t : itree E R) (k : R -> itree E S) :=
  (cofix bind_ u :=
     match u with
     | Ret x => k x
     | Tau t => Tau (bind_ t)
     | Vis e k => Vis e (fun x => bind_ (k x))
     end) t.

Definition trigger {E R} (e : E R) : itree E R :=
  Vis e Ret.

Definition throw {E : Type -> Type} {R} (e : E False) : itree E R :=
  Vis e (fun (x : False) => match x with end).

Notation "'let*' x '<-' e 'in' k" := (bind e (fun x => k))
                 (at level 200, x pattern, right associativity).

CoFixpoint iter {A B E} (body : A -> itree E (sum A B))
  : A -> itree E B :=
  fun a => let* ab <- body a in
        match ab with
        | inl a => Tau (iter body a)
        | inr b => Ret b
        end.

Definition mrec {D E} (rh : forall X, D X -> itree (fun T => sum (D T) (E T)) X) :
  forall {X}, D X -> itree E X :=
  fun R d => iter
(fun t : itree (fun X => sum (D X) (E X)) R =>
   match t with
   | Ret r => Ret (inr r)
   | Tau t => Ret (inl t)
   | Vis (inl d) k => Ret (inl (bind (rh _ d) k))
   | Vis (inr e) k => bind (Vis e (fun x => Ret x)) (fun x => Ret (inl (k x)))
   end) (rh _ d).

Require Import Extraction ExtrOcamlBasic ExtrOCamlInt63 ExtrOcamlNativeString.

Inductive eval_event : Type -> Type :=
| EV_Eval : Env.t runtime_val -> cfwae -> eval_event runtime_val.
Inductive runtime_event : Type -> Type :=
| EV_Err : err -> runtime_event False.

Definition interp_M := itree (fun T => sum (eval_event T) (runtime_event T)).

Definition r_err {A} (e : err) : interp_M A :=
  throw (inr (EV_Err e)).
Definition r_eval (env : Env.t runtime_val) (e : cfwae) : interp_M runtime_val :=
  trigger (inl (EV_Eval env e)).

Fixpoint r_eval_binds
(env acc : Env.t runtime_val) (vs : list string) (es : list cfwae) :
  interp_M (Env.t runtime_val) :=
  match vs, es with
  | nil, nil => Ret acc
  | _, nil => r_err E_ArgNum
  | nil, _ => r_err E_ArgNum
  | v :: vs, e :: es => let* e' <- r_eval env e in
                        r_eval_binds env (Env.add v e' acc) vs es
  end.

Definition eval_primop (p : primop) (n1 n2 : int) : interp_M runtime_val :=
  match p with
  | P_Add => Ret (RV_Num (add n1 n2))
  | P_Sub => Ret (RV_Num (sub n1 n2))
  | P_Mul => Ret (RV_Num (mul n1 n2))
  | P_Div =>
      if n2 =? 0
      then r_err E_Div0
      else Ret (RV_Num (div n1 n2))
  end.

Definition h_eval : forall X,
    eval_event X -> itree (fun T => sum (eval_event T) (runtime_event T)) X :=
  fun _ '(EV_Eval env e) =>
    match e with
    | Num x => Ret (RV_Num x)
    | Primop op e1 e2 =>
        let* x1 <- r_eval env e1 in
        let* x2 <- r_eval env e2 in
        match x1, x2 with
        | RV_Num n1, RV_Num n2 => eval_primop op n1 n2
        | _, _ =>  r_err E_ExpectedNum
        end
    | Var v =>
        match Env.find v env with
        | None => r_err (E_Unbound v)
        | Some x => Ret x
        end
    | If0 c t f =>
        let* cv <- trigger (inl (EV_Eval env c)) in
        match cv with
        | RV_Num x => if eqb x 0
                      then r_eval env t
                      else r_eval env f
        | _ => r_err E_ExpectedNum
        end
    | With bs body =>
        let* env' <- r_eval_binds env env (map fst bs) (map snd bs) in
        r_eval env' body
    | Fun vs body =>
        Ret (RV_Closure env vs body)
    | App f es =>
        let* fv <- r_eval env f in
        match fv with
        | RV_Closure captures vs body =>
            let* esv <- r_eval_binds env captures vs es in
            r_eval esv body
        | _ => r_err E_ExpectedFun
        end
    end.

Fixpoint check_nodup (l : list string) : bool :=
  match l with
  | nil => true
  | h :: t =>
      match List.find (String.eqb h) t with
      | None => check_nodup t
      | Some _ => false
     end
  end.

Fixpoint check (e : cfwae) : bool :=
  match e with
  | Primop _ e1 e2 => check e1 && check e2
  | If0 c t f => check c && check t && check f
  | With bs body => check_nodup (map fst bs) && check body
  | _ => true
  end.

Definition eval (e : cfwae) : itree runtime_event runtime_val :=
  if check e
  then mrec h_eval (EV_Eval (Env.empty _) e)
  else throw (EV_Err E_DuplicateBinding).

Extraction "interpreter.ml" eval.

(* ------------------------------------------------- *)
(* Proofs of correctness                             *)
(* ------------------------------------------------- *)

Require FMapFacts.
Module EnvProps := FMapFacts.Properties (Env).

Definition subst_env := Env.fold (fun v e => subst e v).

(* First, we need to establish the relationship between runtime_vals in the
   interpreter, and CFWAE terms in head normal form (no redexes except until
   lambda). *)
Reserved Notation "a ~ b" (at level 70).
Inductive state_inv : cfwae -> runtime_val -> Prop :=
(* Numbers are easy *)
| SI_Num : forall n, Num n ~ RV_Num n

(* Functions are harder: in the small step semantics, we substituted the
   evaluated function arguments directly into the body.  We have to equate those
   functions with closures where substituting the captured environment would
   result in the same thing.

   If we wanted to allow the interpreter to manipulate variable names, we would
   have to make this smart by allowing alpha-equivalent function bodies. *)
| SI_Fun : forall vs exprs env b1 b2,
    (* Relate each captured runtime_val with an expression to substitute. *)
    (forall v e rv, Env.MapsTo v e exprs -> Env.MapsTo v rv env -> e ~ rv)
    -> Env.fold (fun v e => subst e v) exprs b1 = b2
    -> Fun vs b1 ~ RV_Closure env vs b2
where "a ~ b" := (state_inv a b).

(* Reflexive, transitive closure of step relation *)
Reserved Notation "a -->* b" (at level 55).
Inductive multi_step : cfwae -> cfwae -> Prop :=
| MS_Refl : forall e, e -->* e
| MS_Step : forall e e' e'', e --> e' -> e' -->* e'' -> e -->* e''
where "a -->* b" := (multi_step a b).

Definition frob {E R} (i : itree E R) : itree E R :=
  match i with
  | Ret x => Ret x
  | Tau t => Tau t
  | Vis e k => Vis e k
  end.

(* Force coq to reduce a cofix *)
(* http://adam.chlipala.net/cpdt/html/Coinductive.html *)
Lemma frob_eq {E R} : forall (i : itree E R), i = frob i.
destruct i; reflexivity.
Qed.

Ltac frob := simpl; rewrite frob_eq; simpl.

(* wip *)
CoInductive simulates :
  cfwae -> Env.t runtime_val ->interp_M runtime_val -> Prop :=
| Sim_Val : forall e env rv, e ~ rv -> simulates e env (Ret rv)
| Sim_Step : forall e1 e2 e3 env1 env2 env3 rv k,
    e1 -->* e3
    -> simulates e2 env2 (Ret rv)
    -> simulates e3 env3 (k rv)
    -> simulates e1 env1 (Vis (inl (EV_Eval env2 e2)) k).
