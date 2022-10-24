(*******************************************************************)
Require Import Utf8.
Require Import List. Import ListNotations.
Require Import Arith.
Require Import Program Program.Wf.
Require Import Lia.
Require Import Coq.Lists.List Coq.Bool.Bool.
Scheme Equality for list.

(* Variables are v 0, v 1, v 2, and so on. *)
Inductive Var := v (i: nat).  Scheme Equality for Var.

(* Formulas in the basic language. *)
Inductive Formula0 :=  | Equal0 (x y: Var)
                       | Element0 (x y: Var)
                       | Set0 (x: Var)
                       | Bottom0
                       | Exist0 (x: Var) (φ: Formula0)
                       | If0 (φ ψ: Formula0).
(* Equal0 cannot be reduced to Element0 because of the atoms. *)
(* Set0 could be reduced to (a constant) Empty0, but it wouldn't
   be any simpler in Coq's language. *)

(* Derived notions, still considered to be in basic language. *)
Definition Not0 φ := If0 φ Bottom0.
Definition Or0 φ ψ := If0 (Not0 φ) ψ.
Definition And0 φ ψ := Not0 (Or0 (Not0 φ) (Not0 ψ)).
Definition Iff0 φ ψ := And0 (If0 φ ψ) (If0 ψ φ).
Definition All0 x φ := Not0 (Exist0 x (Not0 φ)).

(* To a variable v is assigned a type t. *)
Notation "v ↦ t" := (pair v t) (at level 60).
(* A block is a finite function from nat to nat,
   implemented as a list of pairs. It gives a typization for a
   block of interconnected variables. *)
Definition block := list (nat * nat).
(* A typization is Some list of blocks for a stratified formula,
   or None for a nonstratified one. *)
Definition Typization := option (list block).

(* Switch on equality of natural numbers. *)
Definition eq_ {T : Type} (i j : nat) (a b : T)
   := if beq_nat i j then a else b.

(* Lookup the type of (v i) in the block b. *)
Fixpoint find (i: nat) (b: block) : option nat := match b with
  | [] => None
  | (k ↦ t) :: b' => eq_ k i (Some t) (find i b')
  end.
Compute find 4 [(1,3);(4,7);(8,9)]. (* v 4 has type 7 here *)
Compute find 5 [(1,3);(4,7);(8,9)]. (* v 5 has no type here *)

(* Two blocks can be in different relationships according to their
   overlapping variables and their assigned types. *)
Inductive Alignment :=
  | Independent (* no overlap at all *)
  | Collision (* blocks are mutually inconsistent *)
  | Exact (* they agree on all the common variables *)
  | Shift1 (s: nat) (* first one can be shifted by s to be Exact *)
  | Shift2 (s: nat) (* second can be shifted by s to be Exact *).

(* How to align a block b so that v i has type t? *)
Definition align1 (i t : nat) (b : block) : Alignment :=
  match find i b with 
  | None => Independent
  | Some t' => match Nat.compare t t' with
               | Eq => Exact
               | Lt => Shift1 (t' - t)
               | Gt => Shift2 (t - t')
  end          end.

(* How to align two blocks. *)
Fixpoint alignblocks (b1 b2: block) : Alignment := match b1 with
  | [] => Independent
  | (i ↦ t) :: b3 => match align1 i t b2, alignblocks b3 b2 with
      | Independent, result | result, Independent => result
      | Exact, Exact => Exact
      | Shift1 s, Shift1 s' => eq_ s s' (Shift1 s) Collision
      | Shift2 s, Shift2 s' => eq_ s s' (Shift2 s) Collision
      | Exact, Shift1 s | Shift1 s, Exact => eq_ 0 s Exact Collision
      | Exact, Shift2 s | Shift2 s, Exact => eq_ 0 s Exact Collision
      | Shift1 s, Shift2 s' | Shift2 s, Shift1 s' =>
          eq_ 0 s (eq_ 0 s' Exact Collision) Collision
      | _, _ => Collision
  end end.
Compute alignblocks [(1,2);(3,4);(4,5)] [(2,6);(3,1);(4,2)].

(* Actually merge two (already aligned) blocks into one,
   keeping the variables sorted by their indices. *)
Program Fixpoint mergealigned (b1 b2: block)
  { measure (length b1 + length b2) } : block := match b1, b2 with 
    | [], _ => b2
    | _, [] => b1
    | (i ↦ t) :: b3, (i' ↦ t') :: b4 => match Nat.compare i i' with
        | Eq => (i ↦ t) :: mergealigned b3 b4
        | Lt => (i ↦ t) :: mergealigned b3 b2
        | Gt => (i' ↦ t') :: mergealigned b1 b4
    end end.
Solve All Obligations with (program_simpl; cbn; lia).
Compute mergealigned [(1,2);(3,4)] [(2,6);(3,4);(4,1)].

(* Actually shift the types in block b by s *)
Fixpoint shiftblock (b: block) (s: nat) : block := match b with
  | [] => nil
  | (k ↦ t) :: b' => (k ↦ t + s) :: shiftblock b' s
  end.

(* In order to merge a block b1 with a list of blocks tp, we
   classify the blocks in tp according to their alignment with b1. *)
Fixpoint merge1 (b1: block) (tp: list block): Typization := (*bug?*)
  match tp with
  | [] => Some [b1]
  | b2 :: bs' => match merge1 b1 bs' with
                 | None => None
                 | Some m => match alignblocks b1 b2 with
         | Collision => None
         | Independent => Some (b2 :: m)
         | Exact => Some [mergealigned b1 b2]
         | Shift1 s => Some [mergealigned (shiftblock b1 s) b2]
         | Shift2 s => Some [mergealigned b1 (shiftblock b2 s)]
  end    end     end.
Compute merge1 [(0,1); (1,1); (3,1)] [].
Compute merge1 [(0,1)] [[(0,1)]].
Compute merge1 [(0,1); (1,1); (3,1)] [[(0,1); (1,1)]].

(* Merging two lists of blocks b1 and b2,
   by merging one by one block from b1 into b2. *)
Fixpoint mergeAll (b1 b2 : list block) : Typization :=
  match b1 with | [] => Some b2
                | b :: b1' => match mergeAll b1' b2 with
                              | Some tp => merge1 b tp
                              | None => None
  end                         end.

(* Calculating the typization of any formula in basic language. *)
Fixpoint typization (φ : Formula0) : Typization :=
  match φ with
  | Equal0 (v i) (v j) => match Nat.compare i j with
                          | Eq => Some [[i ↦ 1]]
                          | Lt => Some [[i ↦ 1; j ↦ 1]]
                          | Gt => Some [[j ↦ 1; i ↦ 1]]
                          end
  | Element0 (v i) (v j) => match Nat.compare i j with
                            | Eq => None
                            | Lt => Some [[i ↦ 1; j ↦ 2]]
                            | Gt => Some [[j ↦ 2; i ↦ 1]]
                            end
  | Set0 (v i) => Some [[i ↦ 1]]
  | Bottom0 => Some []
  | Exist0 (v i) ψ => match typization ψ with
                      | Some b => merge1 [i ↦ 1] b
                      | None => None
                      end
  | If0 φ ψ => match typization φ, typization ψ with
               | Some b1, Some b2 => mergeAll b1 b2
               | _, _ => None
  end          end.

(* Now for extending our language. *)
Inductive Term :=
  | var (v : Var)
  | abs (v : Var) (φ : Formula0).

Inductive Formula1 := 
  | Equal1 (x y: Term)
  | Element1 (x y: Term)
  | Set1 (x: Term)
  | Bottom1
  | Exist1 (x: Var) (φ: Formula1)
  | If1 (φ ψ: Formula1).

(* In order to substitute,
   we must first find (an index of) a fresh variable. *)
Fixpoint max_var_basic (φ: Formula0) : nat :=
  match φ with
  | Equal0 (v i) (v j) | Element0 (v i) (v j) => max i j
  | Set0 (v i) => i
  | Bottom0 => 0 (* better: find fresh directly *)
  | Exist0 (v i) ψ => max i (max_var_basic ψ)
  | If0 φ1 φ2 => max (max_var_basic φ1) (max_var_basic φ2)
  end.

Definition max_var_term (t: Term) : nat :=
  match t with | var (v i) => i
               | abs (v i) ψ => max i (max_var_basic ψ)
  end.
Definition max_var_terms (t1 t2: Term) :=
  max (max_var_term t1) (max_var_term t2).

(* Rename variable x to v in formula φ *)
Definition rename_var (x v y: Var) := if Var_beq x y then v else y.

Fixpoint rename_basic (x: Var) (v: Var) (φ: Formula0) : Formula0 :=
  match φ with
  | Equal0 a b => Equal0 (rename_var x v a) (rename_var x v b)
  | Element0 a b => Element0 (rename_var x v a) (rename_var x v b)
  | Set0 a => Set0 (rename_var x v a)
  | Bottom0 => Bottom0
  | Exist0 a ψ => Exist0 (rename_var x v a) (rename_basic x v ψ)
  | If0 φ ψ => If0 (rename_basic x v φ) (rename_basic x v ψ)
  end.

Fixpoint max_var_extended (φ: Formula1) : nat :=
  match φ with
  | Equal1 t1 t2 | Element1 t1 t2 => max_var_terms t1 t2
  | Set1 t => max_var_term t
  | Bottom1 => 0 (* again *)
  | Exist1 (v i) ψ => max i (max_var_extended ψ)
  | If1 φ ψ => max (max_var_extended φ) (max_var_extended ψ)
  end.

Fixpoint complexity (φ: Formula0) : nat := match φ with
  | Equal0 _ _ | Element0 _ _ | Set0 _ | Bottom0 => 1
  | Exist0 x ψ => S (complexity ψ)
  | If0 φ1 φ2 => S (complexity φ1 + complexity φ2)
  end.

Lemma complexity_rename: ∀ φ x y,
  complexity (rename_basic x y φ) = complexity φ.
Proof. intros φ x y. induction φ; cbn; lia. Qed.
#[local] Hint Rewrite complexity_rename :core.

Definition freshify a φ := rename_basic a (v(S(max_var_basic φ))) φ.
Definition fresh_var_extended φ := v (S (max_var_extended φ)).

(* Substitute (free instances of) variable x
   with variable u in basic formula φ. *)
Program Fixpoint subst (x: Var) (u: Var) (φ: Formula0)
                 {measure (complexity φ)} : Formula0 :=
  match φ with
  | Equal0 _ _ | Element0 _ _ | Set0 _ => rename_basic x u φ
  | Bottom0 => Bottom0
  | If0 φ ψ => If0 (subst x u φ) (subst x u ψ)
  | Exist0 a ψ => if Var_beq a x then φ
                  else if Var_beq a u
                        then subst x u (freshify a ψ)
                        else Exist0 a (subst x u ψ)
  end.
Solve All Obligations with
  program_simpl;
  try (unfold freshify; rewrite complexity_rename);
  cbn; lia.

(* Helpful functions halfway between Element0/1 and Equal0/1. *)
Definition element (x: Var) (t: Term): Formula0 := match t with
  | var y => Element0 x y
  | abs z φ => subst z x φ
end.
Definition equal (x: Var) (t: Term): Formula0 := match t with
  | var y => Equal0 x y
  | abs z φ => And0 (All0 z (Iff0 (Element0 z x) φ)) (Set0 x)
end.

(* Eliminate abstraction terms. *)
Fixpoint tobasic (φ: Formula1): Formula0 := 
  let z := fresh_var_extended φ in match φ with
    | Equal1 (var x) (var y) => Equal0 x y
    | Equal1 a b => All0 z (Iff0 (element z a) (element z b))
    | Element1 (var x) b => element x b
    | Element1 a b => Exist0 z (And0 (element z b) (equal z a))
    | Set1 (var x) => Set0 x
    | Set1 a => Exist0 z (equal z a)
    | Bottom1 => Bottom0
    | Exist1 x φ => Exist0 x (tobasic φ)
    | If1 φ ψ => If0 (tobasic φ) (tobasic ψ)
  end.

(* Notations *)
Declare Custom Entry nff. Declare Custom Entry nft.
Declare Scope nff_scope. Declare Scope nft_scope.
Delimit Scope nff_scope with nff. Delimit Scope nft_scope with nft.
Open Scope nff_scope. Open Scope nft_scope.

Notation "\x" := (var (v 0)) (in custom nft) :nft_scope.
Notation "\y" := (var (v 1)) (in custom nft) :nft_scope.
Notation "\z" := (var (v 2)) (in custom nft) :nft_scope.
Notation "\t" := (var (v 3)) (in custom nft) :nft_scope.
Notation "\u" := (var (v 4)) (in custom nft) :nft_scope.
Notation "\v" := (var (v 5)) (in custom nft) :nft_scope.
Notation "\w" := (var (v 6)) (in custom nft) :nft_scope.
Notation "\s" := (var (v 7)) (in custom nft) :nft_scope.

Notation "$[ e ]" := e (e custom nff).
Notation "( x )" := x (in custom nff).
(* Notation "( x )" := x (in custom nft). *)
Notation "{ x }" := x (in custom nff, x constr).
Notation "\{ x }" := x (in custom nft, x constr).

Notation "x = y" := (Equal1 x y)
  (in custom nff at level 30, x custom nft, y custom nft) :nff_scope.
Notation "x ∈ y" := (Element1 x y)
  (in custom nff at level 30, x custom nft, y custom nft) :nff_scope.
Notation "set( x )" := (Set1 x)
  (in custom nff at level 20, x custom nft) :nff_scope.
Notation "⊥" := Bottom1 (in custom nff at level 0).
Notation "φ → ψ" := (If1 φ ψ) (in custom nff at level 50,
  right associativity, φ custom nff, ψ custom nff) :nff_scope.
Notation "∃ x φ" := (Exist1 x φ)
  (in custom nff at level 30, x custom nft, φ custom nff) :nff_scope.

Notation "¬ φ" := $[{φ} → ⊥]
  (in custom nff at level 40, φ custom nff) :nff_scope.
Notation "φ ∨ ψ" := $[¬ {φ} → {ψ}]
  (in custom nff at level 50) :nff_scope.
Notation "φ ∧ ψ" := $[¬({φ} → ¬ {ψ})]
  (in custom nff at level 40) :nff_scope.
Notation "φ ↔ ψ" := $[({φ} → {ψ}) ∧ ({ψ} → {φ})]
  (in custom nff at level 60) :nff_scope.
Notation "∀ x φ" := $[¬ ∃ \{x} ¬ {φ}]
  (in custom nff at level 30, x custom nft) :nff_scope.
Notation "( ∀ x ∈ S ) φ" := $[∀ \{x} (\{x} ∈ \{S} → {φ})]
  (in custom nff at level 29,
  x custom nft, S custom nft, φ custom nff) :nff_scope.
Notation "( ∃ x ∈ S ) φ" := $[∃ \{x} (\{x} ∈ \{S} ∧ {φ})]
  (in custom nff at level 29,
  x custom nft, S custom nft, φ custom nff) :nff_scope.
Notation "{ x | φ }" := (match x with
  | var y => abs y (tobasic φ)
  | _ => let z := fresh_var_extended φ in
        abs z (tobasic $[ {φ} ∧ {Equal1 (var z) x} ])
  end) (in custom nft at level 25, x custom nft, φ custom nff).

Check $[ \x ∈ \y ∧ \y ∈ \x ].
Check $[{\x | \x ∈ \z} = \z].
Definition tm := (abs (v 12) (Equal0 (v 12) (v 15))).
Compute tobasic $[ \y = \x → \x = \t ].
Compute tobasic $[ \y = \x → \x = \{tm} ].
Compute typization (tobasic $[ \y = \x → \x = \t ]).
Compute typization (tobasic $[ (\y ∈ \x → \w = \t) ↔ (\t = \x) ]).
Compute typization (tobasic $[ \x ∈ \y → \y = \x ]).
Compute typization (tobasic $[ set(\x) → \z ∈ \x ]).
