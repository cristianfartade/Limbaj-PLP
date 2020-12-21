Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import String.
Open Scope string_scope.

Inductive Var : Set :=
| variable : string -> Var.

Scheme Equality for Var.
Coercion variable : string >-> Var.

Definition Var_equality (var1 var2 : Var) : bool :=
  match var1,var2 with
  | variable x, variable y => if (eqb x y) 
                            then true
                            else false
  end. 

Compute Var_equality "aur" "aur".

(* Environment *)

Inductive Value :=
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| string_val: string -> Value.

Coercion nat_val : nat >-> Value.
Coercion bool_val : bool >-> Value.
Coercion string_val : string >-> Value.

Scheme Equality for Value.

Definition Env := Var -> Value.

Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x "variable")
    then nat_val 10
    else undef.

Definition empty_env : Env := fun var => undef.

Definition is_declared (x : Var) (env : Env) :=
  if (Value_beq (env x) undef)
  then false
  else true.

Compute env1 "variable".
Compute env1 "not_a_variable".
Compute is_declared "variable" env1.
Compute is_declared "ms" env1.

Definition update (env : Env)
           (x : Var) (v : Value) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Definition env2 := env1 [ 1045 /' "n" ].
Compute (env2 "n").


(*ArithExp*)

Inductive ArithExp :=
| avar : Var -> ArithExp
| anum : Value -> ArithExp
| aplus : ArithExp -> ArithExp -> ArithExp
| aminus : ArithExp -> ArithExp -> ArithExp
| amul : ArithExp -> ArithExp -> ArithExp
| adiv : ArithExp -> ArithExp -> ArithExp
| aperc : ArithExp -> ArithExp -> ArithExp.


Coercion anum : Value >-> ArithExp.
Coercion avar : Var >-> ArithExp.
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 40).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (aperc A B) (at level 40).

(*Vectorul este implementat cu ajutorul List*)

Definition Vector := list nat.

Definition length (vect : Vector) : nat := List.length vect.
Notation "Size( V )" := (length V) (at level 50).

Definition last_el (vect : Vector) := List.last vect.
Notation "Last( V )" := (last_el V ) (at level 50). 

Definition add_first (vect : Vector) (valoare : nat): Vector := valoare :: vect. 
Notation "Add( V , Val )" := (add_first V Val) (at level 50). 

Definition remove_ls (vect : Vector) : Vector := List.removelast vect.
Notation "RemoveLast( V )" := (remove_ls V) (at level 50).

Definition index (vect : Vector) (valoare : nat) : nat := List.nth valoare vect 0.
Notation " V [* I *]" := (index V I) (at level 40).



Check [1;2;3].
Compute Size( [1;32;11;9] ).
Compute Last( [1;22;13;91] ).

Definition Vector1 := [1;32;11;9].
Definition Vector2 := Add( Vector1 , 100 ).
Compute Vector2.
Compute Vector2 [* 3 *].
Compute RemoveLast( [1;32;11;9] ).

(*BoolExp*)
Inductive BoolExp :=
| btrue : BoolExp
| bfalse : BoolExp
| bvar   : Var -> BoolExp
| bgt    : ArithExp -> ArithExp -> BoolExp
| bge    : ArithExp -> ArithExp -> BoolExp
| beq    : ArithExp -> ArithExp -> BoolExp
| blt    : ArithExp -> ArithExp -> BoolExp
| ble    : ArithExp -> ArithExp -> BoolExp
| bnot   : BoolExp -> BoolExp
| band   : BoolExp -> BoolExp -> BoolExp
| bxor   : BoolExp -> BoolExp -> BoolExp
| bor    : BoolExp -> BoolExp -> BoolExp.

Notation "A >' B" := (bgt A B)(at level 61).
Notation "A >=' B" := (bge A B)(at level 61).
Notation "A ==' B" := (beq A B)(at level 59).
Notation "A <' B" := (blt A B)(at level 60).
Notation "A <=' B" := (ble A B)(at level 60).


(*StringExp*)

Inductive StringExp :=
| str_var : Var -> StringExp 
| str_comp : StringExp -> StringExp -> StringExp
| str_concat : StringExp -> StringExp -> StringExp
| str_len : StringExp -> StringExp.

Coercion str_var : Var >-> StringExp.

Notation "strcompare( Str1 , Str2 )" := (str_comp Str1 Str2) (at level 70).
Notation "strconcat( Str1 , Str2 )" := (str_concat Str1 Str2) (at level 50). 
Notation "strlength( Str1 )" := (str_len Str1) (at level 50). 

Compute strcompare("abcd" , "abcd").


(*Stmt*)

Inductive Stmt :=
(*Declarari si assignments*)
| Nat_decl : Var -> Stmt
| Bool_decl : Var -> Stmt
| String_decl : Var -> Stmt
| Vector_decl : Vector -> Stmt
| nat_assignment : Var -> ArithExp -> Stmt
| string_assignment : Var -> StringExp -> Stmt
| bool_assignment : Var -> BoolExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
(*Structura implementata la nivel de Stmt - notatie*)
| struct : Var -> Stmt -> Stmt
(*Switch*)
| case : ArithExp -> Stmt -> Stmt
| switch : ArithExp -> Stmt -> Stmt
(*I/O*)
| print : string -> Stmt
| scan : Var -> string -> Stmt
(*Instructiuni repetitive si conditionale*)
| ifthen : BoolExp -> Stmt ->Stmt
| ifthenelse : BoolExp -> Stmt -> Stmt -> Stmt 
| while : BoolExp -> Stmt -> Stmt
| for_ : Stmt -> BoolExp -> Stmt -> Stmt -> Stmt.

Inductive Function :=
| call : Stmt -> ArithExp -> Function
| f_return : Value -> Function.

Notation " C ([ A ]) " := (call C A)(at level 80).
Notation "'Return' # R " := (f_return R)(at level 80).

Check Return # 2.

Inductive Format :=
| func_form : Function -> Format
| stmt_form : Stmt -> Format
| func : Function -> Stmt -> Function -> Format
| form_divider : Format -> Format -> Format.
Notation "F1 '$' F2" := (form_divider F1 F2) (at level 99).
Coercion stmt_form : Stmt >-> Format.
Coercion func_form : Function >-> Format.

Notation "-nat- V" := (Nat_decl V) (at level 70).
Notation "-bool- V" := (Bool_decl V) (at level 70).
Notation "-string- V" := (String_decl V) (at level 70).
Notation "-vector- V" := (Vector_decl V) (at level 70).
Notation "'struct' ( NUME ){ S }" := (struct NUME S) (at level 40).
Notation "X ::= A" := (nat_assignment X A) (at level 80).
Notation "[ X ] ::= A" := (bool_assignment X A) (at level 80).
Notation "copy_string( X , A )" := (string_assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation " 'print' \\ S " := (print S) (at level 70).
Notation " 'scan' \\ V \\ S  " := (scan V S) (at level 70).
Notation " 'case' ( A )  S  " := (case A S)  (at level 90).
Notation "'switch' ( A ) { S } " := (switch A S)  (at level 90).
Notation " % Call 'begin_' S R 'end_' % " := (func Call S R)(at level 97).
Notation "'If' ( B ) 'Then' S1 'Else' S2 " := (ifthenelse B S1 S2) (at level 92).
Notation "'If' ( B ) 'IfThen' S1 " := (ifthen B S1) (at level 92).
Notation "'while' ( Cond ) { S }" := (while Cond S)(at level 97).
Notation "'for_' ( I ; Cond ; Pas ) { S }" := (for_ I Cond Pas S)(at level 97).

Check  % -nat- "func" ([ 2 ]) 
      begin_

        for_ ("i" ::=2 ; "i" <=' 6 ; "i" ::= "i" +' 1) {
          "x" ::= "x" +' "i" 
     
          }
        Return # 1
      end_ %.
       
        
Check -string- "sir".
Check print \\ "sir afisat".
Check scan \\ "variabila" \\ "sir citit".
Check [ "bool_v" ] ::= bfalse.
Check copy_string( "sir" , "ana are mere").
Check "n" ::= 10.
Check "n" ::= 10 ;; "x" ::= 0 ;; "i" ::= 0.
Check while ("i" <=' "n" +' 1) {
            "x" ::= "x" +' "i" ;;
            "i" ::= "i" +' 1
      }.
Check for_ ("i" ::=3 ; "i" <=' 3 ; "i"::="i" +' 1) {
            "x" ::= "x" +' "i" ;;
            "aa" ::= "aa" +' 1
      }.

Definition ex1 :=
  struct ("cerc"){
  -nat- "diametru" ;;
  -string- "denumire" ;;
  -bool- "plin"
  }.

Definition ex2 :=
  "x" ::= 10 ;;
   for_ ("i" ::=2 ; "i" <=' 6 ; "i" ::= "i" +' 1) {
          "x" ::= "x" +' "i" 
     
  }.

Definition ex3 :=
  "n" ::= 10 ;;
  -vector-[11;23] ;;
  If("n"<='9)
    Then "i" ::= 2
    Else "i" ::= 1;;
  "sum" ::= 0 ;; 
  while ("i" <=' "n") {
          "sum" ::= "sum" +' "i" ;;
          "i" ::= "i" +' 1
  }.

Definition ex4 :=
  switch (6) 
  {
  case(1)
  "x" ::= 1 ;;
  case(2)
  "x" ::= 2 ;;
  case(3)
  "x" ::= 3
  }.

Definition ex5 :=
  -bool-"global_var"  
$
  -vector-[] 
$
  % -nat- "func" ([ 2 ]) 
      begin_

        for_ ("i" ::=2 ; "i" <=' 6 ; "i" ::= "i" +' 1) {
          "x" ::= "x" +' "i" 
     
          }
        Return # 1
      end_
  %
$
  % -bool- "bool_func" ([ true ])
    begin_
      If("n"<='9)
        Then "i" ::= 2
        Else "i" ::= 1
      Return # 1
    end_
  %
.


