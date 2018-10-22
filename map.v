Require Import Arith.

(* Set to represent things at each cell of map 
    - Obs represents obstacles as walls and boxes
    - Empty represents empty cells
    - Start represents the robot's start position *)

Inductive Things : Type :=
  | Empty : Things
  | Obs : Things
  | Start : Things
  | Unknow : Things.

Inductive rowmap : Type :=
  | nil : rowmap
  | cell : Things -> rowmap -> rowmap.

Notation "[ x ; .. ; y ]" := (cell x .. (cell y nil) ..).
Notation "[ ]" := nil.

Definition RawMap_test1 := [Obs;Start;Empty].

Inductive map: Type :=
  | null : map  
  | row : rowmap -> map -> map.

Definition RawMap_test2 := row [Obs;Obs;Obs;Obs;Obs] (row [Obs;Start;Empty;Empty;Obs] null).

Notation "{ x ; .. ; y }" := (row x .. (row y null) ..).
Notation "{ }" := null.

(*
Sample of map. Below has a natural representation of RoboMind.
  map:
  AAAAA   A, Q -> Obstacles
  A@  A   @ -> Start position
  A Q A
  AAAAA
*)

Definition RawMap :=
{
  [Obs;Obs;Obs;Obs;Obs];
  [Obs;Start;Empty;Empty;Obs];
  [Obs;Empty;Obs;Empty;Obs];
  [Obs;Obs;Obs;Obs;Obs]
}.

Definition fst (p : map) : Things :=
  match p with
  | row x y => match x with
                | cell x2 y2 => x2
                | [ ] => Unknow
               end
  | { } => Unknow
  end.

Compute (fst (RawMap)).










  