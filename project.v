Module Map.

Require Import Arith.
Require Import Vector.
Require Import Bool.
Import VectorNotations.
Require Import List.
Require Import PeanoNat.

(* Set to represent things at each cell of map 
    - Obs represents obstacles as walls and boxes
    - Empty represents empty cells
    - Start represents the robot's start position *)

Inductive Things : Type :=
  | Empty : Things
  | Obs : Things
  | Start : Things
  | Final: Things
  | Unknow : Things.

Inductive rowmap : Type :=
  | empty : rowmap
  | c : Things -> rowmap -> rowmap.

Notation "x :: l" := (c x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (c x .. (c y empty) ..).
Notation "[ ]" := empty.


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

Definition raw_map :=
{
  [Final;Empty;Obs;Obs;Obs];
  [Obs;Start;Empty;Empty;Obs];
  [Obs;Empty;Obs;Empty;Obs];
  [Obs;Obs;Obs;Obs;Obs]
}.

(*Convert the representation above to a tuple with x, y and element at position*)

Inductive cell : Type :=
  | none: cell
  | pos : nat -> nat -> Things -> cell.

Notation "( x , y , z )" := (pos x y z).

Inductive map_new: Type :=
  | nil : map_new 
  | r : cell -> map_new -> map_new.

Inductive map_new2: Type :=
  | nil2 : map_new2 
  | p : map_new -> map_new -> map_new2.

Notation "{ x , .. , z }" := (r x .. (r z nil) ..).
Notation "{ }" := nil.


(*Notation "x !! l" := (r x l)
                     (at level 60, right associativity).
Notation "x !!! l" := (p x l)
                     (at level 60, right associativity).


Fixpoint process_line (line : rowmap) (x : nat) (y : nat) : map_new :=
  match line with
    | empty => nil
    (*| Empty :: tail => process_line tail (S x) y*)
    | element :: tail => (x, y, element) !! process_line tail (S x) y
  end.

Fixpoint map2seq (m: map) (y : nat) : map_new :=
  match m with
    | null => { }
    | row line tail => process_line line 0 (S 0)
  end.

Definition init_map (m: map) : map_new2 :=
  match m with
    | null => nil2 
    | row line tail => map2seq tail 0 !!! map2seq tail 0
  end.

Compute init_map raw_map.*)

Definition map_example := 
{
 (0, 0, Obs), (0, 1, Obs), (0, 2, Obs), (0, 3, Obs), (0, 4, Obs),
 (0, 5, Obs), (0, 6, Obs), (1, 0, Obs), (1, 1, Obs), (1, 2, Obs),
 (1, 3, Obs), (1, 4, Obs), (1, 5, Obs), (1, 6, Obs), (2, 0, Obs),
 (2, 1, Obs), (2, 3, Start), (2, 5, Obs), (2, 6, Obs), (3, 0, Obs),
 (3, 1, Obs), (3, 5, Obs), (3, 6, Obs), (4, 0, Obs), (4, 1, Obs),
 (4, 2, Obs), (4, 4, Obs), (4, 5, Obs), (4, 6, Obs), (5, 0, Obs),
 (5, 1, Obs), (5, 4, Obs), (5, 5, Obs), (5, 6, Obs), (6, 0, Obs),
 (6, 1, Obs), (6, 2, Obs), (6, 4, Obs), (6, 5, Obs), (6, 6, Obs),
 (7, 0, Obs), (7, 1, Obs), (7, 4, Final), (7, 5, Obs), (7, 6, Obs), (8, 0, Obs),
 (8, 1, Obs), (8, 2, Obs), (8, 3, Obs), (8, 4, Obs), (8, 5, Obs),
 (8, 6, Obs), (9, 0, Obs), (9, 1, Obs), (9, 2, Obs), (9, 3, Obs),
 (9, 4, Obs), (9, 5, Obs), (9, 6, Obs)
}.

End Map.

Module RoboModel.
Require Import PeanoNat.
Local Open Scope nat_scope.
Import Map.

Inductive memory : Type :=
  | mem : nat -> nat -> nat -> memory.

Notation "( x ; y ; o )" := (mem x y o).

Fixpoint get_start_pos_x (m : map_new) : nat := 
  match m with
    | nil => 0
    | r i tail => match i with
                    | none => get_start_pos_x tail                
                    | pos x y Start => x
                    | pos x y z => get_start_pos_x tail 
                  end
  end.

Fixpoint get_start_pos_y (m : map_new) : nat := 
  match m with
    | nil => 0
    | r i tail => match i with
                    | none => get_start_pos_y tail                
                    | pos x y Start => y
                    | pos x y z => get_start_pos_y tail 
                  end
  end.

Definition start_x := get_start_pos_x map_example.
Definition start_y := get_start_pos_y map_example.
Definition north : nat := 0.
Definition east :nat := 1.
Definition south :nat := 2.
Definition west :nat := 3.

Fixpoint eqb n m : bool :=
  match n, m with
    | 0, 0 => true
    | 0, S _ => false
    | S _, 0 => false
    | S n', S m' => eqb n' m'
  end.

(* get element at position x y*)
Fixpoint things_at (m: map_new) (x: nat) (y: nat) : Things :=
  match m with
    | nil => Unknow
    | r i tail => match i with
                    | none => things_at tail x y              
                    | pos a b thing => if eqb a x then 
                                          if eqb b y then thing 
                                          else things_at tail x y
                                       else things_at tail x y                                                             
                  end
  end.

Example things_at_1  :
  things_at map_example 2 3 = Start.
Proof. reflexivity. Qed.
Example things_at_2  :
  things_at map_example 2 5 = Obs.
Proof. reflexivity. Qed.

(* looks for obstacles*)
Definition things_in_front (m : map_new) (x : nat) (y: nat) (o : nat) : Things :=
  match o with
    | 0 => things_at m x (minus y 1)
    | 1  => things_at m (plus x 1) y
    | 2 => things_at m x (plus y 1)
    | _  => things_at m (minus x 1) y
  end.

(*return true if there is a obstacle in front of robot and false otherwise*) 
Definition member_map (t: Things) : bool :=
  match t with
    | Obs => true
    | _   => false
  end.

(* check if there is an obstacle in front of the robot*)
Definition front_is_obstacle (m: map_new) (x : nat) (y: nat) (o : nat) : bool :=
 member_map (things_in_front m x y o).
    
(* get element in memory*)
Definition get_element_mem (pos: nat) (mem: memory) : nat :=
  match pos with
    | 1 => match mem with
            | (x;y;o) => x
           end
    | 2 => match mem with
            | (x;y;o) => y
           end
    | _ => match mem with
            | (x;y;o) => o
           end
  end.


(* move_steps move the robot n cells, but if the  specification*)
Fixpoint move_steps (mem: memory) (m: map_new) (n : nat) (i: nat) : memory :=
   match i with
    | O => mem
    | S i' =>  
      match n with
        | 0 => mem
        | _ => match mem with
                | (x;y;0) => if front_is_obstacle m x y north then
                                move_steps mem m 0 i'
                             else
                                move_steps (x;(minus y 1);0) m (minus n 1) i'
                | (x;y;1) => if front_is_obstacle m x y 1 then
                                move_steps mem m 0 i'
                             else
                                move_steps ((plus x 1);y;1) m (minus n 1) i'
                | (x;y;2) => if front_is_obstacle m x y 2 then
                                move_steps mem m 0 i'
                             else
                                move_steps (x;(plus y 1);2) m (minus n 1) i'
                | (x;y;_) => if front_is_obstacle m x y 3 then
                                move_steps mem m 0 i'
                             else
                                move_steps ((minus x 1);y;3) m (minus n 1) i'
               end
      end
  end.

(* forward command specification*)
Definition forward_command (mem: memory) (m: map_new) (n: nat) : memory :=
  move_steps mem m n n.

(*Example: forward(2)
 When the robot is at position (2, 3) and its orientation is north (0) then move 2 cells*)
Example forward_1 : 
  forward_command (2;3;0) map_example 2 = (2;2;0).
Proof. reflexivity. Qed.

(* move_steps_back move the robot n cells backward*)
Fixpoint move_steps_back (mem: memory) (m: map_new) (n : nat) (i: nat) : memory :=
   match i with
    | O => mem
    | S i' =>  
      match n with
        | 0 => mem
        | _ => match mem with
                | (x;y;0) => if front_is_obstacle m x y 2 then
                                move_steps_back mem m 0 i'
                             else
                                move_steps_back (x;(plus y 1);0) m (minus n 1) i'
                | (x;y;1) => if front_is_obstacle m x y 3 then
                                move_steps_back mem m 0 i'
                             else
                                move_steps_back ((minus x 1);y;1) m (minus n 1) i'
                | (x;y;2) => if front_is_obstacle m x y 0 then
                                move_steps_back mem m 0 i'
                             else
                                move_steps_back (x;(minus y 1);2) m (minus n 1) i'
                | (x;y;_) => if front_is_obstacle m x y 1 then
                                move_steps_back mem m 0 i'
                             else
                                move_steps_back ((plus x 1);y;3) m (minus n 1) i'
               end
      end
  end.

(* backward command specification*)
Definition backward_command (mem: memory) (m: map_new) (n: nat) : memory :=
  move_steps_back mem m n n.

(*Example: backward(2)
 When the robot is at position (2, 3) and its orientation is north (0) then move 2 cells*)
Example backward_1 : 
  backward_command (2;3;0) map_example 2 = (2;4;0).
Proof. reflexivity. Qed.


(* change robot's orientation to right*)
Definition right_command (mem : memory) : memory :=
  match mem with
    | (x;y;0) => (x;y;1)
    | (x;y;1) => (x;y;2)
    | (x;y;2) => (x;y;3)
    | (x;y;_) => (x;y;0)
  end.

Example right_0 :
  right_command (2;3;0) = (2;3;1).
Proof. reflexivity. Qed.
Example right_1 :
  right_command (2;3;1) = (2;3;2).
Proof. reflexivity. Qed.
Example right_2 :
  right_command (2;3;2) = (2;3;3).
Proof. reflexivity. Qed.
Example right_3 :
  right_command (2;3;3) = (2;3;0).
Proof. reflexivity. Qed.

(* change robot's orientation to left*)
Definition left_command (mem : memory) : memory :=
  match mem with
    | (x;y;0) => (x;y;3)
    | (x;y;1) => (x;y;0)
    | (x;y;2) => (x;y;1)
    | (x;y;_) => (x;y;2)
  end.

Example left_0 :
  left_command (2;3;0) = (2;3;3).
Proof. reflexivity. Qed.
Example left_1 :
  left_command (2;3;1) = (2;3;0).
Proof. reflexivity. Qed.
Example left_2 :
  left_command (2;3;2) = (2;3;1).
Proof. reflexivity. Qed.
Example left_3 :
  left_command (2;3;3) = (2;3;2).
Proof. reflexivity. Qed.

End RoboModel.


Module Program.

Import Map.
Import RoboModel.

Inductive Command: Type :=
  | forward : nat -> Command
  | backward : nat -> Command 
  | right : Command
  | left : Command.

Inductive Program : Type :=
  | EOF : Program  
  | c : Command -> Program -> Program.

Notation "c1 ;; c2" :=
  (c c1 c2) (at level 80, right associativity).

(*type to indicate the robot's attributes when the program finished (pos x & pos y & orientation) *)
Inductive result : Type :=
  | res : nat -> nat -> nat -> result.

Notation "( x & y & o )" := (res x y o).

Definition example_program1 := 
  forward 1;;
  backward 2;;
  forward 1;;
  right;;
  left;;
  EOF.

Fixpoint length_commands (p: Program) : nat :=
  match p with
    | EOF => O
    | fst ;; tail => S (length_commands tail)
  end.

Fixpoint read_program (p: Program) (m: map_new) (mem: memory): memory := 
  match p with
    | EOF => mem
    | c c1 tail => match c1 with
                    | forward n  => read_program tail m (forward_command mem m n)
                    | backward n => read_program tail m (backward_command mem m n)
                    | right      => read_program tail m (right_command mem)
                    | left       => read_program tail m (left_command mem)
                  end
  end.

(* call read program and return the result when the program finished *)
Definition start_program (p: Program) (m: map_new) (mem: memory) : result :=
  match read_program p m mem with
    | (x;y;o) => (x & y & o)
  end.

(*sample of program ROBO*)
Definition example :=    
  right;;
  forward 3;;
  backward 1;;
  EOF.

Example teste_map_example_program_example : 
  start_program example map_example ( (get_start_pos_x map_example); (get_start_pos_y map_example); north ) = (4 & 3 & 1).
Proof. reflexivity. Qed.



(* examples *)
Definition map1 := 
{
 (0, 0, Obs), (0, 1, Obs), (0, 2, Obs), (0, 3, Obs), (0, 4, Obs),
 (0, 5, Obs), (0, 6, Obs), (1, 0, Obs), (1, 1, Obs), (1, 2, Obs),
 (1, 3, Obs), (1, 4, Obs), (1, 5, Obs), (1, 6, Obs), (2, 0, Obs),
 (2, 1, Obs), (2, 3, Start), (2, 5, Obs), (2, 6, Obs), (3, 0, Obs),
 (3, 1, Obs), (3, 5, Obs), (3, 6, Obs), (4, 0, Obs), (4, 1, Obs),
 (4, 2, Obs), (4, 4, Obs), (4, 5, Obs), (4, 6, Obs), (5, 0, Obs),
 (5, 1, Obs), (5, 4, Obs), (5, 5, Obs), (5, 6, Obs), (6, 0, Obs),
 (6, 1, Obs), (6, 2, Obs), (6, 4, Obs), (6, 5, Obs), (6, 6, Obs),
 (7, 0, Obs), (7, 1, Obs), (7, 5, Obs), (7, 6, Obs), (8, 0, Obs),
 (8, 1, Obs), (8, 2, Obs), (8, 3, Obs), (8, 4, Obs), (8, 5, Obs),
 (8, 6, Obs), (9, 0, Obs), (9, 1, Obs), (9, 2, Obs), (9, 3, Obs),
 (9, 4, Obs), (9, 5, Obs), (9, 6, Obs)
}.

Definition program1 := 
  right;;
  forward 3;;
  left;;
  forward 1;;
  EOF.

Definition init_memory := ( (get_start_pos_x map_example); (get_start_pos_y map_example); 0 ).
Definition goal1 := (5 & 2 & 0).

Example program1_map1:
 start_program program1 map1 init_memory = goal1.
Proof. reflexivity. Qed.



Definition program2 := 
  right;;
  forward 5;;
  EOF.

Definition init_memory := ( (get_start_pos_x map_example); (get_start_pos_y map_example); 0 ).
Definition goal1 := (2 & 2 & 1).
Definition goal2 := (7 & 3 & 1).

Compute start_program program1 map1 init_memory.
Compute start_program program2 map1 init_memory.

Example program1_map1:
 start_program program1 map1 init_memory = goal1.
Proof. reflexivity. Qed.

Example program2_map1:
 start_program program2 map1 init_memory = goal2.
Proof. reflexivity. Qed.



End Program.






  