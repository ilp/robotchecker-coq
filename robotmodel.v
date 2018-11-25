(*
Federal University of Pernambuco
TAES's Project
Professor: Gustavo Carvalho
MSc Student: Iverson Luis Pereira
*)

(*Definicao do modulo Map que especifica elementos relacionados ao mapa e funcoes para gerencia-lo*)
Module Map.

Require Import Arith.
Require Import Vector.
Require Import Bool.
Import VectorNotations.
Require Import List.
Require Import PeanoNat.

(* Tipo para representar coisas presentes em cada celula do mapa
    - Obs representa obstaculos
    - Empty representa celulas vazias
    - Start representa a posicao inicial do robo
    - Final representa a posicao final do robo (opcional no mapa)
    - Unknow utilizado para controle de erro no mapa *)

Inductive Things : Type :=
  | Empty : Things
  | Obs : Things
  | Start : Things
  | Final: Things
  | Unknow : Things.

(*Tipo que representa uma linha do mapa, ou seja, uma lista com os elementos de linha*)

Inductive rowmap : Type :=
  | empty : rowmap
  | c : Things -> rowmap -> rowmap.

Notation "x :: l" := (c x l) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (c x .. (c y empty) ..).
Notation "[ ]" := empty.

(* Tipo que representa um mapa completo, isto e, varias listas do tipo rowmap *)
Inductive map: Type :=
  | null : map  
  | row : rowmap -> map -> map.

Notation "{ x ; .. ; y }" := (row x .. (row y null) ..).
Notation "{ }" := null.

(* Exemplo da representacao do mapa no RoboMind.
  map:
  AAAAA   A, Q -> Obstacles
  A@  A   @ -> Start position
  A Q A
  AAAAA
 Abaixo um exemplo em coq de um mapa equivalente ao exemplo anterior do RoboMind.
*)

Definition raw_map :=
{
  [Final;Empty;Obs;Obs;Obs];
  [Obs;Start;Empty;Empty;Obs];
  [Obs;Empty;Obs;Empty;Obs];
  [Obs;Obs;Obs;Obs;Obs]
}.

(* Tipos para representar um map_new com x, y e o elemento na posicao*)

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


Notation "x !! l" := (r x l)
                     (at level 60, right associativity).
Notation "x !!! l" := (p x l)
                     (at level 60, right associativity).
(* Funcao que processa cada linha do mapa e converte em (x,y,thing) *)
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

(*Exemplo de mapa na representação final de coq, as celulas vazias nao sao colocadas, apenas as celulas com objetos *)

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

(*Modulo que possui a especificacao dos comandos de ROBO, como movimentacao e verificacao de celulas pelo robo.*)
Module RoboModel.
Require Import PeanoNat.
Local Open Scope nat_scope.
Import Map.

(*Tipo para representar uma lista com tres valores *)
Inductive memory : Type :=
  | mem : nat -> nat -> nat -> memory.

Notation "( x ; y ; o )" := (mem x y o).

(* Funcao que busca a posicao inicial x do robo dado um mapa como entrada*)
Fixpoint get_start_pos_x (m : map_new) : nat := 
  match m with
    | nil => 0
    | r i tail => match i with
                    | none => get_start_pos_x tail                
                    | pos x y Start => x
                    | pos x y z => get_start_pos_x tail 
                  end
  end.

(* Funcao que busca a posicao inicial y do robo dado um amapa como entrada*)
Fixpoint get_start_pos_y (m : map_new) : nat := 
  match m with
    | nil => 0
    | r i tail => match i with
                    | none => get_start_pos_y tail                
                    | pos x y Start => y
                    | pos x y z => get_start_pos_y tail 
                  end
  end.

(* Definicoes das posicoes x e y inicial do robo, e 'constantes' para representar as orientacoes possiveis do robo*)

Definition start_x := get_start_pos_x map_example.
Definition start_y := get_start_pos_y map_example.
Definition north : nat := 0.
Definition east :nat := 1.
Definition south :nat := 2.
Definition west :nat := 3.

(*Funcao para verificar igualdade entre dois numeros*)
Fixpoint eqb n m : bool :=
  match n, m with
    | 0, 0 => true
    | 0, S _ => false
    | S _, 0 => false
    | S n', S m' => eqb n' m'
  end.

(* Funcao retorna o objeto presente em determinada posicao x,y do mapa*)
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

(* Exemplo utilizando map_example que busca o objeto na posicacao x,y*)
Example things_at_1  :
  things_at map_example 2 3 = Start.
Proof. reflexivity. Qed.
Example things_at_2  :
  things_at map_example 2 5 = Obs.
Proof. reflexivity. Qed.

(* Funcao que procura por objetos na celula a frente do robo dado uma orientacao*) 
Definition things_in_front (m : map_new) (x : nat) (y: nat) (o : nat) : Things :=
  match o with
    | 0 => things_at m x (minus y 1)
    | 1  => things_at m (plus x 1) y
    | 2 => things_at m x (plus y 1)
    | _  => things_at m (minus x 1) y
  end.

(* Funcao que retorna true ou false se existe obstaculo na frente do robo*) 
Definition member_map (t: Things) : bool :=
  match t with
    | Obs => true
    | _   => false
  end.

(* Espefificacao do comando fronIsObstacle do RoboMind*)
Definition front_is_obstacle (m: map_new) (x : nat) (y: nat) (o : nat) : bool :=
 member_map (things_in_front m x y o).
    
(* Funcao que busca um elemento da memoria*)
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


(* Funcao que atualiza na memoria a posicao atual x,y do robo quando o comando forward eh executado*)
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

(* Especificao do comando forward do RoboMind*)
Definition forward_command (mem: memory) (m: map_new) (n: nat) : memory :=
  move_steps mem m n n.

(*Example: forward(2)
 Quando o robo esta na posicao (2, 3) com orientacao norte (0) entao move 2 celulas para frente e espera-se que esteja posicao (2,2)*)
Example forward_1 : 
  forward_command (2;3;0) map_example 2 = (2;2;0).
Proof. reflexivity. Qed.

(* Funcao equivalente ao move_steps, no entanto, atualiza na posicao contraria, pois eh utilizado o backward*)
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

(* Especificao do comando backward do RoboMind*)
Definition backward_command (mem: memory) (m: map_new) (n: nat) : memory :=
  move_steps_back mem m n n.

(*Example: backward(2)
 Quando o robo esta na posicao (2, 3) com orientacao norte (0) entao move 2 celulas e espera-se que esteja na posicao (2,4)*)
Example backward_1 : 
  backward_command (2;3;0) map_example 2 = (2;4;0).
Proof. reflexivity. Qed.


(* Especificacao do comando right que altera a orientacao do robo a direta*)
Definition right_command (mem : memory) : memory :=
  match mem with
    | (x;y;0) => (x;y;1)
    | (x;y;1) => (x;y;2)
    | (x;y;2) => (x;y;3)
    | (x;y;_) => (x;y;0)
  end.

(*Exemplos de provas para chamadas do comando right e o que se espera apos sua execucao, utilizando apenas reflexivity eh suficiente*)
Example right_0 :
  right_command (2;3;north) = (2;3;east).
Proof. reflexivity. Qed.
Example right_1 :
  right_command (2;3;east) = (2;3;south).
Proof. reflexivity. Qed.
Example right_2 :
  right_command (2;3;south) = (2;3;west).
Proof. reflexivity. Qed.
Example right_3 :
  right_command (2;3;west) = (2;3;north).
Proof. reflexivity. Qed.

(* Especificacao do comando left que altera a orientacao do robo a esquerda*)
Definition left_command (mem : memory) : memory :=
  match mem with
    | (x;y;0) => (x;y;3)
    | (x;y;1) => (x;y;0)
    | (x;y;2) => (x;y;1)
    | (x;y;_) => (x;y;2)
  end.

(*Exemplos de provas para chamadas do comando left e o que se espera apos sua execucao, utilizando apenas reflexivity eh suficiente*)
Example left_0 :
  left_command (2;3;north) = (2;3;west).
Proof. reflexivity. Qed.
Example left_1 :
  left_command (2;3;east) = (2;3;north).
Proof. reflexivity. Qed.
Example left_2 :
  left_command (2;3;south) = (2;3;east).
Proof. reflexivity. Qed.
Example left_3 :
  left_command (2;3;west) = (2;3;south).
Proof. reflexivity. Qed.

End RoboModel.

(*Modulo para representar uma execucao de um programa e sua verificacao*)
Module Program.

Import Map.
Import RoboModel.

(* Tipo para representar os possiveis comandos utilizaveis no programa*)
Inductive Command: Type :=
  | forward : nat -> Command
  | backward : nat -> Command 
  | right : Command
  | left : Command.

(* Tipo para representar um programa, isto e, uma lista de comandos com um fim de arquivo*)
Inductive Program : Type :=
  | EOF : Program  
  | c : Command -> Program -> Program.

Notation "c1 ;; c2" :=
  (c c1 c2) (at level 80, right associativity).

(*Tipo para representar atributos do robo quando o programa termina sua execucao (pos final x, pos final y, orientacao final)*)
Inductive result : Type :=
  | res : nat -> nat -> nat -> result.

Notation "( x & y & o )" := (res x y o).

(*Exemplo de definicao de um programa*)
Definition example_program1 := 
  forward 1;;
  backward 2;;
  forward 1;;
  right;;
  left;;
  EOF.

(* Funcao que retorna a quantidade de comandos de um programa*)
Fixpoint length_commands (p: Program) : nat :=
  match p with
    | EOF => O
    | fst ;; tail => S (length_commands tail)
  end.

(* Funcao para leitura e execucao do programa, le cada comando individuamente e atualiza a memoria a cada chamada dos comandos*)
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

(* Funcao que inicia o programa, retornando o resultado final apos a execucao da leitura do programa *)
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
  start_program example map_example ( (get_start_pos_x map_example); (get_start_pos_y map_example); north ) = (4 & 3 & east).
Proof. reflexivity. Qed.

(* Exemplo de mapa *)
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

(*Exemplo de programas*)
Definition program1 := 
  right;;
  forward 3;;
  left;;
  forward 1;;
  EOF.

Definition program2 := 
  right;;
  forward 5;;
  EOF.

(*Iniciando memoria com dados do robo, lembrando que a orientacao do robo no RoboMind sempre comeca no norte*)
Definition init_memory := ( (get_start_pos_x map1); (get_start_pos_y map1); north ).

(*Exemplos de definicoes de objetivos para as provas*)
Definition goal1 := (5 & 2 & north).
Definition goal2 := (7 & 3 & east).

(* Exemplos de prova para um programa e mapa, verifica dado um objetivo (posicao final e orientacao) se o retorno
da execucao do programa e igual, sendo assim, bastando utiliza reflexivity para provar*)
Example program1_map1:
 start_program program1 map1 init_memory = goal1.
Proof. reflexivity. Qed.

Example program2_map1:
 start_program program2 map1 init_memory = goal2.
Proof. reflexivity. Qed.

End Program.






  