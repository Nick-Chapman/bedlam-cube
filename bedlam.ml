
(* Find solutions to the Bedlam cube... *)

let concat = String.concat ""
let print s = print_string s ; flush stdout
let rec upto i j = if i>j then [] else i :: upto (i+1) j
let (%) f g x = f (g x)

let rec (>>) xs p = match xs with  (* Monadic bind operator for lists *)
| [] -> []
| x::xs -> p x @ (xs >> p)

(* Each cell of the Bedlam cube represented by int 0..63. *)
type cell = CELL of int
(*
12 . . 15  ...  60 . . 63
 .     .
 .     .
 0 1 2 3   ...  48 . . 51
*)

let eqCell (CELL a) (CELL b) = (a=b)
let not0123 a = a<0 || a>3

let mkCell (x,y,z) =
    if (not0123 x) then failwith "mkCell:x" else
    if (not0123 y) then failwith "mkCell:y" else
    if (not0123 z) then failwith "mkCell:z" else
    CELL (x + 4*y + 16 * z)

(* Primitive x/y/z manipulations from which orientations are built. *)
let id          = fun (a,b,c) -> (a,b,c)
let quarterXY   = fun (a,b,c) -> (b,3-a,c)
let halfXY      = fun (a,b,c) -> (3-a,3-b,c)
let quarterXZ   = fun (a,b,c) -> (c,b,3-a)
let clock       = fun (a,b,c) -> (b,c,a)
let anti        = fun (a,b,c) -> (c,a,b)

(* Each piece has 24 orientations - symmetry can make some orientations equivalent. *)
let orientations =
    [id;quarterXY]      >> fun f1 ->
    [id;halfXY]         >> fun f2 ->
    [id;quarterXZ]      >> fun f3 ->
    [id;clock;anti]     >> fun f4 ->
    [f1 % f2 % f3 % f4]

(* The possible "shifts" of a piece depend on its bounding x/y/z size. *)
let shifts (x,y,z) =
    upto 0 (x-1)        >> fun x ->
    upto 0 (y-1)        >> fun y ->
    upto 0 (z-1)        >> fun z ->
    [fun (a,b,c) -> (a+x,b+y,c+z)]

(* A piece is represented by a list of its placements in all possible shifts/orientations;
    A placement is the list of cells which is covered in that placement. *)
type piece = PIECE of string * cell list list

let eqCellList xs ys =
    (List.length xs = List.length ys) && not (List.exists (fun x -> not (List.mem x ys)) xs)

let rec removeDups eq xs = match xs with
| [] -> []
| x::xs -> x :: removeDups eq (if (List.exists (eq x) xs)
                               then List.filter (not % eq x) xs
                               else xs)

(* Make a piece from a raw description. Placements are all pre-calculated. *)
let mkPiece (name,xyz,offsets) =
    PIECE (name,
           removeDups eqCellList (* remove duplicated identical placements, due to symmetry *)
                      (orientations >> fun f ->
                       shifts xyz   >> fun g ->
                       [List.map (mkCell % f % g) offsets]))

(* The "cube" type represents the state of the cube during trial and error placement of pieces.
    Very simplistic representation - list of filled cells (with the name of the filling piece).
*)
type cube = CUBE of (string*cell) list
let emptyCube = CUBE []

let isFilled (CUBE xs) cell = List.exists (fun (_,cell') -> eqCell cell cell') xs

let placePiece (CUBE xs) name cells =
    CUBE (List.map (fun cell -> (name,cell)) cells @ xs)

let lookCube (CUBE xs) cell =
    let rec look = function
                  | [] -> "."
                  | (name,cell')::xs ->
                    if (eqCell cell cell') then name else look xs
    in look xs

(* Display the cube in 4 slices, showing which name of piece in each cell *)
let stringOfCube cube =
    "\n"^concat ([3;2;1;0] >> fun y ->
                 ([0;1;2;3] >> fun z ->
                  ["   "^ concat ([0;1;2;3] >> fun x ->
                                  [lookCube cube (mkCell (x,y,z))])]
                  ) @ ["\n"])

    
(* Type for search & generation - with alt/fail combinators.

Implemented using success/fail continuations.

Makes nice use of OCaml type quantification on 'r to avoid
parametrization on result type - ('a,'r) generate
*)

type 'a generate = {generate: 'r. (unit -> 'r) -> ((unit -> 'r) -> 'a -> 'r) -> 'r}

let resultG x = {generate = fun f s -> s f x}
let altG m1 m2 = {generate = fun f s -> m1.generate (fun () -> (m2()).generate f s) s}
let failG = {generate = fun f _s -> f ()}

let rec tryG xs m = match xs with
| [] -> failG
| x::xs -> altG (m x) (fun () -> tryG xs m)


(* Core backtracking algorithm to search for a Bedlam solution:

Search is organized to progressively fill "cells" in the order given,
trying each piece in each orientation, & checking that the "cells_tobe_covered"
are not already filled in "cube" - if they are, backtracking is initiated.

By attempting to fill cells in an order which relates to the locality of cells
- 0..63 works fine - we hope to discover unfillable cell-gaps sooner
and hence backtrack earlier, than if we search by piece/orientation alone,
which would allow pieces to be scattered through the cube.
*)

let rec find_placements thePieces cube cells placedNames =
    (*print ("find_placements : " ^ concat placedNames^"\n");*)
    match cells with
    | [] -> resultG cube
    | cellToFill::cells ->
        if (isFilled cube cellToFill)
        then find_placements thePieces cube cells placedNames else
        tryG thePieces (fun (PIECE (name,placements)) ->
        if (List.mem name placedNames) then failG else
        tryG placements (fun cells_tobe_covered ->
        if not (List.exists (eqCell cellToFill) cells_tobe_covered) then failG else
        if (List.exists (isFilled cube) cells_tobe_covered) then failG else
        find_placements thePieces (placePiece cube name cells_tobe_covered) cells (name::placedNames)))


(* Search for all solutions, displaying each solution as found. *)
let show m =
    m.generate (fun () -> print "stop\n") (fun f -> fun x -> (print (stringOfCube x) ; f ()))

let go pieces cells =
    show (find_placements pieces emptyCube cells [])

(* Description of the 13 pieces in the Bedlam puzzle.
Pieces are named with a single letter to allow compact printed representation. *)
let thePieces = 
    List.map mkPiece
    [
    (* red pieces *)
     ("A",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(0,1,0);(0,0,1)]); (* base-girder *)
     ("B",(2,3,3),[(0,0,0);(1,0,0);(1,1,0);(2,1,0);(2,1,1)]); (* spiral-staircase *)
     ("C",(2,3,3),[(0,0,0);(1,0,0);(1,1,0);(2,1,0);(1,1,1)]); (* fork *)
     ("D",(2,2,4),[(1,0,0);(1,1,0);(1,2,0);(0,1,0);(2,1,0)]); (* flat-cross *)
     (* blue *)
     ("e",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(1,1,0);(1,1,1)]); (* modern-art *)
     ("f",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(1,1,0);(0,0,1)]); (* bent-f-piece *)
     ("g",(2,3,3),[(0,0,0);(1,0,0);(1,1,0);(1,1,1);(2,1,1)]); (* s-piece *)
     ("h",(2,2,4),[(1,0,0);(0,1,0);(1,1,0);(2,1,0);(0,2,0)]); (* flat-tree *)
     (* yellow *)
     ("v",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(2,0,1);(2,1,1)]); (* L-sign-post *)
     ("w",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(2,1,0);(0,0,1)]); (* hug *)
     ("x",(2,3,3),[(0,0,0);(1,0,0);(2,0,0);(1,1,0);(1,0,1)]); (* middle-girder *)
     ("y",(2,2,4),[(0,0,0);(1,0,0);(1,1,0);(2,1,0);(2,2,0)]); (* simple-stairs *)
     ("z",(3,3,3),[(0,0,0);(1,0,0);(1,1,0);(1,1,1)]); (* small-one *)
     ]

(* Search solution space with given piece-order and cell-order. *)
let () = go thePieces (List.map (fun n -> CELL n) (upto 0 63))
