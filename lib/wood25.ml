open CalendarLib

(* Find solutions to the Wood25 cube... *)


let stamp() =
  let t = Time.now() in
  print_string (Printf.sprintf "[%02d:%02d:%02d]\n"
                  (Time.hour t)
                  (Time.minute t)
                  (Time.second t));
  flush stdout

let concat = String.concat ""
let print s = stamp(); print_string s ; flush stdout
let rec upto i j = if i>j then [] else i :: upto (i+1) j
let (%) f g x = f (g x)

let rec (>>) xs p = match xs with  (* Monadic bind operator for lists *)
| [] -> []
| x::xs -> p x @ (xs >> p)

(* Each cell of the Bedlam cube represented by int 0..124. *)
type cell = CELL of int
(*
20 . . . 24  ...  120 ... 124
15       .
10       .
 5       .
 0 1 2 3 4   ...  100 ... 104
*)

let eqCell (CELL a) (CELL b) = (a=b)
let not01234 a = a<0 || a>4

let mkCell (x,y,z) =
    if (not01234 x) then failwith "mkCell:x" else
    if (not01234 y) then failwith "mkCell:y" else
    if (not01234 z) then failwith "mkCell:z" else
    CELL (x + 5*y + 5*5*z)

(* Primitive x/y/z manipulations from which orientations are built. *)
let id          = fun (a,b,c) -> (a,b,c)
let quarterXY   = fun (a,b,c) -> (b,4-a,c)
let halfXY      = fun (a,b,c) -> (4-a,4-b,c)
let quarterXZ   = fun (a,b,c) -> (c,b,4-a)
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
let dep_mkPiece (name,xyz,offsets) =
    PIECE (name,
           removeDups eqCellList (* remove duplicated identical placements, due to symmetry *)
                      (orientations >> fun f ->
                       shifts xyz   >> fun g ->
                       [List.map (mkCell % f % g) offsets]))

let the_placements =
  let xyz = (2,4,5) in
  let offsets = [(0,0,0);(1,0,0);(2,0,0);(2,1,0);(3,1,0)] in
  removeDups eqCellList (* remove duplicated identical placements, due to symmetry *)
    (orientations >> fun f ->
     shifts xyz   >> fun g ->
     [List.map (mkCell % f % g) offsets])

(* The "cube" type represents the state of the cube during trial and error placement of pieces.
    Very simplistic representation - list of filled cells (with the name of the filling piece).
*)
type cube = CUBE of (char*cell) list
let emptyCube = CUBE []

let isFilled (CUBE xs) cell = List.exists (fun (_,cell') -> eqCell cell cell') xs

let placePiece (CUBE xs) name cells =
    CUBE (List.map (fun cell -> (name,cell)) cells @ xs)

let lookCube (CUBE xs) cell =
    let rec look = function
                  | [] -> '.'
                  | (name,cell')::xs ->
                    if (eqCell cell cell') then name else look xs
    in String.make 1 (look xs)

(* Display the cube in 4 slices, showing which name of piece in each cell *)
let stringOfCube cube =
    "\n"^concat ([4;3;2;1;0] >> fun y ->
                 ([0;1;2;3;4] >> fun z ->
                  ["   "^ concat ([0;1;2;3;4] >> fun x ->
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

(* Search for all solutions, displaying each solution as found. *)
let show m =
    m.generate (fun () -> print "stop\n") (fun f -> fun x -> (print (stringOfCube x) ; f ()))

let mk_name =
  let names = "abcdefghijklmnopqrstuvwxy" in
  fun n ->
  String.get names n


let report =
  let max = ref 0 in
  let min = ref 100 in
  fun n ->
  (if n < !min && n < !max then (min := n; stamp(); Printf.printf "-%d\n%!" n) else ());
  let () = (if n > !max then max := n else ()) in
  ()

let rec new_find_placements cube cells n =
  report n;
  (*print ("new_find_placements : " ^ concat placedNames^"\n");*)
  let name = mk_name n in
  if n=24 then resultG cube else
    match cells with
    | [] -> resultG cube
    | cellToFill::cells ->
       (*print (stringOfCube cube);*)
        if (isFilled cube cellToFill)
        then new_find_placements cube cells n else
        tryG the_placements (fun cells_tobe_covered ->
        if not (List.exists (eqCell cellToFill) cells_tobe_covered) then failG else
        if (List.exists (isFilled cube) cells_tobe_covered) then failG else
        new_find_placements (placePiece cube name cells_tobe_covered) cells (n+1))

let new_go cells =
    show (new_find_placements emptyCube cells 0)

(*
20 . . . 24  ...  120 ... 124
15       .
10       .
 5       .
 0 1 2 3 4   ...  100 ... 104
*)

let run() =
  stamp();
  let _all = upto 0 124 in
  let _face1 = upto 0 24 in
  let _face2 = List.map (fun i -> i*5) (upto 0 24) in
  let _face3 = [ 0;1;2;3;4; 25;26;27;28;29; 50;51;52;53;54; 75;76;77;78;79; 100;101;102;103;104 ] in
  new_go (List.map (fun n -> CELL n) (_face1 @ _face2 @ _face3 @ _all))
