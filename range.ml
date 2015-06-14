
open Format

let print_range range =
    List.iter (fun (a,b) ->
        print_string "[";
        print_int a;
        print_string ", ";
        print_int b;
        print_string "] ";
    ) range

let sort_range range =
    List.sort (fun (a1,b1) (a2,b2) -> a1 - a2) range

let rec simplify_range range =
    let sorted = sort_range range in
    let merge r (a2,b2) = 
        let (a1,b1) = List.hd r in
        let rest = List.tl r in
        if a2 > b1 + 1 then (a2,b2)::r
        else (a1, max b1 b2)::rest in
    sort_range (List.fold_left merge [List.hd sorted] (List.tl sorted))

(* add range r1 and r2 *)
let rec add_range_body r1 r2 r2rest =
    match r1, r2rest with
    []        , _                  -> []
  | rg1::rest , []                 -> add_range_body rest r2 r2
  | (a1,b1)::rest1, (a2,b2)::rest2 -> (a1+a2,b1+b2) :: (add_range_body r1 r2 rest2)

let add_range r1 r2 =
    let result = add_range_body r1 r2 r2 in
    simplify_range result

(* minus range r1 and r2 *)
let rec minus_range_body r1 r2 r2rest =
    match r1, r2rest with
    []        , _                  -> []
  | rg1::rest , []                 -> minus_range_body rest r2 r2
  | (a1,b1)::rest1, (a2,b2)::rest2 -> (a1-b2,b1-a2) :: (minus_range_body r1 r2 rest2)

let minus_range r1 r2 =
    let result = minus_range_body r1 r2 r2 in
    simplify_range result

(* judge whether r2 is in r1 *)
let rec sub_range r1 r2 =
    match r1,r2 with
    _, [] -> true
  | [], _ -> false
  | (a1,b1)::rest1, (a2,b2)::rest2 ->
        if a2 < a1 then false
        else if a2 > b1 then sub_range rest1 r2
        else (if b2 <= b1 then sub_range r1 rest2 else false) 

(* calc union of r1 and r2 *)
let union_range r1 r2 = 
    let union = r1 @ r2 in
    simplify_range union

let in_range n r =
    let pred (left,right) = (n >= left) && (n <= right) in
    List.exists pred r
