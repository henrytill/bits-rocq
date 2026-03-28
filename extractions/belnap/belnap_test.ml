open Belnap

(* Helper: create a Fin.t index for bound n.
   Extracted of_nat_lt takes (p : index) (n : bound). *)
let idx n i = of_nat_lt i n

(* Helper: build a belnapArr from a list of belnap values *)
let of_list n xs =
  let v = ba_all_unknown n in
  List.iteri (fun i x -> ignore (ba_set n (idx n i) x v)) xs;
  (* ba_set is pure, so we need to fold *)
  List.fold_left
    (fun acc (i, x) -> ba_set n (idx n i) x acc)
    (ba_all_unknown n)
    (List.mapi (fun i x -> (i, x)) xs)

(* Helper: extract all elements as a list *)
let to_list n v =
  List.init n (fun i -> ba_get n (idx n i) v)

(* Alcotest testable for belnap *)
let pp_belnap fmt = function
  | Unknown -> Format.fprintf fmt "Unknown"
  | Btrue -> Format.fprintf fmt "True"
  | Bfalse -> Format.fprintf fmt "False"
  | Both -> Format.fprintf fmt "Both"

let eq_belnap a b =
  match (a, b) with
  | Unknown, Unknown | Btrue, Btrue | Bfalse, Bfalse | Both, Both -> true
  | _ -> false

let belnap_t = Alcotest.testable pp_belnap eq_belnap
let check = Alcotest.(check belnap_t)

(* Alcotest testable for belnapArr via element-wise comparison *)
let eq_arr n a b = List.for_all2 eq_belnap (to_list n a) (to_list n b)

let pp_arr n fmt v =
  let xs = to_list n v in
  Format.fprintf fmt "[%a]"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_belnap)
    xs

let arr_testable n = Alcotest.testable (pp_arr n) (eq_arr n)
let check_arr n = Alcotest.check (arr_testable n)

(* ============================= Unit tests ============================= *)

let test_get_set () =
  let n = 4 in
  let v = ba_all_unknown n in
  let v = ba_set n (idx n 0) Unknown v in
  let v = ba_set n (idx n 1) Btrue v in
  let v = ba_set n (idx n 2) Bfalse v in
  let v = ba_set n (idx n 3) Both v in
  check "get 0" Unknown (ba_get n (idx n 0) v);
  check "get 1" Btrue (ba_get n (idx n 1) v);
  check "get 2" Bfalse (ba_get n (idx n 2) v);
  check "get 3" Both (ba_get n (idx n 3) v)

let test_bulk_and () =
  let n = 64 in
  (* Classical AND: True AND False = False *)
  let r = ba_and n (ba_all_true n) (ba_all_false n) in
  check_arr n "and all_true all_false = all_false" (ba_all_false n) r;
  (* AND with self is identity *)
  let r2 = ba_and n (ba_all_true n) (ba_all_true n) in
  check_arr n "and all_true all_true = all_true" (ba_all_true n) r2;
  (* AND with top (all_true) is identity *)
  let r3 = ba_and n (ba_all_both n) (ba_all_true n) in
  check_arr n "and all_both all_true = all_both" (ba_all_both n) r3

let test_bulk_or () =
  let n = 64 in
  (* Classical OR: False OR True = True *)
  let r = ba_or n (ba_all_false n) (ba_all_true n) in
  check_arr n "or all_false all_true = all_true" (ba_all_true n) r;
  (* OR with self is identity *)
  let r2 = ba_or n (ba_all_false n) (ba_all_false n) in
  check_arr n "or all_false all_false = all_false" (ba_all_false n) r2;
  (* OR with bottom (all_false) is identity *)
  let r3 = ba_or n (ba_all_true n) (ba_all_false n) in
  check_arr n "or all_true all_false = all_true" (ba_all_true n) r3

let test_bulk_not () =
  let n = 100 in
  let r = ba_not n (ba_all_true n) in
  check_arr n "not all_true = all_false" (ba_all_false n) r;
  let rr = ba_not n r in
  check_arr n "not not all_true = all_true" (ba_all_true n) rr

let test_bulk_merge () =
  let n = 64 in
  (* Knowledge join: merge all_true all_false = all_both *)
  let r = ba_merge n (ba_all_true n) (ba_all_false n) in
  check_arr n "merge all_true all_false = all_both" (ba_all_both n) r;
  (* Knowledge join with bot (all_unknown) is identity *)
  let r2 = ba_merge n (ba_all_both n) (ba_all_unknown n) in
  check_arr n "merge all_both all_unknown = all_both" (ba_all_both n) r2

let test_bulk_consensus () =
  let n = 64 in
  (* Knowledge meet: consensus all_true all_false = all_unknown *)
  let r = ba_consensus n (ba_all_true n) (ba_all_false n) in
  check_arr n "consensus all_true all_false = all_unknown" (ba_all_unknown n) r;
  (* Knowledge meet with top (all_both) is identity *)
  let r2 = ba_consensus n (ba_all_both n) (ba_all_both n) in
  check_arr n "consensus all_both all_both = all_both" (ba_all_both n) r2

let test_word_boundaries () =
  let n = 65 in
  (* Element 63: bit 63 of word-pair 0 *)
  let v = ba_set n (idx n 63) Both (ba_all_unknown n) in
  check "get 63 is Both" Both (ba_get n (idx n 63) v);
  check "get 62 is Unknown" Unknown (ba_get n (idx n 62) v);
  check "get 64 is Unknown" Unknown (ba_get n (idx n 64) v);
  (* Element 64: bit 0 of word-pair 1 *)
  let v = ba_set n (idx n 64) Btrue v in
  check "get 64 is True" Btrue (ba_get n (idx n 64) v);
  check "get 63 still Both" Both (ba_get n (idx n 63) v)

let test_roundtrip () =
  let n = 4 in
  let xs = [Unknown; Btrue; Bfalse; Both] in
  let v = of_list n xs in
  Alcotest.(check (list belnap_t)) "4 elems" xs (to_list n v);
  (* 65 elements: last element in word-pair 1, bit 0 *)
  let n = 65 in
  let xs = List.init 65 (fun i -> if i = 64 then Bfalse else Btrue) in
  let v = of_list n xs in
  Alcotest.(check (list belnap_t)) "65 elems" xs (to_list n v)

let test_not_involutive () =
  let n = 4 in
  let v = of_list n [Unknown; Btrue; Bfalse; Both] in
  let r = ba_not n (ba_not n v) in
  check_arr n "not (not v) = v" v r

let test_constants () =
  let n = 4 in
  List.iter
    (fun i -> check "all_unknown is Unknown" Unknown (ba_get n (idx n i) (ba_all_unknown n)))
    [0; 1; 2; 3];
  List.iter
    (fun i -> check "all_both is Both" Both (ba_get n (idx n i) (ba_all_both n)))
    [0; 1; 2; 3];
  List.iter
    (fun i -> check "all_true is True" Btrue (ba_get n (idx n i) (ba_all_true n)))
    [0; 1; 2; 3];
  List.iter
    (fun i -> check "all_false is False" Bfalse (ba_get n (idx n i) (ba_all_false n)))
    [0; 1; 2; 3]

(* ============================= Lattice law tests ============================= *)

(* Generate a random belnapArr of size n *)
let random_arr n =
  let vals = [| Unknown; Btrue; Bfalse; Both |] in
  let v = ref (ba_all_unknown n) in
  for i = 0 to n - 1 do
    v := ba_set n (idx n i) vals.(Random.int 4) !v
  done;
  !v

let test_lattice_laws () =
  (* Test with multiple sizes including word boundaries *)
  List.iter
    (fun n ->
      for _ = 1 to 20 do
        let a = random_arr n and b = random_arr n and c = random_arr n in
        let msg s = Printf.sprintf "%s (n=%d)" s n in
        (* Truth lattice: and/or *)
        check_arr n (msg "and comm") (ba_and n a b) (ba_and n b a);
        check_arr n (msg "or comm") (ba_or n a b) (ba_or n b a);
        check_arr n (msg "and assoc") (ba_and n (ba_and n a b) c) (ba_and n a (ba_and n b c));
        check_arr n (msg "or assoc") (ba_or n (ba_or n a b) c) (ba_or n a (ba_or n b c));
        check_arr n (msg "and idemp") (ba_and n a a) a;
        check_arr n (msg "or idemp") (ba_or n a a) a;
        check_arr n (msg "absorb or/and") (ba_or n a (ba_and n a b)) a;
        check_arr n (msg "absorb and/or") (ba_and n a (ba_or n a b)) a;
        (* Truth lattice: identities (bot=all_false, top=all_true) *)
        check_arr n (msg "or bot") (ba_or n a (ba_all_false n)) a;
        check_arr n (msg "and top") (ba_and n a (ba_all_true n)) a;
        (* Knowledge lattice: merge/consensus *)
        check_arr n (msg "merge comm") (ba_merge n a b) (ba_merge n b a);
        check_arr n (msg "consensus comm") (ba_consensus n a b) (ba_consensus n b a);
        check_arr n (msg "merge assoc")
          (ba_merge n (ba_merge n a b) c) (ba_merge n a (ba_merge n b c));
        check_arr n (msg "consensus assoc")
          (ba_consensus n (ba_consensus n a b) c) (ba_consensus n a (ba_consensus n b c));
        check_arr n (msg "merge idemp") (ba_merge n a a) a;
        check_arr n (msg "consensus idemp") (ba_consensus n a a) a;
        (* Knowledge lattice: identities (bot=all_unknown, top=all_both) *)
        check_arr n (msg "merge bot") (ba_merge n a (ba_all_unknown n)) a;
        check_arr n (msg "consensus top") (ba_consensus n a (ba_all_both n)) a;
        (* Negation involution *)
        check_arr n (msg "not involutive") (ba_not n (ba_not n a)) a;
      done)
    [0; 1; 4; 8; 63; 64; 65; 100; 128]

let () =
  Alcotest.run "Belnap extraction"
    [
      ( "unit",
        Alcotest.
          [
            test_case "constants" `Quick test_constants;
            test_case "get/set" `Quick test_get_set;
            test_case "bulk_and" `Quick test_bulk_and;
            test_case "bulk_or" `Quick test_bulk_or;
            test_case "bulk_not" `Quick test_bulk_not;
            test_case "bulk_merge" `Quick test_bulk_merge;
            test_case "bulk_consensus" `Quick test_bulk_consensus;
            test_case "word_boundaries" `Quick test_word_boundaries;
            test_case "roundtrip" `Quick test_roundtrip;
            test_case "not_involutive" `Quick test_not_involutive;
          ] );
      ( "lattice_laws",
        Alcotest.[ test_case "randomized" `Quick test_lattice_laws ] );
    ]
