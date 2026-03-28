type nat = [%import: Stack_machine.nat] [@@deriving eq, show]

let nat_of_int = Stack_machine.nat_of_int

module Typed = struct
  module Ty = struct
    type t = [%import: Stack_machine.Typed.Ty.t] [@@deriving eq, show]
  end

  type tstack = [%import: Stack_machine.Typed.tstack] [@@deriving eq, show]

  module Binop = struct
    type t = [%import: Stack_machine.Typed.Binop.t] [@@deriving eq, show]
  end

  module Instr = struct
    type t = [%import: Stack_machine.Typed.Instr.t] [@@deriving eq, show]
  end

  module Prog = struct
    type t = [%import: Stack_machine.Typed.Prog.t] [@@deriving eq, show]

    include (Stack_machine.Typed.Prog : module type of Stack_machine.Typed.Prog with type t := t)
  end

  module Exp = struct
    type t = [%import: Stack_machine.Typed.Exp.t] [@@deriving eq, show]

    include (Stack_machine.Typed.Exp : module type of Stack_machine.Typed.Exp with type t := t)
  end
end

module Tests = struct
  open Typed

  let testable_nat = Alcotest.testable pp_nat equal_nat
  let testable_prog = Alcotest.testable Prog.pp Prog.equal

  (* Example values *)
  let nconst = Exp.NConst (nat_of_int 42)
  let bconst = Exp.BConst false

  let plus =
    Exp.Binop
      (Ty.Nat, Ty.Nat, Ty.Nat, Binop.Plus, Exp.NConst (nat_of_int 2), Exp.NConst (nat_of_int 2))

  let nested = Exp.Binop (Ty.Nat, Ty.Nat, Ty.Nat, Binop.Times, plus, Exp.NConst (nat_of_int 7))

  let nested_eq =
    Exp.Binop (Ty.Nat, Ty.Nat, Ty.Bool, Binop.Eq Ty.Nat, plus, Exp.NConst (nat_of_int 7))

  let nested_lt = Exp.Binop (Ty.Nat, Ty.Nat, Ty.Bool, Binop.Lt, plus, Exp.NConst (nat_of_int 7))

  let denote_nconst () =
    let expected = nat_of_int 42 in
    let actual = Exp.denote Ty.Nat nconst |> Obj.obj in
    Alcotest.(check testable_nat) "same nat" expected actual

  let denote_bconst () =
    let expected = false in
    let actual = Exp.denote Ty.Nat bconst |> Obj.obj in
    Alcotest.(check bool) "same nat" expected actual

  let denote_plus () =
    let expected = nat_of_int 4 in
    let actual = Exp.denote Ty.Nat plus |> Obj.obj in
    Alcotest.(check testable_nat) "same nat" expected actual

  let denote_nested () =
    let expected = nat_of_int 28 in
    let actual = Exp.denote Ty.Nat nested |> Obj.obj in
    Alcotest.(check testable_nat) "same nat" expected actual

  let denote_nested_eq () =
    let expected = false in
    let actual = Exp.denote Ty.Nat nested_eq |> Obj.obj in
    Alcotest.(check bool) "same bool" expected actual

  let denote_nested_lt () =
    let expected = true in
    let actual = Exp.denote Ty.Nat nested_lt |> Obj.obj in
    Alcotest.(check bool) "same bool" expected actual

  let compile_nconst () =
    let expected =
      Prog.Cons ([], [ Ty.Nat ], [ Ty.Nat ], Instr.NConst ([], nat_of_int 42), Prog.Nil [ Ty.Nat ])
    in
    let actual = Exp.compile Ty.Nat nconst [] in
    Alcotest.(check testable_prog) "same prog" expected actual

  let denote_compile_nconst () =
    let expected = (nat_of_int 42, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Nat nconst []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair testable_nat unit)) "same pair" expected actual

  let denote_compile_bconst () =
    let expected = (false, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Bool bconst []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair bool unit)) "same pair" expected actual

  let denote_compile_plus () =
    let expected = (nat_of_int 4, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Nat plus []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair testable_nat unit)) "same pair" expected actual

  let denote_compile_nested () =
    let expected = (nat_of_int 28, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Nat nested []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair testable_nat unit)) "same pair" expected actual

  let denote_compile_nested_eq () =
    let expected = (false, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Bool nested_eq []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair bool unit)) "same pair" expected actual

  let denote_compile_nested_lt () =
    let expected = (true, ()) in
    let actual = Prog.denote [] [] (Exp.compile Ty.Bool nested_lt []) (Obj.repr ()) |> Obj.obj in
    Alcotest.(check (pair bool unit)) "same pair" expected actual
end

let () =
  let open Alcotest in
  run "Stack_machine"
    [
      ( "Exp",
        [
          test_case "denote_nconst" `Quick Tests.denote_nconst;
          test_case "denote_bconst" `Quick Tests.denote_bconst;
          test_case "denote_plus" `Quick Tests.denote_plus;
          test_case "denote_nested" `Quick Tests.denote_nested;
          test_case "denote_nested_eq" `Quick Tests.denote_nested_eq;
          test_case "denote_nested_lt" `Quick Tests.denote_nested_lt;
          test_case "compile_nconst" `Quick Tests.compile_nconst;
          test_case "denote_compile_nconst" `Quick Tests.denote_compile_nconst;
          test_case "denote_compile_bconst" `Quick Tests.denote_compile_bconst;
          test_case "denote_compile_plus" `Quick Tests.denote_compile_plus;
          test_case "denote_compile_nested" `Quick Tests.denote_compile_nested;
          test_case "denote_compile_nested_eq" `Quick Tests.denote_compile_nested_eq;
          test_case "denote_compile_nested_lt" `Quick Tests.denote_compile_nested_lt;
        ] );
    ]
