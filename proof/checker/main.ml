(* certcheck: run the extracted, verified checkers of Certificate.v on a
   certificate file.  This driver only parses; acceptance is decided by
   [Certcheck.check_coloring] / [Certcheck.check_refutation].

   File format (whitespace-separated tokens; colours are 0-indexed):
     n k m
     u1 v1 ... um vm                      edges of G on vertices 0..n-1
     COLORING  c0 ... c(n-1)              a proper k-colouring, or
     REFUTATION <tree>                    a refutation tree:
       E v | C u v | S v c <yes> <no> | R len w1 ... wlen <tree>          *)

let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: certcheck FILE"; exit 2);
  let ic = open_in Sys.argv.(1) in
  let buf = Buffer.create 65536 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  close_in ic;
  let toks = Array.of_list
      (List.filter (fun s -> s <> "")
         (String.split_on_char ' '
            (String.map (fun c -> if c = '\n' || c = '\t' || c = '\r' then ' ' else c)
               (Buffer.contents buf)))) in
  let pos = ref 0 in
  let next () = let t = toks.(!pos) in incr pos; t in
  let int () = int_of_string (next ()) in
  let n = int () in let k = int () in let m = int () in
  let edges = List.init m (fun _ -> let u = int () in let v = int () in (u, v)) in
  let verts = List.init n (fun i -> i) in
  let rec tree () =
    match next () with
    | "E" -> Certcheck.Empty (int ())
    | "C" -> let u = int () in let v = int () in Certcheck.Clash (u, v)
    | "S" -> let v = int () in let c = int () in
             let yes = tree () in let no = tree () in Certcheck.Split (v, c, yes, no)
    | "R" -> let len = int () in let w = List.init len (fun _ -> int ()) in
             Certcheck.Restrict (w, tree ())
    | t -> failwith ("bad token " ^ t) in
  let ok, what =
    match next () with
    | "COLORING" ->
        let col = Array.init n (fun _ -> int ()) in
        Certcheck.check_coloring edges verts k (fun v -> if v < n then col.(v) else 0),
        Printf.sprintf "proper %d-coloring" k
    | "REFUTATION" ->
        let r = tree () in
        Certcheck.check_refutation edges verts k r,
        Printf.sprintf "no proper %d-coloring exists" k
    | t -> failwith ("bad certificate kind " ^ t) in
  if !pos <> Array.length toks then (print_endline "INVALID (trailing tokens)"; exit 1);
  if ok then (Printf.printf "VALID: %s (n=%d, m=%d)\n" what n m; exit 0)
  else (print_endline "INVALID"; exit 1)
