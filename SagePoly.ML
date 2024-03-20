(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)

(*Local path to the repository*)
val CWD = File.platform_path (Resources.master_directory @{theory})

(*For running sage in a local installation *)
(* val exec = "cd " ^ CWD ^ " ; sage" *)
(* val simp_script = CWD ^ "/python/poly_simp.py" *)
(* val imc_script  = CWD ^ "/python/poly_imc.py" *)

(*For running sage in a container (using podman, docker, etc)*)
val exec = "podman run --rm -v" ^ CWD ^ "/python:/home/sage/python --entrypoint sage sagemath"
val simp_script = "python/poly_simp.py"
val imc_script = "python/poly_imc.py"
(*******************************************************************)

fun simplify_cmd  params  = fn expr => exec ^ " " ^ simp_script ^ " \"false\"" ^ " \"" ^ params ^ "\" \"" ^ expr ^"\""
fun factorize_cmd params = fn expr => exec ^ " " ^ simp_script ^ " \"true\""  ^ " \"" ^ params ^ "\" \"" ^ expr ^"\""
fun imc_cmd params = fn expr => exec ^ " " ^ imc_script ^ " \"" ^ params ^ "\" \"" ^ expr ^"\""

(*Replaces 'goal' term "A" with 'newgoal' term "B" (TODO: implement) *)
fun replace_goal_tac (ctxt : Proof.context) (goal : term) (newgoal : term) = all_tac

fun term2str ctxt = Print_Mode.setmp [] (Syntax.string_of_term ctxt) 
    #> YXML.content_of #> String.translate (fn #"\n" => "" | c => str(c))

fun cmd_exec (ctxt : Proof.context) (cmd : string -> string) =
  fn (goal : term, _) => let
    val newgoal_str = goal |> term2str ctxt |> cmd |> Isabelle_System.bash_output |> fst 
    val _ = writeln ("Sage output: " ^ newgoal_str) (*debugging output*)
    val newgoal = Syntax.read_term ctxt newgoal_str
    val _ = writeln ("Parsed as: " ^ (Syntax.string_of_term ctxt newgoal)) (*debugging output*)
  in replace_goal_tac ctxt goal newgoal end