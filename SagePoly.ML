(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)

(************************ CONFIGURATION ***************************)

(*Local path to the repository*)
val CWD = File.platform_path (Resources.master_directory @{theory})

(*For running sage locally *)
(* val exec = "cd " ^ CWD ^ " ; sage" *)
(* val script = CWD ^ "python/SagePoly.py" *)

(*For running sage in a container (docker/podman)*)
val exec = "podman run --rm -v" ^ CWD ^ "/python:/home/sage/python --entrypoint sage sagemath"
val script = "python/SagePoly.py"
(*******************************************************************)

fun simp_cmd  params  = fn poly => exec ^ " " ^ script ^ " \"false\"" ^ " \"" ^ params ^ "\" \"" ^ poly ^"\""
fun factor_cmd params = fn poly => exec ^ " " ^ script ^ " \"true\""  ^ " \"" ^ params ^ "\" \"" ^ poly ^"\""

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

(*TODO: make the following visible as proof methods from importing theory files*)
(*
Method.setup (Binding.name "polyfact")
(Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (factor_cmd (term2str ctxt params)))))
Method.setup (Binding.name "polysimp")
(Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (simp_cmd (term2str ctxt params)))))
*)