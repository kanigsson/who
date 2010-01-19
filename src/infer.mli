exception Error of string * Loc.loc

val infer_th : Ast.ParseT.theory -> Ast.Infer.theory
val recon_th : Ast.Infer.theory -> Ast.Recon.theory
