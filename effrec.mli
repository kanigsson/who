type t

val from_form_t : Ty.t -> Ast.Recon.t -> t
val from_form : NEffect.t -> Ast.Recon.t -> t

val get_reg : Name.t -> t -> Name.t
val rfold : (Name.t -> Name.t -> 'b -> 'b) -> t -> 'b -> 'b
val efold : (Name.t -> Name.t -> 'b -> 'b) -> t -> 'b -> 'b
