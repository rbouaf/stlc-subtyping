(* 
   William Melançon & Rayane Bouafia
   COMP523 Final Project
*) 

type tp = Func of tp * tp
        | Prod of tp * tp 
        | TpRec of (string * tp) list 
        | Nat
        | TpFloat 
        | Top
        | TyBool
          
type tm = 
  | Var of string 
  | Zero
  | Succ of tm
  | TmFloat of string
  | Lambda of string * tp * tm
  | App of tm * tm
  | Tuple of tm * tm
  | TmFst of tm                 
  | TmSnd of tm
  | TmRec of (string * tm) list
  | TmProj of tm * string     
  | TmTrue
  | TmFalse
  | TmIf of tm * tm * tm

type context = (string * tp) list 
    
let rec to_string t = match t with
  | Nat -> "Nat"
  | TpFloat -> "Float"
  | Top -> "Top"
  | TyBool -> "Bool"
  | Func(t1, t2) -> "(" ^ to_string t1 ^ " -> " ^ to_string t2 ^ ")"
  | Prod(t1, t2) -> "(" ^ to_string t1 ^ " * " ^ to_string t2 ^ ")"
  | TpRec(fields) ->
      let field_strs = List.map (fun (l, ty) -> l ^ ":" ^ to_string ty) fields in
      "{" ^ String.concat ", " field_strs ^ "}"

let rec subtype (sub : tp) (check : tp) : bool = 
  if sub = check then true else
    match (sub, check) with
    
    | (_, Top) -> true
      
    | (Nat, TpFloat) -> true
      
    | (Func (s1, s2), Func (t1, t2)) -> subtype t1 s1 && subtype s2 t2
  
    | (Prod (s1, s2), Prod (t1, t2)) -> subtype s1 t1 && subtype s2 t2 
                                          
    | (TpRec l2, TpRec l1) ->
        List.for_all (fun (l1i, t1i) -> 
            try
              let t2i = List.assoc l1i l2 in subtype t2i t1i
            with Not_found -> false)
          l1 
          
    | (_, _) -> false
      
  
exception TypeError

let rec join ty1 ty2 =
  if subtype ty1 ty2 then ty2
  else if subtype ty2 ty1 then ty1
  else match (ty1, ty2) with
    | (Nat, TpFloat) | (TpFloat, Nat) -> TpFloat
    | (Prod(s1, s2), Prod(t1, t2)) -> Prod(join s1 t1, join s2 t2)
    | (Func(s1, s2), Func(t1, t2)) -> Func(meet s1 t1, join s2 t2) 
    | (TpRec fs, TpRec ft) ->
        let common_fields =
          List.filter_map (fun (ls, tys) ->
              try Some (ls, join tys (List.assoc ls ft))
              with Not_found -> None ) fs in
        TpRec common_fields
    | (_, _) -> Top

and meet ty1 ty2 = 
  if subtype ty1 ty2 then ty1
  else if subtype ty2 ty1 then ty2
  else match (ty1, ty2) with
    | (Nat, TpFloat) | (TpFloat, Nat) -> Nat
      
    | (Prod(s1, s2), Prod(t1, t2)) -> Prod(meet s1 t1, meet s2 t2)
                                        
    | (Func(s1, s2), Func(t1, t2)) -> Func(join s1 t1, meet s2 t2) 
          
    | (TpRec fs, TpRec ft) ->
        let names_s = List.map fst fs in
        let names_t = List.map fst ft in
        let all_names_dup = names_s @ names_t in
        let all_names_uniq = List.sort_uniq compare all_names_dup in

        let meet_fields =
          List.map (fun name ->
              match (List.assoc_opt name fs, List.assoc_opt name ft) with
              | (Some tys, Some tyt) -> (name, meet tys tyt) 
              | (Some tys, None) -> (name, tys)
              | (None, Some tyt) -> (name, tyt)
              | (None, None) -> raise Not_found
            ) all_names_uniq
        in
        TpRec meet_fields
          
    | (_,_) -> raise Not_found
                 
                 
let lookup (ctx : context) (var : string) : tp =
  match List.assoc_opt var ctx with
  | Some a -> a
  | None -> raise TypeError
  

let rec typeof (ctx : context) (t : tm) : tp =
  match t with
  | Var x -> lookup ctx x
               
  | Zero -> Nat
    
  | Succ t' -> typeof ctx t'
                 
  | TmFloat _ -> TpFloat
  | TmTrue -> TyBool
  | TmFalse -> TyBool
    
  | Lambda (_, typ, t') -> Func (typ, typeof ctx t')
                             
  | App (t1, t2) -> 
      let tp1 = typeof ctx t1 in
      let tp2 = typeof ctx t2 in
      begin
        match tp1 with
        | Func (t1', t2') -> if subtype tp2 t1' then t2' else raise TypeError
        | _ -> raise TypeError
      end
      
  | Tuple (t1, t2) -> Prod (typeof ctx t1, typeof ctx t2)
                        
  | TmFst t1 -> 
      begin 
        match typeof ctx t1 with
        | Prod (typ_t11, _) -> typ_t11
        | typ -> raise TypeError
      end
  | TmSnd t1 ->
      begin 
        match typeof ctx t1 with
        | Prod (_, typ_t12) -> typ_t12
        | typ -> raise TypeError
      end
  | TmProj (t_rec, label) -> 
      begin 
        match typeof ctx t_rec with
        | TpRec typed_fields ->
            begin 
              match List.assoc_opt label typed_fields with
              | Some typ_field -> typ_field
              | None -> raise TypeError
            end
        | typ -> raise TypeError
      end
      
  | TmRec l -> let tpl = List.map (fun (li, ti) -> (li, typeof ctx ti)) l in TpRec tpl 
  | TmIf (t_cond, t_then, t_else) ->
      let typ_cond = typeof ctx t_cond in
      if typ_cond = TyBool then
        let typ_then = typeof ctx t_then in
        let typ_else = typeof ctx t_else in
        join typ_then typ_else
      else
        raise TypeError
        (* | _  -> raise TypeError  no longer needed according to OCaml*)


let func1 = Lambda ("x", Nat, TmFloat "3.14159")     (* Nat -> Float *)
let func2 = Lambda ("y", TpFloat, TmFloat "3.14159") (* Float -> Float *) 
let func3 = Lambda ("x", Nat, Succ (Zero))           (* Nat -> Nat *)
let func4 = Lambda ("y", TpFloat, Succ (Zero))       (* Float -> Nat *)
                                                     
let type1 = typeof [] func1
let type2 = typeof [] func2
let type3 = typeof [] func3
let type4 = typeof [] func4

let test1 = subtype type1 type2
let test2 = subtype type2 type3
let test3 = subtype type3 type4
    
let rec1 = TmRec [("x", TmFloat "3.14159"); ("y", TmTrue)]
let rec2 = TmRec [("x", Succ (Succ (Zero))); ("y", TmFalse); ("z", TmFloat "1.5")]
    
let type4 = typeof [] rec1
let type5 = typeof [] rec2
    
let test4 = subtype type4 type5
let test5 = subtype type5 type4
  
let t_then =  TmRec [("x", TmFalse); ("y", TmTrue)]
let t_else =  TmRec [("x", TmFalse); ("z", TmTrue)]
let t_if = TmIf (TmTrue, t_then, t_else)
    
let s_then = func1
let s_else = func3
let s_if = TmIf (TmTrue, s_then, s_else)
    
let type6 = typeof [] t_if  
let type7 = typeof [] s_if  
    

  