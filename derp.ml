open Core.Std

module Grammar = struct
    
    let set_fix f cur = 
        let rec loop cur = 
            let next = f cur in
            if Set.subset next cur then cur else loop (Set.union next cur) in
        loop cur
    
    let fix f cur = 
        let rec loop cur = 
            let next = f cur in
            if next = cur then next else loop next in
        loop cur

    (* take char as for now *)
    type rule = Epsilon | Empty | Token of string | NT of string | 
        Cat of rule * rule | Alt of rule * rule

    type lazyRule = Derive of rule lazy_t | Rule of rule

    let (!!) r = 
        match r with
            |Rule x -> x
            |Derive thunk -> Lazy.force thunk

    let make_derive fx = Derive (lazy fx)

    type grm = string * lazyRule String.Map.t
    
    (* return option *)
    let try_get name grm = String.Map.find (snd grm) name
    
    let get name grm = Option.value ~default:(Rule Empty) (String.Map.find (snd grm) name)

    (* get all NTs reachable from the given list of initial_nt *)
    let get_reachable_nts initial_nt grm = 
        let rec get_referenced_nts acc rule = 
            match rule with
                Epsilon | Empty | Token _ -> String.Set.empty
                |NT other -> String.Set.add acc other
                |Cat (l, r) | Alt (l, r) -> get_referenced_nts (get_referenced_nts acc l) r in
        let f reached_nts = 
            String.Set.fold reached_nts ~init:String.Set.empty 
            ~f:(fun new_nts nt_name -> 
                match try_get nt_name grm with
                    None -> new_nts
                    |Some rule -> 
                        get_referenced_nts String.Set.empty (!!rule) 
                        |> String.Set.union new_nts) in
        set_fix f (String.Set.of_list initial_nt)
    
    let string_of_rule rule = 
        let par x = "(" ^ x ^ ")" in
        let rec loop rule = 
            match rule with
                Epsilon -> "e"
                |Empty -> "E"
                |Token tok -> tok
                |NT other -> other
                |Cat (l, r) -> (loop l) ^ " " ^ (loop r)
                |Alt (l, r) -> (par (loop l)) ^ "|" ^ (par (loop r)) in
        match rule with
            Rule x -> loop x
            |Derive thunk -> Lazy.force thunk |> loop

    let string_of_grm grm = 
        let (start_name, rules) = grm in
        String.Map.fold rules ~init:("start: " ^ start_name) 
            ~f:(fun ~key:rule_name ~data:rule str -> rule_name ^ " -> " ^ (string_of_rule rule) ^ "\n" ^ str)
    
    (* undefined rule *)
    let get_undefined_nts rule grm = 
        let rec loop acc rule = 
            match rule with
            Epsilon | Empty | Token _ -> acc
            |Cat (l, r) | Alt (l, r) -> 
                loop (loop acc l) r
            |NT other -> match try_get other grm with
                None -> String.Set.add acc other
                |Some _ -> acc in
        loop String.Set.empty rule
    
    (* determine parse success or not *)
    let compute_nullable grm = 
        let rec loop_one nt_set rule = 
            match rule with
            Epsilon -> true
            |NT other -> String.Set.mem nt_set other
            |Cat (l, r) -> (loop_one nt_set l) && (loop_one nt_set r)
            |Alt (l, r) -> (loop_one nt_set l) || (loop_one nt_set r)
            |_ -> false in
        let f nts = String.Map.fold (snd grm) ~init:nts 
            ~f:(fun ~key:nt ~data:rule acc_nts -> 
                if loop_one acc_nts (!!rule) then String.Set.add acc_nts nt
                else acc_nts) in
        set_fix f String.Set.empty

    let is_nullable name nullables = String.Set.mem nullables name

    let is_nullable_rule rule nullables = 
        let rec loop rule = 
            match rule with
            Epsilon -> true
            |Empty -> false
            |NT other -> is_nullable other nullables
            |Cat (l, r) -> (loop l) && (loop r)
            |Alt (l, r) -> (loop l) || (loop r)
            |_ -> false in
        loop rule

    let get_next_name token name = 
        "d" ^ token ^ name

    let get_prev_name token next_name = 
        let to_trash = String.length token + 1 in
        String.slice next_name to_trash (String.length next_name)
    
    (* need to recursively derive undefined *)
    let derive_with token grm nullables = 
        let start_name = fst grm in
        let rule = get start_name grm in
        let new_name = get_next_name token start_name in
        let rec derive_rule rule = 
            match rule with
            Epsilon -> Empty
            |Empty -> Empty
            |Token tok -> if tok = token then Epsilon else Empty
            |Cat (l, r) -> if is_nullable_rule l nullables then Alt(Cat(derive_rule l, r), derive_rule r) else Cat(derive_rule l, r)
            |Alt (l, r) -> Alt(derive_rule l, derive_rule r)
            |NT other -> NT (get_next_name token other) in
        let rule' = derive_rule (!!rule) in
        let undefined = get_undefined_nts rule' grm in (* only one level *)
        let rules' = if not (String.Set.mem undefined new_name) then
            String.Map.add (snd grm) ~key:new_name ~data:(make_derive rule')
            else snd grm in (* add non-undefined rules *)
        (new_name, String.Set.fold undefined ~init:rules' 
            ~f:(fun acc_rules name -> let prev_name = get_prev_name token name in
            String.Map.add acc_rules ~key:name ~data:(make_derive (derive_rule (!!(get prev_name grm)))))) (* derive all undefined and add to rules'*)
    
    let all_undefined grm = 
        String.Map.fold (snd grm) ~init:String.Set.empty ~f:(fun ~key:k ~data:d set -> String.Set.union set (get_undefined_nts (!!d) grm))
    
    (* disintegrate name into (token, prev_name), assuming token length 1 *)
    let disint name = (String.slice name 1 2, String.slice name 2 (String.length name))
 
    let rec derive_rule_s rule token nullables = 
        match rule with
        Epsilon -> Empty
        |Empty -> Empty
        |Token tok -> if tok = token then Epsilon else Empty
        |Cat (l, r) -> if is_nullable_rule l nullables then Alt(Cat(derive_rule_s l token nullables, r), derive_rule_s r token nullables) else Cat(derive_rule_s l token nullables, r)
        |Alt (l, r) -> Alt(derive_rule_s l token nullables, derive_rule_s r token nullables)
        |NT other -> NT (get_next_name token other)
   
    (* recursively fill all undefined ones *)
    let rec fill grm = 
        let u = all_undefined grm and nullables = compute_nullable grm in
        if Set.is_empty u then grm
        else (
            let start = fst grm and rules = snd grm in
            let m = String.Set.fold u ~init:rules ~f:(fun ruleset name -> let (token, prev_name) = disint name in String.Map.add ruleset ~key:name ~data:(make_derive (derive_rule_s (!! (get prev_name grm)) token nullables))) 
            in
            let newg = (start, m) in fill newg
        )
    

    let derive token grm = 
        let nullables = compute_nullable grm in
        let g1 = derive_with token grm nullables in
        fill g1

    (* compute the FIRST-set for grm *)

    let compute_first_with grm nullables = 
        let fold_first_maps map_left map_right = 
            String.Map.fold map_left ~init:map_right
                ~f:(fun ~key:name ~data:first_set acc_map -> 
                    match String.Map.find acc_map name with
                    None -> String.Map.add acc_map ~key:name ~data:first_set
                    |Some first_set_acc -> String.Map.add acc_map ~key:name ~data:(String.Set.union first_set first_set_acc)) in
        let rec step first_map_acc name rule = 
            match rule with
            Epsilon | Empty -> String.Map.add first_map_acc ~key:name ~data:String.Set.empty
            |NT other ->
                begin
                match String.Map.find first_map_acc other with
                Some first_set -> String.Map.add first_map_acc ~key:name ~data:first_set
                |None -> String.Map.add first_map_acc ~key:name ~data:String.Set.empty
                end
            |Token tok -> String.Map.add first_map_acc ~key:name ~data:(String.Set.of_list [tok])
            |Alt (l, r) -> let map_left = step first_map_acc name l in
                           let map_right = step first_map_acc name r in
                           fold_first_maps map_left map_right
            |Cat (l, r) -> let map_left = step first_map_acc name l in
                           if not (is_nullable_rule l nullables)
                           then map_left
                           else fold_first_maps map_left (step first_map_acc name r) in
        let first_step first_map = 
            String.Map.fold (snd grm) ~init:first_map 
            ~f:(fun ~key:name ~data:d_rule acc -> step acc name (!!d_rule)) in
        fix first_step String.Map.empty
    
    (* str is a list of token strings *)
     let recognize str grm = 
        let rec loop g l = match l with
            [] -> Set.mem (compute_nullable g) (fst g)
            |h :: t -> loop (derive h g) t
        in loop grm str
    
    (* testing *)

    let add_rule ~key:k ~data:d m = String.Map.add m ~key:k ~data:d
    let e = String.Map.empty

    let test_map = 
    e
    |> add_rule ~key:"B" ~data:(Rule(Alt(Token "0", Token "1")))
    |> add_rule ~key:"S" ~data:(Rule(Alt(Epsilon, Cat(NT "B", NT "S"))))

    let test_grammar : grm = "S", test_map

end
