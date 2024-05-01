

injective : (a : Type) ->
            (b : Type) ->
            (f : a -> b) ->
            Type
injective a b f = (x : a) ->
                  (y : a) ->
                  f x = f y ->
                  x = y


record Subset (st : Type) (t : Type) where
    constructor MkSubset

    i : st -> t
    i_inj : injective st t i


record Group (t : Type) where
    constructor MkGroup

    op : t -> t -> t
    op_assoc : (x : t) ->
               (y : t) ->
               (z : t) ->
               op (op x y) z = op x (op y z)

    id : t
    id_l : (x : t) ->
           op id x = x
    id_r : (x : t) ->
           op x id = x

    inv : t -> t
    inv_l : (x : t) ->
            op (inv x) x = id
    inv_r : (x : t) ->
            op x (inv x) = id

-- TODO: is this the representation we want?
record Subgroup (st : Type) (t : Type) (g : Group t) where
    constructor MkSubgroup

    ss : Subset st t 
    h : Group st

    safe_id : ss.i h.id = g.id
    safe_op : (x : st) ->
              (y : st) ->
              ss.i (h.op x y) = g.op (ss.i x) (ss.i y)

unique_id_l : (t : Type) ->
              (g : Group t) ->
              (id' : t) ->
              ((x : t) -> (g.op id' x) = x) ->
              id' = g.id
unique_id_l t g id' eq =
    trans (sym (g.id_r id')) $ eq g.id
unique_id_r : (t : Type) ->
              (g : Group t) ->
              (id' : t) ->
              ((x : t) -> (g.op x id') = x) ->
              id' = g.id
unique_id_r t g id' eq =
    trans (sym (g.id_l id')) $ eq g.id


mov_l : (t : Type) ->
        (g : Group t) ->
        (x : t) -> 
        (y : t) ->
        (z : t) ->
        g.op x y = z ->
        y = g.op (g.inv x) z
mov_l t g x y z eq =
    trans
        (sym $ g.id_l y) $
        trans 
            (cong (flip g.op y) $ sym $ g.inv_l x) $
            trans
                (g.op_assoc (g.inv x) x y) $
                cong (g.op (g.inv x)) eq

mov_r : (t : Type) ->
        (g : Group t) ->
        (x : t) -> 
        (y : t) ->
        (z : t) ->
        g.op x y = z ->
        x = g.op z (g.inv y)
mov_r t g x y z eq =
    trans
        (sym $ g.id_r x) $
        trans 
            (cong (g.op x) $ sym $ g.inv_r y) $
            trans 
                (sym $ g.op_assoc x y (g.inv y)) $
                cong (flip g.op (g.inv y)) eq

cancel_l : (t : Type) ->
           (g : Group t) ->
           (a : t) ->
           (x : t) ->
           (y : t) ->
           g.op a x = g.op a y ->
           x = y
cancel_l t g a x y eq =
    trans
        (mov_l t g a x (g.op a y) eq) $
        trans
            (sym $ g.op_assoc (g.inv a) a y) $
            trans
                (cong (flip g.op y) $ g.inv_l a) $
                g.id_l y

cancel_r : (t : Type) ->
           (g : Group t) ->
           (a : t) ->
           (x : t) ->
           (y : t) ->
           g.op x a = g.op y a ->
           x = y
cancel_r t g a x y eq =
    trans
        (mov_r t g x a (g.op y a) eq) $
    trans
        (g.op_assoc y a (g.inv a)) $
    trans
        (cong (g.op y) $ g.inv_r a) $
    g.id_r y


inv_inj : (t : Type) ->
          (g : Group t) ->
          (injective t t g.inv)
inv_inj t g x y eq = 
    trans 
        (sym $ g.id_r x) $
    trans 
        (cong (g.op x) $ sym $ g.inv_l y) $
    trans
        (cong (\z => g.op x (g.op z y)) $ sym eq) $
    trans
        (sym $ g.op_assoc x (g.inv x) y) $
    trans
        (cong (flip g.op y) $ g.inv_r x) $
    g.id_l y

inv_order_2 : (t : Type) ->
              (g : Group t) ->
              (x : t) ->
              g.inv (g.inv x) = x
inv_order_2 t g x = sym $
    trans
        (sym $ g.id_l x) $
    trans
        (cong (flip g.op x) $ sym $ g.inv_l $ g.inv x) $
    trans
        (g.op_assoc (g.inv $ g.inv x) (g.inv x) x) $
    trans
        (cong (g.op (g.inv $ g.inv x)) $ g.inv_l x) $
    g.id_r $ g.inv $ g.inv x


inv_unique_r : (t : Type) ->
               (g : Group t) ->
               (x : t) ->
               (y : t) ->
               g.op x y = g.id ->
               y = g.inv x
inv_unique_r t g x y eq =
    trans
        (mov_l t g x y g.id eq) $
    g.id_r $ g.inv x


inv_semicommutes : (t : Type) ->
                   (g : Group t) ->
                   (x : t) ->
                   (y : t) ->
                   g.op (g.inv y) (g.inv x) = g.inv (g.op x y)
inv_semicommutes t g x y =
    inv_unique_r t g 
        (g.op x y)
        (g.op (g.inv y) (g.inv x)) $
    trans
        (g.op_assoc x y (g.op (g.inv y) (g.inv x))) $
    trans
        (cong (g.op x) $
            trans
                (sym $ g.op_assoc y (g.inv y) (g.inv x)) $
            trans
                (cong (flip g.op (g.inv x)) $ g.inv_r y) $
            g.id_l $ g.inv x) $
    g.inv_r x 



record Exists (t : Type) (prop : t -> Type) where
    constructor MkExists
    -- the element
    val : t
    -- a function that takes x and a proof of what it satisfies
    sat : prop val


-- A subgroup is maximal with respect to some property
maximal : (st : Type) ->
          (t : Type) ->
          (Subset st t) ->
          (prop : t -> Type) ->
          Type
maximal st t ss prop =
    (x : t) -> prop x -> Exists st (\v => ss.i v = x)



commutes : (t : Type) ->
           (g : Group t) ->
           (x : t) ->
           Type
commutes t g x =
   (y : t) -> g.op x y = g.op y x 

comm_compose : (t : Type) ->
               (g : Group t) ->
               (x : t) ->
               (y : t) ->
               (commutes t g x) ->
               (commutes t g y) ->
               (commutes t g (g.op x y))
-- TODO: use this
comm_inv : (t : Type) ->
           (g : Group t) ->
           (x : t) ->
           (commutes t g x) ->
           (commutes t g (g.inv x))



record Center (st : Type) (t : Type) (g : Group t) (ss : Subset st t) where
    constructor MkCenter

    sats : (x : st) -> commutes t g (ss.i x)
    maxi : maximal st t ss (\x => commutes t g x)


center_is_subgroup : (st : Type) ->
                     (t : Type)  ->
                     (g : Group t) ->
                     (ss : Subset st t) ->
                     (cent : Center st t g ss) ->
                     Subgroup st t g

center_is_subgroup st t g ss cent =
    MkSubgroup ss h safe_id safe_op
    where
        op' : st -> st -> st
        op'_base x y = cent.maxi (g.op (ss.i x) (ss.i y)) $
                       comm_compose t g (ss.i x) (ss.i y) (cent.sats x) (cent.sats y)
        op' x y = val $ op'_base x y         
        safe_op x y = sat $ op'_base x y
       

        op_assoc' x y z = ss.i_inj 
                            (op' (op' x y) z) 
                            (op' x (op' y z)) $
                            trans 
                                (safe_op (op' x y) z) $
                            trans
                                (cong (flip g.op (ss.i z)) $ safe_op x y) $
                            trans
                                (g.op_assoc (ss.i x) (ss.i y) (ss.i z)) $
                            trans
                                (cong (g.op (ss.i x)) $ sym $ safe_op y z) $
                            (sym $ safe_op x (op' y z))

      
        -- e commutes with everything, so there is an element in 
        -- our underlying set that maps to it
        -- id_p    : Exists st (\m => ss.i m = g.id)
        id_p    = cent.maxi g.id (\y => trans (g.id_l y) $ sym $ g.id_r y)
        -- id'     : st
        id'     = id_p.val
        -- safe_id : ss.i (id_p.val) = g.id
        safe_id = sat id_p

        id_l' x = ss.i_inj (op' id' x) x $ 
                  trans (safe_op id' x) $
                      trans (cong (flip g.op (ss.i x)) $ safe_id) $
                            g.id_l (ss.i x)
        
        id_r' x = ss.i_inj (op' x id') x $ 
                  trans (safe_op x id') $
                      trans (cong (g.op (ss.i x)) $ safe_id) $
                            g.id_r (ss.i x)


        inv'_base x = cent.maxi (g.inv $ ss.i x) $ comm_inv t g (ss.i x) (cent.sats x)
        inv'      x = val $ inv'_base x


        -- honestly i have no clue how this works anymore
        -- i think its i(x'x) = i(e) and then using injectivity
        -- where x'x=e using that the operation is good with i
        inv_l' x = ss.i_inj (op' (inv' x) x) id' $
                   trans (safe_op (inv' x) x) $
                       trans (cong (flip g.op (ss.i x)) $ sat $ inv'_base x) $
                          trans (g.inv_l $ ss.i x)
                                (sym $ safe_id) 
        
        -- thankfully this one is just symmetric
        inv_r' x = ss.i_inj (op' x (inv' x)) id' $
                   trans (safe_op x (inv' x)) $
                       trans (cong (g.op (ss.i x)) $ sat $ inv'_base x) $
                          trans (g.inv_r $ ss.i x)
                                (sym $ safe_id)


        h = MkGroup op' op_assoc' id' id_l' id_r' inv' inv_l' inv_r'


