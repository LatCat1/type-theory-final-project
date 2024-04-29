

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

record Subgroup (st : Type) (t : Type) where
    constructor MkSubgroup

    ss : Subset st t
    
    h : Group st
    g : Group t

    safe : ss.i h.id = g.id

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


-- TODO : center, center is a group, existance and maximality (of a subset)
--   then we want to prove the center of a group is a subgroup
