= : [('t : type) -> 't -> 't -> prop].

G : type.

op : [G -> G -> G].
id : G.

/* Associativity */
#forward op_assoc ((op (op 'a 'b) 'c) : G).
op_assoc : [('a : G) -> ('b : G) -> ('c : G) -> (= (op (op 'a 'b) 'c) (op 'a (op 'b 'c)))].

/* Commutativity */
#forward op_comm ((op 'a 'b) : G).
op_comm : [('a : G) -> ('b : G) -> (= (op 'a 'b) (op 'b 'a))].

/* Identity */
#forward id_l.
id_l : [('a : G) -> (= (op id 'a) 'a)].

/* Inverse */
inv : [G -> G].
#forward inv_l.
inv_l : [('a : G) -> (= (op (inv 'a) 'a) id)].
