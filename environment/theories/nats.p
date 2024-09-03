nat : type.

z : nat.
s : [nat -> nat].

= : [('t : type) -> 't -> 't -> prop].

exists : [('t : type) -> ['t -> prop] -> prop].
ex_intro : [(x : 't) -> ('p : ['t -> prop]) -> ('p x) -> (exists 't 'p)].
ex_elim : [(g : (exists 't 'p)) -> [(x : 't) -> ('p x) -> 'q] -> 'q].

or_elim : [(or 'p 'q) -> ['p -> 'r] -> ['q -> 'r] -> 'r].

leq : [nat -> nat -> prop].
leq_n_n : [('n : nat) -> (leq 'n 'n)].
leq_n_sn : [('n : nat) -> (leq 'n (s 'n))].

leq_trans : [(leq 'a 'b) -> (leq 'b 'c) -> (leq 'a 'c)].

nat_ind : [('p : [nat -> prop]) -> ('p z) -> [('n : nat) -> ('p 'n) -> ('p (s 'n))] -> [('n : nat) -> ('p 'n)]].

add : [nat -> nat -> nat].

add_z : [(n : nat) -> (= (add z n) n)].
add_s : [(n : nat) -> (m : nat) -> (= (add (s m) n) (s (add m n)))].

verify two_plus_two {
    let one : nat = (s z).
    let two : nat = (s one).
    let three : nat = (s two).
    let four : nat = (s three).

    let two_plus_two : nat = (add two two).

    show (= (add two two) (s (add one two))) by add_s.
    show (= (add one two) (s (add z two))) by add_s.
    show (= (add z two) two) by add_z.
    show (= (add one two) three) by rewrite.

    show (= two_plus_two four) by rewrite.
}

theorem z_leq_z : [(n : nat) -> (= z n) -> (= n z)] {
    intro n : nat.
    intro h : (= z n).
    current goal: (= n z).
    show (= z z) by eq_refl.
    show (= n z) by rewrite.
}

theorem z_leq_n : [('n : nat) -> (leq z 'n)] {
    apply nat_ind.
    goal (leq z z) {
        show (leq z z) by leq_n_n.
    }
    goal [('n : nat) -> (leq z 'n) -> (leq z (s 'n))] {
         intro n : nat.
         intro h : (leq z n).
         current goal: (leq z (s n)).
         show (leq n (s n)) by leq_n_sn.
         show (leq z (s n)) by leq_trans.
    }
}

theorem add_z_right : [('n : nat) -> (= (add 'n z) 'n)] {
    apply nat_ind.

    goal (= (add z z) z) {
        show (= (add z z) z) by add_z.
    }
    goal [('n : nat) -> (= (add 'n z) 'n) -> (= (add (s 'n) z) (s 'n))] {
        intro n : nat.
        intro h : (= (add n z) n).
        current goal: (= (add (s n) z) (s n)).

        show (= (add (s n) z) (s (add n z))) by add_s.
        show (= (add (s n) z) (s n)) by rewrite.
    }
}

theorem add_comm : [('n : nat) -> ('m : nat) -> (= (add 'n 'm) (add 'm 'n))] {
    intro n : nat.
    apply nat_ind.
    goal (= (add n z) (add z n)) {
        show (= (add n z) n) by add_z_right.

        show (= (add z n) n) by add_z.
        show (= n (add z n)) by eq_symm.

        show (= (add n z) (add z n)) by rewrite.
    }
    goal [('m : nat) -> (= (add n 'm) (add 'm n)) -> (= (add n (s 'm)) (add (s 'm) n))] {
        apply nat_ind.
        goal [(= (add n z) (add z n)) -> (= (add n (s z)) (add (s z) n))] {

        }
        goal [('m : nat) -> [(= (add n 'm) (add 'm n)) -> (= (add n (s 'm)) (add (s 'm) n))] -> [(= (add n (s 'm)) (add (s 'm) n)) -> (= (add n (s (s 'm))) (add (s (s 'm)) n))]] {

        }
    }
}

theorem ex_pos_nat : (exists nat (lambda ('n : nat) (leq (s z) 'n))) {
    construct one : nat = (s z) by s.
    construct two : nat = (s (s z)) by s.

    apply ex_intro.
    goal (leq (s z) (s (s z))) {
        show (leq (s z) (s (s z))) by leq_n_sn.
    }
}

or : [prop -> prop -> prop].
or_l : [('p : prop) -> ('q : prop) -> 'p -> (or 'p 'q)].
or_r : [('p : prop) -> ('q : prop) -> 'q -> (or 'p 'q)].

or_elim : [('p : prop) -> ('q : prop) -> (or 'p 'q) ->
           ('r : prop) -> ['p -> 'r] -> ['q -> 'r]
           -> 'r].

theorem or_comm : [('p : prop) -> ('q : prop) -> (or 'p 'q) -> (or 'q 'p)] {
    intro p : prop.
    intro q : prop.
    intro h : (or p q).
    apply or_elim.
    goal [p -> (or q p)] {
        intro hp : p.
        show (or q p) by or_r.
    }
    goal [q -> (or q p)] {
        intro hq : q.
        show (or q p) by or_l.
    }
}
