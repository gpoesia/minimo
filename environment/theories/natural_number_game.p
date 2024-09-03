/*
    All definitions and theorems from the natural number game:
    https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game
*/

= : [('t : type) -> 't -> 't -> prop].

nat : type.

z : nat.
s : [nat -> nat].

leq : [nat -> nat -> prop].
lt : [nat -> nat -> prop].
gt : [nat -> nat -> prop].

+ : [nat -> nat -> nat].
* : [nat -> nat -> nat].
^ : [nat -> nat -> nat].

/* Defining axioms for addition */
+_z : [('n : nat) -> (= (+ 'n z) 'n)].
+_s : [('n : nat) -> ('m : nat) -> (= (+ 'n (s 'm)) (s (+ 'n 'm)))].

/* Defining axioms for multiplication */
*_z : [('n : nat) -> (= (* 'n z) z)].
*_s : [('n : nat) -> ('m : nat) -> (= (* 'n (s 'm)) (+ 'n (* 'n 'm)))].

/* Defining axioms for exponentiation */
^_z : [('n : nat) -> (= (^ 'n z) (s z))].
^_s : [('n : nat) -> ('m : nat) -> (= (^ 'n (s 'm)) (* 'n (^ 'n 'm)))].

false : prop.
not : [prop -> prop] = (lambda ('p : prop) ['p -> false]).

and : [prop -> prop -> prop].
or : [prop -> prop -> prop].
iff : [prop -> prop -> prop].


/* Natural number induction */
nat_ind : [('p : [nat -> prop]) -> ('p z) -> [('n : nat) -> ('p 'n) -> ('p (s 'n))] -> [('n : nat) -> ('p 'n)]].

/***

    Tutorial world

***/

lemma t_example1 : [('x : nat) -> ('y : nat) -> ('z : nat) ->
                    (= (+ (* x y) z) (+ (* x y) z))]
{
    intro x : nat.
    intro y : nat.
    intro z : nat.
    show (= (+ (* x y) z) (+ (* x y) z)) by eq_refl.
}

let n7 : nat = (s (s (s (s (s (s (s z))))))).
let n2 : nat = (s (s z)).

lemma t_example2 : [('x : nat) -> ('y : nat) -> (= 'y (+ 'x n7)) -> (= (* n2 'y) (* n2 (+ 'x n7)))]
{
    intro x : nat.
    intro y : nat.
    intro h : (= y (+ x n7)).
    construct a : nat = (* n2 y) by *.
    show (= (* n2 y) (* n2 y)) by eq_refl.
    show (= (* n2 y) (* n2 (+ x n7))) by rewrite.
}

lemma t_example3 : [('a : nat) -> ('b : nat) -> (= (s 'a) 'b) -> (= (s (s 'a)) (s 'b))]
{
    intro a : nat.
    intro b : nat.
    intro h : (= (s a) b).
    show (= (s (s a)) (s (s a))) by eq_refl.
    show (= (s (s a)) (s b)) by rewrite.
}

lemma t_add_succ_zero : [('a : nat) -> (= (+ 'a (s z)) (s 'a))]
{
    intro a : nat.
    show (= (+ a (s z)) (s (+ a z))) by +_s.
    show (= (+ a z) a) by +_z.
    show (= (+ a (s z)) (s a)) by rewrite.
}


/***

    Addition world

***/

lemma a_zero_add : [('n : nat) -> (= (+ z 'n) 'n)] {
    apply nat_ind.

    goal (= (+ z z) z) {
        show (= (+ z z) z) by +_z.
    }
    goal [('n : nat) -> (= (+ z 'n) 'n) -> (= (+ z (s 'n)) (s 'n))] {
        intro n : nat.
        intro h : (= (+ z n) n).
        show (= (+ z (s n)) (s (+ z n))) by +_s.
        show (= (+ z (s n)) (s n)) by rewrite.
    }
}

lemma a_add_assoc : [('a : nat) -> ('b : nat) -> ('c : nat) -> (= (+ (+ 'a 'b) 'c) (+ 'a (+ 'b 'c)))] {
      intro a : nat.
      intro b : nat.
      apply nat_ind.
      goal (= (+ (+ a b) z) (+ a (+ b z))) {
          show (= (+ b z) b) by +_z.
          show (= b (+ b z)) by eq_symm.

          show (= (+ (+ a b) z) (+ a b)) by +_z.
          show (= (+ (+ a b) z) (+ a (+ b z))) by rewrite.
      }
      goal [('c : nat) -> (= (+ (+ a b) 'c) (+ a (+ b 'c))) -> (= (+ (+ a b) (s 'c)) (+ a (+ b (s 'c))))] {
          intro c : nat.
          intro h : (= (+ (+ a b) c) (+ a (+ b c))).

          have (= (s (+ a (+ b c))) (+ (+ a b) (s c))) {
               show (= (+ (+ a b) (s c)) (s (+ (+ a b) c))) by +_s.
               show (= (+ (+ a b) (s c)) (s (+ a (+ b c)))) by rewrite.
               show (= (s (+ a (+ b c))) (+ (+ a b) (s c))) by eq_symm.
          }

          show (= (+ a (s (+ b c))) (s (+ a (+ b c)))) by +_s.
          show (= (+ b (s c)) (s (+ b c))) by +_s.

          show (= (s (+ b c)) (+ b (s c))) by eq_symm.
          show (= (+ a (+ b (s c))) (s (+ a (+ b c)))) by rewrite.
          show (= (+ a (+ b (s c))) (+ (+ a b) (s c))) by rewrite.
          show (= (+ (+ a b) (s c)) (+ a (+ b (s c)))) by eq_symm.
      }
}

lemma a_succ_add : [('a : nat) -> ('b : nat) -> (= (+ (s 'a) 'b) (s (+ 'a 'b)))] {
      intro a : nat. apply nat_ind.
      goal (= (+ (s a) z) (s (+ a z))) {
          show (= (+ (s a) z) (s a)) by +_z.
          show (= (+ a z) a) by +_z.
          show (= a (+ a z)) by eq_symm.
          show (= (+ (s a) z) (s (+ a z))) by rewrite.
      }
      goal [('b : nat) -> (= (+ (s a) 'b) (s (+ a 'b))) -> (= (+ (s a) (s 'b)) (s (+ a (s 'b))))] {
        intro b : nat.
        intro h : (= (+ (s a) b) (s (+ a b))).

        current goal: (= (+ (s a) (s b)) (s (+ a (s b)))).

        show (= (+ (s a) (s b)) (s (+ (s a) b))) by +_s.
        show (= (+ (s a) (s b)) (s (s (+ a b)))) by rewrite.

        show (= (+ a (s b)) (s (+ a b))) by +_s.
        show (= (s (+ a b)) (+ a (s b))) by eq_symm.
        show (= (+ (s a) (s b)) (s (+ a (s b)))) by rewrite.
      }
}

lemma a_add_comm : [('a : nat) -> ('b : nat) -> (= (+ 'a 'b) (+ 'b 'a))] {
      apply nat_ind.
      goal [('b : nat) -> (= (+ z 'b) (+ 'b z))] {
          intro b : nat.
          show (= (+ z b) b) by a_zero_add.
          show (= (+ b z) b) by +_z.
          show (= b (+ b z)) by eq_symm.
          show (= (+ z b) (+ b z)) by rewrite.
      }
      goal [('a : nat) -> [('b : nat) -> (= (+ 'a 'b) (+ 'b 'a))] -> [('b : nat) -> (= (+ (s 'a) 'b) (+ 'b (s 'a)))]] {
          intro a : nat.
          intro ih : [('b : nat) -> (= (+ a 'b) (+ 'b a))].
          intro b : nat.
          show (= (+ (s a) b) (s (+ a b))) by a_succ_add.
          show (= (+ a b) (+ b a)) by ih.
          show (= (+ (s a) b) (s (+ b a))) by rewrite.
          show (= (+ b (s a)) (s (+ b a))) by +_s.
          show (= (s (+ b a)) (+ b (s a))) by eq_symm.
          show (= (+ (s a) b) (+ b (s a))) by rewrite.
      }
}

theorem a_succ_eq_add_one : [('n : nat) -> (= (s 'n) (+ 'n (s z)))] {
    intro n : nat.
    show (= (+ n (s z)) (s (+ n z))) by +_s.
    show (= (+ n z) n) by +_z.
    show (= (+ n (s z)) (s n)) by rewrite.
    show (= (s n) (+ n (s z))) by eq_symm.
}

lemma a_add_right_comm : [('a : nat) -> ('b : nat) -> ('c : nat) -> (= (+ (+ 'a 'b) 'c) (+ (+ 'a 'c) 'b))] {
    intro a : nat.
    intro b : nat.
    intro c : nat.

    show (= (+ (+ a b) c) (+ a (+ b c))) by a_add_assoc.
    show (= (+ b c) (+ c b)) by a_add_comm.
    show (= (+ (+ a b) c) (+ a (+ c b))) by rewrite.

    show (= (+ (+ a c) b) (+ a (+ c b))) by a_add_assoc.
    show (= (+ a (+ c b)) (+ (+ a c) b)) by eq_symm.
    show (= (+ (+ a b) c) (+ (+ a c) b)) by rewrite.
}


/***

   Multiplication world

***/

lemma m_zero_mul : [('m : nat) -> (= (* z 'm) z)] {
    apply nat_ind.
    goal (= (* z z) z) {
        show (= (* z z) z) by *_z.
    }
    goal [('m : nat) -> (= (* z 'm) z) -> (= (* z (s 'm)) z)] {
        intro m : nat.
        intro h : (= (* z m) z).

        show (= (* z (s m)) (+ z (* z m))) by *_s.
        show (= (* z (s m)) (+ z z)) by rewrite.
        show (= (+ z z) z) by +_z.
        show (= (* z (s m)) z) by rewrite.
    }
}

lemma m_mul_one : [('m : nat) -> (= (* 'm (s z)) 'm)] {
    intro m : nat.
    show (= (* m (s z)) (+ m (* m z))) by *_s.
    show (= (* m z) z) by *_z.
    show (= (* m (s z)) (+ m z)) by rewrite.
    show (= (+ m z) m) by +_z.
    show (= (* m (s z)) m) by rewrite.
}

lemma m_one_mul : [('m : nat) -> (= (* (s z) 'm) 'm)] {
    apply nat_ind.
    goal (= (* (s z) z) z) {
         show (= (* (s z) z) z) by *_z.
    }
    goal [('m : nat) -> (= (* (s z) 'm) 'm) -> (= (* (s z) (s 'm)) (s 'm))] {
        intro m : nat.
        intro h : (= (* (s z) m) m).

        show (= (* (s z) (s m)) (+ (s z) (* (s z) m))) by *_s.
        show (= (* (s z) (s m)) (+ (s z) m)) by rewrite.

        show (= (+ (s z) m) (+ m (s z))) by a_add_comm.
        show (= (s m) (+ m (s z))) by a_succ_eq_add_one.
        show (= (+ m (s z)) (s m)) by eq_symm.
        show (= (+ (s z) m) (s m)) by rewrite.

        show (= (* (s z) (s m)) (s m)) by rewrite.
    }
}

lemma m_mul_add : [('t : nat) -> ('a : nat) -> ('b : nat) -> (= (* 't (+ 'a 'b)) (+ (* 't 'a) (* 't 'b)))] {
    intro t : nat.
    intro a : nat.
    apply nat_ind.

    goal (= (* t (+ a z)) (+ (* t a) (* t z))) {
        show (= (+ a z) a) by +_z.
        show (= (* t (+ a z)) (* t (+ a z))) by eq_refl.
        show (= (* t (+ a z)) (* t a)) by rewrite.

        show (= (* t z) z) by *_z.
        show (= z (* t z)) by eq_symm.

        show (= (+ (* t a) z) (* t a)) by +_z.

        show (= (* t a) (+ (* t a) z)) by eq_symm.
        show (= (* t a) (+ (* t a) (* t z))) by rewrite.
        show (= (* t (+ a z)) (+ (* t a) (* t z))) by rewrite.
    }
    goal [('b : nat) -> (= (* t (+ a 'b)) (+ (* t a) (* t 'b))) -> (= (* t (+ a (s 'b))) (+ (* t a) (* t (s 'b))))] {
        intro b : nat.
        intro ih : (= (* t (+ a b)) (+ (* t a) (* t b))).

        show (= (* t (+ a (s b))) (* t (+ a (s b)))) by eq_refl.

        show (= (+ a (s b)) (s (+ a b))) by +_s.
        show (= (* t (+ a (s b))) (* t (s (+ a b)))) by rewrite.

        show (= (* t (s (+ a b))) (+ t (* t (+ a b)))) by *_s.
        show (= (* t (+ a (s b))) (+ t (* t (+ a b)))) by rewrite.
        show (= (* t (+ a (s b))) (+ t (+ (* t a) (* t b)))) by rewrite.

        show (= (+ (* t a) (* t b)) (+ (* t b) (* t a))) by a_add_comm.
        show (= (* t (+ a (s b))) (+ t (+ (* t b) (* t a)))) by rewrite.

        show (= (+ (+ t (* t b)) (* t a)) (+ t (+ (* t b) (* t a)))) by a_add_assoc.
        show (= (+ t (+ (* t b) (* t a))) (+ (+ t (* t b)) (* t a))) by eq_symm.

        show (= (* t (s b)) (+ t (* t b))) by *_s.
        show (= (+ t (* t b)) (* t (s b))) by eq_symm.

        show (= (+ t (+ (* t b) (* t a))) (+ (* t (s b)) (* t a))) by rewrite.

        show (= (* t (+ a (s b))) (+ (* t (s b)) (* t a))) by rewrite.
        show (= (* t (+ a (s b))) (+ (* t (s b)) (* t a))) by rewrite.
        show (= (+ (* t (s b)) (* t a)) (+ (* t a) (* t (s b)))) by a_add_comm.
        show (= (* t (+ a (s b))) (+ (* t a) (* t (s b)))) by rewrite.
    }
}

lemma m_mul_assoc : [('a : nat) -> ('b : nat) -> ('c : nat) -> (= (* (* 'a 'b) 'c) (* 'a (* 'b 'c)))] {
    intro a : nat.
    intro b : nat.
    apply nat_ind.

    goal (= (* (* a b) z) (* a (* b z))) {
        show (= (* (* a b) z) z) by *_z.
        show (= (* b z) z) by *_z.
        show (= (* a (* b z)) (* a (* b z))) by eq_refl.
        show (= (* a (* b z)) (* a z)) by rewrite.
        show (= (* a z) z) by *_z.
        show (= (* a (* b z)) z) by rewrite.
        show (= z (* a (* b z))) by eq_symm.
        show (= (* (* a b) z) (* a (* b z))) by rewrite.
    }
    goal [('c : nat) -> (= (* (* a b) 'c) (* a (* b 'c))) -> (= (* (* a b) (s 'c)) (* a (* b (s 'c))))] {
        intro c : nat.
        intro ih : (= (* (* a b) c) (* a (* b c))).

        show (= (* (* a b) (s c)) (+ (* a b) (* (* a b) c))) by *_s.
        show (= (* (* a b) (s c)) (+ (* a b) (* a (* b c)))) by rewrite.

        show (= (* b (s c)) (+ b (* b c))) by *_s.

        show (= (* a (* b (s c))) (* a (* b (s c)))) by eq_refl.
        show (= (* a (* b (s c))) (* a (+ b (* b c)))) by rewrite.

        show (= (* a (+ b (* b c))) (+ (* a b) (* a (* b c)))) by m_mul_add.
        show (= (* a (* b (s c))) (+ (* a b) (* a (* b c)))) by rewrite.
        show (= (+ (* a b) (* a (* b c))) (* a (* b (s c)))) by eq_symm.
        show (= (* (* a b) (s c)) (* a (* b (s c)))) by rewrite.
    }
}

lemma m_succ_mul : [('a : nat) -> ('b : nat) -> (= (* (s 'a) 'b) (+ (* 'a 'b) 'b))] {
    intro a : nat.

    apply nat_ind.
    goal (= (* (s a) z) (+ (* a z) z)) {
        show (= (* (s a) z) z) by *_z.
        show (= (* a z) z) by *_z.
        show (= (+ (* a z) z) (* a z)) by +_z.
        show (= (+ (* a z) z) z) by rewrite.
        show (= z (+ (* a z) z)) by eq_symm.
        show (= (* (s a) z) (+ (* a z) z)) by rewrite.
    }
    goal [('b : nat) -> (= (* (s a) 'b) (+ (* a 'b) 'b)) -> (= (* (s a) (s 'b)) (+ (* a (s 'b)) (s 'b)))] {
         intro b : nat.
         intro h : (= (* (s a) b) (+ (* a b) b)).

         show (= (* (s a) (s b)) (+ (s a) (* (s a) b))) by *_s.
         show (= (* (s a) (s b)) (+ (s a) (+ (* a b) b))) by rewrite.
         show (= (+ a (s z)) (s a)) by t_add_succ_zero.
         show (= (s a) (+ a (s z))) by eq_symm.

         /* a'b' = (a + 1) + ab + b */
         show (= (* (s a) (s b)) (+ (+ a (s z)) (+ (* a b) b))) by rewrite.

         show (= (+ (+ a (s z)) (+ (* a b) b)) (+ a (+ (s z) (+ (* a b) b)))) by a_add_assoc.

         show (= (+ (+ (s z) b) (* a b)) (+ (s z) (+ b (* a b)))) by a_add_assoc.
         show (= (+ (s z) (+ b (* a b))) (+ (+ (s z) b) (* a b))) by eq_symm.

         show (= (* (s a) (s b)) (+ a (+ (s z) (+ (* a b) b)))) by rewrite.
         show (= (+ (* a b) b) (+ b (* a b))) by a_add_comm.
         show (= (* (s a) (s b)) (+ a (+ (s z) (+ b (* a b))))) by rewrite.

         /* a'b' = a + ((1 + b) + ab) */
         show (= (* (s a) (s b)) (+ a (+ (+ (s z) b) (* a b)))) by rewrite.

         show (= (+ (s z) b) (+ b (s z))) by a_add_comm.
         show (= (+ b (s z)) (s (+ b z))) by +_s.
         show (= (+ b z) b) by +_z.
         show (= (+ b (s z)) (s b)) by rewrite.
         show (= (+ (s z) b) (s b)) by rewrite.
         show (= (* (s a) (s b)) (+ a (+ (s b) (* a b)))) by rewrite.
         show (= (+ (s b) (* a b)) (+ (* a b) (s b))) by a_add_comm.

         /* a'b' = a + (ab + b') */
         show (= (* (s a) (s b)) (+ a (+ (* a b) (s b)))) by rewrite.

         show (= (+ (+ a (* a b)) (s b)) (+ a (+ (* a b) (s b)))) by a_add_assoc.
         show (= (+ a (+ (* a b) (s b))) (+ (+ a (* a b)) (s b))) by eq_symm.
         show (= (* (s a) (s b)) (+ (+ a (* a b)) (s b))) by rewrite.

         show (= (* a (s b)) (+ a (* a b))) by *_s.
         show (= (+ a (* a b)) (* a (s b))) by eq_symm.

         /* a' + b' = ab' + b' */
         show (= (* (s a) (s b)) (+ (* a (s b)) (s b))) by rewrite.
    }
}

lemma m_add_mul : [('a : nat) -> ('b : nat) -> ('t : nat) -> (= (* (+ 'a 'b) 't) (+ (* 'a 't) (* 'b 't)))] {
    intro a : nat.
    intro b : nat.
    apply nat_ind.
    goal (= (* (+ a b) z) (+ (* a z) (* b z))) {
        show (= (* (+ a b) z) z) by *_z.
        show (= (* a z) z) by *_z.
        show (= (* b z) z) by *_z.
        show (= (+ (* a z) (* b z)) (+ (* a z) (* b z))) by eq_refl.
        show (= (+ (* a z) (* b z)) (+ z (* b z))) by rewrite.
        show (= (+ (* a z) (* b z)) (+ z z)) by rewrite.
        show (= (+ z z) z) by +_z.
        show (= (+ (* a z) (* b z)) z) by rewrite.
        show (= z (+ (* a z) (* b z))) by eq_symm.
        show (= (* (+ a b) z) (+ (* a z) (* b z))) by rewrite.
    }
    goal [('t : nat) -> (= (* (+ a b) 't) (+ (* a 't) (* b 't))) -> (= (* (+ a b) (s 't)) (+ (* a (s 't)) (* b (s 't))))] {
         intro t : nat.
         intro h : (= (* (+ a b) t) (+ (* a t) (* b t))).

         show (= (* (+ a b) (s t)) (+ (+ a b) (* (+ a b) t))) by *_s.
         show (= (* (+ a b) (s t)) (+ (+ a b) (+ (* a t) (* b t)))) by rewrite.
         show (= (* (+ a b) (s t)) (+ (+ a b) (+ (* a t) (* b t)))) by rewrite.

         /* Sub-goal: Turn (+ b (* b t)) into (* b (s t)) */
         show (= (* (+ a b) (s t)) (+ (+ a b) (+ (* a t) (* b t)))) by rewrite.

         show (= (+ (+ a b) (+ (* a t) (* b t))) (+ a (+ b (+ (* a t) (* b t))))) by a_add_assoc.
         show (= (+ (* a t) (* b t)) (+ (* b t) (* a t))) by a_add_comm.
         show (= (+ (+ a b) (+ (* a t) (* b t))) (+ a (+ b (+ (* b t) (* a t))))) by rewrite.
         show (= (* (+ a b) (s t)) (+ a (+ b (+ (* b t) (* a t))))) by rewrite.

         show (= (+ (+ b (* b t)) (* a t)) (+ b (+ (* b t) (* a t)))) by a_add_assoc.
         show (= (+ b (+ (* b t) (* a t))) (+ (+ b (* b t)) (* a t))) by eq_symm.
         show (= (* (+ a b) (s t)) (+ a (+ (+ b (* b t)) (* a t)))) by rewrite.

         show (= (* b (s t)) (+ b (* b t))) by *_s.
         show (= (+ b (* b t)) (* b (s t))) by eq_symm.
         show (= (* (+ a b) (s t)) (+ a (+ (* b (s t)) (* a t)))) by rewrite.

         /* Sub-goal: Turn (+ a (* a t)) into (* a (s t)) */
         show (= (+ (* b (s t)) (* a t)) (+ (* a t) (* b (s t)))) by a_add_comm.
         show (= (* (+ a b) (s t)) (+ a (+ (* a t) (* b (s t))))) by rewrite.

         show (= (+ (+ a (* a t)) (* b (s t))) (+ a (+ (* a t) (* b (s t))))) by a_add_assoc.
         show (= (+ a (+ (* a t) (* b (s t)))) (+ (+ a (* a t)) (* b (s t)))) by eq_symm.
         show (= (* (+ a b) (s t)) (+ (+ a (* a t)) (* b (s t)))) by rewrite.
         show (= (* a (s t)) (+ a (* a t))) by *_s.
         show (= (+ a (* a t)) (* a (s t))) by eq_symm.
         show (= (* (+ a b) (s t)) (+ (* a (s t)) (* b (s t)))) by rewrite.
    }
}

lemma m_mul_comm : [('a : nat) -> ('b : nat) -> (= (* 'a 'b) (* 'b 'a))] {
    apply nat_ind.
    goal [('b : nat) -> (= (* z 'b) (* 'b z))] {
        intro b : nat.
        show (= (* z b) z) by m_zero_mul.
        show (= (* b z) z) by *_z.
        show (= z (* b z)) by eq_symm.
        show (= (* z b) (* b z)) by rewrite.
    }
    goal [('a : nat) -> [('b : nat) -> (= (* 'a 'b) (* 'b 'a))] -> [('b : nat) -> (= (* (s 'a) 'b) (* 'b (s 'a)))]] {
         intro a : nat.
         intro ih : [('b : nat) -> (= (* a 'b) (* 'b a))].
         intro b : nat.
         show (= (* (s a) b) (+ (* a b) b)) by m_succ_mul.
         show (= (* a b) (* b a)) by ih.
         show (= (* (s a) b) (+ (* b a) b)) by rewrite.
         show (= (+ (* b a) b) (+ b (* b a))) by a_add_comm.
         show (= (* (s a) b) (+ b (* b a))) by rewrite.
         show (= (* (s a) b) (+ b (* b a))) by rewrite.
         show (= (* b (s a)) (+ b (* b a))) by *_s.
         show (= (+ b (* b a)) (* b (s a))) by eq_symm.
         show (= (* (s a) b) (* b (s a))) by rewrite.
    }
}

lemma m_mul_left_comm : [('a : nat) -> ('b : nat) -> ('c : nat) -> (= (* 'a (* 'b 'c)) (* 'b (* 'a 'c)))] {
    intro a : nat.
    intro b : nat.
    intro c : nat.

    show (= (* (* a b) c) (* a (* b c))) by m_mul_assoc.
    show (= (* a (* b c)) (* (* a b) c)) by eq_symm.
    show (= (* a b) (* b a)) by m_mul_comm.
    show (= (* a (* b c)) (* (* b a) c)) by rewrite.

    show (= (* (* b a) c) (* b (* a c))) by m_mul_assoc.
    show (= (* a (* b c)) (* b (* a c))) by rewrite.
}


/***

Power world

***/

lemma p_zero_pow_zero : (= (^ z z) (s z)) {
    show (= (^ z z) (s z)) by ^_z.
}

lemma p_zero_pow_succ : [('m : nat) -> (= (^ z (s 'm)) z)] {
    intro m : nat.
    show (= (^ z (s m)) (* z (^ z m))) by ^_s.
    show (= (* z (^ z m)) z) by m_zero_mul.
    show (= (^ z (s m)) z) by rewrite.
}

lemma p_pow_one : [('a : nat) -> (= (^ 'a (s z)) 'a)] { }

lemma p_one_pow : [('m : nat) -> (= (^ (s z) 'm) (s z))] { }

lemma p_pow_add : [('a : nat) -> ('m : nat) -> ('n : nat) -> (= (^ 'a (+ 'm 'n)) (* (^ 'a 'm) (^ 'a 'n)))] { }

lemma p_mul_pow : [('a : nat) -> ('b : nat) -> ('n : nat) -> (= (^ (* 'a 'b) 'n) (* (^ 'a 'n) (^ 'b 'n)))] { }

lemma p_pow_pow : [('a : nat) -> ('m : nat) -> ('n : nat) -> (= (^ (^ 'a 'm) 'n) (^ 'a (* 'm 'n)))] { }

lemma p_add_squared : [('a : nat) -> ('b : nat) -> (= (^ (+ 'a 'b) (s (s z))) (+ (+ (^ 'a (s (s z))) (^ 'b (s (s z)))) (* (s (s z)) (* 'a 'b))))] { }

/***

    Function world

***/

empty : type.

lemma f_example1 : [('P : type) -> ('Q : type) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> 'Q] {
    intro P : type.
    intro Q : type.
    intro p : P.
    intro h : [P -> Q].
    construct q : Q = (h p) by h.
}

lemma f_example2 : [nat -> nat] {
    intro n : nat.
    construct _ : nat = (s n) by s.
}

lemma f_example3 : [('P : type) -> ('Q : type) -> ('R : type) -> ('S : type) -> ('T : type) -> ('U : type) ->
('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) ->
('l : ['T -> 'U]) -> 'U] { }

lemma f_example4 : [('P : type) -> ('Q : type) -> ('R : type) -> ('S : type) -> ('T : type) -> ('U : type) ->
('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) ->
('l : ['T -> 'U]) -> 'U] { }

lemma f_example5 : [('P : type) -> ('Q : type) -> ('p : 'P) -> ('q : 'Q) -> 'P] { }

lemma f_example6 : [('P : type) -> ('Q : type) -> ('R : type) ->
('f : ['P -> ('Q -> 'R)]) -> ('g : ['P -> 'Q]) -> ('p : 'P) -> 'R] { }

lemma f_example7 : [('P : type) -> ('Q : type) -> ('F : type) ->
('f : ['P -> 'Q]) -> ('g : ['Q -> 'F]) -> ('p : 'P) -> 'F] { }

lemma f_example8 : [('P : type) -> ('Q : type) ->
('f : ['P -> 'Q]) -> ('g : ['Q -> empty]) -> ('p : 'P) -> empty] { }

lemma f_example9 : [('A : type) -> ('B : type) -> ('C : type) -> ('D : type) -> ('E : type) -> ('F : type) ->
('G : type) -> ('H : type) -> ('I : type) -> ('J : type) -> ('K : type) -> ('L : type) ->
('f1 : ['A -> 'B]) -> ('f2 : ['B -> 'E]) -> ('f3 : ['E -> 'D]) -> ('f4 : ['D -> 'A]) ->
('f5 : ['E -> 'F]) -> ('f6 : ['F -> 'C]) -> ('f7 : ['B -> 'C]) -> ('f8 : ['F -> 'G]) ->
('f9 : ['G -> 'J]) -> ('f10 : ['I -> 'J]) -> ('f11 : ['J -> 'I]) -> ('f12 : ['I -> 'H]) ->
('f13 : ['E -> 'H]) -> ('f14 : ['H -> 'K]) -> ('f15 : ['I -> 'L]) -> ('a : 'A) -> 'L] { }


/***

    Proposition world

***/

lemma p_example1 : [('P : prop) -> ('Q : prop) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> 'Q] {
    intro P : prop.
    intro Q : prop.
    intro p : P.
    intro h : [P -> Q].
    construct q : Q = (h p) by h.
}

lemma p_imp_self : [('P : prop) -> ('p : 'P) -> 'P] {
    intro P : prop.
    intro p : P.
}

lemma p_maze : [('P : prop) -> ('Q : prop) -> ('R : prop) -> ('S : prop) -> ('T : prop) -> ('U : prop) ->
('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) ->
('l : ['T -> 'U]) -> 'U] { }

lemma p_example2 : [('P : prop) -> ('Q : prop) -> 'P -> ['Q -> 'P] ] { }

lemma p_example3 : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
                     ['P -> ['Q -> 'R]] ->
                     [['P -> 'Q] -> ['P -> 'R]]] { }

lemma imp_trans : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
                   ['P -> 'Q] -> ['Q -> 'R] -> ['P -> 'R]] {
    intro P : prop.
    intro Q : prop.
    intro R : prop.
    intro h1 : [P -> Q].
    intro h2 : [Q -> R].
    intro p : P.
    show Q by h1.
    show R by h2.
}

lemma contrapositive : [('P : prop) -> ('Q : prop) ->
                        ['P -> 'Q] ->
                        [(not 'Q) -> (not 'P)]] {
    intro P : prop.
    intro Q : prop.
    intro h : [P -> Q].
    intro h2 : [Q -> false].
    intro p : P.
    show Q by h.
    show false by h2.
}

lemma pw_example5 : [('A : prop) -> ('B : prop) -> ('C : prop) -> ('D : prop) -> ('E : prop) ->
                     ('F : prop) -> ('G : prop) -> ('H : prop) -> ('I : prop) -> ('J : prop) ->
                     ('K : prop) -> ('L : prop) ->
                     ('f1 : ['A -> 'B]) -> ('f2 : ['B -> 'E]) -> ('f3 : ['E -> 'D]) ->
                     ('f4 : ['D -> 'A]) -> ('f5 : ['E -> 'F]) -> ('f6 : ['F -> 'C]) ->
                     ('f7 : ['B -> 'C]) -> ('f8 : ['F -> 'G]) -> ('f9 : ['G -> 'J]) ->
                     ('f10 : ['I -> 'J]) -> ('f11 : ['J -> 'I]) -> ('f12 : ['I -> 'H]) ->
                     ('f13 : ['E -> 'H]) -> ('f14 : ['H -> 'K]) -> ('f15 : ['I -> 'L]) ->
                     'A -> 'L] { }


/***

    Advanced proposition world

***/

lemma apw_example1 : [('P : prop) -> ('Q : prop) -> 'P -> 'Q -> (and 'P 'Q)] { }

lemma and_symm : [('P : prop) -> ('Q : prop) -> (and 'P 'Q) -> (and 'Q 'P)] { }

lemma and_trans : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
                   (and 'P 'Q) -> (and 'Q 'R) -> (and 'P 'R)] { }

lemma iff_trans : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
                   (iff 'P 'Q) -> (iff 'Q 'R) -> (iff 'P 'R)] { }

lemma apw_example2 : [('P : prop) -> ('Q : prop) -> ('q : 'Q) -> (or 'P 'Q)] { }

lemma or_symm : [('P : prop) -> ('Q : prop) -> (or 'P 'Q) -> (or 'Q 'P)] { }

lemma and_or_distrib_left : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
                             (iff (and 'P (or 'Q 'R))
                                  (or (and 'P 'Q) (and 'P 'R)))] { }

lemma contra : [('P : prop) -> ('Q : prop) -> (and 'P (not 'P)) -> 'Q] { }

lemma contrapositive2 : [('P : prop) -> ('Q : prop) -> [(not 'Q) -> (not 'P)] -> ['P -> 'Q]] { }


/***

    Advanced addition world

***/

theorem succ_inj' : [('a : nat) -> ('b : nat) -> (= (s 'a) (s 'b)) -> (= 'a 'b)] { }

theorem succ_succ_inj : [('a : nat) -> ('b : nat) -> (= (s (s 'a)) (s (s 'b))) -> (= 'a 'b)] { }

theorem succ_eq_succ_of_eq : [('a : nat) -> ('b : nat) -> (= 'a 'b) -> (= (s 'a) (s 'b))] { }

theorem succ_eq_succ_iff : [('a : nat) -> ('b : nat) -> (iff (= (s 'a) (s 'b)) (= 'a 'b))] { }

theorem add_right_cancel : [('a : nat) -> ('t : nat) -> ('b : nat) -> (= (+ 'a 't) (+ 'b 't)) -> (= 'a 'b)] { }

theorem add_left_cancel : [('t : nat) -> ('a : nat) -> ('b : nat) -> (= (+ 't 'a) (+ 't 'b)) -> (= 'a 'b)] { }

theorem add_right_cancel_iff : [('t : nat) -> ('a : nat) -> ('b : nat) -> (iff (= (+ 'a 't) (+ 'b 't)) (= 'a 'b))] { }

lemma eq_zero_of_add_right_eq_self : [('a : nat) -> ('b : nat) -> (= (+ 'a 'b) 'a) -> (= 'b z)] { }

theorem succ_ne_zero : [('a : nat) -> (not (= (s 'a) z))] { }

lemma add_left_eq_zero : [('a : nat) -> ('b : nat) -> (= (+ 'a 'b) z) -> (= 'b z)] { }

lemma add_right_eq_zero : [('a : nat) -> ('b : nat) -> (= (+ 'a 'b) z) -> (= 'a z)] { }

theorem add_one_eq_succ : [('d : nat) -> (= (+ 'd (s z)) (s 'd))] { }

lemma ne_succ_self : [('n : nat) -> (not (= 'n (s 'n)))] { }

/***

    Advanced multiplication world

***/

theorem mul_pos : [('a : nat) -> ('b : nat) -> (not (= 'a z)) -> (not (= 'b z)) -> (not (= (* 'a 'b) z))] { }

theorem eq_zero_or_eq_zero_of_mul_eq_zero : [('a : nat) -> ('b : nat) -> (= (* 'a 'b) z) -> (or (= 'a z) (= 'b z))] { }

theorem mul_eq_zero_iff : [('a : nat) -> ('b : nat) -> (iff (= (* 'a 'b) z) (or (= 'a z) (= 'b z)))] { }

theorem mul_left_cancel : [('a : nat) -> ('b : nat) -> ('c : nat) -> (not (= 'a z)) -> (= (* 'a 'b) (* 'a 'c)) -> (= 'b 'c)] { }

/***

    Inequality world

***/

lemma one_add_le_self : [('x : nat) -> (leq 'x (+ (s z) 'x))] { }

lemma le_refl : [('x : nat) -> (leq 'x 'x)] { }

theorem le_succ : [('a : nat) -> ('b : nat) -> (leq 'a 'b) -> (leq 'a (s 'b))] { }

lemma zero_le : [('a : nat) -> (leq z 'a)] { }

theorem le_trans : [('a : nat) -> ('b : nat) -> ('c : nat) -> (leq 'a 'b) -> (leq 'b 'c) -> (leq 'a 'c)] { }

theorem le_antisymm : [('a : nat) -> ('b : nat) -> (leq 'a 'b) -> (leq 'b 'a) -> (= 'a 'b)] { }

lemma le_zero : [('a : nat) -> (leq 'a z) -> (= 'a z)] { }

lemma succ_le_succ : [('a : nat) -> ('b : nat) -> (leq 'a 'b) -> (leq (s 'a) (s 'b))] { }

theorem le_total : [('a : nat) -> ('b : nat) -> (or (leq 'a 'b) (leq 'b 'a))] { }

lemma le_succ_self : [('a : nat) -> (leq 'a (s 'a))] { }

theorem add_le_add_right : [('a : nat) -> ('b : nat) -> (leq 'a 'b) -> ('t : nat) -> (leq (+ 'a 't) (+ 'b 't))] { }

theorem le_of_succ_le_succ : [('a : nat) -> ('b : nat) -> (leq (s 'a) (s 'b)) -> (leq 'a 'b)] { }

theorem not_succ_le_self : [('a : nat) -> (not (leq (s 'a) 'a))] { }

theorem add_le_add_left : [('a : nat) -> ('b : nat) -> (leq 'a 'b) -> ('t : nat) -> (leq (+ 't 'a) (+ 't 'b))] { }

lemma lt_aux_one : [('a : nat) -> ('b : nat) -> (and (leq 'a 'b) (not (leq 'b 'a))) -> (leq (s 'a) 'b)] { }

lemma lt_aux_two : [('a : nat) -> ('b : nat) -> (leq (s 'a) 'b) -> (and (leq 'a 'b) (not (leq 'b 'a)))] { }

lemma lt_iff_succ_le : [('a : nat) -> ('b : nat) -> (iff (lt 'a 'b) (leq (s 'a) 'b))] { }
